export const EXAMPLES = {
  "Empty": {
    chisel: `package examples

import chisel3._

class Empty extends Module {
  val io = IO(new Bundle {
  })
}
`
  },
  "PWMLEDAXI": {
    ebmcParams: {
      method: "ic3",
      bound: "10",
      layers: "layer$PWMLEDAXIVerification,layer$PWMLEDAXIVerification$Assert,layer$PWMLEDAXIVerification$Assume,layer$PWMLEDAXIVerification$Cover"
    },
    chisel: `package examples
import chisel3._
import chisel3.util._
import chisel3.layer.{Layer, Convention, LayerConfig}

// Define verification layers
object PWMLEDAXIVerification extends Layer(if (System.getProperty("chisel.layers.inline") == "true") LayerConfig.Inline else Convention.Bind.asInstanceOf[LayerConfig]) {
  object Assert extends Layer(if (System.getProperty("chisel.layers.inline") == "true") LayerConfig.Inline else Convention.Bind.asInstanceOf[LayerConfig])
  object Assume extends Layer(if (System.getProperty("chisel.layers.inline") == "true") LayerConfig.Inline else Convention.Bind.asInstanceOf[LayerConfig])
  object Cover extends Layer(if (System.getProperty("chisel.layers.inline") == "true") LayerConfig.Inline else Convention.Bind.asInstanceOf[LayerConfig])
  object Auxiliary extends Layer(if (System.getProperty("chisel.layers.inline") == "true") LayerConfig.Inline else Convention.Bind.asInstanceOf[LayerConfig])
}

// AXI4-Lite bundle definitions (master perspective)
class AXI4LiteAddressBundle(addrBits: Int) extends Bundle {
  val addr = UInt(addrBits.W)
  val prot = UInt(3.W)
}
class AXI4LiteWriteDataBundle(dataBits: Int) extends Bundle {
  val data = UInt(dataBits.W)
  val strb = UInt((dataBits / 8).W)
}
class AXI4LiteReadDataBundle(dataBits: Int) extends Bundle {
  val data = UInt(dataBits.W)
  val resp = UInt(2.W)
}
class AXI4LiteWriteResponseBundle extends Bundle {
  val resp = UInt(2.W)
}
class AXI4LiteMaster(addrBits: Int, dataBits: Int) extends Bundle {
  val aw = Decoupled(new AXI4LiteAddressBundle(addrBits))
  val w = Decoupled(new AXI4LiteWriteDataBundle(dataBits))
  val ar = Decoupled(new AXI4LiteAddressBundle(addrBits))
  val r = Flipped(Decoupled(new AXI4LiteReadDataBundle(dataBits)))
  val b = Flipped(Decoupled(new AXI4LiteWriteResponseBundle))
}

// PWM LED with AXI4-Lite wrapper (original model)
class PWMLEDAXI(freq: Int, numLEDs: Int = 1, pwmBits: Int = 8, addrBits: Int = 12, dataBits: Int = 32, simMode: Boolean = false, prescalerBits: Int = 32) extends BaseModule {
  require(numLEDs > 0, "Number of LEDs must be positive")
  require(pwmBits >= 1 && pwmBits <= 16, "PWM bits must be between 1 and 16 for efficiency")
  val io = IO(new Bundle {
    val axi = Flipped(new AXI4LiteMaster(addrBits, dataBits)) // Slave perspective
    val leds = Output(Vec(numLEDs, Bool()))
  })
  val pwmPeriod = 1 << pwmBits
  val pwmMax = (pwmPeriod - 1).U(pwmBits.W)
  val cyclesPerStepDefault = freq * 10000L // ~10 ms
  val prescalerDiv = if (simMode) 1000L else 1L
  val rawPrescalerMax = ((cyclesPerStepDefault / pwmPeriod) / prescalerDiv).max(1L)
  // Clamp default value to fit in prescalerBits (for formal verification abstraction)
  val prescalerMaxDefault = if (prescalerBits < 62) rawPrescalerMax.min((1L << prescalerBits) - 1) else rawPrescalerMax
  // PWM counter
  val (pwmValue, pwmWrap) = Counter(true.B, pwmPeriod)
  // Configurable prescaler register (runtime adjustable via AXI)
  val prescalerReg = RegInit(prescalerMaxDefault.U(prescalerBits.W)) // Wide enough for large values
  // Manual counter for dynamic prescaler max
  val prescalerCount = RegInit(0.U(prescalerBits.W))
  val tick = pwmWrap && (prescalerCount === prescalerReg - 1.U) && (prescalerReg =/= 0.U) // Avoid stall on 0
  when(pwmWrap && (prescalerReg =/= 0.U)) {
    prescalerCount := Mux(prescalerCount === prescalerReg - 1.U, 0.U, prescalerCount + 1.U)
  }
  // Duty cycle and direction
  val dutyReg = RegInit(0.U(pwmBits.W))
  val direction = RegInit(true.B)
  // Automatic fading logic (can be overridden via AXI duty write)
  val autoFadeEnable = RegInit(true.B) // Could add register for this if needed
  when(tick && autoFadeEnable) {
    when(direction) {
      when(dutyReg =/= pwmMax) {
        dutyReg := dutyReg + 1.U
      }.otherwise {
        direction := false.B
      }
    }.otherwise {
      when(dutyReg =/= 0.U) {
        dutyReg := dutyReg - 1.U
      }.otherwise {
        direction := true.B
      }
    }
  }
  // PWM output
  val ledSignal = pwmValue < dutyReg
  io.leds.foreach(_ := ledSignal)
  // AXI4-Lite slave logic (simple single-transaction handler for efficiency)
  val OKAY = 0.U(2.W)
  val SLVERR = 2.U(2.W)
  // Write handling
  val wIdle :: wAddr :: wData :: wResp :: Nil = Enum(4)
  val wState = RegInit(wIdle)
  val wAddrReg = RegInit(0.U(addrBits.W))
  val wDataReg = RegInit(0.U(dataBits.W))
  val wStrbReg = RegInit(0.U((dataBits / 8).W))
  val wRespReg = RegInit(OKAY) // For dynamic resp
  io.axi.aw.ready := wState === wIdle
  io.axi.w.ready := wState === wAddr // Adjusted to accept w after aw (standard AXI allows concurrent, but sequential for simplicity)
  io.axi.b.valid := wState === wResp
  io.axi.b.bits.resp := wRespReg
  switch(wState) {
    is(wIdle) {
      when(io.axi.aw.valid && io.axi.aw.ready) {
        wAddrReg := io.axi.aw.bits.addr
        wState := wAddr
      }
    }
    is(wAddr) {
      when(io.axi.w.valid && io.axi.w.ready) {
        wDataReg := io.axi.w.bits.data
        wStrbReg := io.axi.w.bits.strb
        wState := wData
      }
    }
    is(wData) {
      // Apply write (ignore strb for simplicity, assume full word)
      wRespReg := SLVERR
      when(wAddrReg === 0.U) {
        dutyReg := wDataReg(pwmBits - 1, 0)
        autoFadeEnable := false.B
        wRespReg := OKAY
      } .elsewhen(wAddrReg === 4.U) {
        prescalerReg := wDataReg(prescalerBits - 1, 0)
        prescalerCount := 0.U
        wRespReg := OKAY
      }
      wState := wResp
    }
    is(wResp) {
      when(io.axi.b.ready && io.axi.b.valid) {
        wState := wIdle
      }
    }
  }
  // Read handling
  val rIdle :: rDataState :: Nil = Enum(2)
  val rState = RegInit(rIdle)
  val rAddrReg = RegInit(0.U(addrBits.W))
  val rDataReg = RegInit(0.U(dataBits.W))
  val rRespReg = RegInit(OKAY) // For dynamic resp
  io.axi.ar.ready := rState === rIdle
  io.axi.r.valid := rState === rDataState
  io.axi.r.bits.resp := rRespReg
  io.axi.r.bits.data := rDataReg
  switch(rState) {
    is(rIdle) {
      when(io.axi.ar.valid && io.axi.ar.ready) {
        rAddrReg := io.axi.ar.bits.addr
        rRespReg := SLVERR
        rDataReg := 0.U
        when(io.axi.ar.bits.addr === 0.U) {
          rDataReg := dutyReg
          rRespReg := OKAY
        } .elsewhen(io.axi.ar.bits.addr === 4.U) {
          rDataReg := prescalerReg
          rRespReg := OKAY
        }
        rState := rDataState
      }
    }
    is(rDataState) {
      when(io.axi.r.ready && io.axi.r.valid) {
        rState := rIdle
      }
    }
  }
  // Formal verification with LTL/SVA properties using Chisel 6 layers
  import chisel3.ltl._
  import chisel3.ltl.Sequence.BoolSequence
  chisel3.layer.block(PWMLEDAXIVerification) {
    val pwmPeriodU = pwmPeriod.U(64.W)
    val rank_tick = Mux(prescalerReg === 0.U, 0.U(64.W), ((prescalerReg - prescalerCount - 1.U).pad(64) * pwmPeriodU) + (pwmPeriodU - pwmValue.pad(64)) - 1.U(64.W))
    val fade_rank = Mux(autoFadeEnable, Mux(direction, pwmMax - dutyReg, dutyReg), 0.U(pwmBits.W))
    val interference = (wState === wData && (wAddrReg === 0.U || wAddrReg === 4.U))
    val prescaler_interference = (wState === wData && wAddrReg === 4.U)
    val duty_interference = (wState === wData && wAddrReg === 0.U)
    def always(p: Property): Property = Property.not(Property.eventually(Property.not(p)))
    chisel3.layer.block(PWMLEDAXIVerification.Assert) {
      // PWM output correctness
      AssertProperty(ledSignal === (pwmValue < dutyReg), label = Some("pwm_output_correct"))
      // Assertions for output channels (slave behavior: B, R)
      // For B channel - valid stability (non-overlapping: if valid&&!ready now, then valid next cycle)
      AssertProperty((io.axi.b.valid && !io.axi.b.ready) |-> Sequence(Delay(1), io.axi.b.valid), label = Some("b_valid_stable"))
      // For B channel - resp valid
      AssertProperty(!io.axi.b.valid || (io.axi.b.bits.resp === OKAY || io.axi.b.bits.resp === SLVERR), label = Some("b_resp_valid"))
      // For R channel - valid stability
      AssertProperty((io.axi.r.valid && !io.axi.r.ready) |-> Sequence(Delay(1), io.axi.r.valid), label = Some("r_valid_stable"))
      // For R channel - data stability (if valid&&!ready now, data next cycle matches data now)
      AssertProperty((io.axi.r.valid && !io.axi.r.ready) |-> Sequence(Delay(1), io.axi.r.bits.data === RegNext(io.axi.r.bits.data)), label = Some("r_data_stable"))
      // For R channel - resp valid
      AssertProperty(!io.axi.r.valid || (io.axi.r.bits.resp === OKAY || io.axi.r.bits.resp === SLVERR), label = Some("r_resp_valid"))
      // Functional correctness for writes (same cycle: if completing write now, register updated now)
      AssertProperty((io.axi.b.valid && io.axi.b.ready && wAddrReg === 0.U) |-> (dutyReg === wDataReg(pwmBits - 1, 0)), label = Some("write_duty_correct"))
      AssertProperty((io.axi.b.valid && io.axi.b.ready && wAddrReg === 0.U) |-> !autoFadeEnable, label = Some("write_disable_fade"))
      AssertProperty((io.axi.b.valid && io.axi.b.ready && wAddrReg === 4.U) |-> (prescalerReg === wDataReg(prescalerBits - 1, 0)), label = Some("write_prescaler_correct"))
      // Functional correctness for reads (same cycle invariant)
      AssertProperty((io.axi.ar.valid && io.axi.ar.ready && io.axi.ar.bits.addr === 0.U) |-> Sequence(Delay(1), io.axi.r.bits.data === RegNext(dutyReg).pad(dataBits)), label = Some("read_duty_correct"))
      AssertProperty((io.axi.ar.valid && io.axi.ar.ready && io.axi.ar.bits.addr === 4.U) |-> Sequence(Delay(1), io.axi.r.bits.data === RegNext(prescalerReg).pad(dataBits)), label = Some("read_prescaler_correct"))
      // Fading logic inductive invariants (non-overlapping: if condition now, effect next cycle)
      AssertProperty((tick && autoFadeEnable && direction && (dutyReg =/= pwmMax)) &&
                    !duty_interference |-> Sequence(Delay(1), dutyReg === (RegNext(dutyReg) + 1.U)), label = Some("fade_up_increment"))
      AssertProperty((tick && autoFadeEnable && direction && (dutyReg === pwmMax)) |-> Sequence(Delay(1), !direction), label = Some("fade_up_reverse"))
      AssertProperty((tick && autoFadeEnable && !direction && (dutyReg =/= 0.U)) &&
                    !duty_interference |-> Sequence(Delay(1), dutyReg === (RegNext(dutyReg) - 1.U)), label = Some("fade_down_decrement"))
      AssertProperty((tick && autoFadeEnable && !direction && (dutyReg === 0.U)) |-> Sequence(Delay(1), direction), label = Some("fade_down_reverse"))
      // Helper invariants for induction
      AssertProperty(dutyReg >= 0.U && dutyReg <= pwmMax, label = Some("duty_bounds")) // Boundedness
      // Split monotonic properties to avoid vacuity and strengthen inductiveness
      AssertProperty(autoFadeEnable && direction && (dutyReg < pwmMax) && tick && !duty_interference |-> Sequence(Delay(1), dutyReg === RegNext(dutyReg) + 1.U), label = Some("monotonic_up_increment_on_tick"))
      AssertProperty(autoFadeEnable && direction && (dutyReg < pwmMax) && !tick && !duty_interference |-> Sequence(Delay(1), dutyReg === RegNext(dutyReg)), label = Some("monotonic_up_nochange_no_tick"))
      AssertProperty(autoFadeEnable && !direction && (dutyReg > 0.U) && tick && !duty_interference |-> Sequence(Delay(1), dutyReg === RegNext(dutyReg) - 1.U), label = Some("monotonic_down_decrement_on_tick"))
      AssertProperty(autoFadeEnable && !direction && (dutyReg > 0.U) && !tick && !duty_interference |-> Sequence(Delay(1), dutyReg === RegNext(dutyReg)), label = Some("monotonic_down_nochange_no_tick"))
      AssertProperty(Property.not(Property.eventually(Property.and(Sequence(autoFadeEnable && direction), Property.and(always(Sequence(!interference)), Property.not(Property.eventually(Sequence(dutyReg === pwmMax))))))), label = Some("reach_max_eventual")) // Conditional reachability
      AssertProperty(Property.not(Property.eventually(Property.and(Sequence(autoFadeEnable && !direction), Property.and(always(Sequence(!interference)), Property.not(Property.eventually(Sequence(dutyReg === 0.U))))))), label = Some("reach_zero_eventual")) // Conditional reachability down
      AssertProperty(Property.not(Property.eventually(Property.and(Sequence(autoFadeEnable && dutyReg === 0.U && direction), Property.and(always(Sequence(!interference)), Property.not(Property.eventually(Sequence(dutyReg === 0.U && direction))))))), label = Some("full_cycle_eventual")) // Conditional periodicity
      // Completeness properties (filling gaps)
      AssertProperty(pwmValue < pwmPeriod.U, label = Some("pwm_value_bounded")) // PWM counter bounds
      AssertProperty(Sequence(Delay(1), pwmValue === Mux(RegNext(pwmWrap), 0.U, RegNext(pwmValue) + 1.U)), label = Some("pwm_increment_correct")) // PWM progression
      AssertProperty(pwmWrap |-> (pwmValue === (pwmPeriod - 1).U), label = Some("pwm_wrap_correct")) // Wrap condition
      AssertProperty(prescalerReg === 0.U || prescalerCount < prescalerReg, label = Some("prescaler_bounded")) // Prescaler counter bounds, relaxed for zero
      // Split prescaler progression for write and no-write cases
      AssertProperty((wState === wData && wAddrReg === 4.U) |-> Sequence(Delay(1), prescalerCount === 0.U && prescalerReg === RegNext(wDataReg(prescalerBits - 1, 0))), label = Some("prescaler_write_reset"))
      AssertProperty(!(wState === wData && wAddrReg === 4.U) && (pwmWrap && (prescalerReg =/= 0.U)) |-> Sequence(Delay(1), prescalerCount === Mux(RegNext(prescalerCount) === RegNext(prescalerReg) - 1.U, 0.U, RegNext(prescalerCount) + 1.U)), label = Some("prescaler_increment_correct"))
      AssertProperty(!(wState === wData && wAddrReg === 4.U) && !(pwmWrap && (prescalerReg =/= 0.U)) |-> Sequence(Delay(1), prescalerCount === RegNext(prescalerCount)), label = Some("prescaler_nochange"))
      AssertProperty(tick |-> (prescalerCount === prescalerReg - 1.U && pwmWrap && prescalerReg =/= 0.U), label = Some("tick_generation_correct")) // Tick condition
      AssertProperty(prescalerReg === 0.U |-> !tick, label = Some("no_tick_on_zero_prescaler")) // Stall on zero
      AssertProperty(Property.not(Property.eventually(Property.and(Sequence(prescalerReg =/= 0.U), Property.and(always(Sequence(!prescaler_interference)), Property.not(Property.eventually(Sequence(tick))))))), label = Some("eventual_tick_progress")) // Conditional liveness
      AssertProperty(io.leds.forall(led => led === ledSignal), label = Some("led_uniformity")) // Multi-LED consistency
      AssertProperty((io.axi.b.valid && (wAddrReg =/= 0.U && wAddrReg =/= 4.U)) |-> (io.axi.b.bits.resp === SLVERR), label = Some("write_invalid_slverr")) // Error handling write
      AssertProperty((io.axi.r.valid && (rAddrReg =/= 0.U && rAddrReg =/= 4.U)) |-> (io.axi.r.bits.resp === SLVERR), label = Some("read_invalid_slverr")) // Error handling read
      // Smaller liveness properties to support proof of eventual_tick_progress
      AssertProperty(Property.eventually(Sequence(pwmWrap)), label = Some("eventual_pwm_wrap"))
      AssertProperty(Sequence(prescalerReg =/= 0.U && !prescaler_interference) |-> Property.eventually(Sequence(prescalerCount === prescalerReg - 1.U)), label = Some("eventual_prescaler_max"))
      // Ranking function properties for tick liveness (safety reductions)
      AssertProperty(prescalerReg =/= 0.U |-> rank_tick >= 0.U(64.W), label = Some("rank_tick_nonneg"))
      AssertProperty((prescalerReg =/= 0.U && !prescaler_interference && rank_tick > 0.U(64.W)) |-> Sequence(Delay(1), rank_tick === RegNext(rank_tick) - 1.U(64.W)), label = Some("rank_tick_decrease"))
      AssertProperty(tick |-> (prescalerReg =/= 0.U && rank_tick === 0.U(64.W)), label = Some("tick_implies_rank_zero"))
      AssertProperty((prescalerReg =/= 0.U && rank_tick === 0.U(64.W)) |-> tick, label = Some("rank_zero_implies_tick"))
      // Ranking function properties for fade liveness
      AssertProperty(autoFadeEnable |-> (fade_rank >= 0.U && fade_rank <= pwmMax), label = Some("fade_rank_bounded"))
      AssertProperty((autoFadeEnable && (fade_rank > 0.U) && tick && !duty_interference) |-> Sequence(Delay(1), fade_rank === RegNext(fade_rank) - 1.U), label = Some("fade_rank_decrease_on_tick"))
      AssertProperty((autoFadeEnable && (fade_rank > 0.U) && !tick && !duty_interference) |-> Sequence(Delay(1), fade_rank === RegNext(fade_rank)), label = Some("fade_rank_stable_no_tick"))
      AssertProperty((autoFadeEnable && direction && fade_rank === 0.U) |-> (dutyReg === pwmMax), label = Some("fade_rank_zero_up"))
      AssertProperty((autoFadeEnable && !direction && fade_rank === 0.U) |-> (dutyReg === 0.U), label = Some("fade_rank_zero_down"))
      // Added completeness checks for gaps
      AssertProperty( (!autoFadeEnable && !duty_interference) |-> Sequence(Delay(1), dutyReg === RegNext(dutyReg)), label = Some("duty_stable_when_disabled"))
      AssertProperty( !((tick && autoFadeEnable && direction && (dutyReg === pwmMax)) || (tick && autoFadeEnable && !direction && (dutyReg === 0.U))) |-> Sequence(Delay(1), direction === RegNext(direction)), label = Some("direction_stable"))
      AssertProperty( (prescalerReg === 0.U && !prescaler_interference) |-> Sequence(Delay(1), prescalerCount === RegNext(prescalerCount)), label = Some("prescaler_count_stable_when_zero"))
      AssertProperty( (wState === wAddr && io.axi.w.valid) |-> Sequence(Delay(1), wStrbReg === RegNext(io.axi.w.bits.strb)), label = Some("wstrb_storage_correct"))
    }
    chisel3.layer.block(PWMLEDAXIVerification.Assume) {
      // Assumptions for input channels (master behavior: AW, AR, W)
      // For AW channel - valid stability
      AssumeProperty((io.axi.aw.valid && !io.axi.aw.ready) |-> Sequence(Delay(1), io.axi.aw.valid), label = Some("aw_valid_stable"))
      // For AW channel - addr stability
      AssumeProperty((io.axi.aw.valid && !io.axi.aw.ready) |-> Sequence(Delay(1), io.axi.aw.bits.addr === RegNext(io.axi.aw.bits.addr)), label = Some("aw_addr_stable"))
      // For AW channel - prot stability
      AssumeProperty((io.axi.aw.valid && !io.axi.aw.ready) |-> Sequence(Delay(1), io.axi.aw.bits.prot === RegNext(io.axi.aw.bits.prot)), label = Some("aw_prot_stable"))
      // For W channel - valid stability
      AssumeProperty((io.axi.w.valid && !io.axi.w.ready) |-> Sequence(Delay(1), io.axi.w.valid), label = Some("w_valid_stable"))
      // For W channel - data stability
      AssumeProperty((io.axi.w.valid && !io.axi.w.ready) |-> Sequence(Delay(1), io.axi.w.bits.data === RegNext(io.axi.w.bits.data)), label = Some("w_data_stable"))
      // For W channel - strb stability
      AssumeProperty((io.axi.w.valid && !io.axi.w.ready) |-> Sequence(Delay(1), io.axi.w.bits.strb === RegNext(io.axi.w.bits.strb)), label = Some("w_strb_stable"))
      // For AR channel - valid stability
      AssumeProperty((io.axi.ar.valid && !io.axi.ar.ready) |-> Sequence(Delay(1), io.axi.ar.valid), label = Some("ar_valid_stable"))
      // For AR channel - addr stability
      AssumeProperty((io.axi.ar.valid && !io.axi.ar.ready) |-> Sequence(Delay(1), io.axi.ar.bits.addr === RegNext(io.axi.ar.bits.addr)), label = Some("ar_addr_stable"))
      // For AR channel - prot stability
      AssumeProperty((io.axi.ar.valid && !io.axi.ar.ready) |-> Sequence(Delay(1), io.axi.ar.bits.prot === RegNext(io.axi.ar.bits.prot)), label = Some("ar_prot_stable"))
      // Fairness constraints for AXI interface to prevent stalls
      AssumeProperty(io.axi.b.valid |-> Property.eventually(Sequence(io.axi.b.ready)), label = Some("fair_b_ready"))
      AssumeProperty(io.axi.r.valid |-> Property.eventually(Sequence(io.axi.r.ready)), label = Some("fair_r_ready"))
      // Added fairness assumption for liveness properties
      AssumeProperty(Property.eventually(Sequence(io.axi.aw.valid)), label = Some("fair_aw_valid"))
    }
    chisel3.layer.block(PWMLEDAXIVerification.Cover) {
      // Coverage properties for key states
      CoverProperty(wState === wResp, label = Some("cover_write_response"))
      CoverProperty(rState === rDataState, label = Some("cover_read_data"))
      CoverProperty(tick, label = Some("cover_tick"))
      CoverProperty(dutyReg === pwmMax, label = Some("cover_duty_max"))
      CoverProperty(dutyReg === 0.U, label = Some("cover_duty_zero"))
      // Additional coverage for interesting scenarios to support non-vacuity and comprehensive verification
      CoverProperty(pwmWrap, label = Some("cover_pwm_wrap")) // PWM counter wrap-around
      CoverProperty(prescalerCount === prescalerReg - 1.U && prescalerReg =/= 0.U, label = Some("cover_prescaler_max_reached")) // Prescaler at maximum
      CoverProperty(tick && autoFadeEnable && direction && dutyReg =/= pwmMax, label = Some("cover_fade_up_increment")) // Fading up increment case
      CoverProperty(tick && autoFadeEnable && !direction && dutyReg =/= 0.U, label = Some("cover_fade_down_decrement")) // Fading down decrement case
      CoverProperty(tick && autoFadeEnable && direction && dutyReg === pwmMax, label = Some("cover_fade_up_reverse")) // Direction reverse at max
      CoverProperty(tick && autoFadeEnable && !direction && dutyReg === 0.U, label = Some("cover_fade_down_reverse")) // Direction reverse at min
      CoverProperty(wState === wData && wAddrReg === 0.U, label = Some("cover_duty_write")) // Write to duty register
      CoverProperty(wState === wData && wAddrReg === 4.U, label = Some("cover_prescaler_write")) // Write to prescaler register
      CoverProperty(wState === wData && (wAddrReg =/= 0.U && wAddrReg =/= 4.U), label = Some("cover_invalid_write_addr")) // Invalid write address (error case)
      CoverProperty(rState === rDataState && rAddrReg === 0.U, label = Some("cover_duty_read")) // Read from duty register
      CoverProperty(rState === rDataState && rAddrReg === 4.U, label = Some("cover_prescaler_read")) // Read from prescaler register
      CoverProperty(rState === rDataState && (rAddrReg =/= 0.U && rAddrReg =/= 4.U), label = Some("cover_invalid_read_addr")) // Invalid read address (error case)
      CoverProperty(!autoFadeEnable, label = Some("cover_auto_fade_disabled")) // Auto-fade disabled via write
      CoverProperty(prescalerReg === 0.U, label = Some("cover_prescaler_zero")) // Prescaler set to zero (stall case)
      CoverProperty(duty_interference && autoFadeEnable, label = Some("cover_duty_interference_during_fade")) // Write interference during active fade
      CoverProperty(prescaler_interference, label = Some("cover_prescaler_interference")) // Prescaler write interference
      CoverProperty(ledSignal === true.B, label = Some("cover_led_on")) // LED signal active
      CoverProperty(ledSignal === false.B, label = Some("cover_led_off")) // LED signal inactive
      CoverProperty(autoFadeEnable && direction && fade_rank > 0.U, label = Some("cover_fade_up_progress")) // Fade up in progress (for liveness starting point)
      CoverProperty(autoFadeEnable && !direction && fade_rank > 0.U, label = Some("cover_fade_down_progress")) // Fade down in progress (for liveness starting point)
      CoverProperty(prescalerReg =/= 0.U && rank_tick > 0.U, label = Some("cover_tick_progress")) // Tick ranking function in progress (for liveness)
      CoverProperty(autoFadeEnable && dutyReg === 0.U && direction, label = Some("cover_cycle_start")) // Start of a new fade cycle
    }
  }
}

// Abstracted version for verification (bounded prescaler)
class AbstractedPWMLEDAXI(freq: Int, numLEDs: Int = 1, pwmBits: Int = 8, addrBits: Int = 12, dataBits: Int = 32, simMode: Boolean = false) extends PWMLEDAXI(freq, numLEDs, pwmBits, addrBits, dataBits, simMode, prescalerBits = 4) { // Bound to 4 bits for <16
}
`
  },
  "Adder": {
    chisel: `package examples

import chisel3._

class Adder extends Module {
  val io = IO(new Bundle {
    val a   = Input(UInt(4.W))
    val b   = Input(UInt(4.W))
    val sum = Output(UInt(5.W))
  })
  
  io.sum := io.a +& io.b
}
`
  }
};
