package examples

import chisel3._
import chisel3.util._

/**
 * PWM LED Controller Module
 *
 * This module implements an efficient PWM controller for fading multiple LEDs in and out synchronously.
 * It uses parameterized clock frequency (in MHz), number of LED outputs, PWM resolution bits, and a simulation mode flag.
 * The design employs an 8-bit (default) PWM resolution for smoothness while maintaining resource efficiency.
 * A primary PWM counter and a prescaler counter (driven by PWM overflows) are used to generate fade ticks,
 * optimizing register bit width and power by reducing the size of the slow counter.
 * The fade step period is approximately 10 ms for visibility, with slight approximation due to prescaling.
 * In simulation mode, the prescaler is reduced to accelerate behavior observation without affecting synthesis.
 */
class PWMLED(freq: Int, numLEDs: Int = 1, pwmBits: Int = 8, simMode: Boolean = false) extends BaseModule {
  require(numLEDs > 0, "Number of LEDs must be positive")
  require(pwmBits >= 1 && pwmBits <= 16, "PWM bits must be between 1 and 16 for efficiency")

  val io = IO(new Bundle {
    val leds = Output(Vec(numLEDs, Bool()))
  })

  val pwmPeriod = 1 << pwmBits
  val pwmMax = (pwmPeriod - 1).U(pwmBits.W)
  val cyclesPerStep = freq * 10000L  // Cycles for ~10 ms at given frequency
  val prescalerDiv = if (simMode) 1000L else 1L  // Divider for simulation acceleration
  val prescalerMax = ((cyclesPerStep / pwmPeriod) / prescalerDiv).max(1L)

  // PWM counter: increments every cycle, wraps at pwmPeriod
  val (pwmValue, pwmWrap) = Counter(true.B, pwmPeriod)

  // Prescaler counter: increments on PWM wrap, generates tick for fade steps
  val (_, tick) = Counter(pwmWrap, prescalerMax.toInt)

  // Duty cycle register and direction (true for increasing)
  val dutyReg = RegInit(0.U(pwmBits.W))
  val direction = RegInit(true.B)

  // Update duty on each tick for fading effect
  when(tick) {
    when(direction) {
      when(dutyReg =/= pwmMax) {
        dutyReg := dutyReg + 1.U
      }.otherwise {
        direction := false.B
        dutyReg := dutyReg - 1.U
      }
    }.otherwise {
      when(dutyReg =/= 0.U) {
        dutyReg := dutyReg - 1.U
      }.otherwise {
        direction := true.B
        dutyReg := dutyReg + 1.U
      }
    }
  }

  // Comparator for PWM output signal
  val ledSignal = pwmValue < dutyReg

  // Assign the same signal to all LED outputs for synchronous behavior
  io.leds.foreach(_ := ledSignal)
}
