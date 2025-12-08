// File: PWMLEDAXITest.scala
package examples

import chisel3._
import chiseltest._
import org.scalatest.flatspec.AnyFlatSpec

class PWMLEDAXITest extends AnyFlatSpec with ChiselScalatestTester {
  "PWMLEDAXI" should "allow AXI configuration and generate fading PWM with self-checking" in {
    test(new PWMLEDAXI(50, 1, 8, 12, 32, true))
      .withAnnotations(Seq(WriteVcdAnnotation)) { dut =>
      dut.clock.setTimeout(10000)
      
      // Initialize all AXI signals
      dut.io.axi.aw.valid.poke(false.B)
      dut.io.axi.aw.bits.addr.poke(0.U)
      dut.io.axi.aw.bits.prot.poke(0.U)
      dut.io.axi.w.valid.poke(false.B)
      dut.io.axi.w.bits.data.poke(0.U)
      dut.io.axi.w.bits.strb.poke(0.U)
      dut.io.axi.b.ready.poke(false.B)
      dut.io.axi.ar.valid.poke(false.B)
      dut.io.axi.ar.bits.addr.poke(0.U)
      dut.io.axi.ar.bits.prot.poke(0.U)
      dut.io.axi.r.ready.poke(false.B)
      dut.clock.step(1)

        // Helper to write via AXI
        def axiWrite(addr: Int, data: Int): Unit = {
          dut.io.axi.aw.valid.poke(true.B)
          dut.io.axi.aw.bits.addr.poke(addr.U)
          dut.io.axi.aw.bits.prot.poke(0.U)
          while (!dut.io.axi.aw.ready.peekBoolean()) { dut.clock.step(1) }
          dut.clock.step(1)
          dut.io.axi.aw.valid.poke(false.B)

          dut.io.axi.w.valid.poke(true.B)
          dut.io.axi.w.bits.data.poke(data.U)
          dut.io.axi.w.bits.strb.poke(0xF.U)  // Full word
          while (!dut.io.axi.w.ready.peekBoolean()) { dut.clock.step(1) }
          dut.clock.step(1)
          dut.io.axi.w.valid.poke(false.B)
          dut.clock.step(1)  // FSM: wData state processes, moves to wResp

          dut.io.axi.b.ready.poke(true.B)
          while (!dut.io.axi.b.valid.peekBoolean()) { dut.clock.step(1) }
          dut.clock.step(1)
          dut.io.axi.b.ready.poke(false.B)
        }

        // Helper to read via AXI
        def axiRead(addr: Int): BigInt = {
          dut.io.axi.ar.valid.poke(true.B)
          dut.io.axi.ar.bits.addr.poke(addr.U)
          dut.io.axi.ar.bits.prot.poke(0.U)
          while (!dut.io.axi.ar.ready.peekBoolean()) { dut.clock.step(1) }
          dut.clock.step(1)
          dut.io.axi.ar.valid.poke(false.B)

          dut.io.axi.r.ready.poke(true.B)
          while (!dut.io.axi.r.valid.peekBoolean()) { dut.clock.step(1) }
          val data = dut.io.axi.r.bits.data.peek()
          dut.clock.step(1)
          dut.io.axi.r.ready.poke(false.B)
          data.litValue
        }

        // Helper to check LED pulse width over one PWM period
        def checkLedPulseWidth(expectedDuty: Int): Unit = {
          // Step a full period first to ensure we start at a consistent phase
          for (_ <- 0 until 256) dut.clock.step(1)
          
          var onCount = 0
          for (_ <- 0 until 256) {  // pwmPeriod = 256
            if (dut.io.leds(0).peekBoolean()) onCount += 1
            dut.clock.step(1)
          }
          assert(onCount == expectedDuty, s"LED on count $onCount does not match expected duty $expectedDuty")
        }

        // Test: Set prescaler to 1 for faster auto-fade
        axiWrite(4, 1)
        assert(axiRead(4) == 1, "Prescaler readback failed")

        // Observe auto-fading: duty should increment from initial value
        val initialDuty = axiRead(0).toInt
        println(s"Initial duty: $initialDuty")
        
        // Let it fade for several steps
        dut.clock.step(256 * 10)  // 10 PWM periods = 10 ticks with prescaler=1
        val afterFadeDuty = axiRead(0).toInt
        println(s"After fading duty: $afterFadeDuty")
        assert(afterFadeDuty > initialDuty, s"Duty should have increased during auto-fade ($afterFadeDuty > $initialDuty)")

        // Test: Set duty manually to 128 (this disables auto-fade)
        axiWrite(0, 128)
        assert(axiRead(0) == 128, "Duty cycle readback after manual set failed")
        checkLedPulseWidth(128)

        // Test: advance and check duty remains stable (auto-fade disabled after write)
        dut.clock.step(1024)
        assert(axiRead(0) == 128, "Duty cycle should remain 128 after auto-fade disabled")
      }
  }
}