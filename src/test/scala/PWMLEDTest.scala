package examples

import chisel3._
import chiseltest._
import org.scalatest.flatspec.AnyFlatSpec

/**
 * Testbench for PWMLED
 *
 * This testbench simulates the PWMLED module in simulation mode to accelerate timing
 * and generates a VCD file for waveform inspection. It uses a frequency of 50 MHz,
 * 1 LED output, and runs for a number of cycles sufficient to observe multiple fade steps.
 * For full cycle observation, the simulation duration can be extended as needed.
 */
class PWMLEDTest extends AnyFlatSpec with ChiselScalatestTester {
  "PWMLED" should "generate fading PWM signal" in {
    test(new PWMLED(50, 1, 8, true)).withAnnotations(Seq(WriteVcdAnnotation)) { dut =>
      // Disable timeout for long simulations
      dut.clock.setTimeout(0)
      // Simulate for 100,000 cycles to observe initial fading behavior in accelerated mode
      dut.clock.step(100000)
    }
  }
}
