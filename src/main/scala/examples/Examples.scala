package examples

import chisel3._
import chisel3.util._

/**
 * A simple 4-bit adder module.
 * This serves as a basic example for Verilog generation.
 * 
 * Inputs:
 *   - a: 4-bit unsigned input
 *   - b: 4-bit unsigned input
 * Outputs:
 *   - sum: 5-bit result (includes carry bit)
 */
class Adder extends BaseModule {
  val io = IO(new Bundle {
    val a   = Input(UInt(4.W))
    val b   = Input(UInt(4.W))
    val sum = Output(UInt(5.W))
  })
  
  // Perform addition
  io.sum := io.a +& io.b
}

/**
 * A simple counter module.
 * Demonstrates sequential logic.
 * 
 * Inputs:
 *   - enable: When high, counter increments
 * Outputs:
 *   - count: 8-bit counter value
 */
class Counter extends BaseModule {
  val io = IO(new Bundle {
    val enable = Input(Bool())
    val count  = Output(UInt(8.W))
  })
  
  val counter = RegInit(0.U(8.W))
  
  when(io.enable) {
    counter := counter + 1.U
  }
  
  io.count := counter
}

/**
 * A parameterized multiplexer.
 * Shows how to create reusable modules with parameters.
 * 
 * @param width: Bit width of the inputs/output
 */
class Mux2to1(width: Int = 8) extends BaseModule {
  val io = IO(new Bundle {
    val in0 = Input(UInt(width.W))
    val in1 = Input(UInt(width.W))
    val sel = Input(Bool())
    val out = Output(UInt(width.W))
  })
  
  io.out := Mux(io.sel, io.in1, io.in0)
}

/**
 * A simple ALU (Arithmetic Logic Unit).
 * Demonstrates combining multiple operations and control logic.
 * 
 * Operations:
 *   00: ADD
 *   01: SUB
 *   10: AND
 *   11: OR
 */
class SimpleALU extends BaseModule {
  val io = IO(new Bundle {
    val a      = Input(UInt(8.W))
    val b      = Input(UInt(8.W))
    val opcode = Input(UInt(2.W))
    val result = Output(UInt(8.W))
  })
  
  io.result := MuxLookup(io.opcode, 0.U)(Seq(
    0.U -> (io.a + io.b),
    1.U -> (io.a - io.b),
    2.U -> (io.a & io.b),
    3.U -> (io.a | io.b)
  ))
}
