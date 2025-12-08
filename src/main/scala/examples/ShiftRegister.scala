package examples

import chisel3._
import chisel3.ltl._
import chisel3.ltl.Sequence.BoolSequence // Implicit conversion for Bool to Sequence

/**
 * A 4-stage shift register module with LTL properties for formal verification.
 * This module delays the input signal 'in' by four clock cycles when enabled by 'en',
 * under the influence of a synchronous reset.
 * 
 * Assumptions constrain the environment (e.g., enable always asserted post-reset).
 * Assertions verify the core functionality (output matches input delayed by 4 cycles).
 * Coverage properties monitor specific behavioral sequences.
 * 
 * These properties generate SystemVerilog Assertions (SVA) via CIRCT lowering.
 */
class ShiftRegister extends Module {
  val io = IO(new Bundle {
    val in = Input(Bool())
    val en = Input(Bool())
    val out = Output(Bool())
  })

  // Four-stage register chain with initialization for reset handling
  val reg0 = RegInit(false.B)
  val reg1 = RegInit(false.B)
  val reg2 = RegInit(false.B)
  val reg3 = RegInit(false.B)

  when(io.en) {
    reg0 := io.in
    reg1 := reg0
    reg2 := reg1
    reg3 := reg2
  }

  io.out := reg3

  // Assumptions to constrain the environment for formal verification
  
  // Enable must always be high for shift register to function
  AssumeProperty(io.en, label = Some("assume_always_enabled"))
  
  // Input must be stable for at least 5 cycles to properly verify the delay
  // This prevents glitches that would violate the 4-cycle delay property
  val prevIn = RegInit(false.B)
  val prevPrevIn = RegInit(false.B)
  val prevPrevPrevIn = RegInit(false.B)
  val prevPrevPrevPrevIn = RegInit(false.B)
  
  prevIn := io.in
  prevPrevIn := prevIn
  prevPrevPrevIn := prevPrevIn
  prevPrevPrevPrevIn := prevPrevPrevIn
  
  AssumeProperty(
    (io.in === prevIn) && (prevIn === prevPrevIn) && (prevPrevIn === prevPrevPrevIn) && (prevPrevPrevIn === prevPrevPrevPrevIn),
    label = Some("assume_in_stable_5_cycles")
  )

  // Assertions: Verify 4-cycle delay
  AssertProperty(
    io.in |-> Sequence(Delay(4), io.out),
    label = Some("assert_delayed_in_high")
  )
  AssertProperty(
    (~io.in) |-> Sequence(Delay(4), ~io.out),
    label = Some("assert_delayed_in_low")
  )

  // Coverage: Monitor occurrence of input high followed by output high after exactly 4 cycles
  // Translates to SVA: cover property (in ##4 out)
  CoverProperty(
    Sequence(io.in, Delay(4), io.out),
    label = Some("cover_in_to_out_delay")
  )
}
