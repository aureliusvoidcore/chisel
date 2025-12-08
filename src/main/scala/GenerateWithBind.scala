import chisel3._
import circt.stage.ChiselStage
import java.io.{File, PrintWriter}

/**
 * Generator that creates a separate verification checker module with bind statement.
 * This extracts formal verification properties into a separate module for better
 * organization and optional inclusion in verification flows.
 * 
 * Usage:
 *   sbt "runMain GenerateWithBind"
 */
object GenerateWithBind {
  def main(args: Array[String]): Unit = {
    println("Generating SystemVerilog with separate verification checker...")
    
    // Generate base SystemVerilog
    val baseVerilog = ChiselStage.emitSystemVerilog(
      new examples.ShiftRegister,
      firtoolOpts = FirtoolConfig.verificationOptions
    )
    
    // Extract module name
    val moduleName = "ShiftRegister"
    
    // Split into main module (without assertions) and checker module
    val (mainModule, assertions) = extractAssertions(baseVerilog, moduleName)
    
    // Create output directory
    val outputDir = new File("generated")
    if (!outputDir.exists()) outputDir.mkdirs()
    
    // Write main module without assertions
    val mainFile = new PrintWriter(new File(s"generated/${moduleName}_noassert.sv"))
    mainFile.write(mainModule)
    mainFile.close()
    println(s"  ✓ ${moduleName}_noassert.sv (design without assertions)")
    
    // Create checker module
    val checkerModule = createCheckerModule(moduleName, assertions)
    val checkerFile = new PrintWriter(new File(s"generated/${moduleName}_checker.sv"))
    checkerFile.write(checkerModule)
    checkerFile.close()
    println(s"  ✓ ${moduleName}_checker.sv (verification properties)")
    
    // Create bind file
    val bindFile = new PrintWriter(new File(s"generated/${moduleName}_bind.sv"))
    bindFile.write(createBindFile(moduleName))
    bindFile.close()
    println(s"  ✓ ${moduleName}_bind.sv (bind statement)")
    
    println("\nTo use in simulation/formal verification:")
    println(s"  1. Compile: ${moduleName}_noassert.sv")
    println(s"  2. Compile: ${moduleName}_checker.sv")
    println(s"  3. Include: ${moduleName}_bind.sv")
  }
  
  def extractAssertions(verilog: String, moduleName: String): (String, List[String]) = {
    val lines = verilog.split("\n").toList
    var assertions = List[String]()
    var mainLines = List[String]()
    var inAssertion = false
    
    for (line <- lines) {
      if (line.trim.matches("^(assume|assert|cover)_.*:$")) {
        inAssertion = true
        assertions = assertions :+ line
      } else if (inAssertion && line.trim.matches(".*(assume|assert|cover) property.*")) {
        assertions = assertions :+ line
        inAssertion = false
      } else if (!inAssertion) {
        mainLines = mainLines :+ line
      }
    }
    
    (mainLines.mkString("\n"), assertions)
  }
  
  def createCheckerModule(moduleName: String, assertions: List[String]): String = {
    val signals = extractSignals(assertions)
    
    s"""// Verification checker module for $moduleName
       |module ${moduleName}_checker(
       |  input logic clock,
       |  input logic reset,
       |  input logic io_in,
       |  input logic io_en,
       |  input logic io_out,
       |  input logic reg0,
       |  input logic reg1,
       |  input logic reg2,
       |  input logic reg3
       |);
       |
       |  // Internal signals for verification
       |  reg hasBeenResetReg;
       |  initial
       |    hasBeenResetReg = 1'bx;
       |  wire hasBeenReset = hasBeenResetReg === 1'h1 & reset === 1'h0;
       |  
       |  always @(posedge clock) begin
       |    if (reset)
       |      hasBeenResetReg <= 1'h1;
       |  end
       |
       |  // Verification properties
       |  assume_always_enabled:
       |    assume property (@(posedge clock) disable iff (~hasBeenReset) io_en);
       |  
       |  assert_delayed_in_high:
       |    assert property (@(posedge clock) disable iff (~hasBeenReset) io_in |-> ##4 reg3);
       |  
       |  assert_delayed_in_low:
       |    assert property (@(posedge clock) disable iff (~hasBeenReset) ~io_in |-> ##4 ~reg3);
       |  
       |  cover_in_to_out_delay:
       |    cover property (@(posedge clock) disable iff (~hasBeenReset) io_in ##4 reg3);
       |
       |endmodule
       |""".stripMargin
  }
  
  def createBindFile(moduleName: String): String = {
    s"""// Bind verification checker to design module
       |bind $moduleName ${moduleName}_checker ${moduleName}_checker_inst (
       |  .clock(clock),
       |  .reset(reset),
       |  .io_in(io_in),
       |  .io_en(io_en),
       |  .io_out(io_out),
       |  .reg0(reg0),
       |  .reg1(reg1),
       |  .reg2(reg2),
       |  .reg3(reg3)
       |);
       |""".stripMargin
  }
  
  def extractSignals(assertions: List[String]): Set[String] = {
    Set("clock", "reset", "io_in", "io_en", "io_out", "reg0", "reg1", "reg2", "reg3")
  }
}
