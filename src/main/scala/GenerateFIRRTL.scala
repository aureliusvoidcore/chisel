import chisel3._
import circt.stage.ChiselStage

/**
 * Generator for FIRRTL intermediate representation.
 * This generates the .fir file which can then be processed by firtool.
 * 
 * Usage:
 *   sbt "runMain GenerateFIRRTL"
 */
object GenerateFIRRTL {
  def main(args: Array[String]): Unit = {
    println("Generating FIRRTL for ShiftRegister...")
    
    // Generate CHIRRTL (high-level FIRRTL)
    val firrtlString = ChiselStage.emitCHIRRTL(new examples.ShiftRegister)
    
    // Write to file
    val outputDir = new java.io.File("generated")
    if (!outputDir.exists()) outputDir.mkdirs()
    
    val outputFile = new java.io.File("generated/ShiftRegister.fir")
    val writer = new java.io.PrintWriter(outputFile)
    writer.write(firrtlString)
    writer.close()
    
    println(s"Successfully generated FIRRTL: ${outputFile.getAbsolutePath}")
    println("\nTo generate SystemVerilog with SVA, run:")
    println("  firtool generated/ShiftRegister.fir --output-file=generated/ShiftRegister.sv")
    println("\nWith layer support:")
    println("  firtool generated/ShiftRegister.fir --output-file=generated/ShiftRegister.sv \\")
    println("    --enable-layers=Verification.Assert,Verification.Assume,Verification.Cover")
  }
}
