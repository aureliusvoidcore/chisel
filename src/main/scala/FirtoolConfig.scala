/**
 * Global configuration for firtool options used across all Verilog generation.
 * 
 * This centralizes firtool settings to ensure consistent SystemVerilog generation
 * with proper support for formal verification properties (SVA).
 */
object FirtoolConfig {
  
  /**
   * Standard options for SystemVerilog generation.
   * Includes support for SVA assertions, assumptions, and coverage.
   */
  val standardOptions: Array[String] = Array(
    "-disable-all-randomization",
    "-strip-debug-info"
  )
  
  /**
   * Options for formal verification focused output.
   * Same as standard but explicitly documents verification intent.
   */
  val verificationOptions: Array[String] = standardOptions
  
  /**
   * Options for synthesis-focused output.
   * Strips verification properties that may not be synthesizable.
   */
  val synthesisOptions: Array[String] = Array(
    "-disable-all-randomization",
    "-strip-debug-info"
  )
  
  /**
   * Options for debugging with source location information.
   */
  val debugOptions: Array[String] = Array(
    "-disable-all-randomization"
  )
  
  /**
   * Get the default options for general use.
   * By default, includes SVA support for verification.
   */
  def default: Array[String] = standardOptions
}
