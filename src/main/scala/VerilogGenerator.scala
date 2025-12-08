import chisel3._
import circt.stage.ChiselStage

/**
 * Main application to generate Verilog from Chisel designs.
 * Uses `generation_config.json` (written by the menuconfig TUI) to choose module,
 * verification/synthesis flavor, layer strategy, and preservation settings.
 */
object VerilogGenerator extends App {

  case class GenConfig(
    module: String = "PWMLEDAXI",
    mode: String = "verification",       // verification | synthesis
    layers: String = "inline",           // inline | split (bind)
    preserve_values: String = "named",    // named | all | none
    randomization: String = "disable",    // disable | enable
    run_formal: String = "no"             // no | default | k-induction | ic3
  )

  private def loadConfig(): GenConfig = {
    val configFile = new java.io.File("generation_config.json")
    if (!configFile.exists()) return GenConfig()

    def extract(key: String, default: String, json: String): String = {
      val pattern = s"\"$key\"\\s*:\\s*\"([^\"]+)\"".r
      pattern.findFirstMatchIn(json).map(_.group(1)).getOrElse(default)
    }

    try {
      val source = scala.io.Source.fromFile(configFile)
      val jsonStr = try source.mkString finally source.close()
      GenConfig(
        module = extract("module", "PWMLEDAXI", jsonStr),
        mode = extract("mode", "verification", jsonStr),
        layers = extract("layers", "inline", jsonStr),
        preserve_values = extract("preserve_values", "named", jsonStr),
        randomization = extract("randomization", "disable", jsonStr),
        run_formal = extract("run_formal", "no", jsonStr)
      )
    } catch {
      case _: Exception => GenConfig()
    }
  }

  private def buildFirtoolOpts(moduleName: String, config: GenConfig): Array[String] = {
    val outputDir = s"generated/$moduleName"
    val skipConfig = Set("ShiftRegister", "Adder", "Counter", "Mux2to1", "SimpleALU")

    val opts = scala.collection.mutable.ArrayBuffer[String]()

    // Modules without layers need basic SVA emission without split-verilog
    if (!skipConfig.contains(moduleName)) {
      opts += s"-o=$outputDir"
      opts += "--split-verilog"
      opts += "@firtool_config.txt"
      
      val inlineLayers = config.layers == "inline"
      System.setProperty("chisel.layers.inline", inlineLayers.toString)

      config.preserve_values match {
        case "all"   => opts += "--preserve-values=all"
        case "none"  => opts += "--preserve-values=none"
        case "named" => opts += "--preserve-values=named"
        case _ =>
      }

      if (config.randomization == "enable") opts += "--enable-all-randomization"
    } else {
      // Simple modules: emit properties inline to a specific file  
      opts += s"-o=$outputDir/$moduleName.sv"
      opts += "--verification-flavor=sva"
      opts += "--lowering-options=disallowPackedArrays,disallowLocalVariables,verifLabels"
      opts += "--strip-fir-debug-info"
      opts += "--no-dedup"
      if (config.preserve_values == "all") opts += "--preserve-values=all"
      else if (config.preserve_values == "none") opts += "--preserve-values=none"
      else opts += "--preserve-values=named"
      if (config.randomization == "disable") opts += "--disable-all-randomization"
    }

    opts.toArray
  }

  private def generateVerilog(module: => RawModule, moduleName: String, config: GenConfig): Unit = {
    val firtoolOpts = buildFirtoolOpts(moduleName, config)
    val outputDir = s"generated/$moduleName"
    val skipConfig = Set("ShiftRegister", "Adder", "Counter", "Mux2to1", "SimpleALU")

    println(s"Generating Verilog for module: $moduleName")
    println(s"  Output: $outputDir")
    println(s"  Mode: ${config.mode}")
    println(s"  Layers: ${config.layers}")
    println(s"  Options: ${firtoolOpts.mkString(" ")}")

    try {
      new java.io.File(outputDir).mkdirs()

      ChiselStage.emitSystemVerilog(
        module,
        firtoolOpts = firtoolOpts
      )
      
      println(s"Successfully generated Verilog for $moduleName in $outputDir")

      // For simple modules, inline verification modules and remove binds
      if (skipConfig.contains(moduleName)) {
        val svFile = new java.io.File(s"$outputDir/$moduleName.sv")
        if (svFile.exists()) {
          // Run Python script to inline verification properties
          import sys.process._
          val result = s"./scripts/inline_verification.py $outputDir/$moduleName.sv".!
          if (result != 0) {
            println(s"Warning: Failed to inline verification properties")
          }
        }
      }

      // Remove layer directory that can confuse some tools
      import scala.sys.process._
      val verificationDir = new java.io.File(s"$outputDir/verification")
      if (verificationDir.exists()) {
        try s"rm -rf $outputDir/verification".! catch { case _: Exception => () }
      }

      // Keep filelist.f in sync with layer bind files
      val filelist = new java.io.File(s"$outputDir/filelist.f")
      if (filelist.exists()) {
        val cmd = s"find $outputDir -name layers-*.sv"
        try {
          val bindFiles = cmd.!!.split("\n").filter(_.nonEmpty).map(_.trim)
          val currentContent = scala.io.Source.fromFile(filelist).getLines().toSet
          val newFiles = bindFiles.filterNot(f => currentContent.contains(f) || currentContent.contains(f.stripPrefix(s"$outputDir/")))
          if (newFiles.nonEmpty) {
            val writer = new java.io.FileWriter(filelist, true)
            newFiles.foreach(f => writer.write(f + "\n"))
            writer.close()
            println(s"Updated filelist.f with ${newFiles.length} bind files")
          }
        } catch {
          case e: Exception => println(s"Warning: Failed to update filelist.f: ${e.getMessage}")
        }
      }
    } catch {
      case e: Exception =>
        println(s"Failed to generate Verilog for $moduleName: ${e.getMessage}")
        throw e
    }
  }

  private val knownModules: Map[String, () => RawModule] = Map(
    "Adder" -> (() => new examples.Adder),
    "Counter" -> (() => new examples.Counter),
    "Mux2to1" -> (() => new examples.Mux2to1(8)),
    "SimpleALU" -> (() => new examples.SimpleALU),
    "PWMLED" -> (() => new examples.PWMLED(50, 8, 8, false)),
    "PWMLEDAXI" -> (() => new examples.PWMLEDAXI(50, 1, 8, 12, 32, false)),
    "AbstractedPWMLEDAXI" -> (() => new examples.AbstractedPWMLEDAXI(50, 1, 8, 12, 32, false)),
    "ShiftRegister" -> (() => new examples.ShiftRegister)
  )

  private def runSingle(moduleName: String, config: GenConfig): Unit = {
    knownModules.get(moduleName) match {
      case Some(gen) => generateVerilog(gen(), moduleName, config)
      case None =>
        println(s"Unknown module: $moduleName")
        println(s"Available modules: ${knownModules.keys.mkString(", ")}")
        sys.exit(1)
    }
  }

  // Entry
  val config = loadConfig()
  val moduleName = if (args.nonEmpty) args(0) else config.module
  runSingle(moduleName, config)
}

/** Generate all known modules */
object GenerateAll extends App {
  val modules = Seq(
    "Adder" -> (() => new examples.Adder),
    "Counter" -> (() => new examples.Counter),
    "Mux2to1" -> (() => new examples.Mux2to1(8)),
    "SimpleALU" -> (() => new examples.SimpleALU),
    "PWMLED" -> (() => new examples.PWMLED(50, 8, 8, false)),
    "PWMLEDAXI" -> (() => new examples.PWMLEDAXI(50, 1, 8, 12, 32, false)),
    "ShiftRegister" -> (() => new examples.ShiftRegister)
  )

  val outputDir = new java.io.File("generated")
  if (!outputDir.exists()) outputDir.mkdirs()

  modules.foreach { case (name, gen) =>
    try {
      val firtoolOpts = Array(s"-o=generated/$name", "--split-verilog", "@firtool_config.txt")
      ChiselStage.emitSystemVerilog(gen(), firtoolOpts = firtoolOpts)
      println(s"  ✓ $name")
    } catch {
      case e: Exception => println(s"  X $name (${e.getMessage})")
    }
  }
  println(s"All modules generated in: ${outputDir.getAbsolutePath}")
}
