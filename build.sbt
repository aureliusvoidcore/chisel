// Chisel Sandbox Build Configuration
// This configuration can be reused across projects - just add your designs to src/main/scala/
// SVA (SystemVerilog Assertions) support is enabled by default via FirtoolConfig

name := "chisel-sandbox"
version := "0.1.0"
scalaVersion := "2.13.18"

// Chisel dependencies - using stable versions with verified compatibility
libraryDependencies ++= Seq(
  "org.chipsalliance" %% "chisel" % "7.4.0",
  // "edu.berkeley.cs" %% "chiseltest" % "6.0.0" % "test"
)

// Scala compiler options
scalacOptions ++= Seq(
  "-deprecation",
  "-feature",
  "-unchecked",
  "-language:reflectiveCalls",
  "-Ymacro-annotations"
)

// Enables Chisel elaboration with Verilog generation
addCompilerPlugin("org.chipsalliance" % "chisel-plugin" % "7.4.0" cross CrossVersion.full)
