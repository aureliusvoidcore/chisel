# Chisel Hardware Development Environment

A reproducible Chisel development environment with Linux kernel-style configuration system and integrated formal verification support.

## Overview

This repository provides a complete toolchain for hardware design using Chisel 7.4.0, featuring automated SystemVerilog generation with CIRCT/firtool, an ncurses-based configuration interface modeled after the Linux kernel build system, and formal verification integration with EBMC.

## System Architecture

### Build System

The build system implements a Linux kernel-style interface with the following characteristics:

- **Configuration Management**: Kernel-style menuconfig built with ncurses providing interactive option selection
- **Verbose Control**: Quiet mode by default with abbreviated command output; full verbosity available via `V=1`
- **Color-Coded Output**: ANSI color codes for command status (blue for informational, green for success, yellow for warnings, red for errors)
- **Modular Configuration**: Configuration stored in two synchronized files: `generation_config.json` (for Scala tooling) and `.config.mk` (for Make variables)

### Toolchain Components

**Chisel 7.4.0**: Hardware construction language built on Scala 2.13.12
- Provides high-level hardware abstraction with parameterized generators
- Supports layer-based verification property organization
- Emits FIRRTL intermediate representation

**CIRCT firtool 1.137.0**: SystemVerilog lowering compiler
- Converts FIRRTL to synthesizable SystemVerilog
- Configurable optimization levels for verification vs synthesis
- Supports split-file emission and bind statement generation
- Preserves signal names and verification properties

**SBT 1.10.5**: Scala build tool (bundled locally)
- Manages dependencies and compilation
- No system-wide installation required
- Located in `tools/sbt/`

**EBMC**: Formal verification engine (optional)
- Bounded model checking with multiple algorithms
- Verifies SystemVerilog Assertions (SVA)
- Supports default, k-induction, and IC3/PDR strategies

### Configuration System

The configuration interface provides six primary options:

1. **MODULE**: Target hardware module selection (Adder, Counter, Mux2to1, SimpleALU, PWMLED, PWMLEDAXI, AbstractedPWMLEDAXI, ShiftRegister)
2. **MODE**: Optimization strategy (verification or synthesis)
3. **LAYERS**: Assertion placement (inline within module or split with bind statements)
4. **PRESERVE**: Signal name preservation level (named, all, none)
5. **RANDOMIZATION**: Register initialization behavior (disable or enable)
6. **RUN_FORMAL**: Formal verification control (no, default, k-induction, ic3)

The `RUN_FORMAL` option serves dual purpose: it controls whether formal verification executes and selects the verification algorithm. Setting this to any value except "no" triggers automatic formal verification after SystemVerilog generation.

## Quick Start

### Prerequisites

- Java JDK 11 or later
- GNU Make
- gcc and ncurses development libraries

Install ncurses on Ubuntu/Debian:
```bash
sudo apt-get install libncurses-dev
```

On Fedora/RHEL:
```bash
sudo dnf install ncurses-devel
```

On macOS:
```bash
brew install ncurses
```

### Initial Setup

Download and configure the bundled SBT installation:
```bash
make setup
```

### Configuration

Interactive configuration via ncurses interface:
```bash
make menuconfig
```

Navigation:
- Arrow keys or hjkl (Vim-style) to move between options
- Left/Right or Space to cycle through values
- Tab to enter button navigation mode
- F1 or ? to display help for current option
- F5 or S to save configuration
- F6 to save and exit
- F9 or E to save and execute configured flow
- F10 or Q or ESC to exit

Non-interactive configuration from command line:
```bash
make saveconfig MODULE=PWMLEDAXI MODE=verification RUN_FORMAL=k-induction
```

Predefined configurations:
```bash
make defconfig       # Default: PWMLEDAXI with verification mode
make allyesconfig    # Maximum features enabled
make allnoconfig     # Minimal configuration (Adder, no formal)
```

Update existing configuration interactively:
```bash
make oldconfig       # Prompt for new options only
```

### Build and Generation

Compile Chisel sources:
```bash
make compile
```

Generate SystemVerilog using current configuration:
```bash
make generate
```

Generate SystemVerilog with configuration override:
```bash
make generate MODULE=ShiftRegister
```

Apply saved configuration (generate and optionally run formal verification):
```bash
make apply-config
```

### Cleaning

Remove generated SystemVerilog files:
```bash
make clean
```

Remove configuration and generated files:
```bash
make mrproper
```

Remove all build artifacts:
```bash
make distclean
```

## Hardware Modules

### Verified Modules

**ShiftRegister**: 4-stage shift register with formal properties
- Delays input signal by four clock cycles
- Contains 5 LTL properties (2 assumptions, 2 assertions, 1 coverage)
- All properties formally verified with EBMC
- Properties inline using custom post-processing (Module base class)
- Requires input stability assumption to prevent glitches

Properties verified:
- `assume_always_enabled`: Enable signal constantly asserted
- `assume_in_stable_5_cycles`: Input stable for minimum 5 cycles
- `assert_delayed_in_high`: High input propagates after exactly 4 cycles
- `assert_delayed_in_low`: Low input propagates after exactly 4 cycles
- `cover_in_to_out_delay`: Coverage of input-to-output delay path

**PWMLEDAXI**: PWM LED controller with AXI4-Lite interface
- Supports auto-fade functionality with configurable duty cycle and prescaler
- AXI4-Lite slave interface for runtime configuration
- Contains 15 verification properties organized in layers
- All properties formally verified with EBMC
- Uses BaseModule with Verification layer hierarchy

Properties verified:
- PWM output correctness
- AXI4-Lite write response stability and validity
- AXI4-Lite read response stability and validity
- Register write operations (duty cycle, prescaler, auto-fade disable)
- Register read operations
- Auto-fade increment/decrement behavior
- Direction reversal at duty cycle boundaries

### Utility Modules

**Adder**: 4-bit combinational adder
- Inputs: a (4-bit), b (4-bit)
- Output: sum (5-bit with carry)
- No formal properties

**Counter**: 8-bit sequential counter
- Input: enable (1-bit)
- Output: count (8-bit)
- Increments when enabled
- No formal properties

**Mux2to1**: Parameterized 2-to-1 multiplexer
- Default 8-bit width
- Inputs: in0, in1, sel
- Output: out
- No formal properties

**SimpleALU**: 8-bit arithmetic logic unit
- Inputs: a (8-bit), b (8-bit), opcode (2-bit)
- Output: result (8-bit)
- Operations: ADD (00), SUB (01), AND (10), OR (11)
- No formal properties

**PWMLED**: Basic PWM LED controller
- Auto-fading PWM generator without bus interface
- Configurable frequency and resolution
- Used as base for PWMLEDAXI
- No formal properties

## Formal Verification

### Workflow

Generate SystemVerilog and run formal verification:
```bash
make saveconfig MODULE=PWMLEDAXI RUN_FORMAL=k-induction
make apply-config
```

The formal verification script (`scripts/run_formal.sh`) performs the following:
1. Locates generated SystemVerilog in `generated/<MODULE>/`
2. Invokes EBMC with selected algorithm
3. Reports verification results

### Algorithms

**default**: Bounded model checking with default depth
- Fast execution
- Limited temporal scope
- Suitable for catching shallow bugs

**k-induction**: Inductive proof method
- Attempts to prove properties hold for all time steps
- Requires finding inductive invariants
- More thorough than bounded checking

**ic3**: Incremental Construction of Inductive Clauses (PDR)
- State-of-the-art SAT-based algorithm
- Most powerful but potentially slower
- Can prove properties unreachable by other methods

### Results Summary

| Module         | Properties | Status  | Algorithm Tested    |
|----------------|------------|---------|---------------------|
| ShiftRegister  | 5          | Proved  | default, k-induction|
| PWMLEDAXI      | 15         | Proved  | default, k-induction|
| Adder          | 0          | N/A     | N/A                 |
| Counter        | 0          | N/A     | N/A                 |
| Mux2to1        | 0          | N/A     | N/A                 |
| SimpleALU      | 0          | N/A     | N/A                 |
| PWMLED         | 0          | N/A     | N/A                 |

## Configuration Options Reference

### MODULE

Selects the Chisel module to generate. Available modules:

- **Adder**: Simple 4-bit adder demonstrating combinational logic
- **Counter**: 8-bit counter with enable signal for sequential logic
- **Mux2to1**: Parameterized 2-to-1 multiplexer
- **SimpleALU**: 8-bit ALU with four operations
- **PWMLED**: PWM LED controller with auto-fade
- **PWMLEDAXI**: PWM LED with AXI4-Lite interface (default)
- **AbstractedPWMLEDAXI**: Abstract variant of PWMLEDAXI
- **ShiftRegister**: 4-stage shift register with LTL properties

### MODE

Optimization mode affecting code generation strategy:

- **verification**: Preserves signals and properties for formal tools; disables aggressive optimizations that might remove assertions or intermediate signals
- **synthesis**: Enables synthesis optimizations; may remove debug signals and verification properties for improved area and timing

### LAYERS

Controls how verification properties are emitted:

- **inline**: Properties embedded within module using preprocessor guards; enabled/disabled with define macros; single-file verification workflow
- **split**: Properties in separate files with SystemVerilog bind statements; modular verification; may require tool-specific post-processing

### PRESERVE

Signal name preservation level affecting debugging visibility:

- **named**: Preserve explicitly named signals (default); balance of readability and optimization
- **all**: Preserve all intermediate signals and expressions; maximum debugging capability; larger output files; may cause EBMC type errors with arrays
- **none**: Minimal signal preservation; aggressive optimization; smallest output; reduced debugging capability

For EBMC compatibility, use `named` or `none`. The `all` setting can trigger type conversion errors due to how array element names are preserved.

### RANDOMIZATION

Register initialization behavior:

- **disable**: Initialize all registers to zero; deterministic behavior; suitable for formal verification
- **enable**: Initialize with random values; better for simulation to expose initialization bugs; incompatible with formal verification

### RUN_FORMAL

Controls formal verification execution and algorithm selection:

- **no**: Generate SystemVerilog only; no formal verification (default)
- **default**: Generate SystemVerilog then run EBMC with bounded model checking
- **k-induction**: Generate SystemVerilog then run EBMC with k-induction algorithm
- **ic3**: Generate SystemVerilog then run EBMC with IC3/PDR algorithm

This is the primary control for formal verification. Setting any value except "no" automatically triggers formal verification after generation.

## Build System Internals

### Makefile Structure

The Makefile consists of several sections:

**Color Definitions**: ANSI escape codes for terminal output formatting

**Tool Configuration**: Paths to SBT, menuconfig binary, configuration files

**Configuration Targets**: menuconfig, defconfig, saveconfig, oldconfig, etc.

**Build Targets**: compile, generate, apply-config

**Cleaning Targets**: clean, mrproper, distclean

**Help System**: Organized multi-section help with usage examples

### Menuconfig Implementation

The menuconfig binary is implemented in C using ncurses (approximately 734 lines in `tools/menuconfig/menuconfig.c`). 

Key features:
- Color scheme matching Linux kernel classic theme (cyan text on blue background, white dialog boxes)
- Six configuration options with detailed help text
- Real-time help panel showing current option description
- Button bar for common actions (Select, Help, Save, Execute, Exit)
- Keyboard shortcuts matching kernel menuconfig conventions
- Automatic compilation via Makefile when source changes

The binary reads existing configuration on startup, presents an interactive interface, and writes to both `generation_config.json` and `.config.mk` on save.

### Configuration Flow

1. User runs `make menuconfig` or `make saveconfig`
2. Configuration written to `.config.mk` and `generation_config.json`
3. `make apply-config` reads `.config.mk`
4. SBT invoked with `runMain VerilogGenerator <MODULE>`
5. VerilogGenerator reads `generation_config.json`
6. Chisel emits FIRRTL, firtool converts to SystemVerilog
7. If `RUN_FORMAL != "no"`, `scripts/run_formal.sh` executes
8. EBMC analyzes generated SystemVerilog

### Generator Implementation

VerilogGenerator (Scala) implements the code generation logic:

```scala
case class GenConfig(
  module: String,
  mode: String,
  layers: String,
  preserve_values: String,
  randomization: String,
  run_formal: String
)
```

The generator loads configuration from JSON, maps module names to Chisel constructors, applies firtool options from `firtool_config.txt`, and emits SystemVerilog to `generated/<MODULE>/`.

Key firtool options:
- `--verification-flavor=inline` or `--verification-flavor=module`
- `--split-verilog` for multi-file output
- `--preserve-values=named` for signal name retention
- `--lowering-options=disallowLocalVariables,disallowMuxInlining,disallowExpressionInliningInPorts,noAlwaysComb,verifLabels`
- `--no-dedup` to prevent module merging

## Known Limitations

### AbstractedPWMLEDAXI

This module is an abstracted variant of PWMLEDAXI intended for formal verification with reduced state space. Generation succeeds but formal verification status is not confirmed. The abstraction may require additional constraints or property adjustments.

### Signal Preservation

The `PRESERVE=all` setting attempts to preserve all intermediate signals including array element names. This can cause EBMC to report type conversion errors during formal verification. For EBMC compatibility, use `PRESERVE=named` or `PRESERVE=none`.

### Layer Support

The `LAYERS=split` mode generates bind statements for modular verification. Some tools may require additional configuration or post-processing to properly handle bind files. EBMC works reliably with `LAYERS=inline`.

### Formal Verification Scope

Only ShiftRegister and PWMLEDAXI contain formal properties. Other modules generate valid SystemVerilog but have no assertions to verify. Adding properties to additional modules would require modifying their Chisel source with LTL properties or layer blocks.

## Directory Structure

```
chisel/
├── build.sbt                      Scala build configuration
├── Makefile                        Linux kernel-style build system
├── firtool_config.txt              firtool command-line options
├── generation_config.json          Current configuration (JSON)
├── .config.mk                      Current configuration (Make)
├── README.md                       This file
├── generated/                      SystemVerilog output directory
│   ├── <MODULE>/
│   │   ├── <MODULE>.sv            Main module file
│   │   ├── filelist.f             File list for simulation
│   │   └── layers_*/              Layer files (if split mode)
├── project/                        SBT project metadata
├── scripts/                        Build automation scripts
│   ├── config_gen.py              Configuration generation utilities
│   ├── inline_verification.py     Post-processing for inline layers
│   └── run_formal.sh              Formal verification wrapper
├── src/
│   ├── main/scala/
│   │   ├── VerilogGenerator.scala Main generator entry point
│   │   ├── GenerateWithBind.scala Bind-mode generation
│   │   ├── FirtoolConfig.scala    firtool option management
│   │   └── examples/              Hardware module implementations
│   │       ├── Examples.scala     Adder, Counter, Mux2to1, SimpleALU
│   │       ├── PWM.scala          PWMLED module
│   │       ├── PWMLEDAXI.scala    PWMLEDAXI and AbstractedPWMLEDAXI
│   │       └── ShiftRegister.scala
│   └── test/scala/
│       ├── PWMLEDTest.scala       Simulation testbench
│       └── PWMLEDAXITest.scala    AXI testbench
├── target/                         Scala compilation output
└── tools/
    ├── menuconfig/
    │   ├── menuconfig.c           ncurses configuration UI
    │   └── menuconfig             Compiled binary
    └── sbt/                        Bundled SBT installation
        └── bin/sbt
```

## Advanced Usage

### Custom Module Generation

To add a new module:

1. Implement module in `src/main/scala/examples/`
2. Add to `knownModules` map in `VerilogGenerator.scala`
3. Update modules array in `tools/menuconfig/menuconfig.c`
4. Rebuild menuconfig: `make menuconfig-build`

### Firtool Options

Modify `firtool_config.txt` to adjust SystemVerilog generation behavior. Changes apply to all subsequent generations. Common adjustments include optimization levels, naming strategies, and verification flavor.

### Direct SBT Usage

Bypass the Makefile and invoke SBT directly:

```bash
tools/sbt/bin/sbt compile
tools/sbt/bin/sbt "runMain VerilogGenerator PWMLEDAXI"
tools/sbt/bin/sbt test
```

### Verification Property Development

Properties are defined using Chisel LTL constructs:

```scala
import chisel3.ltl._

AssertProperty(condition, label = Some("property_name"))
AssumeProperty(constraint)
CoverProperty(sequence)
```

For layer-based organization:

```scala
chisel3.layer.block(VerificationLayer.Assert) {
  AssertProperty(property)
}
```

## Troubleshooting

**Menuconfig fails to build**: Ensure gcc and ncurses-dev are installed. Check `pkg-config --cflags ncurses` returns valid output.

**SBT not found**: Run `make setup` to download and install SBT locally.

**EBMC not found**: Install EBMC or set `EBMC_BIN` environment variable to EBMC path.

**Type errors in EBMC**: Change `PRESERVE` setting from `all` to `named` or `none`.

**Generation fails**: Check `target/` directory for Scala compilation errors. Run `make compile` to see detailed output.

**Configuration not applied**: Ensure `make apply-config` is used after `make menuconfig` or `make saveconfig`.

## References

- Chisel Documentation: https://www.chisel-lang.org/
- CIRCT Project: https://circt.llvm.org/
- EBMC: https://www.cprover.org/ebmc/
- SystemVerilog Assertions: IEEE 1800-2017

## License

This project structure and build system configuration are provided as-is for educational and development purposes.
