# Chisel Project Makefile (Linux kernel-style)
# ============================================

# Verbose control (V=1 for verbose, default is quiet)
ifeq ("$(origin V)", "command line")
  KBUILD_VERBOSE = $(V)
endif
ifndef KBUILD_VERBOSE
  KBUILD_VERBOSE = 0
endif

ifeq ($(KBUILD_VERBOSE),1)
  Q =
  quiet =
else
  Q = @
  quiet = quiet_
endif

# ANSI color codes (kernel-style)
ECHO = echo -e
NO_COLOR    = \033[0m
BOLD        = \033[1m
DIM         = \033[2m
OK_COLOR    = \033[32;01m
ERROR_COLOR = \033[31;01m
WARN_COLOR  = \033[33;01m
INFO_COLOR  = \033[36;01m

# Abbreviated command display
cmd_msg = $(ECHO) "  $(1)\t$(2)$(NO_COLOR)"

# Configuration
SBT := tools/sbt/bin/sbt
GENERATED_DIR := generated
SBT_VERSION := 1.10.5
CONFIG_JSON := generation_config.json
CONFIG_MK := .config.mk
DEFCONFIG := defconfig
MENUCONFIG_BIN := tools/menuconfig/menuconfig
MENUCONFIG_SRC := tools/menuconfig/menuconfig.c

.PHONY: help setup compile generate-all clean clean-all test test-pwm menuconfig menuconfig-run \
        saveconfig list-options menuconfig-build apply-config defconfig savedefconfig \
        oldconfig silentoldconfig allyesconfig allnoconfig mrproper distclean


# Default target
all: compile

help:
	@$(ECHO) "$(BOLD)Chisel Project - Configuration & Build System$(NO_COLOR)"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)Configuration targets:$(NO_COLOR)"
	@$(ECHO) "  $(BOLD)menuconfig$(NO_COLOR)      - Interactive ncurses-based configuration UI"
	@$(ECHO) "  $(BOLD)defconfig$(NO_COLOR)       - Create default configuration"
	@$(ECHO) "  $(BOLD)savedefconfig$(NO_COLOR)   - Save minimal defconfig file"
	@$(ECHO) "  $(BOLD)oldconfig$(NO_COLOR)       - Update existing config with new options"
	@$(ECHO) "  $(BOLD)silentoldconfig$(NO_COLOR) - Like oldconfig but less verbose"
	@$(ECHO) "  $(BOLD)allyesconfig$(NO_COLOR)    - Enable all options where possible"
	@$(ECHO) "  $(BOLD)allnoconfig$(NO_COLOR)     - Disable all optional features"
	@$(ECHO) "  $(BOLD)list-options$(NO_CONFIG)   - Show available configuration values"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)Build targets:$(NO_COLOR)"
	@$(ECHO) "  $(BOLD)all$(NO_COLOR)             - Build everything (default target)"
	@$(ECHO) "  $(BOLD)setup$(NO_COLOR)           - Download and install SBT locally"
	@$(ECHO) "  $(BOLD)compile$(NO_COLOR)         - Compile Chisel sources"
	@$(ECHO) "  $(BOLD)generate$(NO_COLOR)        - Generate Verilog for configured module"
	@$(ECHO) "  $(BOLD)generate-all$(NO_COLOR)    - Generate Verilog for all example modules"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)Cleaning targets:$(NO_COLOR)"
	@$(ECHO) "  $(BOLD)clean$(NO_COLOR)           - Remove generated Verilog files"
	@$(ECHO) "  $(BOLD)mrproper$(NO_COLOR)        - Remove config and generated files"
	@$(ECHO) "  $(BOLD)distclean$(NO_COLOR)       - Remove all build artifacts"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)Test targets:$(NO_COLOR)"
	@$(ECHO) "  $(BOLD)test$(NO_COLOR)            - Run all tests"
	@$(ECHO) "  $(BOLD)test-pwm$(NO_COLOR)        - Run PWMLED test and generate VCD waveform"
	@$(ECHO) ""
	@$(ECHO) "$(WARN_COLOR)Usage examples:$(NO_COLOR)"
	@$(ECHO) "  make menuconfig                    # Configure interactively"
	@$(ECHO) "  make                               # Build with current config"
	@$(ECHO) "  make V=1                           # Verbose build"
	@$(ECHO) "  make generate MODULE=PWMLEDAXI     # Generate specific module"
	@$(ECHO) ""
	@$(ECHO) "$(DIM)Use V=1 for verbose output$(NO_COLOR)"



setup:
	@$(call cmd_msg,$(INFO_COLOR)SETUP,Setting up build environment...)
	$(Q)mkdir -p tools
	$(Q)if [ ! -d "tools/sbt-$(SBT_VERSION)" ]; then \
		$(call cmd_msg,$(OK_COLOR)DOWNLOAD,SBT $(SBT_VERSION)...); \
		curl -fsSL https://github.com/sbt/sbt/releases/download/v$(SBT_VERSION)/sbt-$(SBT_VERSION).tgz | tar xz -C tools; \
		mv tools/sbt tools/sbt-$(SBT_VERSION); \
		ln -sf sbt-$(SBT_VERSION) tools/sbt; \
		$(call cmd_msg,$(OK_COLOR)INSTALLED,tools/sbt-$(SBT_VERSION)); \
	else \
		$(call cmd_msg,$(OK_COLOR)FOUND,SBT $(SBT_VERSION) already installed); \
	fi
	@$(call cmd_msg,$(OK_COLOR)DONE,Setup complete)

compile:
	@$(call cmd_msg,$(INFO_COLOR)SBT,Compiling Chisel sources...)
	$(Q)$(SBT) compile
	@$(call cmd_msg,$(OK_COLOR)DONE,Compilation complete)

generate-all:
	@$(call cmd_msg,$(INFO_COLOR)GENERATE,All modules...)
	$(Q)$(SBT) "runMain GenerateAll"
	@$(call cmd_msg,$(OK_COLOR)OUTPUT,$(GENERATED_DIR)/)


generate:
ifndef MODULE
	@if [ -f $(CONFIG_MK) ]; then \
		. $(CONFIG_MK); \
		$(call cmd_msg,$(INFO_COLOR)SBT,Generating Verilog for $$MODULE...); \
		$(SBT) "runMain VerilogGenerator $$MODULE"; \
		$(call cmd_msg,$(OK_COLOR)OUTPUT,$(GENERATED_DIR)/$$MODULE/$$MODULE.sv); \
	else \
		$(call cmd_msg,$(ERROR_COLOR)ERROR,MODULE not specified and no configuration found); \
		$(ECHO) "$(WARN_COLOR)Usage: make generate MODULE=<module_name>$(NO_COLOR)"; \
		$(ECHO) "$(WARN_COLOR)Or run 'make menuconfig' or 'make defconfig' first$(NO_COLOR)"; \
		exit 1; \
	fi
else
	@$(call cmd_msg,$(INFO_COLOR)SBT,Generating Verilog for $(MODULE)...)
	$(Q)$(SBT) "runMain VerilogGenerator $(MODULE)"
	@$(call cmd_msg,$(OK_COLOR)OUTPUT,$(GENERATED_DIR)/$(MODULE)/$(MODULE).sv)
endif

clean:
	@$(call cmd_msg,$(WARN_COLOR)CLEAN,generated files)
	$(Q)rm -rf $(GENERATED_DIR)
	@$(call cmd_msg,$(OK_COLOR)DONE,Clean complete)

mrproper: clean
	@$(call cmd_msg,$(WARN_COLOR)CLEAN,config files)
	$(Q)rm -f $(CONFIG_JSON) $(CONFIG_MK) $(DEFCONFIG)
	@$(call cmd_msg,$(OK_COLOR)DONE,Configuration removed)

distclean: mrproper
	@$(call cmd_msg,$(WARN_COLOR)CLEAN,all build artifacts)
	$(Q)$(SBT) clean
	$(Q)rm -rf target project/target project/project/target $(MENUCONFIG_BIN)
	@$(call cmd_msg,$(OK_COLOR)DONE,All artifacts removed)

clean-all: distclean


# Menuconfig binary build
$(MENUCONFIG_BIN): $(MENUCONFIG_SRC)
	@$(call cmd_msg,$(INFO_COLOR)HOSTCC,$<)
	$(Q)which gcc >/dev/null || ($(call cmd_msg,$(ERROR_COLOR)ERROR,gcc not found) && exit 1)
	$(Q)which pkg-config >/dev/null || ($(call cmd_msg,$(ERROR_COLOR)ERROR,pkg-config not found) && exit 1)
	$(Q)pkg-config --exists ncurses || ($(call cmd_msg,$(ERROR_COLOR)ERROR,ncurses development package missing) && exit 1)
	$(Q)mkdir -p tools/menuconfig
	$(Q)gcc -Wall -Wextra -O2 $< -o $@ $(shell pkg-config --cflags --libs ncurses)
	@$(call cmd_msg,$(OK_COLOR)BUILT,$@)

menuconfig-build: $(MENUCONFIG_BIN)

menuconfig: $(MENUCONFIG_BIN)
	@$(call cmd_msg,$(INFO_COLOR)CONFIG,Interactive configuration...)
	$(Q)TERM=$${TERM:-xterm-256color} $(MENUCONFIG_BIN)

menuconfig-run: menuconfig
	$(Q)$(MAKE) apply-config

# Configuration management

defconfig:
	@$(call cmd_msg,$(INFO_COLOR)DEFCONFIG,Creating default configuration...)
	$(Q)printf '{\n  "module": "PWMLEDAXI",\n  "flow": "generate",\n  "mode": "verification",\n  "layers": "inline",\n  "preserve_values": "named",\n  "randomization": "disable",\n  "run_formal": "no"\n}\n' > $(CONFIG_JSON)
	$(Q)printf 'MODULE=PWMLEDAXI\nFLOW=generate\nMODE=verification\nLAYERS=inline\nPRESERVE=named\nRANDOMIZATION=disable\nRUN_FORMAL=no\n' > $(CONFIG_MK)
	@$(call cmd_msg,$(OK_COLOR)SAVED,$(CONFIG_JSON))

savedefconfig:
	@if [ ! -f $(CONFIG_MK) ]; then \
		$(call cmd_msg,$(ERROR_COLOR)ERROR,No configuration found); \
		$(ECHO) "$(WARN_COLOR)Run 'make menuconfig' or 'make defconfig' first$(NO_COLOR)"; \
		exit 1; \
	fi
	@$(call cmd_msg,$(INFO_COLOR)DEFCONFIG,Saving minimal configuration...)
	$(Q)cp $(CONFIG_MK) $(DEFCONFIG)
	@$(call cmd_msg,$(OK_COLOR)SAVED,$(DEFCONFIG))

oldconfig:
	@if [ ! -f $(CONFIG_MK) ]; then \
		$(call cmd_msg,$(WARN_COLOR)NOTICE,No existing configuration found); \
		$(MAKE) defconfig; \
	else \
		$(call cmd_msg,$(INFO_COLOR)OLDCONFIG,Updating configuration...); \
		$(call cmd_msg,$(OK_COLOR)DONE,Configuration updated); \
	fi

silentoldconfig: oldconfig


allyesconfig:
	@$(call cmd_msg,$(INFO_COLOR)ALLYESCONFIG,Enabling all options...)
	$(Q)printf '{\n  "module": "AbstractedPWMLEDAXI",\n  "flow": "generate+formal",\n  "mode": "synthesis",\n  "layers": "split",\n  "preserve_values": "named",\n  "randomization": "enable",\n  "run_formal": "ic3"\n}\n' > $(CONFIG_JSON)
	$(Q)printf 'MODULE=AbstractedPWMLEDAXI\nFLOW=generate+formal\nMODE=synthesis\nLAYERS=split\nPRESERVE=named\nRANDOMIZATION=enable\nRUN_FORMAL=ic3\n' > $(CONFIG_MK)
	@$(call cmd_msg,$(OK_COLOR)SAVED,$(CONFIG_JSON))

allnoconfig:
	@$(call cmd_msg,$(INFO_COLOR)ALLNOCONFIG,Minimal configuration...)
	$(Q)printf '{\n  "module": "Adder",\n  "flow": "generate",\n  "mode": "verification",\n  "layers": "inline",\n  "preserve_values": "none",\n  "randomization": "disable",\n  "run_formal": "no"\n}\n' > $(CONFIG_JSON)
	$(Q)printf 'MODULE=Adder\nFLOW=generate\nMODE=verification\nLAYERS=inline\nPRESERVE=none\nRANDOMIZATION=disable\nRUN_FORMAL=no\n' > $(CONFIG_MK)
	@$(call cmd_msg,$(OK_COLOR)SAVED,$(CONFIG_JSON))

list-options:
	@$(ECHO) "$(BOLD)Available configuration options:$(NO_COLOR)"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)MODULE:$(NO_COLOR)"
	@$(ECHO) "  Adder Counter Mux2to1 SimpleALU PWMLED PWMLEDAXI AbstractedPWMLEDAXI ShiftRegister"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)FLOW:$(NO_COLOR)"
	@$(ECHO) "  generate generate+formal"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)MODE:$(NO_COLOR)"
	@$(ECHO) "  verification synthesis"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)LAYERS:$(NO_COLOR)"
	@$(ECHO) "  inline split"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)PRESERVE_VALUES:$(NO_COLOR)"
	@$(ECHO) "  named all none"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)RANDOMIZATION:$(NO_COLOR)"
	@$(ECHO) "  disable enable"
	@$(ECHO) ""
	@$(ECHO) "$(INFO_COLOR)RUN_FORMAL:$(NO_COLOR)"
	@$(ECHO) "  no default k-induction ic3"


saveconfig:
	@$(call cmd_msg,$(INFO_COLOR)SAVECONFIG,Non-interactive configuration...)
ifdef MODULE
	$(eval DERIVED_FLOW := $(if $(filter no,$(RUN_FORMAL)),generate,formal))
	$(Q)printf '{\n  "module": "$(MODULE)",\n  "flow": "$(DERIVED_FLOW)",\n  "mode": "$(MODE)",\n  "layers": "$(LAYERS)",\n  "preserve_values": "$(PRESERVE)",\n  "randomization": "$(RANDOMIZATION)",\n  "run_formal": "$(RUN_FORMAL)"\n}\n' > $(CONFIG_JSON)
	$(Q)printf 'MODULE=$(MODULE)\nFLOW=$(DERIVED_FLOW)\nMODE=$(MODE)\nLAYERS=$(LAYERS)\nPRESERVE=$(PRESERVE)\nRANDOMIZATION=$(RANDOMIZATION)\nRUN_FORMAL=$(RUN_FORMAL)\n' > $(CONFIG_MK)
	@$(call cmd_msg,$(OK_COLOR)SAVED,$(CONFIG_JSON))
else
	@$(call cmd_msg,$(ERROR_COLOR)ERROR,No MODULE specified)
	@$(ECHO) "$(WARN_COLOR)Usage: make saveconfig MODULE=<name> MODE=<mode> RUN_FORMAL=<algo> ...$(NO_COLOR)"
	@exit 1
endif


apply-config:
	@if [ ! -f $(CONFIG_MK) ]; then \
		$(call cmd_msg,$(ERROR_COLOR)ERROR,Configuration not found); \
		$(ECHO) "$(WARN_COLOR)Run 'make menuconfig' or 'make defconfig' first$(NO_COLOR)"; \
		exit 1; \
	fi
	@. $(CONFIG_MK); \
	 $(call cmd_msg,$(INFO_COLOR)CONFIG,MODULE=$$MODULE MODE=$$MODE FORMAL=$$RUN_FORMAL); \
	 $(call cmd_msg,$(INFO_COLOR)SBT,Generating Verilog for $$MODULE...); \
	 $(SBT) "runMain VerilogGenerator $$MODULE"; \
	 $(call cmd_msg,$(OK_COLOR)OUTPUT,$(GENERATED_DIR)/$$MODULE/$$MODULE.sv); \
	 if [ "$$RUN_FORMAL" != "no" ]; then \
	   $(call cmd_msg,$(INFO_COLOR)FORMAL,Running formal verification with $$RUN_FORMAL...); \
	   ./scripts/run_formal.sh $$MODULE $$RUN_FORMAL; \
	   $(call cmd_msg,$(OK_COLOR)DONE,Formal verification complete); \
	 fi

# Test targets
test:
	@$(call cmd_msg,$(INFO_COLOR)TEST,Running all tests...)
	$(Q)$(SBT) test
	@$(call cmd_msg,$(OK_COLOR)DONE,Tests complete)

test-pwm:
	@$(call cmd_msg,$(INFO_COLOR)TEST,Running PWMLED test...)
	$(Q)$(SBT) "testOnly PWMLEDTest"
	@$(call cmd_msg,$(OK_COLOR)OUTPUT,test.vcd)

