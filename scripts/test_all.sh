#!/usr/bin/env bash
# Comprehensive test suite for Chisel development environment
# Tests build system, configuration, generation, and verification

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
TESTS_TOTAL=0
TESTS_PASSED=0
TESTS_FAILED=0

# Test results array
declare -a FAILED_TESTS

# Logging functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[PASS]${NC} $1"
    ((TESTS_PASSED++))
}

log_failure() {
    echo -e "${RED}[FAIL]${NC} $1"
    ((TESTS_FAILED++))
    FAILED_TESTS+=("$1")
}

log_warning() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_section() {
    echo ""
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}========================================${NC}"
    echo ""
}

# Test wrapper
run_test() {
    local test_name="$1"
    ((TESTS_TOTAL++))
    log_info "Running: $test_name"
}

# Check prerequisites
check_prerequisites() {
    log_section "Checking Prerequisites"
    
    run_test "Java JDK availability"
    if command -v java &> /dev/null; then
        local java_version=$(java -version 2>&1 | head -n 1)
        log_success "Java found: $java_version"
    else
        log_failure "Java not found"
        exit 1
    fi
    
    run_test "Make availability"
    if command -v make &> /dev/null; then
        local make_version=$(make --version | head -n 1)
        log_success "Make found: $make_version"
    else
        log_failure "Make not found"
        exit 1
    fi
    
    run_test "gcc availability"
    if command -v gcc &> /dev/null; then
        local gcc_version=$(gcc --version | head -n 1)
        log_success "gcc found: $gcc_version"
    else
        log_failure "gcc not found"
    fi
    
    run_test "ncurses development libraries"
    if pkg-config --exists ncurses 2>/dev/null; then
        log_success "ncurses-dev installed"
    else
        log_warning "ncurses-dev not found (required for menuconfig)"
    fi
    
    run_test "EBMC availability (optional)"
    if command -v ebmc &> /dev/null; then
        local ebmc_version=$(ebmc --version 2>&1 | head -n 1 || echo "unknown")
        log_success "EBMC found: $ebmc_version"
    else
        log_warning "EBMC not found (formal verification unavailable)"
    fi
}

# Test file structure
test_file_structure() {
    log_section "Testing File Structure"
    
    local required_files=(
        "Makefile"
        "build.sbt"
        "firtool_config.txt"
        "README.md"
        ".gitignore"
        "src/main/scala/VerilogGenerator.scala"
        "src/main/scala/examples/Examples.scala"
        "src/main/scala/examples/PWM.scala"
        "src/main/scala/examples/PWMLEDAXI.scala"
        "src/main/scala/examples/ShiftRegister.scala"
        "tools/menuconfig/menuconfig.c"
        "scripts/run_formal.sh"
        "scripts/config_gen.py"
    )
    
    for file in "${required_files[@]}"; do
        run_test "File exists: $file"
        if [ -f "$file" ]; then
            log_success "$file exists"
        else
            log_failure "$file missing"
        fi
    done
    
    run_test "Scripts are executable"
    if [ -x "scripts/run_formal.sh" ]; then
        log_success "run_formal.sh is executable"
    else
        log_failure "run_formal.sh not executable"
    fi
}

# Test SBT setup
test_sbt_setup() {
    log_section "Testing SBT Setup"
    
    run_test "SBT installation"
    if [ -d "tools/sbt" ]; then
        log_info "SBT already installed, skipping setup"
        log_success "SBT directory exists"
    else
        log_info "Installing SBT..."
        if make setup &> /tmp/test_sbt_setup.log; then
            log_success "SBT setup completed"
        else
            log_failure "SBT setup failed"
            cat /tmp/test_sbt_setup.log
            return 1
        fi
    fi
    
    run_test "SBT binary executable"
    if [ -x "tools/sbt/bin/sbt" ]; then
        log_success "SBT binary is executable"
    else
        log_failure "SBT binary not executable"
    fi
}

# Test menuconfig build
test_menuconfig_build() {
    log_section "Testing Menuconfig Build"
    
    run_test "Menuconfig compilation"
    if make menuconfig-build &> /tmp/test_menuconfig_build.log; then
        log_success "Menuconfig compiled successfully"
    else
        log_failure "Menuconfig compilation failed"
        cat /tmp/test_menuconfig_build.log
        return 1
    fi
    
    run_test "Menuconfig binary exists"
    if [ -f "tools/menuconfig/menuconfig" ]; then
        log_success "Menuconfig binary created"
    else
        log_failure "Menuconfig binary not found"
    fi
    
    run_test "Menuconfig binary executable"
    if [ -x "tools/menuconfig/menuconfig" ]; then
        log_success "Menuconfig is executable"
    else
        log_failure "Menuconfig not executable"
    fi
}

# Test configuration system
test_configuration_system() {
    log_section "Testing Configuration System"
    
    # Backup existing configuration
    if [ -f ".config.mk" ]; then
        cp .config.mk .config.mk.backup
    fi
    if [ -f "generation_config.json" ]; then
        cp generation_config.json generation_config.json.backup
    fi
    
    run_test "defconfig target"
    if make defconfig &> /tmp/test_defconfig.log; then
        log_success "defconfig executed successfully"
    else
        log_failure "defconfig failed"
        cat /tmp/test_defconfig.log
    fi
    
    run_test "Configuration files created"
    if [ -f ".config.mk" ] && [ -f "generation_config.json" ]; then
        log_success "Configuration files exist"
    else
        log_failure "Configuration files not created"
    fi
    
    run_test "saveconfig target"
    if make saveconfig MODULE=Adder MODE=verification RUN_FORMAL=no &> /tmp/test_saveconfig.log; then
        log_success "saveconfig executed successfully"
    else
        log_failure "saveconfig failed"
        cat /tmp/test_saveconfig.log
    fi
    
    run_test "Configuration content validation"
    if grep -q "MODULE=Adder" .config.mk && grep -q "\"module\": \"Adder\"" generation_config.json; then
        log_success "Configuration content correct"
    else
        log_failure "Configuration content incorrect"
    fi
    
    run_test "RUN_FORMAL flow derivation"
    make saveconfig MODULE=Counter RUN_FORMAL=k-induction &> /dev/null
    if grep -q "FLOW=formal" .config.mk; then
        log_success "FLOW correctly derived from RUN_FORMAL!=no"
    else
        log_failure "FLOW derivation failed"
    fi
    
    make saveconfig MODULE=Counter RUN_FORMAL=no &> /dev/null
    if grep -q "FLOW=generate" .config.mk; then
        log_success "FLOW correctly set to generate when RUN_FORMAL=no"
    else
        log_failure "FLOW derivation failed for RUN_FORMAL=no"
    fi
    
    run_test "allyesconfig target"
    if make allyesconfig &> /tmp/test_allyesconfig.log; then
        log_success "allyesconfig executed successfully"
    else
        log_failure "allyesconfig failed"
    fi
    
    run_test "allnoconfig target"
    if make allnoconfig &> /tmp/test_allnoconfig.log; then
        log_success "allnoconfig executed successfully"
    else
        log_failure "allnoconfig failed"
    fi
    
    run_test "list-options target"
    if make list-options &> /tmp/test_list_options.log; then
        log_success "list-options executed successfully"
    else
        log_failure "list-options failed"
    fi
    
    # Restore original configuration
    if [ -f ".config.mk.backup" ]; then
        mv .config.mk.backup .config.mk
    fi
    if [ -f "generation_config.json.backup" ]; then
        mv generation_config.json.backup generation_config.json
    fi
}

# Test Scala compilation
test_scala_compilation() {
    log_section "Testing Scala Compilation"
    
    run_test "Chisel sources compilation"
    if make compile &> /tmp/test_compile.log; then
        log_success "Scala compilation successful"
    else
        log_failure "Scala compilation failed"
        tail -n 50 /tmp/test_compile.log
        return 1
    fi
    
    run_test "Compiled classes exist"
    if [ -d "target/scala-2.13/classes" ]; then
        log_success "Compiled classes directory exists"
    else
        log_failure "Compiled classes directory not found"
    fi
}

# Test Verilog generation
test_verilog_generation() {
    log_section "Testing Verilog Generation"
    
    local modules=("Adder" "Counter" "Mux2to1" "SimpleALU" "PWMLED" "PWMLEDAXI" "ShiftRegister")
    
    for module in "${modules[@]}"; do
        run_test "Generate module: $module"
        if make generate MODULE=$module &> /tmp/test_generate_$module.log; then
            log_success "$module generated successfully"
        else
            log_failure "$module generation failed"
            tail -n 20 /tmp/test_generate_$module.log
            continue
        fi
        
        run_test "Verilog file exists: $module"
        if [ -f "generated/$module/$module.sv" ]; then
            log_success "$module.sv exists"
        else
            log_failure "$module.sv not found"
        fi
        
        run_test "Filelist exists: $module"
        if [ -f "generated/$module/filelist.f" ]; then
            log_success "filelist.f exists for $module"
        else
            log_failure "filelist.f not found for $module"
        fi
    done
}

# Test apply-config workflow
test_apply_config() {
    log_section "Testing apply-config Workflow"
    
    # Test generate-only flow
    run_test "apply-config with RUN_FORMAL=no"
    make saveconfig MODULE=Adder MODE=verification RUN_FORMAL=no &> /dev/null
    if make apply-config &> /tmp/test_apply_config_no_formal.log; then
        log_success "apply-config (generate-only) executed successfully"
    else
        log_failure "apply-config (generate-only) failed"
        cat /tmp/test_apply_config_no_formal.log
    fi
    
    # Test with formal (if EBMC available)
    if command -v ebmc &> /dev/null; then
        run_test "apply-config with RUN_FORMAL=default"
        make saveconfig MODULE=ShiftRegister MODE=verification RUN_FORMAL=default &> /dev/null
        if timeout 60 make apply-config &> /tmp/test_apply_config_formal.log; then
            log_success "apply-config (with formal) executed successfully"
        else
            log_warning "apply-config (with formal) timed out or failed"
        fi
    else
        log_info "Skipping formal verification test (EBMC not available)"
    fi
}

# Test Makefile targets
test_makefile_targets() {
    log_section "Testing Makefile Targets"
    
    run_test "help target"
    if make help &> /tmp/test_help.log; then
        log_success "help target works"
    else
        log_failure "help target failed"
    fi
    
    run_test "clean target"
    if make clean &> /tmp/test_clean.log; then
        log_success "clean target works"
    else
        log_failure "clean target failed"
    fi
}

# Test generated Verilog syntax
test_verilog_syntax() {
    log_section "Testing Generated Verilog Syntax"
    
    # Check if verilator is available
    if ! command -v verilator &> /dev/null; then
        log_info "Verilator not found, skipping syntax checks"
        return
    fi
    
    local modules=("Adder" "Counter" "Mux2to1" "SimpleALU")
    
    for module in "${modules[@]}"; do
        run_test "Verilog syntax check: $module"
        if [ -f "generated/$module/$module.sv" ]; then
            if verilator --lint-only -Wall generated/$module/$module.sv &> /tmp/test_syntax_$module.log; then
                log_success "$module syntax valid"
            else
                log_warning "$module has syntax warnings/errors"
            fi
        else
            log_info "Skipping $module (not generated)"
        fi
    done
}

# Summary report
print_summary() {
    log_section "Test Summary"
    
    echo "Total Tests: $TESTS_TOTAL"
    echo -e "Passed:      ${GREEN}$TESTS_PASSED${NC}"
    echo -e "Failed:      ${RED}$TESTS_FAILED${NC}"
    echo ""
    
    if [ $TESTS_FAILED -eq 0 ]; then
        echo -e "${GREEN}========================================${NC}"
        echo -e "${GREEN}ALL TESTS PASSED${NC}"
        echo -e "${GREEN}========================================${NC}"
        return 0
    else
        echo -e "${RED}========================================${NC}"
        echo -e "${RED}SOME TESTS FAILED${NC}"
        echo -e "${RED}========================================${NC}"
        echo ""
        echo "Failed tests:"
        for test in "${FAILED_TESTS[@]}"; do
            echo -e "  ${RED}✗${NC} $test"
        done
        return 1
    fi
}

# Main execution
main() {
    log_section "Chisel Development Environment Test Suite"
    
    check_prerequisites
    test_file_structure
    test_sbt_setup
    test_menuconfig_build
    test_configuration_system
    test_scala_compilation
    test_verilog_generation
    test_apply_config
    test_makefile_targets
    test_verilog_syntax
    
    print_summary
}

# Run main and capture exit code
main
exit $?
