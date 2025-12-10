# EBMC Parameters System

## Overview

The ChiselForge IDE now includes a comprehensive, professional parameter configuration system for EBMC (Efficient Bounded Model Checker) formal verification. This system allows users to dynamically configure EBMC parameters through an intuitive UI, with automatic VCD file generation and download capabilities for counterexamples.

## Key Features

### 1. **Dynamic Parameter Configuration**
- **Conditional UI**: Parameters only appear when relevant (e.g., IC3-specific options only show when IC3 method is selected)
- **Smart Defaults**: Parameters are optional - only included in command if user sets a value
- **Inline Help**: Each parameter has contextual help accessible via help icon
- **Categorized Organization**: Parameters grouped into logical categories (Core, Methods, Output, Solver, IC3, Verilog, Advanced)

### 2. **VCD File Support**
- **Automatic Generation**: Specify VCD filename in parameters, EBMC generates trace on failure
- **Download Mechanism**: One-click download of generated VCD files
- **File Management**: VCD files stored in module-specific directories on server

### 3. **Parameter Categories**

#### Core Parameters
- **Bound**: Maximum time frames to unroll (1-1000, default: 10)
- **Property ID**: Check specific property by identifier

#### Methods
- **Verification Method**: 
  - Default BMC (Bounded Model Checking)
  - K-Induction
  - IC3 (Incremental Construction of Inductive Clauses)
  - BDD (Binary Decision Diagrams - unbounded)

#### Output & Traces
- **VCD Output**: Generate VCD waveform file for counterexamples
- **Generate Trace**: Textual trace for failing properties
- **Show Waveform**: Console waveform display
- **Numbered Trace**: Number identifiers by timeframe
- **JSON Output**: Export results in JSON format

#### Solver Options
- **SAT/SMT Solver**: Choose underlying solver
  - AIG (bit-level, default)
  - Z3, CVC4, Boolector, Yices, MathSAT

#### IC3 Specific
- **Constraints File**: Use constraints file (`.cnstr`)
- **New Mode**: Enable IC3 new mode
- **AIGER Output**: Print instance in AIGER format

#### Verilog Options
- **Reset Expression**: Specify reset signal name
- **Ignore Initial Blocks**: Disregard Verilog initial blocks
- **Initialize to Zero**: Initialize all variables with zero

#### Advanced
- **Verbosity**: Output detail level (0=silent, 10=everything)
- **Show Properties**: List all properties before verification
- **Liveness to Safety**: Transform liveness to safety properties

## Architecture

### Frontend (React)

#### `EbmcConfig.jsx` Component
```javascript
// Professional collapsible configuration panel
<EbmcConfig 
  config={ebmcParams} 
  onChange={setEbmcParams} 
/>
```

**Features:**
- Expandable/collapsible interface
- Active parameter counter
- Per-parameter help tooltips
- Automatic dependency handling
- Reset functionality

#### `App.jsx` Integration
- State management for `ebmcParams`
- VCD file download handler
- Visual feedback for generated files
- Integrated into main configuration panel

#### `api.js` Service
```javascript
// Updated verify method
async verify(moduleName, ebmcParams = {})

// VCD download method
async downloadVCD(moduleName, fileName)
```

### Backend (Node.js/Express)

#### `server.js` Endpoint
```javascript
POST /api/verify
Body: {
  moduleName: string,
  ebmcParams: {
    bound?: number,
    method?: string,
    vcd?: string,
    trace?: boolean,
    // ... all other parameters
  }
}

Response: {
  success: boolean,
  results: { proved, failed, inconclusive, unsupported },
  vcdFile?: string,  // If VCD was generated
  stdout: string,
  stderr: string
}
```

#### VCD Download Endpoint
```javascript
GET /api/vcd/:moduleName/:fileName
Response: Binary VCD file (application/octet-stream)
```

**Features:**
- Base64-encoded JSON parameter passing to shell script
- Automatic VCD file detection
- Secure path validation
- Large output buffer support (50MB)

### Shell Script (`run_formal.sh`)

**Parameter Processing:**
1. Receives base64-encoded JSON via `EBMC_PARAMS` environment variable
2. Decodes using `base64 -d`
3. Parses with `jq` (JSON processor)
4. Builds EBMC command dynamically
5. Executes with all specified parameters

**Example Command Building:**
```bash
# Base command
EBMC_BIN --systemverilog file.sv -D layers

# + User parameters (if set)
--bound 50
--k-induction
--vcd generated/Module/counterexample.vcd
--trace
--verbosity 5
```

## Usage Examples

### Example 1: Basic Verification with VCD Output
```javascript
setEbmcParams({
  bound: 20,
  vcd: 'counterexample.vcd'
});
// Click "Verify" button
// If properties fail, VCD file is generated and download button appears
```

### Example 2: K-Induction with Traces
```javascript
setEbmcParams({
  bound: 50,
  method: 'k-induction',
  trace: true,
  numberedTrace: true,
  vcd: 'trace.vcd'
});
```

### Example 3: IC3 with Constraints
```javascript
setEbmcParams({
  method: 'ic3',
  ic3Constr: 'module.cnstr',
  ic3NewMode: true,
  verbosity: 3
});
```

### Example 4: Debug Mode with All Options
```javascript
setEbmcParams({
  bound: 100,
  method: 'k-induction',
  vcd: 'detailed_trace.vcd',
  jsonResult: 'results.json',
  trace: true,
  waveform: true,
  showProperties: true,
  verbosity: 10,
  solver: 'z3'
});
```

## Data Flow

```
User Input (UI)
    ↓
React State (ebmcParams)
    ↓
API Call (/api/verify)
    ↓
Express Server (base64 encode)
    ↓
Shell Script (decode, parse, build command)
    ↓
EBMC Execution
    ↓
Results + VCD File
    ↓
Response to Frontend
    ↓
Display Results + Download Button
```

## File Structure

```
chisel_forge/
├── src/
│   ├── App.jsx                    # Main app with integrated config
│   ├── api.js                     # API service with verify & downloadVCD
│   └── components/
│       └── EbmcConfig.jsx         # Parameter configuration component
├── server/
│   └── server.js                  # Backend with /api/verify & /api/vcd endpoints
└── chisel/
    └── scripts/
        └── run_formal.sh          # Enhanced script with dynamic params
```

## Security Considerations

1. **Path Validation**: All file paths validated to prevent directory traversal
2. **Parameter Sanitization**: JSON parsing with error handling
3. **File Type Restrictions**: Only `.vcd` files downloadable
4. **Size Limits**: 50MB buffer for large verification outputs
5. **Module Isolation**: Files stored in module-specific directories

## Benefits

### For Users
- **Professional Interface**: Clean, organized parameter management
- **Flexibility**: Configure verification exactly as needed
- **Efficiency**: Only set parameters you need, ignore the rest
- **Debugging**: VCD files for visual analysis of counterexamples
- **Discoverability**: Inline help for each parameter

### For Developers
- **Maintainability**: Centralized parameter definitions
- **Extensibility**: Easy to add new parameters
- **Type Safety**: Structured parameter objects
- **Testability**: Clear separation of concerns

## Future Enhancements

1. **Parameter Presets**: Save/load common configurations
2. **Batch Verification**: Run multiple configurations
3. **VCD Viewer**: Integrated waveform viewer
4. **History**: Track verification runs and parameters
5. **Advanced Parsing**: Better EBMC output analysis
6. **Constraint Editor**: GUI for IC3 constraint files
7. **Performance Metrics**: Track verification time/memory

## Technical Notes

- **jq Dependency**: Shell script requires `jq` for JSON parsing (graceful fallback to defaults)
- **EBMC Version**: Tested with EBMC 5.7 (ebmc-5.5-652-g1cc5ca65)
- **File Persistence**: VCD files persist in `generated/<module>/` directory
- **Backward Compatibility**: System works with or without parameters (defaults applied)

## Troubleshooting

**VCD not generated?**
- Ensure property failures occur (VCD only generated on counterexample)
- Check EBMC supports VCD output for your SystemVerilog version
- Verify write permissions in generated directory

**Parameters not applied?**
- Check server logs for EBMC_PARAMS encoding
- Verify `jq` installed on server (`which jq`)
- Inspect EBMC command in console output

**Download fails?**
- Check VCD file exists in module directory
- Verify file permissions
- Check browser console for errors

## Summary

This comprehensive EBMC parameter system transforms ChiselForge into a professional formal verification IDE, providing users with fine-grained control over verification strategies while maintaining an intuitive, user-friendly interface. The conditional UI, automatic file handling, and integrated help system make formal verification accessible to both beginners and experts.
