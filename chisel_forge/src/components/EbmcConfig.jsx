import React, { useState } from 'react';
import { ChevronDown, ChevronUp, Settings, HelpCircle } from 'lucide-react';

/**
 * EbmcConfig Component
 * Professional configuration panel for EBMC formal verification parameters.
 * Uses conditional rendering - parameters are only included in the command if values are set.
 */
const EbmcConfig = ({ config, onChange }) => {
  const [isExpanded, setIsExpanded] = useState(false);
  const [showHelp, setShowHelp] = useState({});

  // Update a specific parameter
  const updateParam = (key, value) => {
    onChange({
      ...config,
      [key]: value === '' ? undefined : value
    });
  };

  const toggleHelp = (key) => {
    setShowHelp(prev => ({ ...prev, [key]: !prev[key] }));
  };

  // Parameter definitions with descriptions and defaults
  const parameters = {
    // Core Verification
    bound: {
      label: 'Bound',
      type: 'number',
      min: 1,
      max: 1000,
      help: 'Maximum number of time frames to unroll (default: 1)',
      category: 'Core'
    },
    top: {
      label: 'Top Module',
      type: 'text',
      placeholder: 'module_name',
      help: 'Set the top module to verify (--top)',
      category: 'Core'
    },
    property: {
      label: 'Property ID',
      type: 'text',
      help: 'Check specific property by ID (leave empty for all)',
      category: 'Core'
    },
    propertyExpr: {
      label: 'Property Expression',
      type: 'text',
      placeholder: 'expr',
      help: 'Specify a property expression directly (-p)',
      category: 'Core'
    },
    
    // Methods
    method: {
      label: 'Verification Method',
      type: 'select',
      options: [
        { value: '', label: 'Default BMC' },
        { value: 'k-induction', label: 'K-Induction' },
        { value: 'ic3', label: 'IC3' },
        { value: 'bdd', label: 'BDD (unbounded)' }
      ],
      help: 'Select the verification algorithm',
      category: 'Methods'
    },
    randomTraces: {
      label: 'Random Traces',
      type: 'checkbox',
      help: 'Generate random traces instead of formal verification',
      category: 'Methods'
    },
    traces: {
      label: 'Number of Traces',
      type: 'number',
      min: 1,
      max: 1000,
      help: 'Number of random traces to generate',
      category: 'Methods',
      dependsOn: { randomTraces: true }
    },
    randomSeed: {
      label: 'Random Seed',
      type: 'number',
      help: 'Random seed for trace generation',
      category: 'Methods',
      dependsOn: { randomTraces: true }
    },
    traceSteps: {
      label: 'Trace Steps',
      type: 'number',
      min: 1,
      max: 1000,
      help: 'Number of random transitions per trace (default: 10)',
      category: 'Methods',
      dependsOn: { randomTraces: true }
    },
    
    // Output & Traces
    outfile: {
      label: 'Output File',
      type: 'text',
      placeholder: 'output.txt',
      help: 'Set output file name (default: stdout)',
      category: 'Output'
    },
    vcd: {
      label: 'VCD Output',
      type: 'text',
      placeholder: 'counterexample.vcd',
      help: 'Generate VCD file for counterexamples (specify filename)',
      category: 'Output'
    },
    trace: {
      label: 'Generate Trace',
      type: 'checkbox',
      help: 'Generate textual trace for failing properties',
      category: 'Output'
    },
    waveform: {
      label: 'Show Waveform',
      type: 'checkbox',
      help: 'Display waveform for failing properties in console',
      category: 'Output'
    },
    numberedTrace: {
      label: 'Numbered Trace',
      type: 'checkbox',
      help: 'Number identifiers by timeframe in trace',
      category: 'Output'
    },
    jsonResult: {
      label: 'JSON Output',
      type: 'text',
      placeholder: 'results.json',
      help: 'Output results in JSON format to file',
      category: 'Output'
    },
    showProperties: {
      label: 'Show Properties',
      type: 'checkbox',
      help: 'List all properties in the model before verification',
      category: 'Output'
    },
    
    // Solver Options
    solver: {
      label: 'SAT/SMT Solver',
      type: 'select',
      options: [
        { value: '', label: 'Default (AIG)' },
        { value: 'aig', label: 'AIG (bit-level)' },
        { value: 'dimacs', label: 'DIMACS CNF' },
        { value: 'smt2', label: 'SMT2 formula' },
        { value: 'z3', label: 'Z3' },
        { value: 'cvc4', label: 'CVC4' },
        { value: 'boolector', label: 'Boolector' },
        { value: 'yices', label: 'Yices' },
        { value: 'mathsat', label: 'MathSAT' }
      ],
      help: 'Select the underlying solver',
      category: 'Solver'
    },
    
    // IC3 Specific
    ic3Constr: {
      label: 'IC3 Constraints File',
      type: 'text',
      placeholder: 'constraints.cnstr',
      help: 'Use constraints file for IC3 (requires --ic3)',
      category: 'IC3',
      dependsOn: { method: 'ic3' }
    },
    ic3NewMode: {
      label: 'IC3 New Mode',
      type: 'checkbox',
      help: 'Enable IC3 new mode',
      category: 'IC3',
      dependsOn: { method: 'ic3' }
    },
    ic3Aiger: {
      label: 'IC3 AIGER Output',
      type: 'checkbox',
      help: 'Print instance in AIGER format (for IC3)',
      category: 'IC3',
      dependsOn: { method: 'ic3' }
    },
    
    // Verilog Options
    includePath: {
      label: 'Include Paths',
      type: 'text',
      placeholder: '/path/to/includes',
      help: 'Verilog include paths, comma-separated (-I)',
      category: 'Verilog'
    },
    defines: {
      label: 'Preprocessor Defines',
      type: 'text',
      placeholder: 'VAR1=value,VAR2,VAR3=123',
      help: 'Comma-separated defines: VAR or VAR=value (-D)',
      category: 'Verilog'
    },
    layers: {
      label: 'Layer Defines',
      type: 'text',
      placeholder: 'layer$Module,layer$Module$Assert',
      help: 'Comma-separated layer defines to enable (-D layer$...)',
      category: 'Verilog'
    },
    systemverilog: {
      label: 'Force SystemVerilog',
      type: 'checkbox',
      help: 'Force SystemVerilog parsing instead of Verilog',
      category: 'Verilog'
    },
    reset: {
      label: 'Reset Expression',
      type: 'text',
      placeholder: 'rst',
      help: 'Set module reset signal name',
      category: 'Verilog'
    },
    ignoreInitial: {
      label: 'Ignore Initial Blocks',
      type: 'checkbox',
      help: 'Disregard Verilog initial blocks',
      category: 'Verilog'
    },
    initialZero: {
      label: 'Initialize to Zero',
      type: 'checkbox',
      help: 'Initialize all variables with zero',
      category: 'Verilog'
    },
    
    // Advanced/Debug
    livenessToSafety: {
      label: 'Liveness to Safety',
      type: 'checkbox',
      help: 'Transform liveness properties to safety properties',
      category: 'Advanced'
    },
    buechi: {
      label: 'Buechi Automaton',
      type: 'checkbox',
      help: 'Translate LTL/SVA properties to Buechi acceptance',
      category: 'Advanced'
    },
    rankingFunction: {
      label: 'Ranking Function',
      type: 'text',
      placeholder: 'function_expr',
      help: 'Prove liveness using ranking function (experimental)',
      category: 'Advanced'
    },
    neuralLiveness: {
      label: 'Neural Liveness',
      type: 'checkbox',
      help: 'Check liveness using neural inference (experimental)',
      category: 'Advanced'
    },
    neuralEngine: {
      label: 'Neural Engine Command',
      type: 'text',
      placeholder: 'neural_cmd',
      help: 'Neural engine to use for liveness checking',
      category: 'Advanced',
      dependsOn: { neuralLiveness: true }
    },
    randomWaveform: {
      label: 'Random Waveform',
      type: 'checkbox',
      help: 'Generate random trace and show in horizontal form',
      category: 'Advanced'
    },
    dotNetlist: {
      label: 'DOT Netlist',
      type: 'checkbox',
      help: 'Show netlist in DOT format',
      category: 'Advanced'
    },
    smvNetlist: {
      label: 'SMV Netlist',
      type: 'checkbox',
      help: 'Show netlist in SMV format',
      category: 'Advanced'
    },
    smvWordLevel: {
      label: 'SMV Word-Level',
      type: 'checkbox',
      help: 'Output word-level SMV',
      category: 'Advanced'
    },
    preprocess: {
      label: 'Show Preprocessed',
      type: 'checkbox',
      help: 'Output the preprocessed source file',
      category: 'Advanced'
    },
    showParse: {
      label: 'Show Parse Tree',
      type: 'checkbox',
      help: 'Display parse trees',
      category: 'Advanced'
    },
    showModules: {
      label: 'Show Modules',
      type: 'checkbox',
      help: 'List all modules in the design',
      category: 'Advanced'
    },
    showModuleHierarchy: {
      label: 'Show Module Hierarchy',
      type: 'checkbox',
      help: 'Display hierarchy of module instantiations',
      category: 'Advanced'
    },
    showVarmap: {
      label: 'Show Variable Map',
      type: 'checkbox',
      help: 'Display variable mapping',
      category: 'Advanced'
    },
    showNetlist: {
      label: 'Show Netlist',
      type: 'checkbox',
      help: 'Display the netlist',
      category: 'Advanced'
    },
    showLdg: {
      label: 'Show Latch Dependencies',
      type: 'checkbox',
      help: 'Display latch dependency graph',
      category: 'Advanced'
    },
    showFormula: {
      label: 'Show Formula',
      type: 'checkbox',
      help: 'Display the generated formula',
      category: 'Advanced'
    },
    showTrans: {
      label: 'Show Transition System',
      type: 'checkbox',
      help: 'Display the transition system',
      category: 'Advanced'
    },
    verbosity: {
      label: 'Verbosity',
      type: 'number',
      min: 0,
      max: 10,
      help: 'Output verbosity (0=silent, 10=everything)',
      category: 'Advanced'
    }
  };

  // Group parameters by category
  const categories = ['Core', 'Methods', 'Output', 'Solver', 'IC3', 'Verilog', 'Advanced'];
  
  const getParamsByCategory = (category) => {
    return Object.entries(parameters).filter(([_, param]) => param.category === category);
  };

  // Check if parameter should be shown (dependencies)
  const shouldShowParam = (param) => {
    if (!param.dependsOn) return true;
    return Object.entries(param.dependsOn).every(([key, value]) => config[key] === value);
  };

  // Render individual parameter input
  const renderParam = (key, param) => {
    if (!shouldShowParam(param)) return null;

    const value = config[key] ?? '';
    
    return (
      <div key={key} className="space-y-1">
        <div className="flex items-center justify-between">
          <label className="text-xs font-medium text-gray-300 flex items-center gap-1">
            {param.label}
            <button
              type="button"
              onClick={() => toggleHelp(key)}
              className="text-gray-500 hover:text-gray-300 transition-colors"
            >
              <HelpCircle className="w-3 h-3" />
            </button>
          </label>
        </div>
        
        {showHelp[key] && (
          <div className="text-xs text-gray-400 bg-neutral-900 p-2 rounded border border-neutral-700 mb-1">
            {param.help}
          </div>
        )}
        
        {param.type === 'text' && (
          <input
            type="text"
            value={value}
            onChange={(e) => updateParam(key, e.target.value)}
            placeholder={param.placeholder || ''}
            className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
          />
        )}
        
        {param.type === 'number' && (
          <input
            type="number"
            value={value}
            onChange={(e) => updateParam(key, e.target.value)}
            min={param.min}
            max={param.max}
            placeholder={param.placeholder || ''}
            className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
          />
        )}
        
        {param.type === 'select' && (
          <select
            value={value}
            onChange={(e) => updateParam(key, e.target.value)}
            className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
          >
            {param.options.map(opt => (
              <option key={opt.value} value={opt.value}>{opt.label}</option>
            ))}
          </select>
        )}
        
        {param.type === 'checkbox' && (
          <label className="flex items-center space-x-2 cursor-pointer">
            <input
              type="checkbox"
              checked={value === true}
              onChange={(e) => updateParam(key, e.target.checked)}
              className="form-checkbox h-4 w-4 text-blue-600 bg-neutral-700 border-neutral-600 rounded focus:ring-blue-500"
            />
            <span className="text-xs text-gray-400">Enable</span>
          </label>
        )}
      </div>
    );
  };

  return (
    <div className="bg-neutral-800 rounded-lg border border-neutral-700">
      {/* Header */}
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full flex items-center justify-between p-3 hover:bg-neutral-750 transition-colors"
      >
        <div className="flex items-center space-x-2">
          <Settings className="w-4 h-4 text-blue-400" />
          <span className="text-sm font-semibold text-gray-200">EBMC Parameters</span>
          <span className="text-xs text-gray-500">
            ({Object.values(config).filter(v => v !== undefined && v !== '').length} active)
          </span>
        </div>
        {isExpanded ? <ChevronUp className="w-4 h-4" /> : <ChevronDown className="w-4 h-4" />}
      </button>

      {/* Expandable Content */}
      {isExpanded && (
        <div className="p-3 border-t border-neutral-700 max-h-96 overflow-y-auto space-y-4">
          {categories.map(category => {
            const params = getParamsByCategory(category);
            if (params.length === 0) return null;
            
            return (
              <div key={category} className="space-y-2">
                <div className="text-xs font-semibold text-blue-400 uppercase tracking-wide border-b border-neutral-700 pb-1">
                  {category}
                </div>
                <div className="space-y-3">
                  {params.map(([key, param]) => renderParam(key, param))}
                </div>
              </div>
            );
          })}
          
          {/* Reset Button */}
          <button
            onClick={() => onChange({})}
            className="w-full mt-4 px-3 py-2 bg-red-900/20 hover:bg-red-900/30 text-red-400 rounded text-xs font-medium transition-colors"
          >
            Reset All Parameters
          </button>
        </div>
      )}
    </div>
  );
};

export default EbmcConfig;
