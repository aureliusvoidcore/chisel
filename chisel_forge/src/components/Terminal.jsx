import React, { useRef, useEffect } from 'react';
import { Terminal as TerminalIcon, X, Copy, Trash2 } from 'lucide-react';
import { useTheme } from '../ThemeContext';

const Terminal = ({ logs = [], title = 'Output', onClear }) => {
  const terminalRef = useRef(null);
  const { theme } = useTheme();

  useEffect(() => {
    if (terminalRef.current) {
      terminalRef.current.scrollTop = terminalRef.current.scrollHeight;
    }
  }, [logs]);

  const handleCopy = () => {
    const text = logs.join('\n');
    navigator.clipboard.writeText(text);
  };

  const getLineColor = (line) => {
    if (line.includes('✓') || line.includes('SUCCESSFUL') || line.includes('success') || line.includes('Proved:')) {
      return theme.success;
    }
    if (line.includes('✗') || line.includes('FAILED') || line.includes('Error') || line.includes('error') || line.includes('Failed:')) {
      return theme.error;
    }
    if (line.includes('Warning') || line.includes('warning') || line.includes('~') || line.includes('Inconclusive:')) {
      return theme.warning;
    }
    if (line.includes('[') || line.includes('Compiler') || line.includes('Backend') || line.includes('Verifier')) {
      return 'text-blue-400';
    }
    return theme.textMuted;
  };

  return (
    <div className={`flex flex-col h-full ${theme.surfaceAlt}`}>
      <div className={`flex items-center justify-between px-4 py-2 ${theme.surface} ${theme.border} border-b`}>
        <div className="flex items-center space-x-2">
          <TerminalIcon className={`w-4 h-4 ${theme.textMuted}`} />
          <span className={`text-sm font-medium ${theme.text}`}>{title}</span>
          <span className={`text-xs ${theme.textDim}`}>({logs.length} lines)</span>
        </div>
        <div className="flex items-center space-x-2">
          <button
            onClick={handleCopy}
            className={`p-1.5 hover:${theme.surface} rounded transition-colors`}
            title="Copy to clipboard"
          >
            <Copy className={`w-4 h-4 ${theme.textMuted}`} />
          </button>
          <button
            onClick={onClear}
            className={`p-1.5 hover:${theme.surface} rounded transition-colors`}
            title="Clear output"
          >
            <Trash2 className={`w-4 h-4 ${theme.textMuted}`} />
          </button>
        </div>
      </div>
      
      <div
        ref={terminalRef}
        className="flex-1 overflow-y-auto p-4 font-mono text-xs space-y-0.5"
      >
        {logs.length === 0 ? (
          <div className={`${theme.textDim} italic`}>Terminal output will appear here...</div>
        ) : (
          logs.map((line, i) => (
            <div key={i} className={`leading-relaxed ${getLineColor(line)}`}>
              <span className={`${theme.textDim} mr-2 select-none`}>{String(i + 1).padStart(3, ' ')}</span>
              {line}
            </div>
          ))
        )}
      </div>
    </div>
  );
};

export default Terminal;

