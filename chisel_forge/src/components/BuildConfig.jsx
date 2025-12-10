import React, { useState } from 'react';
import { Settings2, ChevronDown, ChevronUp } from 'lucide-react';

const BuildConfig = ({ config, onChange }) => {
  const [isExpanded, setIsExpanded] = useState(false);
  const [activeTab, setActiveTab] = useState('chisel');

  const updateConfig = (key, value) => {
    onChange({ ...config, [key]: value });
  };

  return (
    <div className="bg-neutral-800 rounded-lg border border-neutral-700">
      <button
        onClick={() => setIsExpanded(!isExpanded)}
        className="w-full flex items-center justify-between p-3 hover:bg-neutral-750 transition-colors"
      >
        <div className="flex items-center space-x-2">
          <Settings2 className="w-4 h-4 text-purple-400" />
          <span className="text-sm font-semibold text-gray-200">Build Configuration</span>
        </div>
        {isExpanded ? <ChevronUp className="w-4 h-4" /> : <ChevronDown className="w-4 h-4" />}
      </button>

      {isExpanded && (
        <div className="border-t border-neutral-700">
          {/* Tabs */}
          <div className="flex border-b border-neutral-700 bg-neutral-900">
            {['chisel', 'scala', 'makefile'].map(tab => (
              <button
                key={tab}
                onClick={() => setActiveTab(tab)}
                className={`px-4 py-2 text-xs font-medium transition-colors ${
                  activeTab === tab
                    ? 'text-blue-400 border-b-2 border-blue-400 bg-neutral-800'
                    : 'text-gray-500 hover:text-gray-300'
                }`}
              >
                {tab.toUpperCase()}
              </button>
            ))}
          </div>

          {/* Content */}
          <div className="p-3 space-y-3 max-h-80 overflow-y-auto">
            {activeTab === 'chisel' && (
              <>
                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Mode</label>
                  <select
                    value={config.mode || 'verification'}
                    onChange={(e) => updateConfig('mode', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  >
                    <option value="verification">Verification</option>
                    <option value="synthesis">Synthesis</option>
                  </select>
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Layers</label>
                  <select
                    value={config.layers || 'inline'}
                    onChange={(e) => updateConfig('layers', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  >
                    <option value="inline">Inline</option>
                    <option value="split">Split (bind)</option>
                  </select>
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Preserve Values</label>
                  <select
                    value={config.preserve_values || 'named'}
                    onChange={(e) => updateConfig('preserve_values', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  >
                    <option value="named">Named</option>
                    <option value="all">All</option>
                    <option value="none">None</option>
                  </select>
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Randomization</label>
                  <select
                    value={config.randomization || 'disable'}
                    onChange={(e) => updateConfig('randomization', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  >
                    <option value="disable">Disabled</option>
                    <option value="enable">Enabled</option>
                  </select>
                </div>
              </>
            )}

            {activeTab === 'scala' && (
              <>
                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Scala Version</label>
                  <input
                    type="text"
                    value={config.scalaVersion || '2.13.14'}
                    onChange={(e) => updateConfig('scalaVersion', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  />
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">JVM Options</label>
                  <input
                    type="text"
                    value={config.jvmOptions || '-Xmx4G -Xss256M'}
                    onChange={(e) => updateConfig('jvmOptions', e.target.value)}
                    placeholder="-Xmx4G -Xss256M"
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  />
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Compiler Options</label>
                  <input
                    type="text"
                    value={config.scalacOptions || '-deprecation -feature'}
                    onChange={(e) => updateConfig('scalacOptions', e.target.value)}
                    placeholder="-deprecation -feature"
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  />
                </div>
              </>
            )}

            {activeTab === 'makefile' && (
              <>
                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Output Directory</label>
                  <input
                    type="text"
                    value={config.outputDir || 'generated'}
                    onChange={(e) => updateConfig('outputDir', e.target.value)}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  />
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Firtool Options</label>
                  <input
                    type="text"
                    value={config.firtoolOptions || '--disable-all-randomization'}
                    onChange={(e) => updateConfig('firtoolOptions', e.target.value)}
                    placeholder="--disable-all-randomization"
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500"
                  />
                </div>

                <div>
                  <label className="text-xs font-medium text-gray-300 block mb-1">Custom Make Targets</label>
                  <textarea
                    value={config.makeTargets || ''}
                    onChange={(e) => updateConfig('makeTargets', e.target.value)}
                    placeholder="Additional make targets..."
                    rows={3}
                    className="w-full bg-neutral-700 border border-neutral-600 rounded px-2 py-1.5 text-xs text-gray-200 focus:outline-none focus:border-blue-500 resize-none"
                  />
                </div>

                <div>
                  <label className="flex items-center space-x-2 cursor-pointer">
                    <input
                      type="checkbox"
                      checked={config.cleanBuild || false}
                      onChange={(e) => updateConfig('cleanBuild', e.target.checked)}
                      className="form-checkbox h-4 w-4 text-blue-600 bg-neutral-700 border-neutral-600 rounded focus:ring-blue-500"
                    />
                    <span className="text-xs text-gray-300">Clean build before compile</span>
                  </label>
                </div>
              </>
            )}
          </div>
        </div>
      )}
    </div>
  );
};

export default BuildConfig;
