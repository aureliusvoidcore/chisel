import React, { useState, useEffect } from 'react';
import { File, RefreshCw, Eye } from 'lucide-react';
import compilationService from '../api';

const FileSystem = ({ onFileSelect }) => {
  const [files, setFiles] = useState([]);
  const [loading, setLoading] = useState(false);

  const fetchFiles = async () => {
    setLoading(true);
    try {
      const all = await compilationService.listFiles();
      const paths = (all || [])
        .map((f) => (typeof f === 'string' ? f : f?.path))
        .filter(Boolean);
      // Show only verification artifacts by default
      const filtered = paths.filter(p => p.startsWith('/verification/'));
      setFiles(filtered.length ? filtered : paths);
    } catch (error) {
      console.error('Failed to fetch files:', error);
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    fetchFiles();
  }, []);

  const handleFileClick = (file) => {
    console.log('File clicked:', file);
    if (file.endsWith('.vcd')) {
      console.log('Selecting VCD file:', file);
      if (onFileSelect) {
        onFileSelect(file);
      } else {
        console.error('onFileSelect prop is missing');
      }
    } else {
      console.log('Not a VCD file, ignoring');
    }
  };

  return (
    <div className="flex flex-col h-full bg-neutral-900 text-gray-300">
      <div className="flex items-center justify-between p-2 border-b border-neutral-700 bg-neutral-800">
        <span className="font-semibold text-sm">Generated Files</span>
        <button onClick={fetchFiles} className="p-1 hover:bg-neutral-700 rounded">
          <RefreshCw className={`w-4 h-4 ${loading ? 'animate-spin' : ''}`} />
        </button>
      </div>
      <div className="flex-1 overflow-y-auto p-2">
        {files.length === 0 ? (
          <div className="text-center text-gray-500 text-sm mt-4">No files found</div>
        ) : (
          <ul className="space-y-1">
            {files.map((file, index) => (
              <li 
                key={index}
                className={`flex items-center justify-between p-2 rounded hover:bg-neutral-800 cursor-pointer group ${
                  file.endsWith('.vcd') ? 'text-blue-400' : 'text-gray-400'
                }`}
                onClick={() => handleFileClick(file)}
              >
                <div className="flex items-center space-x-2 truncate">
                  <File className="w-4 h-4 shrink-0" />
                  <span className="text-sm truncate" title={file}>{file}</span>
                </div>
                {file.endsWith('.vcd') && (
                  <button 
                    onClick={(e) => {
                      e.stopPropagation();
                      console.log('Eye icon clicked for:', file);
                      handleFileClick(file);
                    }}
                    className="p-1 hover:bg-neutral-700 rounded focus:outline-none"
                    title="View Waveform"
                  >
                    <Eye className="w-4 h-4 text-gray-400 group-hover:text-blue-400 transition-colors" />
                  </button>
                )}
              </li>
            ))}
          </ul>
        )}
      </div>
    </div>
  );
};

export default FileSystem;
