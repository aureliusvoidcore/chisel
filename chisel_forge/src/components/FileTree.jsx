import React, { useState } from 'react';
import { ChevronRight, ChevronDown, File, Folder, FolderOpen, Plus, Upload, Trash2, Edit3, FileText } from 'lucide-react';
import { useTheme } from '../ThemeContext';

const FileTreeItem = ({ item, level = 0, onSelectFile, selectedFile, onRenameFile, onDeleteFile }) => {
  const [isOpen, setIsOpen] = useState(true);
  const [isEditing, setIsEditing] = useState(false);
  const [editName, setEditName] = useState('');
  const { theme } = useTheme();
  const isDirectory = item.children !== undefined;
  const isSelected = selectedFile === item.path;

  const handleRename = () => {
    setEditName(item.name);
    setIsEditing(true);
  };

  const handleRenameSubmit = () => {
    if (editName && editName !== item.name) {
      const newPath = item.path.replace(item.name, editName);
      onRenameFile(item.path, newPath);
    }
    setIsEditing(false);
  };

  const handleRenameCancel = () => {
    setIsEditing(false);
    setEditName('');
  };

  return (
    <div>
      {isDirectory ? (
        <div>
          <div
            className={`flex items-center space-x-2 py-1.5 px-2 cursor-pointer hover:${theme.surface} rounded transition-colors`}
            style={{ paddingLeft: `${level * 12 + 8}px` }}
            onClick={() => setIsOpen(!isOpen)}
          >
            {isOpen ? (
              <ChevronDown className={`w-4 h-4 ${theme.textMuted}`} />
            ) : (
              <ChevronRight className={`w-4 h-4 ${theme.textMuted}`} />
            )}
            {isOpen ? (
              <FolderOpen className="w-4 h-4 text-yellow-500" />
            ) : (
              <Folder className="w-4 h-4 text-yellow-500" />
            )}
            <span className={`text-sm ${theme.text}`}>{item.name || 'root'}</span>
          </div>
          {isOpen && (
            <div>
              {item.children.map((child, idx) => (
                <FileTreeItem
                  key={idx}
                  item={child}
                  level={level + 1}
                  onSelectFile={onSelectFile}
                  selectedFile={selectedFile}
                  onRenameFile={onRenameFile}
                  onDeleteFile={onDeleteFile}
                />
              ))}
              {item.files.map((file, idx) => (
                <FileTreeItem
                  key={`file-${idx}`}
                  item={file}
                  level={level + 1}
                  onSelectFile={onSelectFile}
                  selectedFile={selectedFile}
                  onRenameFile={onRenameFile}
                  onDeleteFile={onDeleteFile}
                />
              ))}
            </div>
          )}
        </div>
      ) : (
        <div
          className={`flex items-center justify-between space-x-2 py-1.5 px-2 cursor-pointer rounded transition-colors group ${
            isSelected ? 'bg-blue-900/40 text-blue-300 border border-blue-700/50' : `${theme.textMuted} hover:${theme.surface}`
          }`}
          style={{ paddingLeft: `${level * 12 + 8}px` }}
          onClick={() => onSelectFile(item)}
        >
          <div className="flex items-center space-x-2 flex-1 min-w-0">
            <FileText className="w-4 h-4 flex-shrink-0 text-orange-500" />
            {isEditing ? (
              <input
                type="text"
                value={editName}
                onChange={(e) => setEditName(e.target.value)}
                onBlur={handleRenameSubmit}
                onKeyDown={(e) => {
                  if (e.key === 'Enter') handleRenameSubmit();
                  if (e.key === 'Escape') handleRenameCancel();
                }}
                className={`flex-1 ${theme.surfaceAlt} border border-blue-500 rounded px-1 py-0 text-xs ${theme.text} focus:outline-none`}
                autoFocus
                onClick={(e) => e.stopPropagation()}
              />
            ) : (
              <span className="text-sm truncate">{item.name}</span>
            )}
          </div>
          <div className="flex items-center space-x-1 opacity-0 group-hover:opacity-100 transition-opacity">
            <button
              onClick={(e) => {
                e.stopPropagation();
                handleRename();
              }}
              className="p-1 hover:bg-neutral-600 rounded"
              title="Rename"
            >
              <Edit3 className="w-3 h-3" />
            </button>
            <button
              onClick={(e) => {
                e.stopPropagation();
                onDeleteFile(item.path);
              }}
              className="p-1 hover:bg-red-900/50 rounded"
              title="Delete"
            >
              <Trash2 className="w-3 h-3" />
            </button>
          </div>
        </div>
      )}
    </div>
  );
};

const FileTree = ({ tree, onSelectFile, selectedFile, onCreateFile, onUploadFile, onRenameFile, onDeleteFile }) => {
  const [showNewFileInput, setShowNewFileInput] = useState(false);
  const [newFileName, setNewFileName] = useState('');

  const handleCreateFile = () => {
    if (newFileName) {
      onCreateFile(newFileName);
      setNewFileName('');
      setShowNewFileInput(false);
    }
  };

  const handleFileUpload = (e) => {
    const file = e.target.files[0];
    if (file) {
      const reader = new FileReader();
      reader.onload = (event) => {
        onUploadFile(file.name, event.target.result);
      };
      reader.readAsText(file);
    }
  };

  return (
    <div className="flex flex-col h-full">
      <div className="flex items-center justify-between p-3 border-b border-neutral-700">
        <span className="font-semibold text-xs uppercase tracking-wider text-gray-500">Files</span>
        <div className="flex items-center space-x-1">
          <button
            onClick={() => setShowNewFileInput(true)}
            className="p-1.5 hover:bg-neutral-700 rounded transition-colors"
            title="New File"
          >
            <Plus className="w-4 h-4 text-gray-400" />
          </button>
          <label className="p-1.5 hover:bg-neutral-700 rounded transition-colors cursor-pointer" title="Upload File">
            <Upload className="w-4 h-4 text-gray-400" />
            <input type="file" onChange={handleFileUpload} className="hidden" accept=".scala,.sv,.v" />
          </label>
        </div>
      </div>
      
      <div className="flex-1 overflow-y-auto p-2">
        {showNewFileInput && (
          <div className="mb-2 px-2">
            <input
              type="text"
              value={newFileName}
              onChange={(e) => setNewFileName(e.target.value)}
              onBlur={handleCreateFile}
              onKeyDown={(e) => {
                if (e.key === 'Enter') handleCreateFile();
                if (e.key === 'Escape') {
                  setShowNewFileInput(false);
                  setNewFileName('');
                }
              }}
              placeholder="filename.scala"
              className="w-full bg-neutral-700 border border-blue-500 rounded px-2 py-1 text-xs text-gray-200 focus:outline-none"
              autoFocus
            />
          </div>
        )}
        
        {tree ? (
          <FileTreeItem
            item={tree}
            onSelectFile={onSelectFile}
            selectedFile={selectedFile}
            onRenameFile={onRenameFile}
            onDeleteFile={onDeleteFile}
          />
        ) : (
          <div className="text-xs text-gray-500 italic p-2">No files yet</div>
        )}
      </div>
    </div>
  );
};

export default FileTree;
