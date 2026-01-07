// File system management using IndexedDB for local storage
// This provides a virtual file system for the IDE

const DB_NAME = 'ChiselForgeFS';
const DB_VERSION = 1;
const STORE_NAME = 'files';

export default class FileSystem {
  constructor() {
    this.db = null;
    this.ready = false;
  }

  async init() {
    if (this.ready) return;
    
    return new Promise((resolve, reject) => {
      const request = indexedDB.open(DB_NAME, DB_VERSION);
      
      request.onerror = () => reject(request.error);
      
      request.onsuccess = () => {
        this.db = request.result;
        this.ready = true;
        resolve();
      };
      
      request.onupgradeneeded = (event) => {
        const db = event.target.result;
        if (!db.objectStoreNames.contains(STORE_NAME)) {
          const store = db.createObjectStore(STORE_NAME, { keyPath: 'path' });
          store.createIndex('directory', 'directory', { unique: false });
          store.createIndex('type', 'type', { unique: false });
        }
      };
    });
  }

  async ensureReady() {
    if (!this.ready) {
      await this.init();
    }
  }

  async createFile(path, content = '', type = 'scala') {
    await this.ensureReady();
    
    const file = {
      path,
      content,
      type,
      directory: this.getDirectory(path),
      name: this.getFileName(path),
      created: Date.now(),
      modified: Date.now()
    };

    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readwrite');
      const store = transaction.objectStore(STORE_NAME);
      const request = store.add(file);
      
      request.onsuccess = () => resolve(file);
      request.onerror = () => reject(request.error);
    });
  }

  async readFile(path) {
    await this.ensureReady();
    
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readonly');
      const store = transaction.objectStore(STORE_NAME);
      const request = store.get(path);
      
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }

  async updateFile(path, content) {
    await this.ensureReady();
    
    const file = await this.readFile(path);
    if (!file) {
      throw new Error(`File not found: ${path}`);
    }
    
    file.content = content;
    file.modified = Date.now();

    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readwrite');
      const store = transaction.objectStore(STORE_NAME);
      const request = store.put(file);
      
      request.onsuccess = () => resolve(file);
      request.onerror = () => reject(request.error);
    });
  }

  async deleteFile(path) {
    await this.ensureReady();
    
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readwrite');
      const store = transaction.objectStore(STORE_NAME);
      const request = store.delete(path);
      
      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }

  async listFiles(directory = '') {
    await this.ensureReady();
    
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readonly');
      const store = transaction.objectStore(STORE_NAME);
      const index = store.index('directory');
      const request = directory === '' ? store.getAll() : index.getAll(directory);
      
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }

  async renameFile(oldPath, newPath) {
    await this.ensureReady();
    
    const file = await this.readFile(oldPath);
    if (!file) {
      throw new Error(`File not found: ${oldPath}`);
    }
    
    await this.deleteFile(oldPath);
    file.path = newPath;
    file.name = this.getFileName(newPath);
    file.directory = this.getDirectory(newPath);
    file.modified = Date.now();
    
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([STORE_NAME], 'readwrite');
      const store = transaction.objectStore(STORE_NAME);
      const request = store.add(file);
      
      request.onsuccess = () => resolve(file);
      request.onerror = () => reject(request.error);
    });
  }

  async exportToZip() {
    // TODO: Implement ZIP export using JSZip
    const files = await this.listFiles();
    return files;
  }

  async importFromZip(zipFile) {
    // TODO: Implement ZIP import
  }

  getDirectory(path) {
    const lastSlash = path.lastIndexOf('/');
    return lastSlash === -1 ? '' : path.substring(0, lastSlash);
  }

  getFileName(path) {
    const lastSlash = path.lastIndexOf('/');
    return lastSlash === -1 ? path : path.substring(lastSlash + 1);
  }

  // Get all unique directories for tree view
  async getDirectoryTree() {
    const files = await this.listFiles();
    const tree = { name: 'root', path: '', children: [], files: [] };
    
    files.forEach(file => {
      const parts = file.path.split('/');
      let current = tree;
      
      // Navigate/create directory structure
      for (let i = 0; i < parts.length - 1; i++) {
        const dirName = parts[i];
        let child = current.children.find(c => c.name === dirName);
        
        if (!child) {
          child = {
            name: dirName,
            path: parts.slice(0, i + 1).join('/'),
            children: [],
            files: []
          };
          current.children.push(child);
        }
        
        current = child;
      }
      
      // Add file to current directory
      current.files.push(file);
    });
    
    return tree;
  }

  // Initialize with example files
  async initializeExamples(examples) {
    await this.ensureReady();
    
    const existingFiles = await this.listFiles();
    if (existingFiles.length > 0) {
      console.log('File system already initialized');
      return;
    }
    
    console.log('Initializing file system with examples...');
    
    for (const [name, example] of Object.entries(examples)) {
      await this.createFile(`examples/${name}.scala`, example.chisel, 'scala');
    }
  }
}

