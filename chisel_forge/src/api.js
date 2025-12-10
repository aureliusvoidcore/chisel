// API Service for ChiselForge
// Handles communication with the backend compilation server

const API_BASE_URL = import.meta.env.VITE_API_URL || 'http://localhost:3001/api';

class CompilationService {
  constructor() {
    this.baseUrl = API_BASE_URL;
  }

  /**
   * Check if the backend server is available
   */
  async health() {
    try {
      const response = await fetch(`${this.baseUrl}/health`);
      return await response.json();
    } catch (error) {
      throw new Error(`Backend server unreachable: ${error.message}`);
    }
  }

  /**
   * Compile Chisel code to Verilog
   * @param {string} code - The Chisel source code
   * @param {string} moduleName - Name of the module
   * @param {object} config - Compilation configuration
   * @returns {Promise<object>} Compilation result
   */
  async compile(code, moduleName = 'UserModule', config = {}) {
    const response = await fetch(`${this.baseUrl}/compile`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        code,
        moduleName,
        config
      })
    });

    const result = await response.json();
    
    if (!response.ok) {
      throw new Error(result.error || 'Compilation failed');
    }

    return result;
  }

  /**
   * Get list of available examples
   */
  async getExamples() {
    const response = await fetch(`${this.baseUrl}/examples`);
    return await response.json();
  }

  /**
   * Get content of a specific example
   */
  async getExample(name) {
    const response = await fetch(`${this.baseUrl}/examples/${name}`);
    return await response.json();
  }

  /**
   * Run formal verification on a compiled module
   * @param {string} moduleName - Name of the module to verify
   * @param {object} ebmcParams - EBMC parameters configuration object
   * @param {string} verilogCode - Optional modified Verilog code
   * @returns {Promise<object>} Verification result
   */
  async verify(moduleName, ebmcParams = {}, verilogCode = null) {
    const body = {
      moduleName,
      ebmcParams
    };

    if (verilogCode) {
      body.verilogCode = verilogCode;
    }

    const response = await fetch(`${this.baseUrl}/verify`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify(body)
    });

    const result = await response.json();
    
    if (!response.ok && !result.results) {
      throw new Error(result.error || 'Verification failed');
    }

    return result;
  }

  /**
   * Upload a file to the server workspace
   * @param {string} fileName - Name of the file
   * @param {string} content - File content
   * @returns {Promise<object>} Upload result
   */
  async uploadFile(fileName, content) {
    const response = await fetch(`${this.baseUrl}/files/upload`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ fileName, content })
    });

    if (!response.ok) {
      const result = await response.json();
      throw new Error(result.error || 'Upload failed');
    }

    return await response.json();
  }

  /**
   * List files in the server workspace
   * @returns {Promise<Array>} List of files
   */
  async listFiles() {
    const response = await fetch(`${this.baseUrl}/files`);
    
    if (!response.ok) {
      throw new Error('Failed to list files');
    }

    return await response.json();
  }

  /**
   * Download a file from the server workspace
   * @param {string} fileName - Name of the file
   * @returns {Promise<object>} File content
   */
  async downloadFile(fileName) {
    const response = await fetch(`${this.baseUrl}/files/${encodeURIComponent(fileName)}`);
    
    if (!response.ok) {
      const result = await response.json();
      throw new Error(result.error || 'Download failed');
    }

    return await response.json();
  }

  /**
   * Delete a file from the server workspace
   * @param {string} fileName - Name of the file
   * @returns {Promise<object>} Delete result
   */
  async deleteFile(fileName) {
    const response = await fetch(`${this.baseUrl}/files/${encodeURIComponent(fileName)}`, {
      method: 'DELETE'
    });

    if (!response.ok) {
      const result = await response.json();
      throw new Error(result.error || 'Delete failed');
    }

    return await response.json();
  }

  /**
   * Rename a file on the server workspace
   * @param {string} oldName - Current name
   * @param {string} newName - New name
   * @returns {Promise<object>} Rename result
   */
  async renameFile(oldName, newName) {
    const response = await fetch(`${this.baseUrl}/files/rename`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({ oldName, newName })
    });

    if (!response.ok) {
      const result = await response.json();
      throw new Error(result.error || 'Rename failed');
    }

    return await response.json();
  }

  /**
   * Get list of available example modules
   * @returns {Promise<object>} List of examples
   */
  async getExamples() {
    const response = await fetch(`${this.baseUrl}/examples`);
    
    if (!response.ok) {
      throw new Error('Failed to fetch examples');
    }

    return await response.json();
  }

  /**
   * Get content of a specific example file
   * @param {string} name - Example name
   * @returns {Promise<object>} Example content
   */
  async getExample(name) {
    const response = await fetch(`${this.baseUrl}/examples/${name}`);
    
    if (!response.ok) {
      throw new Error(`Example '${name}' not found`);
    }

    return await response.json();
  }

  /**
   * Download VCD file from verification result
   * @param {string} moduleName - Module name
   * @param {string} fileName - VCD file name
   * @returns {Promise<Blob>} VCD file as blob
   */
  async downloadVCD(moduleName, fileName) {
    const response = await fetch(`${this.baseUrl}/vcd/${moduleName}/${fileName}`);
    
    if (!response.ok) {
      const result = await response.json();
      throw new Error(result.error || 'VCD file not found');
    }

    return await response.blob();
  }
}

export default new CompilationService();
