import React, { useEffect, useRef } from 'react';

const SurferViewer = ({ vcdUrl }) => {
  const iframeRef = useRef(null);

  useEffect(() => {
    if (iframeRef.current && vcdUrl) {
      // Construct the URL with the load_url parameter
      // We use the proxy configured in vite.config.js to access /api/files
      // If vcdUrl is already a full URL (e.g. external), use it.
      // Otherwise, assume it's a relative path to a generated file.
      
      // Note: We need to pass a URL that is accessible from the browser.
      // Since we have a proxy for /api, we can use the current origin + /api/files
      
      const fileUrl = vcdUrl.startsWith('http') 
        ? vcdUrl 
        : `${window.location.origin}/api/files/${vcdUrl}`;
        
      const surferUrl = `/surfer/index.html?load_url=${encodeURIComponent(fileUrl)}`;
      iframeRef.current.src = surferUrl;
    }
  }, [vcdUrl]);

  return (
    <div className="w-full h-full bg-neutral-900 flex flex-col">
      <iframe
        ref={iframeRef}
        title="Surfer Waveform Viewer"
        className="w-full h-full border-none"
        allow="clipboard-read; clipboard-write"
      />
    </div>
  );
};

export default SurferViewer;
