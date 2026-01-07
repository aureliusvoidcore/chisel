import React, { useEffect, useRef, useState } from 'react';
import compilationService from '../api';

const BASE_URL = (import.meta.env.BASE_URL ?? './');

const SurferViewer = ({ vcdUrl }) => {
  const iframeRef = useRef(null);
  const [blobUrl, setBlobUrl] = useState(null);

  useEffect(() => {
    const loadVcd = async () => {
      if (!vcdUrl) return;

      try {
        let blob;
        // Check if it's a full path or the module/file format
        if (vcdUrl.startsWith('/')) {
             blob = await compilationService.readFileBlob(vcdUrl);
        } else {
             // Try to guess. If it has a slash, maybe it's module/file
             // App.jsx sends "PWMLEDAXI/trace.vcd"
             // And my api.js saved it to "/verification/PWMLEDAXI/trace.vcd"
             
             // Let's try the verification path first if it looks like module/file
             if (vcdUrl.includes('/') && !vcdUrl.startsWith('verification')) {
                 try {
                     blob = await compilationService.readFileBlob(`/verification/${vcdUrl}`);
                 } catch (e) {
                     // Fallback to root
                     blob = await compilationService.readFileBlob(vcdUrl);
                 }
             } else {
                 blob = await compilationService.readFileBlob(vcdUrl);
             }
        }
        
        const url = URL.createObjectURL(blob);
        setBlobUrl(url);
      } catch (e) {
        console.error("Failed to load VCD", e);
      }
    };
    loadVcd();
  }, [vcdUrl]);

  useEffect(() => {
    if (iframeRef.current && blobUrl) {
      const surferUrl = `${BASE_URL}surfer/index.html?load_url=${encodeURIComponent(blobUrl)}`;
      iframeRef.current.src = surferUrl;
    }
  }, [blobUrl]);

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
