import React, { useState, useRef, useEffect } from 'react';

const ResizablePanel = ({ 
  children, 
  width,
  onResize,
  minWidth = 200,
  maxWidth = 800,
  side = 'left', // 'left', 'right', 'bottom'
  className = ''
}) => {
  const [isResizing, setIsResizing] = useState(false);
  const panelRef = useRef(null);
  const startPosRef = useRef(0);
  const startSizeRef = useRef(0);

  const handleMouseDown = (e) => {
    setIsResizing(true);
    startPosRef.current = side === 'bottom' ? e.clientY : e.clientX;
    startSizeRef.current = width;
    e.preventDefault();
  };

  useEffect(() => {
    const handleMouseMove = (e) => {
      if (!isResizing) return;

      const currentPos = side === 'bottom' ? e.clientY : e.clientX;
      let delta = currentPos - startPosRef.current;
      
      // Adjust delta based on panel side
      if (side === 'right') delta = -delta;
      if (side === 'bottom') delta = -delta;
      
      const newSize = Math.max(minWidth, Math.min(maxWidth, startSizeRef.current + delta));
      onResize(newSize);
    };

    const handleMouseUp = () => {
      setIsResizing(false);
    };

    if (isResizing) {
      document.addEventListener('mousemove', handleMouseMove);
      document.addEventListener('mouseup', handleMouseUp);
      document.body.style.cursor = side === 'bottom' ? 'ns-resize' : 'ew-resize';
      document.body.style.userSelect = 'none';
    }

    return () => {
      document.removeEventListener('mousemove', handleMouseMove);
      document.removeEventListener('mouseup', handleMouseUp);
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    };
  }, [isResizing, side, minWidth, maxWidth, onResize]);

  const style = side === 'bottom' 
    ? { height: `${width}px` }
    : { width: `${width}px` };

  // Position resize handle based on side
  const handleClass = side === 'left' 
    ? 'right-0 top-0 bottom-0 w-1 cursor-ew-resize'
    : side === 'right'
    ? 'left-0 top-0 bottom-0 w-1 cursor-ew-resize'
    : 'left-0 right-0 top-0 h-1 cursor-ns-resize';

  return (
    <div ref={panelRef} style={style} className={`relative ${className}`}>
      {children}
      <div
        onMouseDown={handleMouseDown}
        className={`absolute ${handleClass} hover:bg-blue-500/50 active:bg-blue-500 ${
          isResizing ? 'bg-blue-500' : 'bg-transparent hover:bg-blue-400/30'
        } transition-colors z-50`}
      />
    </div>
  );
};

export default ResizablePanel;

