import React, { createContext, useContext, useState, useEffect } from 'react';

const ThemeContext = createContext();

export const useTheme = () => {
  const context = useContext(ThemeContext);
  if (!context) {
    throw new Error('useTheme must be used within ThemeProvider');
  }
  return context;
};

export const themes = {
  dark: {
    name: 'dark',
    background: 'bg-neutral-900',
    surface: 'bg-neutral-800',
    surfaceAlt: 'bg-neutral-950',
    border: 'border-neutral-700',
    text: 'text-gray-200',
    textMuted: 'text-gray-400',
    textDim: 'text-gray-500',
    primary: 'bg-blue-600',
    primaryHover: 'hover:bg-blue-500',
    secondary: 'bg-purple-600',
    secondaryHover: 'hover:bg-purple-500',
    success: 'text-green-400',
    error: 'text-red-400',
    warning: 'text-yellow-400',
    monacoTheme: 'vs-dark'
  },
  light: {
    name: 'light',
    background: 'bg-gray-50',
    surface: 'bg-white',
    surfaceAlt: 'bg-gray-100',
    border: 'border-gray-300',
    text: 'text-gray-900',
    textMuted: 'text-gray-600',
    textDim: 'text-gray-500',
    primary: 'bg-blue-500',
    primaryHover: 'hover:bg-blue-600',
    secondary: 'bg-purple-500',
    secondaryHover: 'hover:bg-purple-600',
    success: 'text-green-600',
    error: 'text-red-600',
    warning: 'text-yellow-600',
    monacoTheme: 'vs'
  }
};

export const ThemeProvider = ({ children }) => {
  const [currentTheme, setCurrentTheme] = useState('dark');

  useEffect(() => {
    // Load theme preference from localStorage
    const savedTheme = localStorage.getItem('chiselforge-theme');
    if (savedTheme && themes[savedTheme]) {
      setCurrentTheme(savedTheme);
    }
  }, []);

  const toggleTheme = () => {
    const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
    setCurrentTheme(newTheme);
    localStorage.setItem('chiselforge-theme', newTheme);
  };

  const theme = themes[currentTheme];

  return (
    <ThemeContext.Provider value={{ theme, currentTheme, toggleTheme, themes }}>
      {children}
    </ThemeContext.Provider>
  );
};
