import { configureStore, createSlice } from '@reduxjs/toolkit'

const uiSlice = createSlice({
  name: 'ui',
  initialState: { theme: 'dark' },
  reducers: {
    setTheme(state, action) { state.theme = action.payload }
  }
});

export const { setTheme } = uiSlice.actions;

export const store = configureStore({
  reducer: {
    ui: uiSlice.reducer
  },
})
