# Quick EBMC Parameters Guide

## Most Common Use Cases

### 1. Generate VCD for Failed Properties
```javascript
// In ChiselForge UI, expand "EBMC Parameters"
Bound: 20
VCD Output: counterexample.vcd
```
Click Verify → If properties fail → Download button appears

### 2. Deeper Bound Verification
```javascript
Bound: 100
Method: K-Induction
```

### 3. Use IC3 for Complex Properties
```javascript
Method: IC3
Verbosity: 3  // See progress
```

### 4. Debug Mode
```javascript
Bound: 50
VCD Output: debug.vcd
Trace: ✓ Enable
Waveform: ✓ Enable
Verbosity: 5
```

## Parameter Quick Reference

| Parameter | Type | Purpose | Example |
|-----------|------|---------|---------|
| Bound | Number | Max unroll depth | 20, 50, 100 |
| Method | Select | Algorithm | k-induction, ic3, bdd |
| VCD Output | Text | CEX waveform file | counter.vcd |
| Trace | Checkbox | Text trace | ✓ |
| Verbosity | Number | Debug level | 0-10 |
| Solver | Select | SAT/SMT engine | z3, cvc4 |

## Tips

- **Start Small**: Bound 10-20 for initial verification
- **Increase Gradually**: If inconclusive, try larger bounds
- **Use K-Induction**: Often faster for safety properties
- **Enable VCD**: Always helpful for understanding failures
- **Try IC3**: Best for complex state machines
- **Watch Verbosity**: High values slow verification

## VCD Files

- Generated only when properties **fail**
- Download via green button in UI
- Open with GTKWave or similar viewer
- Shows exact counterexample trace
