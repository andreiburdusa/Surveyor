# Surveyor

R1CS binary format to Lean extractor.

## Dependencies

Requires Haskell stack.

## Usage

```
stack run *.r1cs
```

Resulting extracted Lean outputted to stdout, tested with `leanprover/lean4:v4.17.0-rc1`.
See `examples/circom/` for circom examples and `examples/Lean` for extracted examples.
