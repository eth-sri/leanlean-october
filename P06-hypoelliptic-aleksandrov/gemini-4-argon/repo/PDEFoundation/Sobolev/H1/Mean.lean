module

public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.W1p.Mean

/-!
# Integral means for representative-level `H¹`

This file is the LIH-compatible `p = 2` facade over the generic
`W1pFunction` mean API. Constants, addition of constants, subtraction of the
average, and the zero-mean theorem are transported without repeating the
underlying integrability or weak-derivative arguments.
-/

