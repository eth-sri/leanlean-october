module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import DensityEnergyGM.DFIWeight
public import GuthMaynard.NativeSource.GuthMaynard.QuadraticDivisor

@[expose] public section

/-!
# DFI equations (9)--(19): the delta symbol
The source chooses an even smooth function `w`, supported where
`Q ≤ |u| ≤ 2Q`, normalized by `∑_{r≥1} w(r)=1`, and satisfying
`w^(j)(u) ≪_j Q^(-j-1)`.  These are equations (9) and (13).
The support makes every series in the delta symbol finite at each argument.
The definitions below expose an explicit radius large enough to contain every
nonzero term; later identities can therefore use ordinary `Finset` algebra.
-/
