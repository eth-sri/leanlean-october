module
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ResidueCalcOnRectangles
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ZetaBoundsUpstream
public import GuthMaynard.NativeSource.GuthMaynard.GammaPairBound
public import GuthMaynard.NativeSource.GuthMaynard.TwistedDiagonal

@[expose] public section

open Complex Filter MeasureTheory Set Topology ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation

noncomputable section

/-!
# The completed-zeta contour for the smooth fourth-moment AFE
This file formalizes the source entry to Hughes--Young Proposition 2.1 in
the unshifted case.  The pole-cancelling completion below is entire, has the
functional-equation symmetry required to reflect the left side of the
contour, and retains the exact zeta factors on the critical line.
-/
-- The literal half argument matches the source statement and is intentionally retained.
