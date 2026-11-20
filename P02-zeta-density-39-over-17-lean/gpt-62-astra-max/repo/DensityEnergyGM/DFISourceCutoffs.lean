module
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import DensityEnergyGM.DFIEstimates
public import Mathlib.Analysis.Calculus.FDeriv.Const

@[expose] public section

open Complex Set
open scoped ContDiff Topology

namespace GuthMaynard.NativeMoment

/-!
# Source cutoffs for DFI equations (9) and (21)

The structures used earlier in the DFI chain record the exact source
hypotheses, but those hypotheses also have to be inhabited.  This file
constructs the two smooth cutoffs from ordinary `ContDiffBump`s.  The
derivative constants are obtained from compact support, so no analytic
existence assumption is introduced.
-/

/-- The centered bump used for the redundant factor before DFI equation
(21). -/
noncomputable def dfiStandardRedundantBump (U : ℝ) (hU : 0 < U) :
    ContDiffBump (0 : ℝ) :=
  ⟨U / 2, U, by positivity, by linarith⟩

/-! ## A genuinely scale-uniform redundant-cutoff family -/

/-- One fixed unit-scale bump.  Rescaling this function, rather than choosing
a new bump at every physical scale, preserves one family of derivative
constants. -/
noncomputable def dfiUnitRedundantBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-! ## A genuinely scale-uniform equation-(9) family -/

/-! ## Uniform quotient profile for the canonical equation-(9) family -/

end GuthMaynard.NativeMoment
