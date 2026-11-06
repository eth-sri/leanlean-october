module
public import GuthMaynard.AffineSource.Foundation
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded
public import DensityEnergyGM.DFIDelta
public import DensityEnergyGM.DFIEstimates
public import DensityEnergyGM.DFIEquation21

@[expose] public section

open Complex
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



/-! ## A genuinely scale-uniform redundant-cutoff family -/

/- One fixed unit-scale bump.  Rescaling this function, rather than choosing
a new bump at every physical scale, preserves one family of derivative
constants. -/
export RiemannZeta.GuthMaynard (dfiUnitRedundantBump)

/-! ## A genuinely scale-uniform equation-(9) family -/

/-! ## Uniform quotient profile for the canonical equation-(9) family -/


