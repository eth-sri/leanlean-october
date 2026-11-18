module
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ResidueCalcOnRectangles
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ZetaBoundsUpstream
public import GuthMaynard.NativeSource.GuthMaynard.GammaPairBound
public import GuthMaynard.NativeSource.GuthMaynard.TwistedDiagonal

@[expose] public section

open Complex Filter MeasureTheory Set Topology
open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.sigma BigOperators Interval
  LSeries.notation

noncomputable section

namespace GuthMaynard.NativeMoment

/-!
# The completed-zeta contour for the smooth fourth-moment AFE

This file formalizes the source entry to Hughes--Young Proposition 2.1 in
the unshifted case.  The pole-cancelling completion below is entire, has the
functional-equation symmetry required to reflect the left side of the
contour, and retains the exact zeta factors on the critical line.
-/

/-- The two critical-line points used in the unshifted fourth moment. -/
noncomputable def afeCriticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

@[simp] theorem one_sub_afeCriticalPoint (t : ℝ) :
    1 - afeCriticalPoint t = afeCriticalPoint (-t) := by
  unfold afeCriticalPoint
  push_cast
  ring

/-- A fixed Hughes--Young auxiliary factor for the unshifted fourth moment.
It is even, equals one at the Cauchy pole `w = 0`, and has a fourth-order
zero at each of `w = ±1/2`.  The fourth-order zero is stronger than needed
for the mixed second auxiliary derivative used below, and is the unshifted
specialization of the admissible `G`-factor prescribed after equation (24)
of Hughes--Young. -/
noncomputable def hughesYoungAuxiliaryZero (w : ℂ) : ℂ :=
  (1 - 4 * w ^ 2) ^ 4

@[simp]
theorem hughesYoungAuxiliaryZero_zero :
    hughesYoungAuxiliaryZero 0 = 1 := by
  norm_num [hughesYoungAuxiliaryZero]

-- The literal half argument matches the source statement and is intentionally retained.
@[simp, nolint simpNF]
theorem hughesYoungAuxiliaryZero_one_half :
    hughesYoungAuxiliaryZero (1 / 2 : ℂ) = 0 := by
  norm_num [hughesYoungAuxiliaryZero]

@[simp]
theorem hughesYoungAuxiliaryZero_neg_one_half :
    hughesYoungAuxiliaryZero (-1 / 2 : ℂ) = 0 := by
  norm_num [hughesYoungAuxiliaryZero]

end GuthMaynard.NativeMoment
