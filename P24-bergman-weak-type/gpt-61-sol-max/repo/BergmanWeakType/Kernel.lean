
import BergmanWeakType.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic

variable {z w : ℂ}

/-! # Elementary identities for the Bergman kernels

These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/






namespace BergmanWeakType

@[simp]
theorem mem_disk_iff (z ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp_all [disk]

/-- The kernel's base lies in the right half-plane on the disk. -/
def kernel_denominator_re_pos  (h : ‖z‖ * ‖w‖ < 1)  := by
  simpa only [Complex.sub_re, Complex.one_re] using
    sub_pos.mpr ((Complex.re_le_norm _).trans_lt
      (show ‖z * star w‖ < 1 by simp_all))

/-- The weighted pointwise comparison requires no weak type estimate. -/
@[simp]
def norm_weightedKernel (α ) (z w )  := show ‖weightedKernel α z w‖ = _ from by
  convert (Complex.norm_cpow_real (1 - z * star w) (-(α + 2))) using 1 <;> simp [weightedKernel]

@[simp]
theorem weightedKernel_zero : weightedKernel 0 = kernel := by
  aesop (add norm [weightedKernel, kernel, Complex.cpow_neg])

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

@[simp]
theorem gammaConstant_zero : gammaConstant 0 = 1 := by
  simp [gammaConstant]

theorem gammaConstant_pos {α } (hα : -1 < α) : 0 < gammaConstant α := by
  apply_rules [div_pos, sq_pos_of_pos, Real.Gamma_pos_of_pos] <;> linarith

end BergmanWeakType
