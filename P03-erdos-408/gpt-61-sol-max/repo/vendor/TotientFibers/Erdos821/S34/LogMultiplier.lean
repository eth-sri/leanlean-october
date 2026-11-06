module
public import Mathlib.Tactic

public import Erdos821.S34.CellCosts

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def unitPhase (t : ℝ)  := Complex.exp (Complex.I * t)

section
variable (s t : ℝ)

theorem norm_unitPhase   : ‖unitPhase t‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

theorem unitPhase_add   : unitPhase (s + t) = unitPhase s * unitPhase t := by
  simp only [unitPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_unitPhase_sub   : ‖unitPhase s - unitPhase t‖ ≤ |s - t| := by
  have he : unitPhase s - unitPhase t = unitPhase t * (unitPhase (s - t) - 1) := by
    rw [mul_sub, ← unitPhase_add]
    congr 1
    · congr 1
      ring
    · ring
  rw [he, norm_mul, norm_unitPhase, one_mul]
  simpa only [unitPhase, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

end

def logMultiplier (ζ β v : ℝ)  := unitPhase (ζ * v + 2 * Real.pi * β * Real.exp v)

section
variable (ζ β u v H : ℝ) (hu : u ≤ H) (hv : v ≤ H)

theorem norm_logMultiplier   : ‖logMultiplier ζ β v‖ = 1 := norm_unitPhase _

include hu hv in
theorem exp_difference_bound       :
    |Real.exp v - Real.exp u| ≤ Real.exp H * |v - u| := by
  have hb : ∀ t ∈ Set.Iic H, ‖deriv Real.exp t‖ ≤ Real.exp H := by
    simp_all
  simpa only [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ht : t ∈ Set.Iic H) => Real.differentiableAt_exp) hb
      (convex_Iic H) hu hv)

include hu hv in
theorem logMultiplier_difference       :
    ‖logMultiplier ζ β v - logMultiplier ζ β u‖ ≤
      (|ζ| + 2 * Real.pi * |β| * Real.exp H) * |v - u| := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hβ : 0 ≤ 2 * Real.pi * |β| := by positivity
  calc
    _ ≤ |(ζ * v + 2 * Real.pi * β * Real.exp v) -
          (ζ * u + 2 * Real.pi * β * Real.exp u)| := norm_unitPhase_sub _ _
    _ = |ζ * (v - u) + (2 * Real.pi * β) * (Real.exp v - Real.exp u)| := by congr 1; ring
    _ ≤ |ζ * (v - u)| + |(2 * Real.pi * β) * (Real.exp v - Real.exp u)| := abs_add_le _ _
    _ = |ζ| * |v - u| + (2 * Real.pi * |β|) * |Real.exp v - Real.exp u| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hπ]
    _ ≤ |ζ| * |v - u| + (2 * Real.pi * |β|) * (Real.exp H * |v - u|) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (exp_difference_bound u v H hu hv) hβ)
    _ = _ := by ring

end

end
end Erdos821.S34Core
