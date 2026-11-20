module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

/-! # Literal square integrals and restricted L2 norms

These identities translate the localized value, gradient, and Hessian estimates to the
norms stored in the weak-derivative families.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory

/-- The literal real square integral is the square of the real L2 seminorm. -/
theorem integral_square_eq_eLpNorm_two_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ => sq_nonneg _) _), ENNReal.toReal_ofNat,
    Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

end HypoellipticAleksandrov.Parabolic.LocalHolder
