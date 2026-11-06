module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! # Differentiating the literal source angular coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/- The real-valued radius used in a separated test on positive position. -/
def bellmanTestRadius (q : ℝ × ℝ) : ℝ := q.1 ^ ((3 : ℝ)⁻¹)

/- The angular coordinate used in a separated test on positive position. -/
def bellmanTestAngle (q : ℝ × ℝ) : ℝ := q.2 / bellmanTestRadius q

/- The literal separated expression, before extension across the position axis. -/
def bellmanSeparatedExpression (ζ φ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  ζ (bellmanTestRadius q) * φ (bellmanTestAngle q)

/- The radial coordinate equals s at the source coordinate point. -/
theorem bellmanTestRadius_angularPoint (w : BellmanPositiveTime × ℝ) :
    bellmanTestRadius (bellmanAngularPoint w).val = w.1.val :=  Real.pow_rpow_inv_natCast w.1.property.le (by norm_num : (3 : ℕ) ≠ 0)

/- The angular coordinate equals y at the source coordinate point. -/
theorem bellmanTestAngle_angularPoint (w : BellmanPositiveTime × ℝ) :
    bellmanTestAngle (bellmanAngularPoint w).val = w.2 := by
  rw [bellmanTestAngle, bellmanTestRadius_angularPoint]
  change w.1.val * w.2 / w.1.val = w.2
  field_simp [w.1.property.ne']

/- The radial coordinate has derivative dX/(3s²) on positive position. -/
theorem bellmanTestRadius_hasFDerivAt (w : BellmanPositiveTime × ℝ) :
    HasFDerivAt bellmanTestRadius
      ((1 / (3 * w.1.val ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
      (bellmanAngularPoint w).val := by
  have hx := pow_pos w.1.property 3
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := (bellmanAngularPoint w).val)).rpow_const
    (p := (3 : ℝ)⁻¹) (Or.inl hx.ne')
  change HasFDerivAt bellmanTestRadius
    (((3 : ℝ)⁻¹ * ((bellmanAngularPoint w).val.1 ^ ((3 : ℝ)⁻¹ - 1))) •
      ContinuousLinearMap.fst ℝ ℝ ℝ) _ at hd
  have he : ((bellmanAngularPoint w).val.1 ^ ((3 : ℝ)⁻¹ - 1)) =
      (w.1.val ^ 2)⁻¹ := by
    change (w.1.val ^ 3) ^ ((3 : ℝ)⁻¹ - 1) = _
    rw [← Real.rpow_natCast_mul w.1.property.le]
    norm_num
  rw [he] at hd
  convert hd using 1
  congr 1
  simp only [one_div, mul_inv_rev]
  ring

/- The angular coordinate has the chain-rule differential dv/s-y dX/(3s³). -/
end HypoellipticAleksandrov.KineticAleksandrov
