module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationCoordinates
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The first derivatives of separated angular tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/- The chain rule for a separated expression in the actual angular coordinates. -/
theorem bellmanSeparatedExpression_hasFDerivAt (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    HasFDerivAt (bellmanSeparatedExpression ζ φ)
      ((ζ w.1.val * deriv φ w.2) •
        (w.1.val⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ -
          (w.2 / (3 * w.1.val ^ 3)) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
        (φ w.2 * deriv ζ w.1.val) •
          ((1 / (3 * w.1.val ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ))
      (bellmanAngularPoint w).val := by
  have hz : HasDerivAt ζ (deriv ζ w.1.val)
      (bellmanTestRadius (bellmanAngularPoint w).val) := by
    rw [bellmanTestRadius_angularPoint]
    exact hζ.hasDerivAt
  have hp : HasDerivAt φ (deriv φ w.2)
      (bellmanTestAngle (bellmanAngularPoint w).val) := by
    rw [bellmanTestAngle_angularPoint]
    exact hφ.hasDerivAt
  have _h_xinl_0 : HasFDerivAt bellmanTestAngle (w.1.val⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ - (w.2 / (3 * w.1.val ^ 3)) • ContinuousLinearMap.fst ℝ ℝ ℝ) (bellmanAngularPoint w).val := by
    have hn : bellmanTestRadius (bellmanAngularPoint w).val ≠ 0 := by
      rw [bellmanTestRadius_angularPoint]
      exact w.1.property.ne'
    have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := (bellmanAngularPoint w).val)).mul ((hasDerivAt_inv hn).comp_hasFDerivAt (bellmanAngularPoint w).val (bellmanTestRadius_hasFDerivAt w))
    rw [bellmanTestRadius_angularPoint] at hd
    convert! hd using 1
    rw [Function.comp_apply, bellmanTestRadius_angularPoint]
    apply ContinuousLinearMap.ext
    intro z
    change w.1.val⁻¹ * z.2 - w.2 / (3 * w.1.val ^ 3) * z.1 =
      (w.1.val * w.2) * (-(w.1.val ^ 2)⁻¹ *
        (1 / (3 * w.1.val ^ 2) * z.1)) + w.1.val⁻¹ * z.2
    field_simp [w.1.property.ne']
    ring
  convert! ((hz.comp_hasFDerivAt (bellmanAngularPoint w).val (bellmanTestRadius_hasFDerivAt w)).mul (hp.comp_hasFDerivAt (bellmanAngularPoint w).val _h_xinl_0)) using 1
  simp only [Function.comp_apply, bellmanTestRadius_angularPoint,
    bellmanTestAngle_angularPoint, smul_smul, mul_assoc]

/- The transport derivative has exactly the source factors y/(3s) and -y²/(3s²). -/
theorem bellmanSeparatedExpression_transport (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    (bellmanAngularPoint w).val.2 *
      fderiv ℝ (bellmanSeparatedExpression ζ φ) (bellmanAngularPoint w).val (1, 0) =
      w.2 / (3 * w.1.val) * deriv ζ w.1.val * φ w.2 -
        w.2 ^ 2 / (3 * w.1.val ^ 2) * ζ w.1.val * deriv φ w.2 := by
  rw [(bellmanSeparatedExpression_hasFDerivAt ζ φ w hζ hφ).fderiv]
  change (w.1.val * w.2) *
    ((ζ w.1.val * deriv φ w.2) * (w.1.val⁻¹ * 0 - w.2 / (3 * w.1.val ^ 3) * 1) +
      (φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 1)) = _
  field_simp [w.1.property.ne']
  ring

/- The first velocity derivative is ζ(s)φ'(y)/s. -/
theorem bellmanSeparatedExpression_velocity (ζ φ : ℝ → ℝ)
    (w : BellmanPositiveTime × ℝ) (hζ : DifferentiableAt ℝ ζ w.1.val)
    (hφ : DifferentiableAt ℝ φ w.2) :
    fderiv ℝ (bellmanSeparatedExpression ζ φ) (bellmanAngularPoint w).val (0, 1) =
      ζ w.1.val * deriv φ w.2 / w.1.val := by
  rw [(bellmanSeparatedExpression_hasFDerivAt ζ φ w hζ hφ).fderiv]
  change (ζ w.1.val * deriv φ w.2) *
    (w.1.val⁻¹ * 1 - w.2 / (3 * w.1.val ^ 3) * 0) +
      (φ w.2 * deriv ζ w.1.val) * (1 / (3 * w.1.val ^ 2) * 0) = _
  simp only [mul_one, mul_zero, sub_zero, add_zero, div_eq_mul_inv]

end HypoellipticAleksandrov.KineticAleksandrov
