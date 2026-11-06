/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.EnvelopePower
public import DOZZ.GMC.FieldChaosNegativePower
public import Mathlib.MeasureTheory.Measure.Prod

/-! The exact finite-cutoff Wick-density ratio of the separated joint-tail estimate, with the
variance discrepancy retained. -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs
section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)

/-- Spatial almost-everywhere circle splits can be placed on a common sample event.
This is a Fubini step, not a pointwise assertion on all spatial points. -/
theorem separatedTail_circle_split_ae_sample
    [SFinite P] (ν : Measure S) [SFinite ν]
    (Φ Ψ H : Ω → S → ℝ) (L : Ω → ℝ)
    (hΦ : Measurable (fun q : Ω × S => Φ q.1 q.2))
    (hΨ : Measurable (fun q : Ω × S => Ψ q.1 q.2))
    (hH : Measurable (fun q : Ω × S => H q.1 q.2)) (hL : Measurable L)
    (hsplit : ∀ᵐ x ∂ν, (fun ω => Ψ ω x) =ᵐ[P] fun ω => Φ ω x+H ω x-L ω) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, Ψ ω x = Φ ω x+H ω x-L ω := by
  have hm' :=
    measurableSet_eq_fun (hΨ.comp measurable_swap)
      (((hΦ.comp measurable_swap).add (hH.comp measurable_swap)).sub (hL.comp measurable_snd))
  exact (Measure.ae_ae_comm hm').mp hsplit

/-- The Wick ratio for the full and Dirichlet fields is dominated by the correlated
harmonic/restoration envelope and the deterministic covariance correction. -/
theorem separatedTail_fieldChaosMass_le_of_circle_split
    (ν : Measure S) [SFinite ν]
    (Φ Ψ H : Ω → S → ℝ) (L : Ω → ℝ) (E : Ω → ℝ≥0∞)
    (w : S → ℝ≥0) (hw : Measurable w)
    (hfield : IsCenteredGaussianField P Φ) (γ C : ℝ)
    (hsplit : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, Ψ ω x = Φ ω x+H ω x-L ω)
    (hvar : ∀ᵐ x ∂ν, |(∫ ω, Ψ ω x^2 ∂P)-(∫ ω, Φ ω x^2 ∂P)| ≤ C)
    (hE : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      ENNReal.ofReal (Real.exp (γ*(H ω x-L ω))) ≤ E ω) :
    ∀ᵐ ω ∂P, fieldChaosMass P Ψ ν w γ ω ≤
      ENNReal.ofReal (Real.exp (γ^2*C/2))*E ω*fieldChaosMass P Φ ν w γ ω := by
  have hvInt : Measurable (fun x => ∫ ω, Φ ω x^2 ∂P) := by
    simpa only [gaussianVariance, gaussianCovariance, pow_two] using (centeredGaussianField_variance_measurable P Φ hfield)
  filter_upwards [hsplit,hE] with ω hs he
  unfold fieldChaosMass
  -- Keep the random envelope outside the spatial integral, including extended values.
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp (γ^2*C/2))*E ω)*
        ((w x)*ENNReal.ofReal (Real.exp
          (γ*Φ ω x-γ^2/2*(∫ ω', Φ ω' x^2 ∂P)))) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [hs,he,hvar] with x hx hex hvarx
      have hdiff : -(γ^2/2)*((∫ ω', Ψ ω' x^2 ∂P)-(∫ ω', Φ ω' x^2 ∂P)) ≤ γ^2*C/2 := by
        have hl := (abs_le.mp hvarx).1
        nlinarith
      have heq : γ*Ψ ω x-γ^2/2*(∫ ω', Ψ ω' x^2 ∂P) =
          γ*(H ω x-L ω) + -(γ^2/2)*((∫ ω', Ψ ω' x^2 ∂P)-
            (∫ ω', Φ ω' x^2 ∂P)) + (γ*Φ ω x-γ^2/2*(∫ ω', Φ ω' x^2 ∂P)) := by
        grind
      rw [heq, Real.exp_add, Real.exp_add,
        ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      calc
        _ ≤ (w x : ℝ≥0∞)*((E ω*ENNReal.ofReal (Real.exp (γ^2*C/2)))*
          ENNReal.ofReal (Real.exp (γ*Φ ω x-γ^2/2*(∫ ω', Φ ω' x^2 ∂P)))) :=
            mul_le_mul_right (mul_le_mul_left (mul_le_mul' hex (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hdiff))) _) _
        _ = _ := by ac_rfl
    _ = _ := by
      have hsp : Measurable (fun x => Φ ω x) :=
        hfield.1.comp (measurable_const.prodMk measurable_id)
      have hm : Measurable (fun x => (w x : ℝ≥0∞)*ENNReal.ofReal
          (Real.exp (γ*Φ ω x-γ^2/2*(∫ ω', Φ ω' x^2 ∂P)))) := hw.coe_nnreal_ennreal.mul
        (((hsp.const_mul γ).sub (hvInt.const_mul (γ^2/2))).exp.ennreal_ofReal)
      rw [lintegral_const_mul'' _ hm.aemeasurable]

end

end DOZZ.Proofs
