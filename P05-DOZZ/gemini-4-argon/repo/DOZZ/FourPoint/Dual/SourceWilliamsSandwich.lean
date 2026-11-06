/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MaximumExpectation
public import DOZZ.FourPoint.Dual.SourceParetoWeights
/-! Integrated maximum sandwich on the actual source reflection witness. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual source retained mass, radial likelihood and random last-cut Williams mass
have an integrable signed inverse-power increment. All inputs come from the supplied GMC
and reflection data. -/
theorem dual_source_williams_expectation_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p c : ℝ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    z (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let R := (brownianMaximumReferenceLaw (Q γ-α₁)).prod P
    let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := dual_radial_scale γ (Q γ-α₁) h Xc z
    let E := fun (J : ℝ × Ω → ℝ) (v : Ω × (ℝ × Ω)) =>
      (A v.1+b v.1*(Real.exp (γ*v.2.1)*J v.2))^(-p)-(A v.1)^(-p)
    (∫ v, E (fun q => (twoSidedReflectionMass γ B Z q.2).toReal) v ∂P.prod R) ≤
      (∫ v, E (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) v ∂P.prod R) ∧
    (∫ v, E (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) v ∂P.prod R) ≤
      (∫ v, E (fun q => (twoSidedReflectionCutMass γ c B Z q.2).toReal) v ∂P.prod R) +
      p*Real.exp (γ*c)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*
        (∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ (Q γ-α₁) h Xc z
  let R := (brownianMaximumReferenceLaw (Q γ-α₁)).prod P
  have hs := dual_williams_increment_expectation_sandwich P R p γ c hp hγ.le A b
    (fun q => q.1) (fun q => (twoSidedReflectionMass γ B Z q.2).toReal)
    (fun q => (twoSidedReflectionCutMass γ c B Z q.2).toReal)
    (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal)
    ((dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hz (by simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz (sub_nonneg.mpr hξ1.le))).mono (fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne)) (ae_of_all _ (fun _ => (Real.exp_pos _).le)) (by filter_upwards [dual_williams_cut_real_bounds P γ α₁ c hγ hγ₂ hα₁ B Z hData, measurePreserving_snd.quasiMeasurePreserving.ae (reflected_reflection_mass_positive_finite_ae P γ α₁ B Z hγ hγ₂ hα₁ hData)] with q hq hf; exact ⟨hq.1, hq.2.1, ENNReal.toReal_nonneg, ENNReal.toReal_mono hf.2.ne (twoSidedReflectionCutMass_le_mass γ c B Z q.2), hq.2.2⟩) (((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal) (by dsimp only [b, dual_radial_scale]; exact ((((hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable).const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp)
    measurable_fst.aemeasurable ((twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1).ennreal_toReal).comp_snd ((twoSidedReflectionCutMass_aemeasurable P γ c B Z (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1).ennreal_toReal).comp_snd (dual_williams_cut_real_aemeasurable P γ α₁ hα₁ B Z hData) (by simpa only [Real.rpow_zero, one_mul] using ((dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc (Q γ-α₁) h 0 α₁ α₂ α₃ ξ p hh hξ hξ1 hp.le z hz0 hz).1)) (show Integrable (fun ω => b ω*(A ω)^(-p-1)) P by simpa only [Real.rpow_one, show -(p+1) = -p-1 by ring] using ((dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc (Q γ-α₁) h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz).1)) ((show Integrable (fun ω => (twoSidedReflectionMass γ B Z ω).toReal) P by simpa only [Real.rpow_one] using (reflected_reflection_real_moment P γ α₁ 1 B Z hα₁ hData (by rw [lt_div_iff₀ (sq_pos_of_pos hγ)]; nlinarith only [hγ, hγ₂])).1).comp_snd _)
  dsimp only at hs ⊢
  rw [(show (∫ q : ℝ × Ω, (twoSidedReflectionMass γ B Z q.2).toReal ∂R) = ∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ∂P by simpa only [probReal_univ, one_smul] using (integral_fun_snd (μ := brownianMaximumReferenceLaw (Q γ-α₁)) (ν := P) (fun ω => (twoSidedReflectionMass γ B Z ω).toReal)))] at hs
  exact hs

end DOZZ.Proofs
