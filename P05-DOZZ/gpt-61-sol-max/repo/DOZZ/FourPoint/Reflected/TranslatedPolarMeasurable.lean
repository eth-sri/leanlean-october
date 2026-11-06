/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedWilliamsLaw
public import DOZZ.Brownian.MeasureTranslationFinite
/-! Measurability of the literal translated inner polar mass. -/
public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_translated_polar_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → BrownianPath) (hD : AEMeasurable D P) (Z : Ω → Measure ℝ)
    (hZ : AEMeasurable Z P) (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤)
    (γ ν T : ℝ) : AEMeasurable (fun ω : Ω × Ω => ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0)
        ∂(Z ω.2).map (fun s => s-T)) (P.prod P) := by
  let W := fun ω => locallyFiniteTranslation (-T,Z ω)
  have hW : AEMeasurable W P := measurable_locallyFiniteTranslation.comp_aemeasurable
    (aemeasurable_const.prodMk hZ)
  have he : W =ᵐ[P] (fun ω => (Z ω).map (fun s => s-T)) := by
    filter_upwards [hfin] with ω hω
    exact locallyFiniteTranslation_eq_map (-T) (Z ω)
      (fun n => hω (-(n : ℝ)) (n : ℝ))
  have hWf : ∀ᵐ ω ∂P, ∀ a b : ℝ, W ω (Icc a b) < ⊤ := by
    filter_upwards [he,hfin] with ω hω hf a b
    rw [hω,Measure.map_apply (show Measurable (fun s : ℝ => s-T) from measurable_id.sub_const T) measurableSet_Icc]
    simp_all
  have hc := (reflected_measurable_inwardPolarMassCode γ ν).comp_aemeasurable
    ((hD.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
      (hW.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving))
  apply hc.congr
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae he,
    measurePreserving_snd.quasiMeasurePreserving.ae hWf] with ω heω hfω
  dsimp only [Function.comp_apply]
  rw [reflected_inwardPolarMassCode_eq γ ν (D ω.1) (W ω.2) hfω,heω]

end DOZZ.Proofs
