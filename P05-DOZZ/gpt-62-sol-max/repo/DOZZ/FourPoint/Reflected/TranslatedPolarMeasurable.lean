/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedWilliamsLaw
/-! Measurability of the literal translated inner polar mass. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Local finiteness on bounded intervals is preserved by translation. -/
theorem ae_map_sub_const_lt_top_Icc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → Measure ℝ) (T : ℝ) (hf : ∀ᵐ ω ∂P, ∀ a b, Z ω (Icc a b) < ⊤) :
    ∀ᵐ ω ∂P, ∀ a b, ((Z ω).map (· - T)) (Icc a b) < ⊤ := by
  filter_upwards [hf] with ω hω a b
  rw [Measure.map_apply (show Measurable (fun s : ℝ => s - T) from measurable_id.sub_const T) measurableSet_Icc,
    show (· - T) ⁻¹' Icc a b = Icc (a + T) (b + T) by
      ext
      simp [le_sub_iff_add_le, sub_le_iff_le_add]]
  exact hω _ _

theorem reflected_translated_polar_aemeasurable
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (S : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure S]
    (D : Ω → BrownianPath) (hD : AEMeasurable D P) (Z : Λ → Measure ℝ)
    (hZ : AEMeasurable Z S) (hfin : ∀ᵐ ω ∂S, ∀ a b : ℝ, Z ω (Icc a b) < ⊤)
    (γ ν T : ℝ) : AEMeasurable (fun ω : Ω × Λ => ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0)
        ∂(Z ω.2).map (fun s => s-T)) (P.prod S) := by
  have hW := (Measure.measurable_map _ (measurable_id.sub_const T)).comp_aemeasurable hZ
  apply ((reflected_measurable_inwardPolarMassCode γ ν).comp_aemeasurable
    (hD.comp_fst.prodMk hW.comp_snd)).congr
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae
    (ae_map_sub_const_lt_top_Icc S Z T hfin)] with ω hω
  exact reflected_inwardPolarMassCode_eq γ ν (D ω.1) _ hω

end DOZZ.Proofs
