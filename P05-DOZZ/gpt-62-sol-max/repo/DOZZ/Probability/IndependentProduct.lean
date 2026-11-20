/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! Product-space observations of independent random variables. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Independent source copies push forward to the product of their actual marginal laws. -/
theorem map_prod_of_aemeasurable
    {Ω Λ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure Λ) (P : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (F : Λ → α) (G : Ω → β)
    (hF : AEMeasurable F Q) (hG : AEMeasurable G P) :
    (Q.prod P).map (fun ω : Λ × Ω => (F ω.1, G ω.2)) = (Q.map F).prod (P.map G) := by
  have hf : ∀ᵐ ω : Λ × Ω ∂Q.prod P, F ω.1 = hF.mk F ω.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hF.ae_eq_mk
  have hg : ∀ᵐ ω : Λ × Ω ∂Q.prod P, G ω.2 = hG.mk G ω.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hG.ae_eq_mk
  have he : (fun ω : Λ × Ω => (F ω.1, G ω.2)) =ᵐ[Q.prod P]
      Prod.map (hF.mk F) (hG.mk G) := by
    filter_upwards [hf, hg] with ω hω hω'
    exact Prod.ext hω hω'
  rw [Measure.map_congr he, ← Measure.map_prod_map Q P hF.measurable_mk hG.measurable_mk,
    ← Measure.map_congr hF.ae_eq_mk, ← Measure.map_congr hG.ae_eq_mk]

/-- Expectation of a measurable functional of independent variables, expressed on a product space. -/
theorem lintegral_indepFun_prod {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → A} {g : Ω → B}
    (h : IndepFun f g P) (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    {F : A × B → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ ω, F (f ω,g ω) ∂P) = ∫⁻ p : Ω × Ω, F (f p.1,g p.2) ∂P.prod P := by
  have hp : AEMeasurable (fun p : Ω × Ω => (f p.1,g p.2)) (P.prod P) :=
    (hf.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
      (hg.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
  rw [← lintegral_map' hF.aemeasurable (hf.prodMk hg),
    (indepFun_iff_map_prod_eq_prod_map_map hf hg).mp h,
    ← map_prod_of_aemeasurable P P f g hf hg, lintegral_map' hF.aemeasurable hp]

end DOZZ.Proofs
