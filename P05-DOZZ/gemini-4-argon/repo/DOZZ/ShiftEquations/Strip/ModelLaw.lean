/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.WilliamsLimit
public import DOZZ.Brownian.ReflectionJointInputLaw
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Product-law identification for the Williams model. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs


/-- A conditioned pair independent of the supplied lateral measure realizes exactly the
Williams model input law, on the product with the independent maximum carrier. -/
theorem lastone_williamsInput_law_on_given_space
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [SFinite μ] ν (Q : Measure BrownianPath)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν)
    (hZm : AEMeasurable Z P) (hInd : IndepFun B Z P) :
    (μ.prod P).map (fun z : ℝ × Ω =>
      (((z.1, negativeConditionedLastExitSegment z.1 (B z.2).2), (B z.2).1), Z z.2)) =
      ((((μ.prod Q).map (fun z =>
        (z.1, negativeConditionedLastExitSegment z.1 z.2))).prod Q).prod (P.map Z)) := by
  have lastone_williamsInput_model_map (L : Measure (Measure ℝ)) [SFinite μ] [SFinite Q] [SFinite L] : (μ.prod ((Q.prod Q).prod L)).map (fun z : ℝ × ((BrownianPath × BrownianPath) × Measure ℝ) => (((z.1, negativeConditionedLastExitSegment z.1 z.2.1.2), z.2.1.1), z.2.2)) = ((((μ.prod Q).map (fun z => (z.1, negativeConditionedLastExitSegment z.1 z.2))).prod Q).prod L) := by
    let T : ℝ × BrownianPath → ℝ × StoppedBrownianPath := fun z =>
      (z.1, negativeConditionedLastExitSegment z.1 z.2)
    have hT : Measurable T := measurable_fst.prodMk measurable_lastExitSegment_joint
    let R : ℝ × ((BrownianPath × BrownianPath) × Measure ℝ) →
        ((ℝ × BrownianPath) × BrownianPath) × Measure ℝ := fun z =>
      (((z.1, z.2.1.2), z.2.1.1), z.2.2)
    have hR : MeasurePreserving R (μ.prod ((Q.prod Q).prod L)) (((μ.prod Q).prod Q).prod L) := ((MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ Q Q)).prod (MeasurePreserving.id L)).comp ((MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ (Q.prod Q) L)).comp ((MeasurePreserving.id μ).prod ((Measure.measurePreserving_swap (μ := Q) (ν := Q)).prod (MeasurePreserving.id L))))
    let F : ((ℝ × BrownianPath) × BrownianPath) × Measure ℝ →
        ((ℝ × StoppedBrownianPath) × BrownianPath) × Measure ℝ :=
      Prod.map (Prod.map T id) id
    have hn : (((μ.prod Q).prod Q).prod L).map F =
        (((μ.prod Q).map T).prod Q).prod L := by
      have h1 := Measure.map_prod_map (μ.prod Q) Q hT measurable_id
      have h2 := Measure.map_prod_map ((μ.prod Q).prod Q) L
        (hT.prodMap measurable_id) measurable_id
      simp only [Measure.map_id] at h1 h2
      exact h2.symm.trans (congrArg (fun N => N.prod L) h1.symm)
    change (μ.prod ((Q.prod Q).prod L)).map (F ∘ R) = _
    rw [← Measure.map_map ((hT.prodMap measurable_id).prodMap measurable_id) hR.measurable, hR.map_eq]
    exact hn
  let : IsProbabilityMeasure Q := hQ.2.1
  let : IsProbabilityMeasure (P.map Z) := (Measure.isProbabilityMeasure_map_iff hZm).2 inferInstance
  have hBm := aemeasurable_of_twoSidedConditioned hB
  let pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ := fun ω => (B ω, Z ω)
  have hp := hBm.prodMk hZm
  have hplaw : P.map pair = (Q.prod Q).prod (P.map Z) := by
    simpa only [pair, (by simpa only [Prod.eta, (isNegativeConditionedBrownianLaw_eq ν hB.1.2 hQ), (isNegativeConditionedBrownianLaw_eq ν hB.2.1.2 hQ)] using ((indepFun_iff_map_prod_eq_prod_map_map hB.1.1 hB.2.1.1).mp hB.2.2))] using ((indepFun_iff_map_prod_eq_prod_map_map hBm hZm).mp hInd)
  let g : ℝ × Ω → ℝ × ((BrownianPath × BrownianPath) × Measure ℝ) :=
    fun z => (z.1, pair z.2)
  have hglaw : (μ.prod P).map g = μ.prod (P.map pair) := by
    rw [Measure.map_congr (show g =ᵐ[μ.prod P] Prod.map id (hp.mk pair) by filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := P)).ae hp.ae_eq_mk] with z hz; exact congrArg (fun x => (z.1, x)) hz)]
    have hmap := Measure.map_prod_map μ P measurable_id hp.measurable_mk
    simp only [Measure.map_id] at hmap
    rw [← hmap, ← Measure.map_congr hp.ae_eq_mk]
  let T : ℝ × ((BrownianPath × BrownianPath) × Measure ℝ) →
      ((ℝ × StoppedBrownianPath) × BrownianPath) × Measure ℝ := fun z =>
    (((z.1, negativeConditionedLastExitSegment z.1 z.2.1.2), z.2.1.1), z.2.2)
  have hT : Measurable T := (((measurable_fst.prodMk
    (measurable_lastExitSegment_joint.comp
      (measurable_fst.prodMk measurable_snd.fst.snd))).prodMk
        measurable_snd.fst.fst).prodMk measurable_snd.snd)
  change (μ.prod P).map (T ∘ g) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable (measurable_fst.aemeasurable.prodMk (hp.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := P))) : AEMeasurable g (μ.prod P)),
    hglaw, hplaw]
  exact lastone_williamsInput_model_map (P.map Z)

end DOZZ.Proofs
