/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsReferenceInputLaw
public import DOZZ.Brownian.Reflection.MassBlocks
public import DOZZ.Brownian.Lateral.LawUniqueness

/-! The Williams reference law on the given source reflection witness. -/

public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω)

include Ω _inst1 P in
theorem conditioned_pair_reference_law
    
    (B : Ω → BrownianPath × BrownianPath) (ν : ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    P.map B = Qν.prod Qν := by
  let  := isProbabilityMeasure_of_twoSidedConditioned hB
  have hm₁ := hB.1.1
  have hm₂ := hB.2.1.1
  have hl₁ := isNegativeConditionedBrownianLaw_eq ν hB.1.2 hQν
  have hl₂ := isNegativeConditionedBrownianLaw_eq ν hB.2.1.2 hQν
  have hl := (indepFun_iff_map_prod_eq_prod_map_map hm₁ hm₂).mp hB.2.2
  simpa only [Prod.eta,hl₁,hl₂] using hl

include Ω _inst1 P in
theorem lateral_law_locally_finite
    
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    ∀ᵐ μ ∂P.map Z, ∀ a b : ℝ, μ (Icc a b) < ⊤ := by
  have hn (n : ℕ) : ∀ᵐ μ ∂P.map Z, μ (Icc (-(n : ℝ)) n) < ⊤ := by
    apply (ae_map_iff hZ.2.2.2.1 ?_).mpr
    · exact hZ.2.2.2.2.1.mono fun ω hω => hω _ _
    · exact measurableSet_lt (Measure.measurable_coe measurableSet_Icc) measurable_const
  filter_upwards [ae_all_iff.mpr hn] with μ hμ
  intro a b
  obtain ⟨n,hn⟩ := exists_nat_ge (max |a| |b|)
  apply lt_of_le_of_lt (measure_mono ?_) (hμ n)
  grind

include Ω _inst1 P in
theorem williams_source_input_law
    
    (γ α : ℝ) (hα : α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw (Q γ-α) Qν) :
    (((((brownianMaximumReferenceLaw (Q γ-α)).prod Qν).map
      (fun v => (v.1,negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
        (P.map Z)).map (williamsMassFunctional γ) =
    ((brownianMaximumReferenceLaw (Q γ-α)).prod P).map
      (fun q => ENNReal.ofReal (Real.exp (γ*q.1))*
        twoSidedReflectionCutMass γ q.1 B Z q.2) := by
  let  := hData.2.1.2.2.1
  let  := hQν.2.1
  have hZm := hData.2.1.2.2.2.1
  let  := (Measure.isProbabilityMeasure_map_iff hZm).mpr inferInstance
  let μ := brownianMaximumReferenceLaw (Q γ-α)
  let  := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα)
  let pair := fun ω => (B ω,Z ω)
  have hp  := (aemeasurable_of_twoSidedConditioned hData.1).prodMk hZm
  have hJoint : P.map pair = (Qν.prod Qν).prod (P.map Z) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map
      (aemeasurable_of_twoSidedConditioned hData.1) hZm).mp hData.2.2,
      conditioned_pair_reference_law P B _ hData.1 Qν hQν]
  rw [williams_reference_input_law γ _ (sub_pos.mpr hα) Qν (P.map Z)
    (lateral_law_locally_finite P γ Z hData.2.1),← hJoint]
  let pm := hp.mk pair
  have hpm  := hp.measurable_mk
  have heq  := hp.ae_eq_mk
  have hInput : (μ.prod P).map (fun q : ℝ × Ω => (q.1,pair q.2)) = μ.prod (P.map pair) := by
    have heq' := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae heq
    have hlift : (fun q : ℝ × Ω => (q.1,pair q.2)) =ᵐ[μ.prod P]
        (fun q => (q.1,pm q.2)) := heq'.mono fun q hq => Prod.ext rfl hq
    rw [Measure.map_congr hlift,Measure.map_congr heq,
      ← Measure.map_id (μ := μ),Measure.map_prod_map _ _ measurable_id hpm]
    simp only [Measure.map_id]
    rfl
  have hInp : AEMeasurable (fun q : ℝ × Ω => (q.1,pair q.2)) (μ.prod P) :=
    measurable_fst.aemeasurable.prodMk
      (hp.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
  rw [← hInput,AEMeasurable.map_map_of_aemeasurable
    (measurable_williamsInputMassCode γ).aemeasurable hInp]
  apply Measure.map_congr
  have hfin := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae
    hData.2.1.2.2.2.2.1
  filter_upwards [hfin] with q hq
  exact congrArg (fun t => ENNReal.ofReal (Real.exp (γ*q.1))*t)
    (williamsCutMassCode_eq γ q.1 (B q.2) (Z q.2) hq)


end DOZZ.Proofs
