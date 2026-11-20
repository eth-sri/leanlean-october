/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.MeasureTheory.MeasureMassCode
public import DOZZ.Brownian.Lateral.ConcentricInversion
public import DOZZ.Brownian.Lateral.LawUniqueness
public import DOZZ.GMC.Moments.InversionAnnularTestLaw
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Finite radial evaluations and open masses determine the joint law of an ENTIRE
continuous radial path and finite random measure. Null-event measurability suffices. -/
theorem finite_random_radial_measure_law_of_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → TwoSidedPath) (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) (hNf : ∀ ω, IsFiniteMeasure (N ω))
    (hfdd : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (s : ι → ℚ)
      (U : κ → Set ℂ), (∀ j, IsOpen (U j)) →
      P.map (fun ω => (fun i => A ω (s i : ℝ), fun j => M ω (U j))) =
      P.map (fun ω => (fun i => B ω (s i : ℝ), fun j => N ω (U j)))) :
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (A ω, (⟨M ω, hMf ω⟩ : FiniteMeasure ℂ))) =
      P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (B ω, (⟨N ω, hNf ω⟩ : FiniteMeasure ℂ))) := by
  have hm : AEMeasurable (fun ω => (A ω, (⟨M ω, hMf ω⟩ : FiniteMeasure ℂ))) P :=
    hA.prodMk (hM.subtype_mk (hfs := hMf))
  exact (identDistrib_prod_of_coded_fdd hm (hB.prodMk (hN.subtype_mk (hfs := hNf))) radialRationalCode_measurableEmbedding.comap_eq
    finiteOpenMassCode_comap_eq fun s t => hfdd s t (fun i => i.1) (fun j => j.1.1) (fun j => j.1.2)).map_eq

/-- Inversion preserves finite vectors of open masses jointly with reversed radial
coordinates, on the original probability space. -/
theorem gmc_inversion_joint_open_mass_fintype_law
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : ι → ℝ) (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => (M ω).map
      (fun z : ℂ => z⁻¹) (U j))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => M ω (U j))) := by
  classical
  let := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNfin (ω : Ω) : IsFiniteMeasure (N ω) := by let := hM.1 ω; infer_instance
  apply (identDistrib_open_mass_pair U hU N M (fun ω _ => by let := hNfin ω; exact measure_lt_top _ _)
    (fun ω _ => by let := hM.1 ω; exact measure_lt_top _ _) ?_).map_eq
  intro n
  let eι := (Fintype.equivFin ι).symm
  let eκ := (Fintype.equivFin κ).symm
  let f := fun j => gmcOpenApprox (U (eκ j)) (hU (eκ j)) n
  apply identDistrib_pair_pi_of_reindex eι eκ
  exact ⟨(AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable).prodMk
      (AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (f j)),
    (AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable).prodMk
      (AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (f j)),
    gmc_inversion_joint_test_vector_law P X hX Xc hc γ hγ hγ2 M hM (s ∘ eι) f⟩

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
  (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
  (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
  (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X Xc hX hc hcont γ hγ hγ2 M hM

/-- The entire radial path and the actual finite GMC have the simultaneous
radial-reversal/complex-inversion joint law. -/
theorem originRadialGMC_inversion_joint_law :
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (originReversedRadialPath (originRadialPath Xc ω),
      FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹))) =
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (originRadialPath Xc ω, (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ))) := by
  let  := hX.1
  let A := originRadialPath Xc
  let N := fun ω => (M ω).map (fun x : ℂ => x⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm  := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNf  := fun ω =>
    (FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹)).2
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hAr := originReversedRadialPath_aemeasurable P A hA
  apply finite_random_radial_measure_law_of_open_fdd P
    (fun ω => originReversedRadialPath (A ω)) A hAr hA N M hNm hMm hNf hM.1
  intro ι κ _ _ s U hU
  have hlaw := gmc_inversion_joint_open_mass_fintype_law P X hX Xc hc γ hγ hγ2 M hM
    (fun i => (s i : ℝ)) U hU
  calc
    _ = P.map (fun ω => (fun i => Xc ω 0 (-(s i : ℝ)), fun j => N ω (U j))) := by
      apply Measure.map_congr
      filter_upwards [originRadialPath_eval_ae hcont] with ω hω
      apply Prod.ext
      · funext i
        apply hω <;> assumption
      · rfl
    _ = P.map (fun ω => (fun i => Xc ω 0 (s i : ℝ), fun j => M ω (U j))) := hlaw
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [originRadialPath_eval_ae hcont] with ω hω
      apply Prod.ext
      · funext i
        exact (hω (s i : ℝ)).symm
      · rfl

/-- Reflection preserves the law of the ENTIRE actual polar projection
`DOZZ.lateralProjectedGMC`. Its proof uses simultaneous radial/GMC inversion,
retaining their source coupling. -/
theorem lateralProjectedGMC_reflection_law :
    P.map (fun ω => (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map
      (fun s : ℝ => -s)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  let T : TwoSidedPath × FiniteMeasure ℂ → Measure ℝ := fun q =>
    lateralProjectedGMC γ q.1 (q.2 : Measure ℂ)
  have harg : Measurable (fun q : TwoSidedPath × FiniteMeasure ℂ => ((γ, q.1), q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hT : Measurable T := by
    change Measurable ((fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
      lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) ∘
      fun q : TwoSidedPath × FiniteMeasure ℂ => ((γ, q.1), q.2))
    exact measurable_lateralProjectedGMC_finite.comp harg
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMF  :=
    @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hMm _ hM.1
  have hNf  := fun ω =>
    (FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹)).2
  have hNm  :=
    (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNF := @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ _ P hNm _ hNf
  have hL := (originReversedRadialPath_aemeasurable P _ hA).prodMk hNF
  have hR := hA.prodMk hMF
  have hj := originRadialGMC_inversion_joint_law P X Xc hX hc hcont γ hγ hγ2 M hM
  have h := (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hL).symm.trans
    ((congrArg (fun μ => μ.map T) hj).trans
      (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hR))
  change P.map (fun ω => lateralProjectedGMC γ (originReversedRadialPath (originRadialPath Xc ω))
    ((M ω).map (fun x : ℂ => x⁻¹))) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) at h
  simpa only [lateralProjectedGMC_reversed_inversion] using h

end

/-- The actual equator GMC has its complete two-sided radial/lateral
decomposition, including whole-measure stationarity and reflection. -/
theorem equatorGFF_lateral_GMC_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧ (∀ᵐ ω ∂P, A ω 0 = 0) ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
        IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
          (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
        AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IndepFun (fun ω => A ω) (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IsLateralGMCOf P γ (fun ω =>
          lateralProjectedGMC γ (A ω) (M ω)) := by
  obtain ⟨Xc, hcircle, hSource, hfin⟩ :=
    equatorGFF_exists_sourceLateralProjection P X hX γ hγ hγ2 M hM
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hcircle.isCircleAverage hcircle.continuous_ae
  have hB := originRadialPath_isBrownian P X Xc hX hcircle.isCircleAverage hcircle.continuous_ae
  have hZ := lateralProjectedGMC_aemeasurable P γ A hA M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  have hi := lateralProjectedGMC_indep P X Xc hX hcircle γ hγ hγ2 M hM
  refine ⟨A, ⟨Xc, hcircle.isCircleAverage, ?_⟩, hA, originRadialPath_zero_ae P X Xc hcircle.isCircleAverage hcircle.continuous_ae,
    hB.1, hB.2, originRadialPath_halves_indep P X Xc hX hcircle.isCircleAverage hcircle.continuous_ae, hZ, hi, ?_⟩
  · intro s
    exact (originRadialPath_eval_ae hcircle.continuous_ae).mono (fun ω hω => hω s)
  · refine ⟨hγ, hγ2, hX.1, hZ, hfin, ?_, ?_, ?_, ⟨X, M, hSource⟩⟩
    · exact fun t => lateralProjectedGMC_translation_law P X Xc hX hcircle.isCircleAverage hcircle.measurable hcircle.continuous_ae
        γ hγ hγ2 M hM t
    · exact lateralProjectedGMC_reflection_law P X Xc hX hcircle.isCircleAverage
        hcircle.continuous_ae γ hγ hγ2 M hM
    · exact fun a b _hab => lateralProjectedGMC_interval_intensity P X Xc hX hcircle.isCircleAverage hcircle.measurable hcircle.continuous_ae
        γ hγ hγ2 M hM a b

end DOZZ.Proofs
