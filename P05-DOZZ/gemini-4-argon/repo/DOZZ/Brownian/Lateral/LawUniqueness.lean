/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.GMC.EquatorGFFChaosTransportLaw
public import DOZZ.GMC.CircleAverageLimits
public import DOZZ.Statements.Brownian.IsLateralGMCOf
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Uniqueness of the lateral projection law

A common measurable reconstruction of the radial path uses rational circle averages.
For two given models, successive subsequence extraction makes the same annular test
approximations converge almost surely in both. Their limsup is consequently a common
function of the field evaluations. The joint field/GMC law then transports the literal
polar projection. No inverse chaos moment or change of regularization is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs


/-- An annular test approximation converges in measure to any authored circle witness. -/
theorem circle_test_approximation_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) Xc
    (hc : IsCircleAverage P X Xc) x r
    (f : ℕ → TestFn) (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => X ω (f n)) atTop (fun ω => Xc ω x r) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  change Tendsto (fun n => eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P) atTop (𝓝 0)
  simpa only [(fun n => eLpNorm_sub_comm _ _ _ _)] using hc.2.2 x r f hf


/-- Rational evaluations determine a full continuous radial path. -/
def radialRationalCode (A : TwoSidedPath) : ℚ → ℝ := fun q => A (q : ℝ)

/-- Encoding a path by its rational evaluations is measurable. -/
theorem measurable_radialRationalCode : Measurable radialRationalCode :=
  Measurable.of_eval fun q => ContinuousMap.measurable_eval (q : ℝ)

/-- Equality on the dense rational set is equality of continuous paths. -/
theorem radialRationalCode_injective : Function.Injective radialRationalCode := by
  intro A A' h
  apply ContinuousMap.ext
  exact congrFun (Rat.denseRange_cast.equalizer A.continuous A'.continuous h)

/-- The path code has a measurable inverse on its image. -/
theorem radialRationalCode_measurableEmbedding : MeasurableEmbedding radialRationalCode :=
  measurable_radialRationalCode.measurableEmbedding radialRationalCode_injective

/-- Reconstruct a continuous path from its rational code, with a measurable default off the image. -/
noncomputable def radialPathFromRationalCode : (ℚ → ℝ) → TwoSidedPath :=
  radialRationalCode_measurableEmbedding.invFun

/-- Reconstruction is measurable, including on codes which do not extend continuously. -/
theorem measurable_radialPathFromRationalCode : Measurable radialPathFromRationalCode :=
  radialRationalCode_measurableEmbedding.measurable_invFun

/-- Every actual continuous path is reconstructed exactly. -/
theorem radialPathFromRationalCode_code A :
    radialPathFromRationalCode (radialRationalCode A) = A :=
  radialRationalCode_measurableEmbedding.leftInverse_invFun A



/-- The field-and-radial-path input to transport is almost everywhere measurable. -/
theorem radial_GMC_pair_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (A : Ω → TwoSidedPath)
    Xc (hc : IsCircleAverage P X Xc)
    (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) :
    AEMeasurable (fun ω => (A ω, M ω)) P := by
  have radial_circle_witness_aemeasurable : AEMeasurable A P := by
    apply aemeasurable_twoSidedPath_of_eval
    intro s
    exact (hc.2.1 0 s).aemeasurable.congr ((hA s).mono fun ω hω => hω.symm)
  exact (radial_circle_witness_aemeasurable).prodMk
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)



/-- Extend a finite plane measure to a total measurable operation on all plane measures.
Infinite measures are replaced by zero only outside the finite carrier. -/
noncomputable def finitePlaneMeasureValue (μ : Measure ℂ) : Measure ℂ := by
  classical
  exact if μ univ < ⊤ then μ else 0

/-- Totalization always produces a finite measure. -/
theorem finitePlaneMeasureValue_finite (μ : Measure ℂ) :
    IsFiniteMeasure (finitePlaneMeasureValue μ) := by
  classical
  by_cases h : μ univ < ⊤
  · exact ⟨by simpa only [finitePlaneMeasureValue, ite_eq_left h] using h⟩
  · simp only [finitePlaneMeasureValue, ite_eq_right h]
    infer_instance

/-- Pack the totalized value in the measurable finite-measure carrier. -/
noncomputable def finitePlaneMeasureOrZero (μ : Measure ℂ) : FiniteMeasure ℂ :=
  ⟨finitePlaneMeasureValue μ, finitePlaneMeasureValue_finite μ⟩



/-- The actual radial projection has a measurable extension to all path/measure inputs. -/
noncomputable def totalizedLateralProjection (γ : ℝ) (A : TwoSidedPath)
    (μ : Measure ℂ) : Measure ℝ :=
  lateralProjectedGMC γ A (finitePlaneMeasureOrZero μ : Measure ℂ)


/-- On a finite chaos, the extension is the literal projection `DOZZ.lateralProjectedGMC`. -/
theorem totalizedLateralProjection_eq γ A
    (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
    totalizedLateralProjection γ A μ = lateralProjectedGMC γ A μ := by
  unfold totalizedLateralProjection
  rw [(show (finitePlaneMeasureOrZero μ : Measure ℂ) = μ by simp only [finitePlaneMeasureOrZero, finitePlaneMeasureValue, ite_eq_left hμ.measure_univ_lt_top, FiniteMeasure.toMeasure_mk])]



/-- The circle-average lateral projection has the same law across characterized field/GMC
models. See [KRV, §3.1]. -/
theorem isLateralGMCOf_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') γ (Z : Ω → Measure ℝ) (Z' : Ω' → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZ' : IsLateralGMCOf P' γ Z') :
    P.map Z = P'.map Z' := by
  have sourceLateralProjection_map_eq (hγ : 0 < γ) (hγ2 : γ < 2) (X : Ω → Distr) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ) (X' : Ω' → Distr) (M' : Ω' → Measure ℂ) (Z' : Ω' → Measure ℝ) (hZ : IsSourceLateralProjection P X γ M Z) (hZ' : IsSourceLateralProjection P' X' γ M' Z') : P.map Z = P'.map Z' := by
    have equatorGFF_radial_projection_map_eq (hX : IsEquatorGFF P X) (P' : Measure Ω') X' (hX' : IsEquatorGFF P' X') γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M') (A : Ω → TwoSidedPath) Xc (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) (A' : Ω' → TwoSidedPath) Xc' (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) : P.map (fun ω => lateralProjectedGMC γ (A ω) (M ω)) = P'.map (fun ω => lateralProjectedGMC γ (A' ω) (M' ω)) := by
      have measurable_totalizedLateralProjection : Measurable (fun p : TwoSidedPath × Measure ℂ => totalizedLateralProjection γ p.1 p.2) := by
        have measurable_finitePlaneMeasureOrZero : Measurable finitePlaneMeasureOrZero := by
          classical
          apply Measurable.subtype_mk
          change Measurable (fun μ : Measure ℂ => if μ univ < ⊤ then μ else 0)
          exact Measurable.ite (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const) measurable_id measurable_const
        change Measurable ((fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
          lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) ∘
          (fun p : TwoSidedPath × Measure ℂ => ((γ, p.1), finitePlaneMeasureOrZero p.2)))
        exact Measurable.comp measurable_lateralProjectedGMC_finite ((measurable_const.prodMk measurable_fst).prodMk (measurable_finitePlaneMeasureOrZero.comp measurable_snd))
      have equatorGFF_radial_GMC_map_eq (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M') (A : Ω → TwoSidedPath) Xc (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) (A' : Ω' → TwoSidedPath) Xc' (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) : P.map (fun ω => (A ω, M ω)) = P'.map (fun ω => (A' ω, M' ω)) := by
        have equatorGFF_radial_GMC_lintegral_law (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M') (A : Ω → TwoSidedPath) Xc (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) (A' : Ω' → TwoSidedPath) Xc' (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) (W : TwoSidedPath → Measure ℂ → ℝ≥0∞) (hW : Measurable (fun p : TwoSidedPath × Measure ℂ => W p.1 p.2)) : (∫⁻ ω, W (A ω) (M ω) ∂P) = ∫⁻ ω, W (A' ω) (M' ω) ∂P' := by
          have exists_common_radial_field_proxy (P : Measure Ω) (X : Ω → Distr) (A : Ω → TwoSidedPath) Xc (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) (P' : Measure Ω') (X' : Ω' → Distr) (A' : Ω' → TwoSidedPath) Xc' (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) : ∃ G : (TestFn → ℝ) → TwoSidedPath, Measurable G ∧ (fun ω => G (fun f => X ω f)) =ᵐ[P] A ∧ (fun ω => G (fun f => X' ω f)) =ᵐ[P'] A' := by
            classical
            have exists_common_circle_field_proxy x r : ∃ G : (TestFn → ℝ) → ℝ, Measurable G ∧ (fun ω => G (fun f => X ω f)) =ᵐ[P] (fun ω => Xc ω x r) ∧ (fun ω => G (fun f => X' ω f)) =ᵐ[P'] (fun ω => Xc' ω x r) := by
              have exists_common_subsequence_tendsto_ae (f : ℕ → Ω → ℝ) g (f' : ℕ → Ω' → ℝ) g' (h : TendstoInMeasure P f atTop g) (h' : TendstoInMeasure P' f' atTop g') : ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ᵐ ω ∂P, Tendsto (fun n => f (k n) ω) atTop (𝓝 (g ω))) ∧ (∀ᵐ ω ∂P', Tendsto (fun n => f' (k n) ω) atTop (𝓝 (g' ω))) := by
                obtain ⟨i, hi, hia⟩ := h.exists_seq_tendsto_ae
                obtain ⟨j, hj, hja⟩ := (h'.comp hi.tendsto_atTop).exists_seq_tendsto_ae
                refine ⟨i ∘ j, hi.comp hj, ?_, hja⟩
                filter_upwards [hia] with ω hω
                exact hω.comp hj.tendsto_atTop
              obtain ⟨f, _, _, hf⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
              obtain ⟨k, -, hk, hk'⟩ := exists_common_subsequence_tendsto_ae
                (fun n ω => X ω (f n)) (fun ω => Xc ω x r)
                (fun n ω => X' ω (f n)) (fun ω => Xc' ω x r)
                (circle_test_approximation_tendstoInMeasure P X Xc hc x r f hf)
                (circle_test_approximation_tendstoInMeasure P' X' Xc' hc' x r f hf)
              refine ⟨(fun e => limsup (fun n => e (f (k n))) atTop), Measurable.limsup (fun n => measurable_pi_apply _), ?_, ?_⟩
              · filter_upwards [hk] with ω hω
                exact hω.limsup_eq
              · filter_upwards [hk'] with ω hω
                exact hω.limsup_eq
            choose g hg he he' using (fun q : ℚ => exists_common_circle_field_proxy 0 (q : ℝ))
            refine ⟨(fun e => radialPathFromRationalCode (fun q => g q e)), (measurable_radialPathFromRationalCode.comp (Measurable.of_eval hg)), ?_, ?_⟩
            · filter_upwards [(by filter_upwards [(ae_all_iff.mpr he), (ae_all_iff.mpr (fun q : ℚ => hA (q : ℝ)))] with ω hω ha; funext q; exact (hω q).trans (ha q).symm)] with ω hω
              exact (congrArg radialPathFromRationalCode hω).trans (radialPathFromRationalCode_code _)
            · filter_upwards [(by filter_upwards [(ae_all_iff.mpr he'), (ae_all_iff.mpr (fun q : ℚ => hA' (q : ℝ)))] with ω hω ha; funext q; exact (hω q).trans (ha q).symm)] with ω hω
              exact (congrArg radialPathFromRationalCode hω).trans (radialPathFromRationalCode_code _)
          obtain ⟨G, hG, he, he'⟩ := exists_common_radial_field_proxy
            P X A Xc hc hA P' X' A' Xc' hc' hA'
          let H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun e μ => W (G e) μ
          calc
            _ = ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P := by
              apply lintegral_congr_ae
              filter_upwards [he] with ω hω
              change W (A ω) (M ω) = W (G (fun f => X ω f)) (M ω)
              rw [hω]
            _ = ∫⁻ ω, H (fun f => X' ω f) (M' ω) ∂P' :=
              equatorGFF_GMC_law_transport P X hX P' X' hX' γ hγ hγ2 M hM M' hM' H (hW.comp ((hG.comp measurable_fst).prodMk measurable_snd))
            _ = _ := by
              apply lintegral_congr_ae
              filter_upwards [he'] with ω hω
              change W (G (fun f => X' ω f)) (M' ω) = W (A' ω) (M' ω)
              rw [hω]
        have hm := radial_GMC_pair_aemeasurable P X hX γ hγ hγ2 M hM A Xc hc hA
        have hm' := radial_GMC_pair_aemeasurable P' X' hX' γ hγ hγ2 M' hM' A' Xc' hc' hA'
        apply Measure.ext
        intro S hS
        rw [Measure.map_apply_of_aemeasurable hm hS, Measure.map_apply_of_aemeasurable hm' hS]
        have h := equatorGFF_radial_GMC_lintegral_law
          M hM M' hM' A Xc hc hA A' Xc' hc' hA'
          (fun A μ => S.indicator (fun _ => 1) (A, μ))
          (measurable_const.indicator hS)
        rw [(show (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (A ω, M ω)) = ((fun ω => (A ω, M ω)) ⁻¹' S).indicator (fun _ => 1) by funext ω; by_cases hω : (A ω, M ω) ∈ S <;> simp [hω]), (show (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (A' ω, M' ω)) = ((fun ω => (A' ω, M' ω)) ⁻¹' S).indicator (fun _ => 1) by funext ω; by_cases hω : (A' ω, M' ω) ∈ S <;> simp [hω])] at h
        change (∫⁻ ω, ((fun ω => (A ω, M ω)) ⁻¹' S).indicator 1 ω ∂P) =
          (∫⁻ ω, ((fun ω => (A' ω, M' ω)) ⁻¹' S).indicator 1 ω ∂P') at h
        rw [lintegral_indicator_one₀ (hm.nullMeasurable hS),
          lintegral_indicator_one₀ (hm'.nullMeasurable hS)] at h
        exact h
      let T : TwoSidedPath × Measure ℂ → Measure ℝ := fun p => totalizedLateralProjection γ p.1 p.2
      have hT := measurable_totalizedLateralProjection
      rw [(show (fun ω => lateralProjectedGMC γ (A ω) (M ω)) = T ∘ (fun ω => (A ω, M ω)) by funext ω; exact (totalizedLateralProjection_eq γ (A ω) (M ω) (hM.1 ω)).symm), (show (fun ω => lateralProjectedGMC γ (A' ω) (M' ω)) = T ∘ (fun ω => (A' ω, M' ω)) by funext ω; exact (totalizedLateralProjection_eq γ (A' ω) (M' ω) (hM'.1 ω)).symm), ← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable (radial_GMC_pair_aemeasurable P X hX γ hγ hγ2 M hM A Xc hc hA),
        ← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable (radial_GMC_pair_aemeasurable P' X' hX' γ hγ hγ2 M' hM' A' Xc' hc' hA'),
        equatorGFF_radial_GMC_map_eq
          M hM M' hM' A Xc hc hA A' Xc' hc' hA']
    rcases hZ with ⟨hX, hM, A, ⟨Xc, hc, hAc⟩, -, -, -, -, -, -, -, he⟩
    rcases hZ' with ⟨hX', hM', A', ⟨Xc', hc', hAc'⟩, -, -, -, -, -, -, -, he'⟩
    rw [Measure.map_congr he, Measure.map_congr he']
    exact equatorGFF_radial_projection_map_eq hX P' X' hX' γ hγ hγ2
      M hM M' hM' A Xc hc hAc A' Xc' hc' hAc'
  obtain ⟨X, M, hS⟩ := hZ.2.2.2.2.2.2.2.2
  obtain ⟨X', M', hS'⟩ := hZ'.2.2.2.2.2.2.2.2
  exact sourceLateralProjection_map_eq hZ.1 hZ.2.1 X M Z X' M' Z' hS hS'

end DOZZ.Proofs
