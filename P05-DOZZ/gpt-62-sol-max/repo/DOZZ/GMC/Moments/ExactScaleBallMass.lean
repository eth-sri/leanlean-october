/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.GMC.Moments.ExactScaleLimit
public import DOZZ.GMC.Moments.OpenBallApproximation
public import DOZZ.GMC.Moments.SetMassMeasurable

/-! Exact affine scaling of open-ball masses for arbitrary `IsGMCOf` versions. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

private theorem gmc_test_integral_aemeasurable_of_support (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : MeasurableSet K)
    (hKunit : ∀ x ∈ K, ‖x‖ ≤ 1)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hfzero : ∀ x, x ∉ K → f x = 0) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  have hcut (n : ℕ) := regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n f f.continuous.measurable
  have hconv := (hMlim f).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact hconv.aemeasurable hcut

/-- Affine scaling of the test integrals passes to disk masses by approximation from
within each disk. This works both at a finite cutoff and for the limiting measures. -/
theorem affine_openBall_mass_law_of_tests [IsProbabilityMeasure P]
    (G : Measure ℝ) [IsProbabilityMeasure G] (μ ν : Ω → Measure ℂ)
    (hμ : ∀ᵐ ω ∂P, IsFiniteMeasure (μ ω)) (hν : ∀ᵐ ω ∂P, IsFiniteMeasure (ν ω))
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (W : ℝ → ℝ) (hW : Measurable W)
    (hf : ∀ n : ℕ, AEMeasurable (fun ω => ∫ x, openBallAffineApprox a c R n x ∂μ ω) P)
    (hg : ∀ n : ℕ, AEMeasurable (fun ω => ∫ x, openBallApprox 0 R n x ∂ν ω) P)
    (hlaw : ∀ n : ℕ,
      Measure.map (fun ω (_ : Fin 1) => ∫ x, openBallAffineApprox a c R n x ∂μ ω) P =
        Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 =>
          W q.2 * ∫ x, openBallAffineApprox a c R n (a + c • x) ∂ν q.1) (P.prod G)) :
    Measure.map (fun ω => (μ ω (Metric.ball a (c * R))).toReal) P =
      Measure.map (fun q : Ω × ℝ => W q.2 * (ν q.1 (Metric.ball 0 R)).toReal) (P.prod G) := by
  let f (n : ℕ) (ω : Ω) := ∫ x, openBallAffineApprox a c R n x ∂μ ω
  let g (n : ℕ) (ω : Ω) := ∫ x, openBallApprox 0 R n x ∂ν ω
  let F (ω : Ω) := (μ ω (Metric.ball a (c * R))).toReal
  let J (ω : Ω) := (ν ω (Metric.ball 0 R)).toReal
  have hfT : TendstoInMeasure P f atTop F := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hf n).aestronglyMeasurable)
    filter_upwards [hμ] with ω hw
    exact openBallAffineApprox_integral_tendsto hc (μ ω)
  have hgT : TendstoInMeasure P g atTop J := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hg n).aestronglyMeasurable)
    filter_upwards [hν] with ω hw
    exact openBallApprox_integral_tendsto 0 R (ν ω)
  let g' (n : ℕ) (q : Ω × ℝ) := W q.2 * g n q.1
  have hg' (n : ℕ) : AEMeasurable (g' n) (P.prod G) :=
    (hW.comp measurable_snd).aemeasurable.mul (hg n).comp_fst
  have hg'T := tendstoInMeasure_mul_snd_of_tendstoInMeasure (Q := G) g J W hW hgT
  refine map_eq_of_seq_map_eq_of_tendstoInMeasure f g' F _ hf hg'
    (hfT.aemeasurable hf) (hg'T.aemeasurable hg') ?_ hfT hg'T
  intro n
  have h := hlaw n
  simp_rw [openBallAffineApprox_comp_affine a c R hc.ne'] at h
  have he : Measurable (fun v : Fin 1 → ℝ => v 0) := measurable_pi_apply 0
  have hm := congrArg (Measure.map (fun v : Fin 1 → ℝ => v 0)) h
  rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable (.of_eval fun _ => hf n),
    AEMeasurable.map_map_of_aemeasurable he.aemeasurable (.of_eval fun _ => hg' n)] at hm
  exact hm

private theorem openBallApprox_test_measurable_of_chart (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : MeasurableSet K) (hKunit : ∀ x ∈ K, ‖x‖ ≤ 1)
    (f : ℂ →ᵇ ℝ) (hf : tsupport (f : ℂ → ℝ) ⊆ K) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P :=
  gmc_test_integral_aemeasurable_of_support P X hX γ M hM K hK hKunit f
    (boundedContinuousFunction_eq_zero_off_tsupport_subset f K hf)

end

/-- Open balls in the logarithmic chart lie in the unit disk. -/
theorem norm_le_one_of_mem_closedBall_in_chart {a : ℂ} {R : ℝ}
    (h : ‖a‖ + R ≤ 1) : ∀ x ∈ Metric.closedBall a R, ‖x‖ ≤ 1 := by
  intro x hx
  have hxa : ‖x - a‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  calc
    ‖x‖ = ‖x - a + a‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - a‖ + ‖a‖ := norm_add_le _ _
    _ ≤ 1 := by linarith

/-- For a disk compactly contained in the logarithmic chart, the affine scaling law holds for its
mass, including the independent scalar Gaussian. The result applies to every `IsGMCOf` version. -/
theorem gmc_affine_openBall_mass_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1) :
    Measure.map (fun ω : Ω =>
      (M ω (Metric.ball a (c * R))).toReal) P =
    Measure.map (fun p : Ω × ℝ =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
        (M p.1 (Metric.ball 0 R)).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  have := hX.1
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩
  have : IsProbabilityMeasure G := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  refine affine_openBall_mass_law_of_tests P G
    M M (ae_of_all _ hM.1) (ae_of_all _ hM.1) hc
    (fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))) (by fun_prop) ?_ ?_ ?_
  · intro n
    exact openBallApprox_test_measurable_of_chart P X hX γ M hM _
      Metric.isClosed_closedBall.measurableSet (norm_le_one_of_mem_closedBall_in_chart hTsmall.le)
      _ (openBallAffineApprox_tsupport_subset hc n)
  · intro n
    exact openBallApprox_test_measurable_of_chart P X hX γ M hM _
      Metric.isClosed_closedBall.measurableSet
      (norm_le_one_of_mem_closedBall_in_chart (a := 0) (by simpa using hRsmall.le))
      _ (openBallApprox_tsupport_subset 0 R n)
  · intro n
    exact gmc_affine_test_vector_law P X hX γ M hM hc hc1 hR hRsmall hTsmall
      (fun _ => openBallAffineApprox a c R n)
      (fun _ x => (openBallApproxFun_bounds 0 R n ((c : ℂ)⁻¹ • (x - a))).1)
      (fun _ => openBallAffineApprox_tsupport_subset hc n)

end DOZZ.Proofs
