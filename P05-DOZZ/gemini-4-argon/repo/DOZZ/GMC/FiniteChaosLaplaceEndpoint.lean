/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosLaplaceDomination

/-! Endpoint comparison for the finite Laplace interpolation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The concrete interior derivative sign makes the finite Laplace interpolation antitone. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_antitoneOn
    {n} A B
    (a : Fin (n + 1) → ℝ) γ s
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s)
    (hcov : ∀ i j, finiteChaosMatrixRowCovariance A i j ≤
      finiteChaosMatrixRowCovariance B i j) :
    AntitoneOn (finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s)
      (Set.Ioo 0 1) := by
  have hderiv (t : ℝ) (ht : t ∈ Set.Ioo 0 1) := finiteChaosMatrixLaplaceInterpolationExpectation_deriv_nonpos_concrete
      A B a γ s t ha hs ht.1 ht.2 hcov
  have hfderiv : ∀ t ∈ Set.Ioo 0 1, deriv (finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s) t ≤ 0 := by
    intro t ht
    rw [(hderiv t ht).1.deriv]
    exact (hderiv t ht).2
  exact antitoneOn_of_deriv_nonpos (convex_Ioo 0 1) (by intro t ht; exact (hderiv t ht).1.continuousAt.continuousWithinAt)
    (by simpa using (by intro t ht; exact (hderiv t ht).1.differentiableAt.differentiableWithinAt)) (by simpa using hfderiv)

/-- The Laplace expectation at the `A` endpoint is bounded by the expectation at the `B`
endpoint, with no nonsingularity requirement on either matrix. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_endpoint_le
    {n} A B
    (a : Fin (n + 1) → ℝ) γ s
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s)
    (hcov : ∀ i j, finiteChaosMatrixRowCovariance A i j ≤
      finiteChaosMatrixRowCovariance B i j) :
    finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s 1 ≤
      finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s 0 := by
  classical
  let f := finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s
  let μ := standardGaussianFinMeasure n
  let ν := μ.prod μ
  let g : ℝ → ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) → ℝ := fun t z =>
    Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z)
  have hgcont z :
      Continuous (fun t => g t z) := by
    change Continuous (fun t => Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z))
    fun_prop [kahaneInterpolatedMass, finiteChaosMatrixTwoBlockField,
      finiteChaosMatrixTwoBlockVariance, finiteChaosMatrixRowVariance,
      finiteChaosMatrixRowCovariance, finiteChaosLinearImageVector,
      finiteChaosVectorMass, finiteChaosVectorWeight]
  have hgz t : Continuous (g t) := by
    change Continuous (fun z => Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z))
    fun_prop [kahaneInterpolatedMass, finiteChaosMatrixTwoBlockField,
      finiteChaosMatrixTwoBlockVariance, finiteChaosMatrixRowVariance,
      finiteChaosMatrixRowCovariance, finiteChaosLinearImageVector,
      finiteChaosVectorMass, finiteChaosVectorWeight]
  have hbound t z :
      ‖g t z‖ ≤ 1 := by
    have hmass : 0 ≤ kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z :=
      finiteChaosVectorMass_nonneg a (finiteChaosMatrixTwoBlockVariance A B t) γ ha
        (finiteChaosMatrixTwoBlockField A B t z.1 z.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hs, hmass]
  have hconstInt : Integrable (fun _ : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => (1 : ℝ)) ν := integrable_const 1
  have hDCT (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
      Tendsto (fun k => ∫ z, g (u k) z ∂ν) atTop (𝓝 (∫ z, g 0 z ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : (Fin (n + 1) → ℝ) ×
      (Fin (n + 1) → ℝ) => (1 : ℝ))
    · intro k
      exact (hgz (u k)).aestronglyMeasurable
    · exact hconstInt
    · intro k
      filter_upwards [] with z
      exact hbound (u k) z
    · filter_upwards [] with z
      exact (hgcont z).continuousAt.tendsto.comp hu
  have hDCTone (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 1)) :
      Tendsto (fun k => ∫ z, g (u k) z ∂ν) atTop (𝓝 (∫ z, g 1 z ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : (Fin (n + 1) → ℝ) ×
      (Fin (n + 1) → ℝ) => (1 : ℝ))
    · intro k
      exact (hgz (u k)).aestronglyMeasurable
    · exact hconstInt
    · intro k
      filter_upwards [] with z
      exact hbound (u k) z
    · filter_upwards [] with z
      exact (hgcont z).continuousAt.tendsto.comp hu
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hu0 : Tendsto u atTop (𝓝 0) := by
    simpa [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlow := eventually_atTop.2 ⟨1, fun _ hk => hk⟩
  have hcomparison : ∀ᶠ k : ℕ in atTop, f (1 - u k) ≤ f (u k) := by
    filter_upwards [hlow] with k hk
    have huHalf : u k ≤ (1 / 2 : ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num)
      simpa [u] using (by exact_mod_cast (by omega))
    have huPos : 0 < u k := by dsimp [u]; positivity
    have huLtOne : u k < 1 := lt_of_le_of_lt huHalf (by norm_num)
    have hupperPos : 0 < 1 - u k := by linarith
    have hupperLtOne : 1 - u k < 1 := by linarith
    exact finiteChaosMatrixLaplaceInterpolationExpectation_antitoneOn
      A B a γ s ha hs hcov ⟨huPos, huLtOne⟩ ⟨hupperPos, hupperLtOne⟩ (by linarith)
  exact le_of_tendsto_of_tendsto (by simpa [f, g, finiteChaosMatrixLaplaceInterpolationExpectation, ν, μ] using hDCTone (fun k => 1 - u k) (by simpa using tendsto_const_nhds.sub hu0)) (by simpa [f, g, finiteChaosMatrixLaplaceInterpolationExpectation, ν, μ] using hDCT u hu0) hcomparison

/-- At the endpoints, the unused independent Gaussian block integrates out, leaving the usual
single standard-Gaussian expectation of each matrix linear image. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_endpoint_eq
    {n} A B
    (a : Fin (n + 1) → ℝ) γ s
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s) :
    finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s 1 =
        ∫ x : Fin (n + 1) → ℝ,
          Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ
            (finiteChaosLinearImageVector A x)) ∂(standardGaussianFinMeasure n) ∧
      finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s 0 =
        ∫ x : Fin (n + 1) → ℝ,
          Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ
            (finiteChaosLinearImageVector B x)) ∂(standardGaussianFinMeasure n) := by
  classical
  let μ := standardGaussianFinMeasure n
  let ν := μ.prod μ
  let gA : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ
      (finiteChaosLinearImageVector A x))
  let gB : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ
      (finiteChaosLinearImageVector B x))
  have hboundA x : ‖gA x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hs, (finiteChaosVectorMass_nonneg a (finiteChaosMatrixRowVariance A) γ ha _ : 0 ≤ finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ (finiteChaosLinearImageVector A x))]
  have hboundB x : ‖gB x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hs, (finiteChaosVectorMass_nonneg a (finiteChaosMatrixRowVariance B) γ ha _ : 0 ≤ finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ (finiteChaosLinearImageVector B x))]
  have hfieldA (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 1 z =
        finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ
          (finiteChaosLinearImageVector A z.1) := by
    simp [kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight,
      finiteChaosMatrixRowVariance, finiteChaosMatrixRowCovariance,
      finiteChaosLinearImageVector]
  have hfieldB (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 0 z =
        finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ
          (finiteChaosLinearImageVector B z.2) := by
    simp [kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight,
      finiteChaosMatrixRowVariance, finiteChaosMatrixRowCovariance,
      finiteChaosLinearImageVector]
  constructor
  · change (∫ z, Real.exp (-s * kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 1 z) ∂ν) = _
    rw [(show (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => Real.exp (-s * kahaneInterpolatedMass (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B) (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 1 z)) = fun z => gA z.1 by funext z; rw [hfieldA]), integral_prod _ ((Integrable.of_bound (show Continuous gA by change Continuous (fun x => Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance A) γ (finiteChaosLinearImageVector A x))); fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight, finiteChaosLinearImageVector]).aestronglyMeasurable 1 (ae_of_all μ hboundA)).comp_fst μ)]
    simp [gA, μ]
  · change (∫ z, Real.exp (-s * kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 0 z) ∂ν) = _
    rw [(show (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => Real.exp (-s * kahaneInterpolatedMass (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B) (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ 0 z)) = fun z => gB z.2 by funext z; rw [hfieldB]), integral_prod _ ((Integrable.of_bound (show Continuous gB by change Continuous (fun x => Real.exp (-s * finiteChaosVectorMass a (finiteChaosMatrixRowVariance B) γ (finiteChaosLinearImageVector B x))); fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight, finiteChaosLinearImageVector]).aestronglyMeasurable 1 (ae_of_all μ hboundB)).comp_snd μ)]
    simp [gB, μ]


end DOZZ.Proofs
