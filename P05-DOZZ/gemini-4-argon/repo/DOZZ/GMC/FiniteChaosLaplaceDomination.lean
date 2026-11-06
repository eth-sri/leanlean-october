/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosLaplaceInterpolation

/-! Concrete Gaussian domination for the finite Laplace interpolation derivative. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The derivative of a finite Laplace test is bounded by a finite linear combination of the
absolute standard Gaussian coordinates, uniformly on compact subintervals of `(0,1)`. -/
theorem finiteChaosMatrixLaplaceInterpolationTestDerivative_norm_le
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t ε : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s)
    (hε : 0 < ε) (hεt : 2 * ε ≤ t) (hεt' : 2 * ε ≤ 1 - t)
    (r : ℝ) (hr : r ∈ Metric.ball t ε)
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    ‖kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) r z‖ ≤
      ∑ i, ((|γ| / (2 * Real.sqrt ε)) *
          ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
        (γ ^ 2 / 2) * |finiteChaosMatrixRowVariance A i -
          finiteChaosMatrixRowVariance B i|) := by
  classical
  have hrball : |r - t| < ε := by
    simpa [Real.dist_eq] using hr
  have hrlo : ε ≤ r := by
    have := abs_lt.mp hrball
    linarith
  have hrhi : ε ≤ 1 - r := by
    have := abs_lt.mp hrball
    linarith
  have hsqrtR := Real.sqrt_le_sqrt hrlo
  have hsqrtS := Real.sqrt_le_sqrt hrhi
  have hdenE : 0 < 2 * Real.sqrt ε := by positivity
  let vA := finiteChaosMatrixRowVariance A
  let vB := finiteChaosMatrixRowVariance B
  let V := finiteChaosMatrixTwoBlockVariance A B r
  let W := finiteChaosMatrixTwoBlockField A B r
  let H := |γ| / (2 * Real.sqrt ε)
  let score (i : Fin (n + 1)) := finiteChaosMatrixLaplaceScore A B a γ s r i z
  let deriv (i : Fin (n + 1)) :=
    γ * (finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r) -
      finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))) -
      γ ^ 2 / 2 * (vA i - vB i)
  have hscore (i : Fin (n + 1)) : ‖score i‖ ≤ 1 := by
    dsimp [score, finiteChaosMatrixLaplaceScore, V, W, vA, vB]
    exact finiteChaos_laplace_first_weight_bound a
      (finiteChaosMatrixTwoBlockVariance A B r) γ s ha hs
      (finiteChaosMatrixTwoBlockField A B r z.1 z.2) i
  have hArow (i : Fin (n + 1)) :
      |finiteChaosLinearImageVector A z.1 i| ≤ ∑ k, |A i k| * |z.1 k| := by
    calc
      |finiteChaosLinearImageVector A z.1 i| =
          |∑ k, A i k * z.1 k| := by rfl
      _ ≤ ∑ k, |A i k * z.1 k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |A i k| * |z.1 k| := by simp [abs_mul]
  have hBrow (i : Fin (n + 1)) :
      |finiteChaosLinearImageVector B z.2 i| ≤ ∑ k, |B i k| * |z.2 k| := by
    calc
      |finiteChaosLinearImageVector B z.2 i| =
          |∑ k, B i k * z.2 k| := by rfl
      _ ≤ ∑ k, |B i k * z.2 k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |B i k| * |z.2 k| := by simp [abs_mul]
  have hderiv (i : Fin (n + 1)) :
      ‖deriv i‖ ≤ H *
        ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
          (γ ^ 2 / 2) * |vA i - vB i| := by
    have :
        |finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r)| ≤
          |finiteChaosLinearImageVector A z.1 i| / (2 * Real.sqrt ε) := by
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 hε) hsqrtR))]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hdenE (by nlinarith [hsqrtR])
    have :
        |finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))| ≤
          |finiteChaosLinearImageVector B z.2 i| / (2 * Real.sqrt ε) := by
      rw [abs_div, abs_of_pos (mul_pos (by norm_num) (lt_of_lt_of_le (Real.sqrt_pos.2 hε) hsqrtS))]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hdenE (by nlinarith [hsqrtS])
    have htriangle : |deriv i| ≤
        |γ| * (|finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r)| +
          |finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))|) +
          |γ ^ 2 / 2 * (vA i - vB i)| := by
      dsimp [deriv]
      calc
        |γ * (finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r) -
            finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))) -
            γ ^ 2 / 2 * (vA i - vB i)| ≤
          |γ * (finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r) -
              finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r)))| +
            |γ ^ 2 / 2 * (vA i - vB i)| := abs_sub _ _
        _ = |γ| * |finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r) -
              finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))| +
            |γ ^ 2 / 2 * (vA i - vB i)| := by rw [abs_mul]
        _ ≤ |γ| * (|finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r)| +
              |finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))|) +
            |γ ^ 2 / 2 * (vA i - vB i)| := by
              gcongr
              exact abs_sub _ _
    rw [Real.norm_eq_abs]
    calc
      |deriv i| ≤
          |γ| * (|finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt r)| +
            |finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - r))|) +
            |γ ^ 2 / 2 * (vA i - vB i)| := htriangle
      _ ≤ |γ| * (|finiteChaosLinearImageVector A z.1 i| / (2 * Real.sqrt ε) +
            |finiteChaosLinearImageVector B z.2 i| / (2 * Real.sqrt ε)) +
            |γ ^ 2 / 2 * (vA i - vB i)| := by
              gcongr
      _ = H * (|finiteChaosLinearImageVector A z.1 i| +
            |finiteChaosLinearImageVector B z.2 i|) +
            (γ ^ 2 / 2) * |vA i - vB i| := by
              rw [(show |γ ^ 2 / 2 * (vA i - vB i)| = (γ ^ 2 / 2) * |vA i - vB i| by rw [abs_mul, abs_of_nonneg (show 0 ≤ γ ^ 2 / 2 by positivity)])]
              dsimp [H]
              ring
      _ ≤ H * ((∑ k, |A i k| * |z.1 k|) +
            (∑ k, |B i k| * |z.2 k|)) +
            (γ ^ 2 / 2) * |vA i - vB i| := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left (add_le_add (hArow i) (hBrow i)) (by dsimp [H]; positivity)) le_rfl
  calc
    ‖kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) r z‖ =
      ‖∑ i, score i * deriv i‖ := by
        rw [kahaneInterpolatedLaplaceTestDerivative_eq_score_sum]
    _ ≤ ∑ i, ‖score i * deriv i‖ := norm_sum_le _ _
    _ ≤ ∑ i,
        (H * ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
          (γ ^ 2 / 2) * |vA i - vB i|) := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            ‖score i * deriv i‖ = ‖score i‖ * ‖deriv i‖ := norm_mul _ _
            _ ≤ 1 * ‖deriv i‖ := mul_le_mul_of_nonneg_right (hscore i) (norm_nonneg _)
            _ = ‖deriv i‖ := by simp
            _ = |deriv i| := Real.norm_eq_abs _
            _ ≤ H * ((∑ k, |A i k| * |z.1 k|) +
                (∑ k, |B i k| * |z.2 k|)) +
                (γ ^ 2 / 2) * |vA i - vB i| := hderiv i
    _ = _ := by simp [H, vA, vB]

/-- A concrete integrable majorant for the finite Laplace interpolation derivative. -/
noncomputable def finiteChaosMatrixLaplaceInterpolationDerivativeBound
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (γ ε : ℝ) (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  ∑ i, ((|γ| / (2 * Real.sqrt ε)) *
      ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
        (γ ^ 2 / 2) * |finiteChaosMatrixRowVariance A i -
          finiteChaosMatrixRowVariance B i|)

/-- The concrete majorant is integrable under the product standard-Gaussian law. -/
theorem finiteChaosMatrixLaplaceInterpolationDerivativeBound_integrable
    {n} A B
    γ ε :
    Integrable (finiteChaosMatrixLaplaceInterpolationDerivativeBound A B γ ε)
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) := by
  classical
  let μ := standardGaussianFinMeasure n
  let ν := μ.prod μ
  have hcoordPi k : Integrable
      (fun x : Fin (n + 1) → ℝ => x k) μ := by
    simpa [μ, standardGaussianFinMeasure] using
      (integrable_eval IsGaussian.integrable_id :
        Integrable (fun x : Fin (n + 1) → ℝ => x k)
          (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
  have hcoordX k : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => |z.1 k|) ν := by
    simpa only [Real.norm_eq_abs] using ((hcoordPi k).norm).comp_fst μ
  have hcoordY k : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => |z.2 k|) ν := by
    simpa only [Real.norm_eq_abs] using ((hcoordPi k).norm).comp_snd μ
  have hArow i : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ∑ k, |A i k| * |z.1 k|) ν := by
    apply integrable_finsetSum Finset.univ
    intro k hk
    simpa [mul_comm] using (hcoordX k).const_mul (|A i k|)
  have hBrow i : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ∑ k, |B i k| * |z.2 k|) ν := by
    apply integrable_finsetSum Finset.univ
    intro k hk
    simpa [mul_comm] using (hcoordY k).const_mul (|B i k|)
  have hterm i : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ((|γ| / (2 * Real.sqrt ε)) *
            ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
          (γ ^ 2 / 2) * |finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i|)) ν := by
    exact (show Integrable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => (|γ| / (2 * Real.sqrt ε)) * ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|))) ν by exact (show (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) * (|γ| / (2 * Real.sqrt ε))) = (fun z => (|γ| / (2 * Real.sqrt ε)) * ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|))) by funext z; ring) ▸ (((hArow i).add (hBrow i)).const_mul (|γ| / (2 * Real.sqrt ε)))).add (integrable_const _)
  change Integrable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      ∑ i, ((|γ| / (2 * Real.sqrt ε)) *
          ((∑ k, |A i k| * |z.1 k|) + (∑ k, |B i k| * |z.2 k|)) +
        (γ ^ 2 / 2) * |finiteChaosMatrixRowVariance A i -
          finiteChaosMatrixRowVariance B i|)) ν
  simpa [μ, ν] using (integrable_finsetSum Finset.univ fun i hi => hterm i)

/-- The expectation derivative sign is now concrete: the only analytic input is the finite
standard-Gaussian first moment, which supplies the derivative majorant. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_deriv_nonpos_concrete
    {n} A B
    (a : Fin (n + 1) → ℝ) γ s t
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s) (ht : 0 < t) (ht1 : t < 1)
    (hcov : ∀ i j, finiteChaosMatrixRowCovariance A i j ≤
      finiteChaosMatrixRowCovariance B i j) :
    HasDerivAt (finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s)
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z
        ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) t ∧
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z
        ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) ≤ 0 := by
  classical
  let ε : ℝ := min (t / 2) ((1 - t) / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have h2εt : 2 * ε ≤ t := by
    calc
      2 * ε ≤ 2 * (t / 2) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
      _ = t := by ring
  have h2εt' : 2 * ε ≤ 1 - t := by
    calc
      2 * ε ≤ 2 * ((1 - t) / 2) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = 1 - t := by ring
  let μ := standardGaussianFinMeasure n
  let ν := μ.prod μ
  let F : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) → ℝ := fun z =>
    Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z)
  have hFcont : Continuous F := by
    change Continuous (fun z => Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z))
    fun_prop [finiteChaosLinearImageVector, kahaneInterpolatedMass,
      finiteChaosVectorMass, finiteChaosVectorWeight]
  have hInt : Integrable F ν := by
    have hmass z :
        0 ≤ kahaneInterpolatedMass
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z := finiteChaosVectorMass_nonneg a
        (finiteChaosMatrixTwoBlockVariance A B t) γ ha
        (finiteChaosMatrixTwoBlockField A B t z.1 z.2)
    have hbound z :
        ‖F z‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [hs, hmass z]
    apply (integrable_const (1 : ℝ)).mono'
    · exact hFcont.aestronglyMeasurable
    · filter_upwards [] with z
      exact hbound z
  let b := finiteChaosMatrixLaplaceInterpolationDerivativeBound A B γ ε
  have hbound : ∀ᵐ z ∂ν, ∀ r ∈ Metric.ball t ε,
      ‖kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) r z‖ ≤ b z := by
    filter_upwards [] with z
    intro r hr
    exact finiteChaosMatrixLaplaceInterpolationTestDerivative_norm_le
      A B a γ s t ε ha hs hε h2εt h2εt' r hr z
  simpa [μ, ν] using (finiteChaosMatrixLaplaceInterpolationExpectation_deriv_nonpos A B a γ s t ε ha hs ht ht1 hcov hε (by linarith) (show ε ≤ 1 - t by linarith) (by filter_upwards [] with r; exact (show Continuous (fun z => Real.exp (-s * kahaneInterpolatedMass (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B) (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ r z)) by fun_prop [finiteChaosLinearImageVector, kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight]).aestronglyMeasurable) (by simpa [F, μ, ν] using hInt) (by exact (show Continuous (fun z => kahaneInterpolatedTestDerivative (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B) (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ (fun x => -s * Real.exp (-s * x)) t z) by fun_prop [finiteChaosLinearImageVector, kahaneInterpolatedTestDerivative, kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight]).aestronglyMeasurable) b (by simpa [b, ν] using (finiteChaosMatrixLaplaceInterpolationDerivativeBound_integrable A B γ ε)) (by simpa [b, ν] using hbound))


end DOZZ.Proofs
