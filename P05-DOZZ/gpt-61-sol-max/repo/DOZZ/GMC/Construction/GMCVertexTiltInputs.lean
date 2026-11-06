/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.CircleAverageLimits
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Gaussian `L²` closure input for finite linear combinations of circle averages. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal
open DOZZ.Proofs.CirclePotential
open scoped BoundedContinuousFunction

namespace DOZZ.Proofs

/-- Linearity of a distribution identifies the combined approximation error. -/
private theorem finite_sum_test_error_eq
    {Ω : Type*} {N : ℕ} (X : Ω → Distr) (α : Fin N → ℝ)
    (L : Fin N → Ω → ℝ) (f : Fin N → TestFn) (ω : Ω) :
    (∑ k, α k * L k ω) - X ω (∑ k, α k • f k) =
      ∑ k, α k • (L k ω - X ω (f k)) := by
  simp [Finset.sum_sub_distrib, mul_sub, smul_eq_mul]

/-- A finite linear combination of `L²` limits of test evaluations is again in their closure.
The approximating tests are the same finite linear combinations of the individual tests. -/
private theorem gaussianL2Limit_finset_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr)
    {N : ℕ} (α : Fin N → ℝ) (L : Fin N → Ω → ℝ)
    (hmem : ∀ k, MemLp (L k) 2 P)
    (f : Fin N → ℕ → TestFn)
    (hf : ∀ k, Tendsto (fun n => eLpNorm (fun ω => L k ω - X ω (f k n)) 2 P)
      atTop (𝓝 0)) :
    IsGaussianL2Limit P X (fun ω => ∑ k, α k * L k ω) := by
  classical
  let g  := fun n => ∑ k, α k • f k n
  have hmem'  :=
    memLp_finsetSum Finset.univ (fun k hk => (hmem k).const_mul (α k))
  have hmem'' : MemLp (fun ω => ∑ k, α k * L k ω) 2 P := hmem'
  have herror (k : Fin N) :
      Tendsto (fun n => eLpNorm (fun ω => α k • (L k ω - X ω (f k n))) 2 P)
        atTop (𝓝 0) := by
    rw [show (fun n => eLpNorm (fun ω => α k • (L k ω - X ω (f k n))) 2 P) =
        fun n => ‖α k‖ₑ * eLpNorm (fun ω => L k ω - X ω (f k n)) 2 P by
      funext n
      exact eLpNorm_const_smul (α k) _ _ _]
    simpa [enorm_eq_nnnorm] using ENNReal.Tendsto.const_mul (hf k) (Or.inr (by
      simp_all))
  have hsum : Tendsto
      (fun n => ∑ k, eLpNorm (fun ω => α k • (L k ω - X ω (f k n))) 2 P)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin N))
      (fun k hk => herror k)
  have hbound (n : ℕ) :
      eLpNorm (fun ω => (∑ k, α k * L k ω) - X ω (g n)) 2 P ≤
        ∑ k, eLpNorm (fun ω => α k • (L k ω - X ω (f k n))) 2 P := by
    calc
      eLpNorm (fun ω => (∑ k, α k * L k ω) - X ω (g n)) 2 P =
          eLpNorm (fun ω => ∑ k, α k • (L k ω - X ω (f k n))) 2 P := by
            apply eLpNorm_congr_ae
            exact ae_of_all _ fun ω => finite_sum_test_error_eq X α L (fun k => f k n) ω
      _ = eLpNorm (∑ k, fun ω => α k • (L k ω - X ω (f k n))) 2 P := by
          congr 1
          funext ω
          simp
      _ ≤ ∑ k, eLpNorm (fun ω => α k • (L k ω - X ω (f k n))) 2 P := eLpNorm_sum_le
            (p := (2 : ℝ≥0∞)) (μ := P)
            (f := fun k ω => α k • (L k ω - X ω (f k n)))
            (s := Finset.univ) (by norm_num)
  refine ⟨hmem'', g, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hbound)

/-- A finite linear combination of circle averages belongs to the Gaussian `L²` closure of test
evaluations. Approximate each circle average by tests and combine those tests linearly. -/
theorem circleAverage_sum_isGaussianL2Limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (r : ℝ) :
    IsGaussianL2Limit P X (fun ω => ∑ k, α k * Xc ω (z k) r) := by
  classical
  let L  := fun k ω => Xc ω (z k) r
  let f  := fun k => Classical.choose
    (isCircleAverage_isGaussianL2Limit P X hX Xc hXc (z k) r).2
  have hf (k : Fin N) :
      Tendsto (fun n => eLpNorm (fun ω => L k ω - X ω (f k n)) 2 P) atTop (𝓝 0) := Classical.choose_spec
      (isCircleAverage_isGaussianL2Limit P X hX Xc hXc (z k) r).2
  exact gaussianL2Limit_finset_sum P X α L
    (fun k => hXc.2.1 (z k) r) f hf

/-- The averaged Green potential of a fixed insertion circle is bounded on the whole plane. -/
private theorem innerPot_abs_le (y : ℂ) (s : ℝ) (x : ℂ) :
    |innerPot y s x| ≤
      max |Real.log (max (Real.exp (-s))⁻¹ (1 + ‖y‖ / Real.exp (-s)))|
        |Real.log (max (1 + ‖y‖) (Real.exp (-s)))| + |regAvg y s| := by
  let b  := Real.exp (-s)
  let m  := max ‖x - y‖ b
  let q  := normPlus x
  let A  := max b⁻¹ (1 + ‖y‖ / b)
  let D  := max (1 + ‖y‖) b
  have hb : 0 < b := by positivity
  have hm : 0 < m := lt_of_lt_of_le hb (le_max_right _ _)
  have hq  := normPlus_pos x
  have hA : 0 < A := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hD : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hm_b : b ≤ m := le_max_right _ _
  have hm_d : ‖x - y‖ ≤ m := le_max_left _ _
  have hq_le : q ≤ A * m := by
    have h1 : 1 ≤ b⁻¹ * m := by
      field_simp <;> nlinarith
    have hy : ‖y‖ ≤ (‖y‖ / b) * m := by
      calc
        ‖y‖ = (‖y‖ / b) * b := by field_simp
        _ ≤ (‖y‖ / b) * m := mul_le_mul_of_nonneg_left hm_b (div_nonneg (norm_nonneg _) hb.le)
    have hx : ‖x‖ ≤ (1 + ‖y‖ / b) * m := by
      calc
        ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
        _ ≤ m + (‖y‖ / b) * m := add_le_add hm_d hy
        _ = (1 + ‖y‖ / b) * m := by ring
    exact max_le
      (le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hm.le))
      (le_trans hx (mul_le_mul_of_nonneg_right (le_max_right _ _) hm.le))
  have hm_q : m ≤ D * q := by
    have hq1 : 1 ≤ q := le_max_left _ _
    have hd : ‖x - y‖ ≤ (1 + ‖y‖) * q := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        _ ≤ q + ‖y‖ * q := add_le_add (le_max_right _ _)
          (by bound)
        _ = (1 + ‖y‖) * q := by ring
    have hbq : b ≤ b * q := by simp_all
    exact max_le
      (le_trans hd (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le))
      (le_trans hbq (mul_le_mul_of_nonneg_right (le_max_right _ _) hq.le))
  have hupper : Real.log q - Real.log m ≤ Real.log A := by
    have h := Real.log_le_log hq hq_le
    rw [Real.log_mul hA.ne' hm.ne'] at h
    linarith
  have hlower : -Real.log D ≤ Real.log q - Real.log m := by
    have h := Real.log_le_log hm hm_q
    rw [Real.log_mul hD.ne' hq.ne'] at h
    linarith
  have hdiff : |Real.log q - Real.log m| ≤ max |Real.log A| |Real.log D| := by
    grind
  calc
    |innerPot y s x| = |(Real.log q - Real.log m) + regAvg y s| := by
      congr 1
      simp [innerPot, b, m, q]
      ring
    _ ≤ |Real.log q - Real.log m| + |regAvg y s| := abs_add_le _ _
    _ ≤ max |Real.log A| |Real.log D| + |regAvg y s| := add_le_add hdiff le_rfl
    _ = _ := by simp [A, D, b]

private noncomputable def boundedInnerPot (y : ℂ) (s : ℝ) :
    BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨innerPot y s, continuous_innerPot y s⟩
    (2 * (max |Real.log (max (Real.exp (-s))⁻¹ (1 + ‖y‖ / Real.exp (-s)))|
      |Real.log (max (1 + ‖y‖) (Real.exp (-s)))| + |regAvg y s|))
    (by
      intro x x'
      rw [Real.dist_eq]
      calc
        |innerPot y s x - innerPot y s x'| ≤ |innerPot y s x| + |innerPot y s x'| := abs_sub _ _
        _ ≤ 2 * (max |Real.log (max (Real.exp (-s))⁻¹ (1 + ‖y‖ / Real.exp (-s)))|
            |Real.log (max (1 + ‖y‖) (Real.exp (-s)))| + |regAvg y s|) := by
              have hx := innerPot_abs_le y s x
              have hx' := innerPot_abs_le y s x'
              linarith)

/-- Bounded-continuous potential for a finite weighted collection of insertion circles. -/
private noncomputable def circleVertexPotential {N : ℕ} (α : Fin N → ℝ)
    (z : Fin N → ℂ) (r : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  ∑ k, α k • boundedInnerPot (z k) r

private theorem circleVertexPotential_apply {N : ℕ} (α : Fin N → ℝ)
    (z : Fin N → ℂ) (r : ℝ) (x : ℂ) :
    circleVertexPotential α z r x =
      ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r := by
  have hreg (k : Fin N) : regAvg (z k) r =
      ∫ w, Real.log (normPlus w) ∂circleMeasure (z k) r := by
    rw [regAvg, ← DOZZ.Proofs.CirclePotential.integral_circleMeasure_eq_circleAverage
      continuous_log_normPlus.measurable (z k) r]
  simp [circleVertexPotential, boundedInnerPot,
    BoundedContinuousFunction.mkOfBound_coe, integral_gffKernel_circleMeasure,
    smul_eq_mul, innerPot, norm_sub_rev, max_comm, hreg]

/-- Bilinearity of the mixed second moment only needs square integrability. -/
private theorem gaussianCovariance_sum_right {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Y : Ω → ℝ) (Z : ι → Ω → ℝ) (a : ι → ℝ)
    (hY : MemLp Y 2 P) (hZ : ∀ i, MemLp (Z i) 2 P) :
    gaussianCovariance P Y (fun ω => ∑ i, a i * Z i ω) =
      ∑ i, a i * gaussianCovariance P Y (Z i) := by
  classical
  simp only [gaussianCovariance, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (f := fun i ω => Y ω * (a i * Z i ω))
    (fun i _ => hY.integrable_mul ((hZ i).const_mul (a i)))]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_left_comm] using integral_const_mul (a i) (fun ω => Y ω * Z i ω)

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (α : Fin N → ℝ) (z : Fin N → ℂ) (r : ℝ)

include Ω _inst1 N P X hX Xc hXc α z r in
/-- The covariance of a test evaluation with a weighted sum of insertion circles is the matching
weighted sum of the circle/test cross-covariances. -/
theorem circleAverage_sum_test_covariance
     (f : TestFn) :
    gaussianCovariance P (fun ω => X ω f)
      (fun ω => ∑ k, α k * Xc ω (z k) r) =
      ∑ k, α k * circleCross (z k) r f := by
  rw [gaussianCovariance_sum_right P (fun ω => X ω f) (fun k ω => Xc ω (z k) r) α
    (equatorGFF_test_memLp X hX f) (fun k => hXc.2.1 (z k) r)]
  simp_rw [isCircleAverage_cross_covariance P X hX Xc hXc]

include Ω _inst1 N P X hX Xc hXc α z r in
/-- The covariance potential of a finite weighted set of insertion circles converges uniformly
to the averaged Green potential, which is a bounded continuous function. -/
theorem circleAverage_sum_covariance_uniform
     :
    ∃ c : BoundedContinuousFunction ℂ ℝ,
      (∀ x, c x = ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r) ∧
      TendstoUniformly
        (fun (s : ℝ) (x : ℂ) => gaussianCovariance P
          (fun ω => Xc ω x s) (fun ω => ∑ k, α k * Xc ω (z k) r)) c atTop := by
  classical
  let C  := (∑ k, |α k|) * (Real.exp r + 1)
  let c  := circleVertexPotential α z r
  have hc (x : ℂ) : c x = ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r := circleVertexPotential_apply α z r x
  have hcov (s : ℝ) (x : ℂ) :
      gaussianCovariance P (fun ω => Xc ω x s)
        (fun ω => ∑ k, α k * Xc ω (z k) r) =
        ∑ k, α k * circleKernel x s (z k) r := by
    rw [gaussianCovariance_sum_right P (fun ω => Xc ω x s) (fun k ω => Xc ω (z k) r) α
      (hXc.2.1 x s) (fun k => hXc.2.1 (z k) r)]
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun q : ℝ => α k * q)
      (isCircleAverage_covariance P X hX Xc hXc x (z k) s r)
  have hbound (s : ℝ) (x : ℂ) :
      |(∑ k, α k * circleKernel x s (z k) r) - c x| ≤ C * Real.exp (-s) := by
    rw [hc x]
    have hsum :
        (∑ k, α k * circleKernel x s (z k) r) -
            ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r =
          ∑ k, α k * (circleKernel x s (z k) r -
            ∫ v, gffKernel x v ∂circleMeasure (z k) r) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext k
      ring
    rw [hsum]
    calc
      |∑ k, α k * (circleKernel x s (z k) r -
          ∫ v, gffKernel x v ∂circleMeasure (z k) r)| ≤
        ∑ k, |α k * (circleKernel x s (z k) r -
          ∫ v, gffKernel x v ∂circleMeasure (z k) r)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |α k| * ((Real.exp r + 1) * Real.exp (-s)) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (abs_circleKernel_sub_integral_gffKernel_le x (z k) s r) (abs_nonneg _)
      _ = C * Real.exp (-s) := by
            rw [← Finset.sum_mul]
            simp only [C]
            ring
  have hdecay : Tendsto (fun s : ℝ => C * Real.exp (-s)) atTop (𝓝 0) := by
    have hmul  :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (𝓝 C)).mul
        Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using hmul
  refine ⟨c, hc, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hev := hdecay.eventually (Iio_mem_nhds hε)
  filter_upwards [hev] with s hs x
  rw [Real.dist_eq, hcov]
  exact lt_of_le_of_lt (by rw [abs_sub_comm]; exact hbound s x) hs


end DOZZ.Proofs
