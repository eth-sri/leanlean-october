/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/

public section

noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-! ## The Weierstrass factor -/

/-- The Weierstrass elementary factor `E_m`. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]

@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor, Pi.mul_def, Pi.sub_def, Function.comp_def] using
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa [Pi.sub_def] using (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm, Function.comp_def] using
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  change HasDerivAt (fun z => (1-z)*Complex.exp (partialLogSum m z)) _ 1
  simpa [Pi.mul_def] using hsub.mul hexp

@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv

lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcomp

@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv

/-- For `‖z‖ < 1` and `z ≠ 1`, `E_m(z) = exp(-logTail_m(z))`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

/-! ## Power bound -/

/-- For `‖z‖ ≤ 1 / 2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor, Pi.mul_def, Pi.sub_def, Function.comp_def] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/

/-! ## Locally uniform convergence of products of scaled factors -/

private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn

private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))

lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa [Function.comp_def] using (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)

lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring

lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    simpa [Pi.sub_def] using (continuousOn_weierstrassFactor_div (m n) (a n) K).sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)

end Complex
