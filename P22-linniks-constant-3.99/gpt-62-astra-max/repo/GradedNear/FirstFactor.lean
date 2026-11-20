module

public import GradedNear.Basic

/-!
# (A) The first Cauchy–Schwarz factor: a Mertens-type upper Riemann sum

For `φ` bounded on `[0, X]` and continuous at every point of `(0, X)` outside a finite set,
`𝓛⁻¹ Σ_{1 ≤ n ≤ q^X} Λ(n)/n · φ(log n / 𝓛) ≤ ∫₀^X φ + ε` for all large `q`, where `𝓛 = log q`.
The proof uses Mertens' estimate `Σ_{n ≤ x} Λ(n)/n = log x + O(1)`.

## Proof outline

* `FirstFactor.abs_mertensSum_sub_log_le`: `|Σ_{n ≤ x} Λ(n)/n - log x| ≤ 7` for `x ≥ 1`, from
  `log N! = Σ_{n ≤ N} Λ(n) ⌊N/n⌋`, Chebyshev's bound `ψ(N) ≤ (log 4 + 4) N` and
  `N log N - N ≤ log N! ≤ N log N`.
* View the prime sum as the integral of a histogram. The cell for `n` has length
  `Λ(n)/(n log q)` and right endpoint `S(n)/log q`, within `7/log q` of `t_n`.
  Carry the mesh beyond the support of `φ`, giving the extra cells height zero.
  On a fixed interval containing all nonzero cells the sample locations converge
  to the integration variable. Apply dominated convergence.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace FirstFactor

open Filter Topology MeasureTheory

/-! ### Mertens' first theorem -/

/-- The Mertens partial sum `Σ_{1 ≤ n ≤ y} Λ(n)/n`. -/
noncomputable def mertensSum (y : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 y, primeMass n

/-- In the divisor expansion of `log ⌊x⌋!`, replacing `⌊x/n⌋` by `x/n`
costs at most `ψ(x)`. -/
lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) : |mertensSum ⌊x⌋₊ - Real.log x| ≤ 7 := by
  let S := Finset.Ioc 0 ⌊x⌋₊
  have hlog : ∑ n ∈ S, Real.log n = ∑ n ∈ S, Λ n * (⌊x/n⌋₊ : ℝ) := by
    have := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ ⌊x⌋₊
    simp [S, Nat.floor_div_natCast] at *; linarith
  have hprod : ∑ n ∈ S, Λ n * (x/n) = x * mertensSum ⌊x⌋₊ := by
    simp [S, mertensSum, primeMass, Finset.mul_sum, div_eq_mul_inv, mul_left_comm]
  have hlo := Real.le_sum_log' hx
  rw [hlog] at hlo
  have hx0 : 0 < x := by linarith
  grw [Nat.floor_le (by positivity : 0 ≤ x/(_ : ℕ)), hprod] at hlo
  have hhi := Finset.sum_le_sum (s := S) fun n _ => mul_le_mul_of_nonneg_left
    (Nat.lt_floor_add_one (x/n)).le (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  simp [hprod, mul_add, Finset.sum_add_distrib, ← hlog] at hhi
  have hψ := Chebyshev.psi_le_const_mul_self (x := x) hx0.le
  change ∑ n ∈ S, Λ n ≤ _ at hψ
  rw [abs_le]; constructor <;> nlinarith [Real.sum_log_le' hx, Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)]

open Finset Set

/-- Sample `v i` on successive half-open cells of a mesh `s`. -/
noncomputable def histogram (s v : ℕ → ℝ) (N : ℕ) (t : ℝ) :=
  ∑ i ∈ range N, (Set.Ioc (s i) (s (i+1))).indicator (fun _ => v i) t

lemma histogram_value {s v : ℕ → ℝ} (hs : Monotone s) {N i : ℕ} (hv : ∀ j ≥ N, v j = 0)
    {t : ℝ} (ht : t ∈ Set.Ioc (s i) (s (i+1))) : histogram s v N t = v i := by
  rw [histogram, sum_eq_single i, Set.indicator_of_mem ht]
  · exact fun j _ hj => indicator_of_notMem
      (Set.disjoint_left.mp (hs.pairwise_disjoint_on_Ioc_succ hj.symm) ht) _
  · aesop

lemma integrable_sample (a b c : ℝ) : Integrable ((Set.Ioc a b).indicator (fun _ => c)) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (hs := by simp))

lemma integral_histogram {s : ℕ → ℝ} (hs : Monotone s) (v : ℕ → ℝ) (N : ℕ) {U : ℝ}
    (hU : s N ≤ U) : ∫ t in Set.Ioc (s 0) U, histogram s v N t = ∑ i ∈ range N, (s (i+1) - s i) * v i := by
  simp only [histogram, integral_finsetSum _ (fun _ _ => (integrable_sample ..).integrableOn)]
  refine sum_congr rfl fun i hi => ?_
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr
    (Set.Ioc_subset_Ioc (hs (Nat.zero_le i)) ((hs (mem_range.mp hi)).trans hU))]
  simp [Real.volume_real_Ioc_of_le (hs (Nat.le_succ i))]

end FirstFactor

open FirstFactor Filter Topology MeasureTheory Finset

theorem riemann_upper (φ : ℝ → ℝ) (X M : ℝ) (P : Finset ℝ) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 (X+2), |φ u| ≤ M)
    (hz : ∀ u ≥ X, φ u = 0) (hcont : ∀ u, 0 < u → u ∉ P → ContinuousAt φ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      (∑ n ∈ samples q X, primeMass n * φ (tn q n)) /
          Real.log q ≤ (∫ u in Set.Ioi (0 : ℝ), φ u) + ε := by
  let ℓ (q : ℕ) := Real.log q
  let N (q : ℕ) := ⌊(q : ℝ)^X⌋₊
  let s (q i : ℕ) := mertensSum i / ℓ q
  let v q (i : ℕ) := φ (tn q (i+1))
  let F q := histogram (s q) (v q) (N q)
  have err q (hq : 2 ≤ q) x (hx : 1 ≤ x) : |s q ⌊x⌋₊ - Real.log x / ℓ q| ≤ 7 / ℓ q := by
    simpa [s, ← sub_div, abs_div, abs_of_pos (log_q_pos hq), ℓ] using
      div_le_div_of_nonneg_right (abs_mertensSum_sub_log_le x hx) (log_q_pos hq).le
  have rank q (hq : 2 ≤ q) y (hy : 0 ≤ y) : |s q ⌊(q:ℝ)^y⌋₊ - y| ≤ 7/ℓ q := by
    simpa [Real.log_rpow (by positivity : (0:ℝ) < q), ℓ, (log_q_pos hq).ne'] using
      err q hq _ (Real.one_le_rpow (by bound : (1:ℝ) ≤ q) hy)
  have h0 q : s q 0 = 0 := by aesop
  have step q i : s q (i+1) - s q i = primeMass (i+1) / ℓ q := by
    simp [s, mertensSum, ← sub_div, sum_Ioc_succ_top]
  have mono q (hq : 2 ≤ q) := monotone_nat_of_le_succ fun i =>
    sub_nonneg.mp ((step q i).symm ▸ div_nonneg (primeMass_nonneg _) (log_q_pos hq).le)
  let U := X+1
  have mesh := (log_level_atTop.const_div_atTop 7).eventually_le_const zero_lt_one
  have sample q (hq : 2 ≤ q) (hm : 7/ℓ q ≤ 1) t (ht : t ∈ Set.Ioc 0 U) :
      ∃ z, F q t = φ z ∧ |φ z| ≤ M ∧ dist z t ≤ 7/ℓ q := by
    have hs0 : 0 ≤ 7/ℓ q := by positivity [log_q_pos hq]
    let K := ⌊(q:ℝ)^(t+7/ℓ q)⌋₊
    have hK : t ∈ Set.Ioc (s q 0) (s q K) := by
      rw [h0]; exact ⟨ht.1, by dsimp [K]; linarith [(abs_le.mp (rank q hq (t+7/ℓ q) (by linarith [ht.1]))).1]⟩
    rw [← (mono q hq).biUnion_Ico_Ioc_map_succ 0 K] at hK
    obtain ⟨i, hi, hit⟩ : ∃ i < K, t ∈ Set.Ioc (s q i) (s q (i+1)) := by aesop
    have he := histogram_value (v := v q) (mono q hq) (fun i hi => hz _ (tn_ge_of_gt hq (Nat.lt_succ_of_le hi))) hit
    have high : tn q (i+1) ≤ t+7/ℓ q := (Real.logb_le_iff_le_rpow (by exact_mod_cast hq) (by positivity)).mpr
      ((Nat.le_floor_iff (by positivity)).mp hi)
    refine ⟨_, he, hbd _ ⟨tn_nonneg _ _ hq, by linarith [ht.2]⟩, ?_⟩
    have low := err q hq (i+1 : ℕ) (by exact_mod_cast Nat.succ_pos i)
    rw [Nat.floor_natCast] at low; rw [Real.dist_eq, abs_le]
    change -_ ≤ Real.log _/ℓ q - t ∧ _
    constructor <;> linarith [hit.2, (abs_le.mp low).2]
  have hint : Tendsto (fun q => ∫ t in Set.Ioc 0 U, F q t) atTop (𝓝 (∫ t in Set.Ioc 0 U, φ t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact Eventually.of_forall fun q => (integrable_finsetSum _ fun _ _ => (integrable_sample ..).integrableOn).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 2, mesh] with q hq hm
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      obtain ⟨_, he, hh, _⟩ := sample q hq hm t ht; rwa [he]
    · exact integrableOn_const (hs := by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (P.finite_toSet.measure_zero volume))] with t hI ht
      apply Metric.tendsto_nhds.mpr; intro ε hε
      obtain ⟨δ, hδ, hφ⟩ := Metric.continuousAt_iff.mp (hcont _ hI.1 ht) ε hε
      filter_upwards [eventually_ge_atTop 2, mesh, (log_level_atTop.const_div_atTop 7).eventually_lt_const hδ] with q hq hm hsmall
      obtain ⟨z, he, _, hh⟩ := sample q hq hm t hI
      simpa [he] using hφ (hh.trans_lt hsmall)
  rw [truncate_Ioi (fun t (ht : U ≤ t) => hz t (by bound))]
  filter_upwards [eventually_ge_atTop 2, mesh,
    hint.eventually_le_const (lt_add_of_pos_right _ hε)] with q hq hsmall h
  apply le_trans (le_of_eq ?_) h
  have hi := integral_histogram (mono q hq) (v q) (N q) (by bound [(abs_le.mp (rank q hq X hX.le)).2] : _ ≤ U)
  rw [h0] at hi; rw [hi, sum_div]
  simp_rw [step, div_mul_eq_mul_div, v, ℓ]
  simp [samples, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, N, add_comm]

end GradedNear
