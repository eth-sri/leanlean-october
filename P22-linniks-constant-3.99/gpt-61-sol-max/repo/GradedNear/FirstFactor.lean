import GradedNear.SieveError

import GradedNear.Tactics
import GradedNear.Basic

/-!
# (A) The first Cauchy–Schwarz factor: a Mertens-type upper Riemann sum

For `φ` bounded on `[0, X]` and continuous at every point of `(0, X)` outside a finite set,
`𝓛⁻¹ Σ_{1 ≤ n ≤ q^X} Λ(n)/n · φ(log n / 𝓛) ≤ ∫₀^X φ + ε` for all large `q`, where `𝓛 = log q`.
The proof uses Mertens' estimate `Σ_{n ≤ x} Λ(n)/n = log x + O(1)`.

The proof bounds the integrand on the positive ray using compact support, approximates it
by cell suprema on a uniform mesh, and applies dominated convergence away from the finitely
many sieve breakpoints. Mertens' estimate on each cell gives an error of at most `12 M`;
after fixing the mesh, dividing by `log q` makes the total error arbitrarily small.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace FirstFactor

open Filter Topology MeasureTheory Set

/-! ### Mertens' first theorem -/

/-- The Mertens partial sum `Σ_{1 ≤ n ≤ y} Λ(n)/n`. -/
noncomputable def mertensSum (y : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n / n

/-- **Mertens' first theorem**: `|Σ_{n ≤ x} Λ(n)/n - log x| ≤ 6` for `x ≥ 1`. -/
lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |mertensSum x - Real.log x| ≤ 6 := by
  let N := ⌊x⌋₊

  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast  by simp_all [N]
  let S := ∑ n ∈ Finset.Ioc 0 N, Λ n / n
  let A := ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ)
  have h1 := Real.le_sum_log_nat N
  have h2 := Real.sum_log_le' (x := ↑N) (by simp_all)
  rw [Nat.floor_natCast] at h2
  have hlog := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
  simp only [ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.log_apply] at hlog
  rw [hlog] at h1 h2
  have hup : A ≤ N * S := by
    dsimp only [A, S]
    rw [Finset.mul_sum]
    gcongr 1 with n _
    grw [Nat.cast_div_le]
    ring_nf
    rfl
  have hlo : N * S - Chebyshev.psi N ≤ A := by
    simp only [S, A, Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib]
    gcongr 1 with n _
    have h := (Nat.sub_one_lt_floor ((N : ℝ) / n)).le
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
    linear_combination  Λ n  * h
  have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)

  have hfl2 : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlog1 := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hlog2 : Real.log x ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    bound
  have hl2 := Real.log_two_lt_d9
  have hl4 := Real.log_four_eq
  change |S - Real.log x| ≤ 6
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Summation over a partition -/

/-! ### Step-function majorants -/

set_option maxHeartbeats 1000000 in
theorem _root_.GradedNear.first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop,
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n *
          (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))) /
        Real.log q ≤ D.IB + ε := by
  let φ (u : ℝ) := Real.exp (2 * D.s * u) * D.f u ^ 2 / D.omega u
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  have hfc : ContinuousOn D.f (Icc 0 D.xf) := hD.f_cond.cont.mono Icc_subset_Ici_self
  have hcont0 : ContinuousOn (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / c)
      (Icc 0 D.xf) := by fun_prop
  obtain ⟨M, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont0
  have hM := (norm_nonneg _).trans (hMb 0 ⟨le_rfl, hD.f_cond.pos.le⟩)
  have hbd u : 0 ≤ u → |φ u| ≤ M := by
    intro hu
    by_cases hx : u ≤ D.xf
    ·
      refine le_trans ?_ (by simpa only [Real.norm_eq_abs] using hMb u ⟨hu, hx⟩)
      dsimp only [φ]
      by_cases hf : D.f u = 0
      · simp [hf]
      · have hω := hcω u hu hf
        have hωpos := hc.trans_le hω
        gcongr
    · simpa [φ, hD.f_cond.vanish u (by linarith)] using hM
  let cell (h : ℝ) (i : ℕ) := sSup (φ '' Set.Icc (i * h) ((i + 1) * h))
  let stepFn h t := cell h (⌈t / h⌉₊ - 1)
  have le_cell {h : ℝ} (hh : 0 < h) {i : ℕ} {t : ℝ}
      (ht : t ∈ Set.Icc (↑i * h) ((i + 1) * h)) : φ t ≤ cell h i :=
    le_csSup ⟨M, by
      rintro _ ⟨v, hv, rfl⟩
      exact (abs_le.1 (hbd v ((by positivity : 0 ≤ (i : ℝ) * h).trans hv.1))).2⟩ ⟨t, ht, rfl⟩
  have abs_cell_le {h : ℝ} (hh : 0 < h) {i : ℕ} : |cell h i| ≤ M := by
    have hmem : (i : ℝ) * h ∈ Set.Icc ((i : ℝ) * h) ((i + 1) * h) :=
      ⟨le_rfl, by bound⟩
    rw [abs_le]
    constructor
    · exact (abs_le.1 (hbd _ (by positivity))).1.trans (le_cell hh hmem)
    · exact csSup_le ⟨_, _, hmem, rfl⟩ (by
        rintro _ ⟨v, hv, rfl⟩
        exact (abs_le.1 (hbd v ((by positivity : 0 ≤ (i : ℝ) * h).trans hv.1))).2)
  have hint : ∫ u in (0 : ℝ)..D.xf, φ u = D.IB := by
    rw [intervalIntegral.integral_of_le hD.f_cond.pos.le]

    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro v hv

    simp [hD.f_cond.vanish v (by grind)]
  let X := D.xf
  let P := (Finset.range (D.m + 1)).image D.t

  have hcont u : 0 < u → u ∉ P → ContinuousAt φ u := by
    intro hu huP

    have hf := hD.f_cond.cont.continuousAt (Ici_mem_nhds hu)
    have hg := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu)
    have hH : ContinuousAt D.sieveH u := by
      unfold NearData.sieveH
      apply tendsto_finsetSum
      intro k hk
      change ContinuousAt _ u
      convert (continuousOn_const (c := D.h k) (s := interior (Ico (D.t k) (D.t (k + 1))))).continuousAt_indicator
          (x := u) (by grind [frontier_Ico, GradedNear.NearData.Valid.t_lt]) using 1
      ext v
      simp [Set.indicator]
    have hω : ContinuousAt D.omega u := by
      show ContinuousAt (fun v => D.g v * Real.exp (D.s₁ * v) + D.sieveH v) u
      fun_prop
    have hnum : ContinuousAt (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2) u := by fun_prop
    apply (hnum.div (continuousAt_const.max hω) (ne_of_gt (hc.trans_le (le_max_left _ _)))).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hu] with v hv
    by_cases hf : D.f v = 0
    · simp [φ, hf]
    · simp [φ, max_eq_right (hcω v hv.le hf)]
  rw [← hint]
  change ∀ᶠ q : ℕ in Filter.atTop,
    (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊, Λ n / n * φ (Real.log n / Real.log q)) /
      Real.log q ≤ (∫ u in (0 : ℝ)..X, φ u) + ε
  have hintlim : Tendsto (fun K : ℕ => ∫ t in (0 : ℝ)..X, stepFn (X / K) t) atTop
      (𝓝 (∫ u in (0 : ℝ)..X, φ u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence fun _ => M
    · filter_upwards with K
      exact Measurable.aestronglyMeasurable (by unfold stepFn; fun_prop)
    · refine eventually_atTop.2 ⟨1, fun K hK => Filter.Eventually.of_forall fun t ht => ?_ ⟩
      have hK0 : 0 < K := by omega

      have hh := div_pos hD.f_cond.pos (Nat.cast_pos.2 hK0)
      bound
    · simp_all
    · filter_upwards [P.finite_toSet.countable.ae_notMem volume] with t hP htI

      rw [Set.uIoc_of_le hD.f_cond.pos.le] at htI
      have hc := hcont t htI.1 hP
      rw [Metric.tendsto_nhds]
      intro η hη
      obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 hc (η / 2) (by linarith)
      filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat X).eventually (gt_mem_nhds hδ),
        eventually_gt_atTop (0 : ℕ)] with K hhδ hK0
      have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK0
      let h := X / K
      have hh : 0 < h := div_pos hD.f_cond.pos hKR
      set i := ⌈t / h⌉₊ - 1
      obtain ⟨hi1, hi2⟩ : (i : ℝ) * h < t ∧ t ≤ ((i : ℝ) + 1) * h := by
        have ht := div_pos htI.1 hh
        have hm := Nat.ceil_pos.2 ht
        have h1 := Nat.ceil_lt_add_one ht.le
        have h2 := Nat.le_ceil (t / h)
        dsimp only [i]
        simp only [Nat.cast_sub (by omega : 1 ≤ ⌈t / h⌉₊), Nat.cast_one]
        exact ⟨(lt_div_iff₀ hh).1 (by linarith), by simpa using (div_le_iff₀ hh).1 h2⟩
      change dist (cell h i) (φ t) < η
      rw [Real.dist_eq, abs_lt]
      have hlow := le_cell hh ⟨hi1.le, hi2⟩

      have hup : cell h i ≤ φ t + η / 2 := by

        refine csSup_le ⟨φ t, t, ⟨hi1.le, hi2⟩, rfl⟩ ?_
        rintro _ ⟨v, hv, rfl⟩
        have hdist : dist v t < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hv.1, hv.2]
        grind [Real.dist_eq, abs_lt]
      bound
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 hintlim).2 _
      (lt_add_of_pos_right _ (half_pos hε)))
  set K : ℕ := K₁ + 1
  have hK : 0 < K := Nat.succ_pos _
  have hKint := hK₁ K (Nat.le_succ _)

  set h : ℝ := X / K with hhdef
  have hh := div_pos hD.f_cond.pos (Nat.cast_pos.2 hK)
  have hKh : ↑K * h = X := by grind
  filter_upwards [tendsto_log_nat_atTop.eventually
    (eventually_gt_atTop (24 * K * M / ε)), eventually_ge_atTop (2 : ℕ)] with q hbig hq
  have hq1 : 1 < q := by omega
  have hqR : (1 : ℝ) < q := by simp_all
  have hℓ := Real.log_pos hqR
  have hℓbig := (div_lt_iff₀ hε).mp hbig
  let u (i : ℕ) := (q : ℝ) ^ ((i : ℝ) * h)
  -- The endpoints of the multiplicative partition.
  have hpart (j : ℕ) :
      ∑ n ∈ Finset.Ioc 0 ⌊u j⌋₊,
        Λ n / n * φ (Real.log n / Real.log q) ≤
      ∑ i ∈ Finset.range j, cell h i *
        (mertensSum (u (i + 1)) - mertensSum (u i)) := by
    induction j with
    | zero => simp [u]
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hmonoF : ⌊u j⌋₊ ≤ ⌊u (j + 1)⌋₊ := by dsimp [u]; gcongr <;> linarith
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF]
      unfold mertensSum
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF, add_sub_cancel_left,
        Finset.mul_sum]
      apply add_le_add ih
      gcongr 1 with n hn
      rw [Finset.mem_Ioc] at hn
      have hn0 := lt_of_le_of_lt (Nat.zero_le _) hn.1
      have hnR : (0 : ℝ) < n := by positivity


      have hφn : φ (Real.log n / Real.log q) ≤ cell h j := by
        apply le_cell hh
        constructor
        · exact ((Real.lt_logb_iff_rpow_lt hqR hnR).2 ((Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg q) _)).1 hn.1)).le
        · simpa [Real.logb, hhdef] using (Real.logb_le_iff_le_rpow hqR hnR).2 ((Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg q) _)).1 hn.2)
      rw [mul_comm (cell h j)]
      gcongr
  have hpart := hpart K
  simp only [u, hKh, ← Finset.Icc_add_one_left_eq_Ioc, zero_add] at hpart
  -- each cell contributes `c_i h 𝓛 + 12 M`
  have hterm : ∀ i ∈ Finset.range K,
      cell h i * (mertensSum (u (i + 1)) -
        mertensSum (u i)) ≤ cell h i * h * Real.log q + 12 * M := by
    intro i hi
    have hs : |mertensSum (u (i + 1)) -
        mertensSum (u i) - h * Real.log q| ≤ 12 := by
      have h1 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR.le (by positivity : 0 ≤ ((i + 1 : ℕ) : ℝ) * h))
      have h2 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR.le (by positivity : 0 ≤ (i : ℝ) * h))
      rw [Real.log_rpow (by positivity)] at h1 h2
      push_cast at *
      grind
    have hc := abs_cell_le hh (i := i)
    have he := mul_le_mul hc hs (abs_nonneg _) hM
    rw [← abs_mul, abs_le] at he
    bound
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_mul] at hsum
  have hEq (j : ℕ) : stepFn h =ᵐ[volume.restrict (Set.uIoc ((j : ℝ) * h)
      (((j + 1 : ℕ) : ℝ) * h))] fun _ => cell h j := by
    rw [Set.uIoc_of_le (by bound : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h)]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      have hc : ⌈t / h⌉₊ = j + 1 := by
        rwa [Nat.ceil_eq_iff (Nat.succ_ne_zero j), Nat.succ_sub_one,
          lt_div_iff₀ hh, div_le_iff₀ hh]
      simp [stepFn, hc]
  have hint : ∫ t in (0 : ℝ)..X, stepFn h t = ∑ i ∈ Finset.range K, cell h i * h := by
    convert (intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j => (j : ℝ) * h) (n := K)
       fun j _ => (intervalIntegrable_const (c := cell h j)).congr_ae (hEq j).symm ).symm using 1
    · simp [hKh]
    · congr! 1 with j _
      rw [intervalIntegral.integral_congr_ae_restrict (hEq j), intervalIntegral.integral_const]
      push_cast
      ring

  rw [div_le_iff₀ hℓ]

  nlinarith

end FirstFactor

end GradedNear
