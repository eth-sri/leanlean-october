module

public import GradedNear.Basic

/-!
# The first Cauchy–Schwarz factor

Use each normalized Mangoldt mass as the length of a cell of a step function.
Mertens' estimate places that cell close to its sample point `log n / log q`.
Dominated convergence then gives the limit of the weighted sums.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace FirstFactor

open Filter Topology MeasureTheory Finset

/-! ### Mertens' first theorem -/

/-- The Mertens partial sum `Σ_{1 ≤ n ≤ y} Λ(n)/n`. -/
noncomputable def mertensSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, Λ n / n

/-- Mertens' first theorem, by summing `Λ * ζ = log` and bounding the floor error. -/
lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |mertensSum ⌊x⌋₊ - Real.log x| ≤ 7 := by
  let A := ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n
  have hA : A = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (⌊x / n⌋₊ : ℝ) := by
    simpa [A, Nat.floor_div_natCast, ArithmeticFunction.vonMangoldt_mul_zeta,
      ArithmeticFunction.log_apply] using (ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ ⌊x⌋₊)
  have hψ : x * mertensSum ⌊x⌋₊ - A ∈ Set.Icc 0 (Chebyshev.psi x) := by
    rw [mertensSum, hA, mul_sum, ← sum_sub_distrib, Chebyshev.psi]
    simp_rw [mul_comm x, div_mul_eq_mul_div, mul_div_assoc, ← mul_sub]
    refine ⟨sum_nonneg fun n _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (sub_nonneg.mpr (Nat.floor_le (by positivity))), sum_le_sum fun n _ => ?_⟩
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (by linarith [Nat.lt_floor_add_one (x / n)])
  rw [abs_sub_le_iff]
  constructor <;> apply le_of_mul_le_mul_left _ (show 0 < x by linarith) <;>
    nlinarith [hψ.1, hψ.2, Real.le_sum_log' hx, Real.sum_log_le' hx, Chebyshev.psi_le_const_mul_self (x := x) (by positivity),
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4), (by positivity : 0 ≤ x)]

private lemma mertens_succ (n : ℕ) : mertensSum (n + 1) - mertensSum n =
    Λ (n + 1) / (↑(n + 1 : ℕ) : ℝ) := by
  simp only [mertensSum, sum_Ioc_succ_top (Nat.zero_le _), add_sub_cancel_left]

open Set in
private noncomputable def steps (u c : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ range N, (Ioc (u i) (u (i + 1))).indicator (fun _ => c i) t

open Set in
private lemma steps_at {u c : ℕ → ℝ} (hu : Monotone u) {N : ℕ} {t : ℝ}
    (ht : t ∈ Ioc (u 0) (u N)) : ∃ i ∈ range N, t ∈ Ioc (u i) (u (i + 1)) ∧ steps u c N t = c i := by
  obtain ⟨i, hi, ht⟩ : ∃ i ∈ range N, t ∈ Ioc (u i) (u (i + 1)) := by
    simpa only [Set.mem_iUnion, exists_prop] using Ioc_subset_biUnion_Ioc N u ht
  refine ⟨i, hi, ht, ?_⟩
  rw [steps, sum_eq_single_of_mem i hi, indicator_of_mem ht]
  intro j _ hji
  apply indicator_of_notMem
  exact fun hj => Set.disjoint_left.mp (hu.pairwise_disjoint_on_Ioc_succ hji) hj ht

lemma sum_mertens_tendsto (φ : ℝ → ℝ) {X M : ℝ} {P : Set ℝ} (hP : P.Countable) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    (hcont : ∀ u ∈ Set.Ioo 0 X, u ∉ P → ContinuousAt φ u) :
    Tendsto (fun q : ℕ => (∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ X⌋₊,
      Λ n / n * φ (Real.log n / Real.log q)) / Real.log q) atTop
      (𝓝 (∫ u in (0 : ℝ)..X, φ u)) := by
  let L (q : ℕ) := Real.log q
  let N (q : ℕ) := ⌊(q : ℝ) ^ X⌋₊
  let u := mertensSum
  let r q := u (N q) / X
  let x (q i : ℕ) := Real.log (↑(i + 1 : ℕ)) / L q
  let G q (t : ℝ) := steps u (fun i => φ (x q i)) (N q) (t * r q)
  have hu : Monotone u := monotone_nat_of_le_succ fun i => by
    rw [← sub_nonneg, mertens_succ]; positivity
  have h0 : u 0 = 0 := by simp [u, mertensSum]
  have hx q i (hq : 1 < q) (hi : i ∈ range (N q)) : x q i ∈ Set.Icc 0 X := by
    refine ⟨tn_nonneg q _, (div_le_iff₀ (log_q_pos hq)).2 ?_⟩
    rw [← Real.log_rpow (by positivity : (0 : ℝ) < q)]
    exact Real.log_le_log (by positivity) ((Nat.le_floor_iff (by positivity)).1 (mem_range.mp hi))
  have hXr q : X * r q = u (N q) := mul_div_cancel₀ _ hX.ne'
  have hmass q (hq : 1 < q) : X * |r q - L q| ≤ 7 := by
    rw [← abs_of_pos hX, ← abs_mul, mul_sub, hXr]
    simpa only [N, L, Real.log_rpow (by positivity : (0 : ℝ) < q)] using
      abs_mertensSum_sub_log_le _ (Real.one_le_rpow (Nat.one_le_cast.mpr hq.le) hX.le)
  have hr : Tendsto (fun q => r q / L q) atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (tendsto_div_log_nat (7 / X))
    filter_upwards [eventually_gt_atTop 1] with q hq
    have hℓ := log_q_pos hq
    rw [Real.norm_eq_abs, div_sub' hℓ.ne', mul_one, abs_div, abs_of_pos hℓ]
    gcongr
    apply (le_div_iff₀ hX).mpr
    simpa [mul_comm] using hmass q hq
  have hR : ∀ᶠ q in atTop, 1 < q ∧ 0 < r q := by
    filter_upwards [eventually_gt_atTop 1, hr.eventually_const_lt zero_lt_one] with q hq hrq
    exact ⟨hq, (div_pos_iff_of_pos_right (log_q_pos hq)).mp hrq⟩
  have hclose q i (hq : 1 < q) {t : ℝ} (ht : t ∈ Set.Ioc 0 X)
      (hi : t * r q ∈ Set.Ioc (u i) (u (i + 1))) : dist (x q i) t ≤ 15 / L q := by
    have hb := abs_mertensSum_sub_log_le (i + 1 : ℕ) (by exact_mod_cast Nat.succ_pos i)
    rw [Nat.floor_natCast] at hb
    have hw : u (i + 1) - u i ≤ 1 := by
      rw [mertens_succ, div_le_one (by positivity)]
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self (by positivity))
    have he : |t * r q - t * L q| ≤ 7 := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ht.1.le]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans (hmass q hq)
    change |u (i + 1) - _| ≤ 7 at hb
    dsimp only [x]
    rw [Real.dist_eq, div_sub' (log_q_pos hq).ne', abs_div,
      abs_of_pos (log_q_pos hq), div_le_div_iff_of_pos_right (log_q_pos hq), abs_le]
    grind [abs_le]
  have happ : ∀ᶠ q in atTop, ∀ t ∈ Set.Ioc 0 X, ∃ v ∈ Set.Icc 0 X,
      G q t = φ v ∧ dist v t ≤ 15 / L q := by
    filter_upwards [hR] with q ⟨hq, hrq⟩ t ht
    obtain ⟨i, hi, hc, hF⟩ := steps_at (c := fun i => φ (x q i)) (N := N q) hu
      ⟨h0 ▸ mul_pos ht.1 hrq, hXr q ▸ mul_le_mul_of_nonneg_right ht.2 hrq.le⟩
    grind
  have hlim : Tendsto (fun q => ∫ t in (0 : ℝ)..X, G q t) atTop (𝓝 (∫ t in (0 : ℝ)..X, φ t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact Eventually.of_forall fun q => ((Finset.measurable_fun_sum _ fun i _ =>
        measurable_const.indicator measurableSet_Ioc).comp (by fun_prop)).aestronglyMeasurable
    · rw [Set.uIoc_of_le hX.le]
      filter_upwards [happ] with q hq
      exact .of_forall fun t ht => by grind [Real.norm_eq_abs]
    · exact intervalIntegrable_const
    · have hnull := measure_eq_zero_iff_ae_notMem.mp (hP.measure_zero volume)
      filter_upwards [hnull, (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := X)).symm] with t hp ht htI
      rw [Set.uIoc_of_le hX.le] at htI
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hc⟩ := Metric.continuousAt_iff.mp (hcont _ (ht.mp htI) hp) ε hε
      filter_upwards [happ, (tendsto_div_log_nat 15).eventually_lt_const hδ] with q hq hqδ
      grind
  have H := hr.mul hlim
  rw [one_mul] at H
  refine H.congr' ?_
  filter_upwards [hR] with q ⟨hq, hrq⟩
  dsimp only [G]
  rw [div_mul_eq_mul_div, ← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_right, zero_mul, hXr]
  dsimp only [steps]
  rw [intervalIntegral.integral_of_le (h0 ▸ hu (Nat.zero_le (N q))), integral_finsetSum, sum_Ioc_eq_range]
  · simp only [Nat.sub_zero, zero_add]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc
      (by rw [← h0]; exact hu (Nat.zero_le _)) (hu (mem_range.mp hi))),
      setIntegral_const, Real.volume_real_Ioc_of_le (hu (Nat.le_succ _)),
      smul_eq_mul, mertens_succ]
    simp [x, L, Nat.add_comm 1]
  · exact fun i _ => (integrableOn_const (by simp [Real.volume_Ioc])).indicator measurableSet_Ioc

/-! ### The tested first factor -/

open NearData

/-- The integrand `φ(u) = e^{2su} f(u)² / ω(u)` of `I_B`. -/
noncomputable def phi (D : NearData) (u : ℝ) : ℝ := Real.exp (2 * D.s * u) * D.f u ^ 2 / D.omega u

theorem first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      (∑ n ∈ Ioc 0 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n * phi D (tn q n)) /
          Real.log q ≤ D.IB + ε := by
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  let p (u : ℝ) := Real.exp (2 * D.s * u) * D.f u ^ 2
  have hp : ContinuousOn p (Set.Ici 0) := by
    have hf := hD.f_cond.cont
    unfold p; fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hp.div_const c).mono Set.Icc_subset_Ici_self)
  have hclamped {u : ℝ} (hu : 0 ≤ u) : phi D u = p u / max c (D.omega u) := by
    grind [phi]
  have hbd u (hu : u ∈ Set.Icc 0 D.xf) : |phi D u| ≤ M := by
    rw [hclamped hu.1, abs_of_nonneg (by positivity)]
    exact (div_le_div_of_nonneg_left (by positivity) hc (le_max_left _ _)).trans
      (by simpa [Real.norm_of_nonneg (show 0 ≤ p u / c by positivity)] using hM u hu)
  have hcont u (hu : u ∈ Set.Ioo 0 D.xf) (huP : u ∉ Set.range D.t) : ContinuousAt (phi D) u := by
    have hne k : u ≠ D.t k := by grind
    have hH : ContinuousAt D.sieveH u := by
      unfold NearData.sieveH
      refine tendsto_finsetSum _ fun k hk => ?_
      have hk' := mem_range.mp hk
      have h : u ∉ frontier (Set.Ico (D.t k) (D.t (k + 1))) := by
        simp [frontier_Ico (hD.t_lt k hk'), hne]
      exact ((continuousOn_const (c := D.h k)).continuousAt_indicator h).congr
        (.of_forall fun v => by simp [Set.indicator])
    have hg := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu.1)
    have hω : ContinuousAt D.omega u := by unfold NearData.omega; fun_prop
    refine ((hp.continuousAt (Ici_mem_nhds hu.1)).div (continuousAt_const.max hω)
      (ne_of_gt (hc.trans_le (le_max_left _ _)))).congr ?_
    filter_upwards [Ioi_mem_nhds hu.1] with v hv
    exact (hclamped hv.le).symm
  have H := sum_mertens_tendsto (phi D) (Set.countable_range _) hD.f_cond.pos hbd hcont
  rw [integral_support_interval hD.f_cond.pos.le
    (fun u hu => by simp [phi, hD.f_cond.vanish u hu])] at H
  change Tendsto _ _ (𝓝 D.IB) at H
  exact H.eventually_le_const (lt_add_of_pos_right _ hε)
end FirstFactor

end GradedNear
