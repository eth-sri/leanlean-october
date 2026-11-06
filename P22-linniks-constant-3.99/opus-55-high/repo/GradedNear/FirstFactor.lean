module

public import Mathlib

/-!
# (A) The first Cauchy–Schwarz factor: a Mertens-type upper Riemann sum

For `φ` bounded on `[0, X]` and continuous at every point of `(0, X)` outside a finite set,
`𝓛⁻¹ Σ_{1 ≤ n ≤ q^X} Λ(n)/n · φ(log n / 𝓛) ≤ ∫₀^X φ + ε` for all large `q`, where `𝓛 = log q`.
The proof uses Mertens' estimate `Σ_{n ≤ x} Λ(n)/n = log x + O(1)` on each cell of a uniform
mesh, and dominated convergence for the upper step functions of `φ`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace FirstFactor

open Filter Topology MeasureTheory

/-- The Mertens partial sum `Σ_{1 ≤ n ≤ y} Λ(n)/n`. -/
noncomputable def mertensSum (y : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n / n

/-- **Mertens' first theorem**: `|Σ_{n ≤ x} Λ(n)/n - log x| ≤ 7` for `x ≥ 1`. -/
lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) : |mertensSum x - Real.log x| ≤ 7 := by
  set N := ⌊x⌋₊
  have hN : (1 : ℝ) ≤ N := mod_cast Nat.le_floor (by grind)
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
  simp at h
  have h2 := Real.sum_log_le' hN
  have h3 := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at h2
  rw [Chebyshev.psi, Nat.floor_natCast] at h3
  have h4 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) ≤ N * mertensSum x := by
    rw [mertensSum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [mul_div_left_comm]
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
  have h5 : N * mertensSum x - ∑ n ∈ Finset.Ioc 0 N, Λ n ≤
      ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
    rw [mertensSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := Nat.sub_one_lt_floor ((N : ℝ) / n)
    rw [Nat.floor_div_natCast, Nat.floor_natCast] at this
    rw [mul_div_left_comm, ← mul_sub_one]
    exact mul_le_mul_of_nonneg_left this.le ArithmeticFunction.vonMangoldt_nonneg
  have h6 : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h7 : Real.log x ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul two_ne_zero (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith [Nat.lt_floor_add_one x])
  have h8 := Real.log_le_sub_one_of_pos (zero_lt_two (α := ℝ))
  have h9 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlo : Real.log N - 1 ≤ mertensSum x :=
    le_of_mul_le_mul_left (by linarith [Real.le_sum_log_nat N]) (by linarith : (0 : ℝ) < N)
  have hup : mertensSum x ≤ Real.log N + 7 :=
    le_of_mul_le_mul_left (by nlinarith) (by linarith : (0 : ℝ) < N)
  grind

/-- One cell of the partition: if `φ ≤ c` on `(y, z]`, the weighted sum over `q^y < n ≤ q^z` is
at most `c (z - y) log q + 14 M` for `|c| ≤ M`. -/
lemma block (φ : ℝ → ℝ) {q : ℕ} (hq : 1 < (q : ℝ)) {y z c M : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    (hc : |c| ≤ M) (hφ : ∀ t, y < t → t ≤ z → φ t ≤ c) :
    ∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ z⌋₊, Λ n / n * φ (Real.log n / Real.log q) -
      ∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ y⌋₊, Λ n / n * φ (Real.log n / Real.log q) ≤
      (z - y) * c * Real.log q + 14 * M := by
  have hmono : ⌊(q : ℝ) ^ y⌋₊ ≤ ⌊(q : ℝ) ^ z⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hq.le hyz)
  have h1 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hq.le hy)
  have h2 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hq.le (hy.trans hyz))
  rw [Real.log_rpow (by linarith)] at h1 h2
  rw [abs_le] at hc h1 h2
  refine le_trans (b := c * (mertensSum ((q : ℝ) ^ z) - mertensSum ((q : ℝ) ^ y))) ?_ (by nlinarith)
  rw [mertensSum, mertensSum, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmono,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmono, add_sub_cancel_left,
    add_sub_cancel_left, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Ioc, Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity)] at hn
  have hn0 : (0 : ℝ) < n := (Real.rpow_pos_of_pos (by linarith) y).trans hn.1
  rw [mul_comm c, Real.log_div_log]
  exact mul_le_mul_of_nonneg_left (hφ _ ((Real.lt_logb_iff_rpow_lt hq hn0).2 hn.1)
    ((Real.logb_le_iff_le_rpow hq hn0).2 hn.2)) (by positivity)

/-- The upper step function of `φ` on the cells `(i h, (i + 1) h]`, restricted to `[0, X]`. -/
noncomputable def stepFn (φ : ℝ → ℝ) (X h t : ℝ) : ℝ :=
  sSup (φ '' {v ∈ Set.Icc 0 X | ⌈v / h⌉₊ = ⌈t / h⌉₊})

lemma measurable_stepFn (φ : ℝ → ℝ) (X h : ℝ) : Measurable (stepFn φ X h) :=
  measurable_from_nat (f := fun m => sSup (φ '' {v ∈ Set.Icc 0 X | ⌈v / h⌉₊ = m})) |>.comp
    (measurable_id.div_const h).nat_ceil

variable {φ : ℝ → ℝ} {X M h t : ℝ}

lemma le_stepFn (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M) {v : ℝ} (hv : v ∈ Set.Icc 0 X)
    (hvt : ⌈v / h⌉₊ = ⌈t / h⌉₊) : φ v ≤ stepFn φ X h t :=
  le_csSup ⟨M, by rintro _ ⟨u, hu, rfl⟩; exact (abs_le.1 (hbd u hu.1)).2⟩ ⟨v, ⟨hv, hvt⟩, rfl⟩

lemma stepFn_le {B : ℝ} (ht : t ∈ Set.Icc 0 X)
    (hB : ∀ u ∈ Set.Icc 0 X, ⌈u / h⌉₊ = ⌈t / h⌉₊ → φ u ≤ B) : stepFn φ X h t ≤ B :=
  csSup_le ⟨_, t, ⟨ht, rfl⟩, rfl⟩ (by rintro _ ⟨u, hu, rfl⟩; exact hB u hu.1 hu.2)

lemma abs_stepFn_le (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M) (ht : t ∈ Set.Icc 0 X) :
    |stepFn φ X h t| ≤ M :=
  abs_le.2 ⟨(abs_le.1 (hbd t ht)).1.trans (le_stepFn hbd ht rfl),
    stepFn_le ht fun u hu _ => (abs_le.1 (hbd u hu)).2⟩

lemma stepFn_cell (hh : 0 < h) {i : ℕ} (ht : t ∈ Set.Ioc (i * h) ((i + 1 : ℕ) * h)) :
    stepFn φ X h t = stepFn φ X h ((i + 1 : ℕ) * h) := by
  have key : ∀ s ∈ Set.Ioc (i * h) ((i + 1 : ℕ) * h), ⌈s / h⌉₊ = i + 1 := fun s hs => by
    rw [Nat.ceil_eq_iff (by omega), lt_div_iff₀ hh, div_le_iff₀ hh]
    grind
  grind [stepFn]

end FirstFactor

open Filter Topology MeasureTheory FirstFactor in
theorem riemann_upper (φ : ℝ → ℝ) (X M : ℝ) (P : Finset ℝ) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    (hcont : ∀ u ∈ Set.Ioo 0 X, u ∉ P → ContinuousAt φ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊, Λ n / n * φ (Real.log n / Real.log q)) /
          Real.log q ≤ (∫ u in (0 : ℝ)..X, φ u) + ε := by
  have hT : Tendsto (fun K : ℕ => ∫ t in (0 : ℝ)..X, stepFn φ X (X / K) t) atTop
      (𝓝 (∫ u in (0 : ℝ)..X, φ u)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (.of_forall fun K => (measurable_stepFn φ X _).aestronglyMeasurable)
      (.of_forall fun K => .of_forall fun t ht => ?_) intervalIntegrable_const ?_
    · rw [Set.uIoc_of_le hX.le] at ht
      exact abs_stepFn_le hbd (Set.Ioc_subset_Icc_self ht)
    filter_upwards [((P : Set ℝ).toFinite.insert X).countable.ae_notMem _] with t htP ht
    rw [Set.uIoc_of_le hX.le] at ht
    simp at htP
    have htI : t ∈ Set.Icc 0 X := Set.Ioc_subset_Icc_self ht
    refine tendsto_order.2 ⟨fun a ha => .of_forall fun K => ha.trans_le (le_stepFn hbd htI rfl),
      fun a ha => ?_⟩
    obtain ⟨b, hb, hba⟩ := exists_between ha
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1
      ((hcont t ⟨ht.1, lt_of_le_of_ne ht.2 htP.1⟩ htP.2).eventually (gt_mem_nhds hb))
    filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat X).eventually (gt_mem_nhds hδ),
      eventually_gt_atTop 0] with K hK hK0
    have hh : 0 < X / K := by positivity
    refine (stepFn_le htI fun u hu hut => (hδb ?_).le).trans_lt hba
    have h1 := hut ▸ Nat.le_ceil (u / (X / K))
    have h2 := hut ▸ Nat.ceil_lt_add_one (div_nonneg hu.1 hh.le)
    have h3 := Nat.le_ceil (t / (X / K))
    have h4 := Nat.ceil_lt_add_one (div_nonneg htI.1 hh.le)
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [div_mul_cancel₀ u hh.ne', div_mul_cancel₀ t hh.ne']
  obtain ⟨K, hK, hK0⟩ := (((tendsto_order.1 hT).2 _ (lt_add_of_pos_right _ (half_pos hε))).and
    (eventually_gt_atTop 0)).exists
  have hh : 0 < X / K := by positivity
  have hKh : (K : ℝ) * (X / K) = X := by field_simp
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.1 ((tendsto_natCast_atTop_atTop.eventually
    (Real.tendsto_log_atTop.eventually_gt_atTop (28 * K * M / ε))).and (eventually_ge_atTop 2))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨hlog, hq2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) < q := mod_cast hq2
  have hℓ := Real.log_pos hq1
  have hiK : ∀ i < K, ((i + 1 : ℕ) : ℝ) * (X / K) ≤ X := fun i hi =>
    (mul_le_mul_of_nonneg_right (mod_cast hi) hh.le).trans_eq hKh
  have hpiece : ∀ i < K, Set.EqOn (stepFn φ X (X / K))
      (fun _ => stepFn φ X (X / K) ((i + 1 : ℕ) * (X / K))) (Set.uIoc (i * (X / K))
        ((i + 1 : ℕ) * (X / K))) := fun i _ t ht => by
    rw [Set.uIoc_of_le (by grind)] at ht
    exact stepFn_cell hh ht
  have hint := intervalIntegral.sum_integral_adjacent_intervals (a := fun i : ℕ => i * (X / K))
    (μ := volume) fun i hi => (intervalIntegrable_congr (hpiece i hi)).2 intervalIntegrable_const
  rw [Finset.sum_congr rfl fun i hi =>
    intervalIntegral.integral_congr_ae (.of_forall (hpiece i (Finset.mem_range.1 hi)))] at hint
  simp [hKh] at hint
  have key := Finset.sum_le_sum fun i (hi : i ∈ Finset.range K) => block φ hq1
    (y := i * (X / K)) (z := ((i + 1 : ℕ) : ℝ) * (X / K)) (by positivity) (by grind)
    (abs_stepFn_le hbd ⟨by positivity, hiK i (Finset.mem_range.1 hi)⟩) fun t ht1 ht2 =>
      stepFn_cell hh ⟨ht1, ht2⟩ ▸ le_stepFn hbd ⟨(by positivity : (0 : ℝ) ≤ i * (X / K)).trans
        ht1.le, ht2.trans (hiK i (Finset.mem_range.1 hi))⟩ rfl
  rw [Finset.sum_range_sub (fun i : ℕ => ∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ ((i : ℝ) * (X / K))⌋₊,
    Λ n / n * φ (Real.log n / Real.log q))] at key
  norm_num [hKh, Finset.sum_add_distrib, ← Finset.sum_mul] at key
  rw [div_le_iff₀ hℓ, show Finset.Icc 1 _ = Finset.Ioc 0 _ from Finset.Icc_add_one_left_eq_Ioc 0 _]
  nlinarith [(div_lt_iff₀ hε).1 hlog]
