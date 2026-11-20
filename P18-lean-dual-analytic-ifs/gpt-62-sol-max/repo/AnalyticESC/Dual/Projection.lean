module

public import AnalyticESC.Basic
public import AnalyticESC.Words

@[expose] public section

/-!
# The dual natural projection

Convergence and holomorphy of the series (1.4) defining `H_w`, its uniform bounds, the cocycle
identity for prepended words, the formula (2.7) `H_{v^←} = f_v''/f_v'` for finite words, and
Lemma 2.5, analyticity and Hölder continuity: `H_w ∈ C^ω_ε([0,1])` and Hölder dependence on the word.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## The terms of the series -/

theorem norm_dualTerm_le {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (w : Word N) (n : ℕ) (z : ℂ)
    (hd : ∀ v, ‖deriv (Φ.comp v) z‖ ≤ c ^ v.length)
    (hn : ∀ i v, ‖Φ.nonlin i (Φ.comp v z)‖ ≤ C) : ‖Φ.dualTerm w n z‖ ≤ C * c ^ n := by
  cases h : w.get? n with
  | none => simp_all [dualTerm, mul_nonneg, pow_nonneg]
  | some i =>
    grind [dualTerm, norm_mul, Word.length_take_of_get?_eq_some, mul_le_mul, norm_nonneg]

/-- The terms are uniformly dominated by a summable sequence on `cl B_ε`. -/
private theorem exists_dualTerm_bound : ∃ B : ℕ → ℝ, Summable B ∧ (∀ n, 0 ≤ B n) ∧
    ∀ w n z, z ∈ closedNbhd ε → ‖Φ.dualTerm w n z‖ ≤ B n := by
  obtain ⟨C, hC₀, hC⟩ := Φ.exists_nonlin_bound
  exact ⟨fun n => C * Φ.cmax ^ n,
    (summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C,
    fun n => mul_nonneg hC₀ (pow_nonneg Φ.cmax_nonneg n),
    fun w n z hz => Φ.norm_dualTerm_le Φ.cmax_nonneg hC₀ w n z
      (fun v => (Φ.norm_deriv_comp_bounds v hz).2) (fun i v => hC i _ (Φ.mapsTo_comp_closure v hz))⟩

theorem summable_dualTerm (w : Word N) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨B, hs, -, hB⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded hs fun n => hB w n z hz

@[simp] theorem dualProj_nil : Φ.dualProj (.fin []) = 0 := by
  funext z
  simp [dualProj, dualTerm]

/-- For a finite word, `H_a` is the finite sum of its `|a|` terms. -/
theorem dualProj_fin_eq_sum (a : List (Fin N)) (z : ℂ) :
    Φ.dualProj (.fin a) z = ∑ n ∈ Finset.range a.length, Φ.dualTerm (.fin a) n z := by
  refine tsum_eq_sum fun n hn => ?_
  simp_all [dualTerm]

theorem dualProj_singleton (i : Fin N) (z : ℂ) : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  simp [dualProj_fin_eq_sum, dualTerm]

/-! ## Bounds -/

/-- The uniform bound `‖H_w‖ ≤ M` on `cl B_ε`. -/
theorem exists_norm_dualProj_le :
    ∃ M, 0 ≤ M ∧ ∀ w : Word N, ∀ z ∈ closedNbhd ε, ‖Φ.dualProj w z‖ ≤ M := by
  obtain ⟨B, hs, h₀, hB⟩ := Φ.exists_dualTerm_bound
  exact ⟨∑' n, B n, tsum_nonneg h₀, fun w z hz =>
    tsum_of_norm_bounded hs.hasSum fun n => hB w n z hz⟩

/-! ## Holomorphy -/

theorem differentiableOn_dualTerm (w : Word N) (n : ℕ) :
    DifferentiableOn ℂ (Φ.dualTerm w n) (nbhd ε) := by
  intro z hz
  unfold dualTerm
  split
  · fun_prop
  · rename_i i _
    have h := Φ.analyticAt_comp (w.take n).reverse (subset_closure hz)
    exact (((Φ.analyticAt_nonlin i (Φ.mapsTo_comp_closure _ (subset_closure hz))).comp h).mul
      h.deriv).differentiableAt.differentiableWithinAt

theorem differentiableOn_dualProj (w : Word N) : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨B, hs, -, hB⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm hs
    (fun n => Φ.differentiableOn_dualTerm w n) (isOpen_nbhd ε)
    fun n z hz => hB w n z (subset_closure hz)

/-! ## The cocycle identity and (2.7) -/

/-- Split the dual cocycle at a prefix of length `n`. -/
theorem dualProj_split (w : Word N) (n : ℕ) (hn : (w.take n).length = n) {z : ℂ}
    (hz : z ∈ closedNbhd ε) : Φ.dualProj w z =
      Φ.dualProj (.fin (w.take n)) z + deriv (Φ.comp (w.take n).reverse) z *
        Φ.dualProj (w.drop n) (Φ.comp (w.take n).reverse z) := by
  rw [dualProj_fin_eq_sum, hn]
  unfold dualProj
  rw [← (Φ.summable_dualTerm w hz).sum_add_tsum_nat_add n, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have h := Finset.mem_range.1 hk
    have htake : (w.take n).take k = w.take k :=
      List.ext_getElem? fun j => by simp only [List.getElem?_take, Word.getElem?_take_word]; grind
    simp only [dualTerm, Word.get?_fin, Word.getElem?_take_word, ite_eq_left h, Word.take_fin, htake]
  · refine tsum_congr fun k => ?_
    simp only [Nat.add_comm k n, dualTerm, Word.get?_drop, Word.take_add_drop]
    split
    · simp
    · rw [List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

theorem dualTerm_inf_succ (w : ℕ → Fin N) (n : ℕ) {z : ℂ}
    (hz : z ∈ closedNbhd ε) : Φ.dualTerm (.inf w) (n + 1) z =
    deriv (Φ.f (w 0)) z * Φ.dualTerm (.inf (Word.shift w 1)) n (Φ.f (w 0) z) := by
  simp only [IFS.dualTerm, Word.get?_inf, Word.take_inf, List.ofFn_succ, List.reverse_cons, Fin.val_succ]
  rw [Φ.deriv_comp_append _ _ hz, Φ.comp_append]
  simp; ring

/-- The cocycle identity for the first letter of an infinite word. -/
theorem dualProj_inf_head (w : ℕ → Fin N) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    Φ.dualProj (.inf w) z = Φ.nonlin (w 0) z + deriv (Φ.f (w 0)) z *
      Φ.dualProj (.inf fun k => w (k + 1)) (Φ.f (w 0) z) := by
  simpa [Word.drop, dualProj_singleton] using Φ.dualProj_split (.inf w) 1 (by simp) hz

/-- (2.7): `H_{v^←} = f_v''/f_v'` for a finite word `v`. -/
theorem dualProj_fin_reverse (v : List (Fin N)) {z : ℂ} (hz : z ∈ closedNbhd ε) :
    Φ.dualProj (.fin v.reverse) z = deriv (deriv (Φ.comp v)) z / deriv (Φ.comp v) z := by
  induction v with
  | nil => simp
  | cons i v ih =>
    rw [Φ.dualProj_split (.fin (i :: v).reverse) v.reverse.length (by simp) hz]
    simp only [List.reverse_cons, Word.take_fin, Word.drop, List.take_left, List.drop_left,
      ih, List.reverse_reverse, dualProj_singleton, Φ.deriv_comp_cons i v hz, nonlin]
    have h := iteratedDeriv_comp_two (Φ.analyticAt_f i (Φ.mapsTo_comp_closure v hz)).contDiffAt
      (Φ.analyticAt_comp v hz).contDiffAt
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, ← comp_cons] at h
    rw [h]
    have := (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hz)
    grind

/-- Long shared prefixes imply uniform convergence of the projections. -/
theorem tendstoUniformlyOn_dualProj {a : ℕ → Word N} {w : ℕ → Fin N}
    (h : ∀ n, ∀ᶠ k in atTop, (a k).take n = (Word.inf w).take n) :
    TendstoUniformlyOn (fun k => Φ.dualProj (a k)) (Φ.dualProj (.inf w)) atTop (closedNbhd ε) := by
  obtain ⟨M, hM₀, hM⟩ := Φ.exists_norm_dualProj_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hlim : Tendsto (fun n => Φ.cmax ^ n * (2 * M)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_const (2 * M)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  set p := (Word.inf w).take n
  filter_upwards [h n] with k hk z hz
  rw [Φ.dualProj_split (a k) n (by simp_all) hz,
    Φ.dualProj_split (.inf w) n (by simp) hz, hk, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  have hza := Φ.mapsTo_comp_closure p.reverse hz
  refine lt_of_le_of_lt (mul_le_mul ?_ ?_ (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)) hn
  · change ‖deriv (Φ.comp p.reverse) z‖ ≤ Φ.cmax ^ n
    simpa only [List.length_reverse, p, Word.take_inf, List.length_ofFn] using (Φ.norm_deriv_comp_bounds p.reverse hz).2
  · exact (norm_sub_le ..).trans (by grind)

end IFS

end AnalyticESC
