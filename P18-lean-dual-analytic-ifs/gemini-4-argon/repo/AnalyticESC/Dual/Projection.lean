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

theorem dualTerm_of_get?_eq_none {w : Word N} {n : ℕ} (h : w.get? n = none) (z : ℂ) :
    Φ.dualTerm w n z = 0 := by
  simp [dualTerm, h]

theorem dualTerm_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N} (h : w.get? n = some i)
    (z : ℂ) :
    Φ.dualTerm w n z =
      Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z := by
  simp [dualTerm, h]

/-- If `w` has a letter in position `n`, then its prefix of length `n` has length `n`. -/
theorem length_take_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N}
    (h : w.get? n = some i) : (w.take n).length = n :=
  Word.length_take_of_le ((Word.isSome_get?_iff w n).1 (by simp [h])).le

/-- The terms of (1.4) decay geometrically on `cl B_ε`, uniformly in the word. -/
theorem exists_dualTerm_bound : ∃ C, 0 ≤ C ∧ ∀ (w : Word N) (n : ℕ), ∀ z ∈ closure (nbhd ε),
    ‖Φ.dualTerm w n z‖ ≤ C * Φ.cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_nonlin_bound
  refine ⟨C, hC0, fun w n z hz => ?_⟩
  cases h : w.get? n with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]
    exact mul_nonneg hC0 (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have h2 := Φ.norm_deriv_comp_le (w.take n).reverse hz
    rw [List.length_reverse, length_take_of_get?_eq_some h] at h2
    exact mul_le_mul (hC i _ (Φ.mapsTo_comp_closure (w.take n).reverse hz)) h2 (norm_nonneg _) hC0

theorem summable_dualTerm (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    fun n => hC w n z hz

/-- For a finite word, `H_a` is the finite sum of its `|a|` terms. -/
theorem dualProj_fin_eq_sum (a : List (Fin N)) (z : ℂ) :
     Φ.dualProj (.fin a) z = ∑ n ∈ Finset.range a.length, Φ.dualTerm (.fin a) n z := by
  refine tsum_eq_sum fun n hn => Φ.dualTerm_of_get?_eq_none ?_ z
  simp only [Finset.mem_range, not_lt] at hn
  simp [hn]

theorem dualProj_singleton (i : Fin N) (z : ℂ) : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  rw [dualProj_fin_eq_sum]; simp [dualTerm]

/-! ## Bounds -/

/-- The uniform bound `‖H_w‖ ≤ M` on `cl B_ε`. -/
theorem exists_norm_dualProj_le :
    ∃ M, 0 ≤ M ∧ ∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_dualTerm_bound
  exact ⟨C * (1 - Φ.cmax)⁻¹,
    mul_nonneg hC0 (inv_nonneg.2 (sub_nonneg.2 Φ.cmax_lt_one.le)), fun w z hz =>
      tsum_of_norm_bounded ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
        fun n => hC w n z hz⟩

/-! ## Holomorphy and realness -/

theorem differentiableOn_dualTerm (w : Word N) (n : ℕ) :
    DifferentiableOn ℂ (Φ.dualTerm w n) (nbhd ε) := by
  cases h : w.get? n with
  | none =>
    rw [funext (Φ.dualTerm_of_get?_eq_none h)]
    exact differentiableOn_const 0
  | some i =>
    rw [funext (Φ.dualTerm_of_get?_eq_some h)]
    exact DifferentiableOn.mul (fun z hz => ((Φ.differentiableAt_nonlin i
      (subset_closure (Φ.mapsTo_comp _ hz))).comp z
      (Φ.differentiableAt_comp _ (subset_closure hz))).differentiableWithinAt)
      ((Φ.differentiableOn_comp _).deriv (isOpen_nbhd ε))

theorem differentiableOn_dualProj (w : Word N) : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (fun n => Φ.differentiableOn_dualTerm w n) (isOpen_nbhd ε)
    fun n z hz => hC w n z (subset_closure hz)

theorem im_dualTerm_ofReal (w : Word N) (n : ℕ) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualTerm w n t).im = 0 := by
  cases h : w.get? n with
  | none => simp [Φ.dualTerm_of_get?_eq_none h]
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h]
    have h1 : Φ.comp (w.take n).reverse t = ((Φ.comp (w.take n).reverse t).re : ℂ) := by
      apply Complex.ext <;> simp [Φ.im_comp_ofReal _ ht]
    have h3 := Φ.im_nonlin_ofReal i (h1 ▸ Φ.mapsTo_comp _ ht)
    rw [← h1] at h3
    simp [Complex.mul_im, h3, Φ.im_deriv_comp_ofReal _ ht]

theorem im_dualProj_ofReal (w : Word N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualProj w t).im = 0 := by
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm w (subset_closure ht))]
  simp [Φ.im_dualTerm_ofReal w _ ht]

/-! ## The cocycle identity and (2.7) -/

/-- The cocycle identity: `H_{a w}(z) = H_a(z) + f_{a^←}'(z) · H_w(f_{a^←}(z))`, where
`f_{a^←} = f_{a_{|a|}} ∘ ⋯ ∘ f_{a_1}`. -/
theorem dualProj_prepend (a : List (Fin N)) (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
     Φ.dualProj (w.prepend a) z =
      Φ.dualProj (.fin a) z + deriv (Φ.comp a.reverse) z * Φ.dualProj w (Φ.comp a.reverse z) := by
  rw [dualProj_fin_eq_sum]
  unfold dualProj
  rw [← (Φ.summable_dualTerm (w.prepend a) hz).sum_add_tsum_nat_add a.length, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    simp only [dualTerm, Word.get?_prepend, hn', ↓reduceIte, Word.take_prepend_of_le a w hn'.le,
      Word.get?_fin, Word.take_fin]
  · refine tsum_congr fun m => ?_
    simp only [dualTerm, add_comm m a.length, Word.get?_prepend,
      Nat.not_lt.2 (Nat.le_add_right _ _), ↓reduceIte, add_tsub_cancel_left,
      Word.take_prepend_add a w m]
    cases w.get? m with
    | none => simp
    | some i =>
      rw [List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

/-- (2.7): `H_{v^←} = f_v''/f_v'` for a finite word `v`. -/
theorem dualProj_fin_reverse (v : List (Fin N)) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualProj (.fin v.reverse) z = deriv (deriv (Φ.comp v)) z / deriv (Φ.comp v) z := by
  induction v with
  | nil => simp [dualProj, dualTerm, deriv_id']
  | cons i v ih =>
    have hcl := subset_closure hz
    have ho := isOpen_nbhd ε
    have ho2 := isOpen_nbhd (2 * ε)
    have huU := ho.mem_nhds hz
    have hv2 := ho2.mem_nhds (nbhd_subset_two (Φ.mapsTo_comp v hz))
    have hd := Φ.differentiableOn_comp v
    have heq : deriv (Φ.comp (i :: v)) =ᶠ[𝓝 z]
        fun u => deriv (Φ.f i) (Φ.comp v u) * deriv (Φ.comp v) u :=
      Filter.eventually_of_mem huU fun u hu => Φ.deriv_comp_cons i v (subset_closure hu)
    have hdd : deriv (deriv (Φ.comp (i :: v))) z =
        deriv (deriv (Φ.f i)) (Φ.comp v z) * deriv (Φ.comp v) z ^ 2 +
          deriv (Φ.f i) (Φ.comp v z) * deriv (deriv (Φ.comp v)) z := by
      rw [heq.deriv_eq]
      exact (((((Φ.differentiableOn_f i).deriv ho2).differentiableAt hv2).hasDerivAt.comp z
        (hd.differentiableAt huU).hasDerivAt).mul
        ((hd.deriv ho).differentiableAt huU).hasDerivAt).deriv.trans
        (by rw [Function.comp_apply]; ring)
    have hfin : (Word.fin [i]).prepend v.reverse = Word.fin (i :: v).reverse := by
      rw [List.reverse_cons]; rfl
    rw [← hfin, Φ.dualProj_prepend _ _ hcl, ih, List.reverse_reverse, dualProj_singleton,
      hdd, Φ.deriv_comp_cons i v hcl, nonlin]
    have h1 := (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hcl)
    have h2 := Φ.deriv_comp_ne_zero v hcl
    field_simp; ring

/-! ## Lemma 2.5 -/

/-- Uniform bound for `H_w` on `cl B_ε` and the bound `2M c_max^m` for words sharing a prefix of
length `m`. -/
theorem exists_dualProj_bounds :
    ∃ M, 0 ≤ M ∧ (∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M) ∧
      ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj i z - Φ.dualProj j z‖ ≤ 2 * M * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  refine ⟨M, hM0, hM, fun i j m hm z hz => ?_⟩
  obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
  rw [Φ.dualProj_prepend a i' hz, Φ.dualProj_prepend a j' hz, add_sub_add_left_eq_sub,
    ← mul_sub, norm_mul]
  have hz' := Φ.mapsTo_comp_closure a.reverse hz
  have h1 := Φ.norm_deriv_comp_le a.reverse hz
  rw [List.length_reverse, ha] at h1
  exact (mul_le_mul h1 ((norm_sub_le _ _).trans (add_le_add (hM _ _ hz') (hM _ _ hz')))
    (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)).trans_eq (by ring)

end IFS

end AnalyticESC
