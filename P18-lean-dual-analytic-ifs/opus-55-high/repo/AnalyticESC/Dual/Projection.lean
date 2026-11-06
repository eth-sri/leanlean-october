module

public import AnalyticESC.Basic
public import AnalyticESC.Words

public section

set_option hygiene false
local notation "𝕻" => Φ.comp v
local notation "𝕺" => .fin a
local notation "𝕹" => (summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C
local notation "𝕸" => hg.trans h
local notation "𝔒" => Φ.comp v z

local notation "𝔈" => Φ.comp a.reverse z

/-!
# The dual natural projection

Convergence and holomorphy of the series (1.4) defining `H_w`, its uniform bounds, the cocycle
identity for prepended words, the formula (2.7) `H_{v^←} = f_v''/f_v'` for finite words, and
Lemma 2.5, analyticity and Hölder continuity: `H_w ∈ C^ω_ε([0,1])` and Hölder dependence on the word.
-/

namespace AnalyticESC

variable {n : ℕ} {t : ℝ} {z : ℂ}

open Topology

namespace IFS

variable (Φ : IFS N ε) {i : Fin N} {w : Word N}

/-! ## The terms of the series -/

theorem dualTerm_of_get?_eq_none (h : w.get? n = none) z :
    Φ.dualTerm w n z = 0 := by
  simp [dualTerm, h]

theorem dualTerm_of_get?_eq_some (h : w.get? n = some i)
    z :
    Φ.dualTerm w n z =
      Φ.nonlin i (Φ.comp 𝔱 z) * 𝔡ᶜ Φ 𝔱 z := by
  simp [dualTerm, h]

/-- If `w` has a letter in position `n`, then its prefix of length `n` has length `n`. -/
theorem length_take_of_get?_eq_some
    (h : w.get? n = some i) : (w.take n).length = n := by
  cases w with
  | fin w =>
    have := (List.getElem?_eq_some_iff.1 h).1
    simp
    omega
  | inf w => simp

/-- The terms of (1.4) decay geometrically on `cl B_ε`, uniformly in the word. -/
theorem exists_dualTerm_bound : ∃ C, 0 ≤ C ∧ ∀ (w : Word N) n, ∀ z ∈ 𝔹 ε,
    ‖Φ.dualTerm w n z‖ ≤ C * Φ.cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_nonlin_bound
  refine ⟨C, hC0, fun w n z hz => ?_⟩
  cases h : w.get? n with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]
    exact mul_nonneg hC0 (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have h2 := Φ.norm_deriv_comp_le 𝔱 hz
    rw [List.length_reverse, length_take_of_get?_eq_some h] at h2
    exact mul_le_mul (hC i _ (Φ.mapsTo_comp_closure 𝔱 hz)) h2 (norm_nonneg _) hC0

theorem summable_dualTerm w (hz : z ∈ 𝔹 ε) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded
    𝕹
    fun n => hC w n z hz

@[simp] theorem dualProj_nil : Φ.dualProj (.fin []) = 0 := by
  funext z
  simp [dualProj, dualTerm]

/-- For a finite word, `H_a` is the finite sum of its `|a|` terms. -/
theorem dualProj_fin_eq_sum a z :
    Φ.dualProj 𝕺 z = ∑ n ∈ Finset.range a.length, Φ.dualTerm 𝕺 n z := by
  refine tsum_eq_sum fun n hn => Φ.dualTerm_of_get?_eq_none ?_ z
  simp_all

theorem dualProj_singleton i z : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  rw [dualProj_fin_eq_sum]
  simp [dualTerm]

/-! ## Bounds -/

/-- The uniform bound `‖H_w‖ ≤ M` on `cl B_ε`. -/
theorem exists_norm_dualProj_le :
    ∃ M, 0 ≤ M ∧ ∀ w, ∀ z ∈ 𝔹 ε, ‖Φ.dualProj w z‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_dualTerm_bound
  refine ⟨C * (1 - Φ.cmax)⁻¹,
    mul_nonneg hC0 (inv_nonneg.2 (sub_nonneg.2 Φ.cmax_lt_one.le)), fun w z hz => ?_⟩
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C) fun n => hC w n z hz

/-! ## Holomorphy and realness -/

theorem differentiableOn_dualTerm w n :
    DifferentiableOn ℂ (Φ.dualTerm w n) (nbhd ε) := by
  cases h : w.get? n with
  | none =>
    have : Φ.dualTerm w n = fun _ => 0 := funext (Φ.dualTerm_of_get?_eq_none h)
    exact this ▸ differentiableOn_const 0
  | some i =>
    have : Φ.dualTerm w n = fun z => Φ.nonlin i (Φ.comp 𝔱 z) *
        𝔡ᶜ Φ 𝔱 z := funext (Φ.dualTerm_of_get?_eq_some h)
    rw [this]
    obtain ⟨U, -, hU, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨V, hVo, hV, hc⟩ := Φ.exists_differentiableOn_comp 𝔱
    refine DifferentiableOn.mul ?_ ?_
    · exact hnl.comp (Φ.differentiableOn_comp _) fun z hz =>
        hU (subset_closure (Φ.mapsTo_comp _ hz))
    · exact (hc.deriv hVo).mono (subset_closure.trans hV)

theorem differentiableOn_dualProj w : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm
    𝕹
    (Φ.differentiableOn_dualTerm w) isOpen_nbhd
    fun n z hz => hC w n z (subset_closure hz)

theorem im_dualTerm_ofReal w n (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualTerm w n t).im = 0 := by
  cases h : w.get? n with
  | none => simp [Φ.dualTerm_of_get?_eq_none h]
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h]
    have h1 : Φ.comp 𝔱 t = ((Φ.comp 𝔱 t).re : ℂ) := by
      apply Complex.ext <;> simp [Φ.im_comp_ofReal _ ht]
    have h3 := Φ.im_nonlin_ofReal i (h1 ▸ Φ.mapsTo_comp _ ht)
    rw [← h1] at h3
    simp [h3, Φ.im_deriv_comp_ofReal _ ht]

theorem im_dualProj_ofReal w (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualProj w t).im = 0 := by
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm w (subset_closure ht))]
  simp [Φ.im_dualTerm_ofReal w _ ht]

/-! ## The cocycle identity and (2.7) -/

/-- The cocycle identity: `H_{a w}(z) = H_a(z) + f_{a^←}'(z) · H_w(f_{a^←}(z))`, where
`f_{a^←} = f_{a_{|a|}} ∘ ⋯ ∘ f_{a_1}`. -/
theorem dualProj_prepend a w (hz : z ∈ 𝔹 ε) :
    Φ.dualProj (w.prepend a) z =
      Φ.dualProj 𝕺 z + 𝔡ᶜ Φ a.reverse z * Φ.dualProj w 𝔈 := by
  rw [dualProj_fin_eq_sum]
  unfold dualProj
  rw [← (Φ.summable_dualTerm (w.prepend a) hz).sum_add_tsum_nat_add a.length, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hg := Word.get?_prepend_of_lt a w (Finset.mem_range.1 hn)
    have ht : (w.prepend a).take n = (Word.fin a).take n := Word.take_prepend_of_le a w (Finset.mem_range.1 hn).le
    cases h : (Word.fin a).get? n with
    | none => rw [Φ.dualTerm_of_get?_eq_none 𝕸, Φ.dualTerm_of_get?_eq_none h]
    | some i => rw [Φ.dualTerm_of_get?_eq_some 𝕸, Φ.dualTerm_of_get?_eq_some h, ht]
  · refine tsum_congr fun m => ?_
    have hg : (w.prepend a).get? (m + a.length) = w.get? m := by
      rw [add_comm]; exact Word.get?_prepend_add a w m
    have ht : (w.prepend a).take (m + a.length) = a ++ w.take m := by
      rw [add_comm]; exact Word.take_prepend_add a w m
    cases h : w.get? m with
    | none =>
      rw [Φ.dualTerm_of_get?_eq_none 𝕸, Φ.dualTerm_of_get?_eq_none h, mul_zero]
    | some i =>
      rw [Φ.dualTerm_of_get?_eq_some 𝕸, Φ.dualTerm_of_get?_eq_some h, ht,
        List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

/-- The second derivative of `f_i ∘ f_v` by the chain rule. -/
theorem deriv_deriv_comp_cons i v
    (hz : z ∈ 𝔹 ε) :
    deriv (𝔡ᶜ Φ (i :: v)) z =
      𝔇 (Φ.f i) 𝔒 * 𝔡ᶜ Φ v z ^ 2 +
        𝔡 Φ i 𝔒 * 𝔇 𝕻 z := by
  obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_comp v
  have hfi := Φ.differentiableOn_f i
  have hW : IsOpen (U ∩ Φ.comp v ⁻¹' 𝔑 ε) :=
    hd.continuousOn.isOpen_inter_preimage hUo isOpen_nbhd
  have hzW : z ∈ U ∩ Φ.comp v ⁻¹' 𝔑 ε :=
    ⟨hU hz, closure_nbhd_subset_two (Φ.mapsTo_comp_closure v hz)⟩
  have heq : 𝔡ᶜ Φ (i :: v) =ᶠ[𝓝 z]
      fun u => 𝔡 Φ i (Φ.comp v u) * 𝔡ᶜ Φ v u := by
    filter_upwards [hW.mem_nhds hzW] with u hu
    exact deriv_comp u ((hfi _ hu.2).differentiableAt (isOpen_nbhd.mem_nhds hu.2))
      ((hd u hu.1).differentiableAt (hUo.mem_nhds hu.1))
  have hdf : DifferentiableAt ℂ (𝔡 Φ i) 𝔒 :=
    ((hfi.deriv isOpen_nbhd) _ hzW.2).differentiableAt (isOpen_nbhd.mem_nhds hzW.2)
  have hdh : DifferentiableAt ℂ (𝔡ᶜ Φ v) z :=
    ((hd.deriv hUo) z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)
  exact heq.deriv_eq ▸ ((hdf.hasDerivAt.comp z ((hd z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)).hasDerivAt).mul hdh.hasDerivAt).deriv.trans (by grind)

/-- (2.7): `H_{v^←} = f_v''/f_v'` for a finite word `v`. -/
theorem dualProj_fin_reverse v (hz : z ∈ 𝔹 ε) :
    Φ.dualProj (.fin v.reverse) z = 𝔇 𝕻 z / 𝔡ᶜ Φ v z := by
  induction v with
  | nil => simp
  | cons i v ih =>
    have hfin : (Word.fin [i]).prepend v.reverse = Word.fin (i :: v).reverse := by aesop
    rw [← hfin, Φ.dualProj_prepend _ _ hz, ih, List.reverse_reverse, dualProj_singleton,
      Φ.deriv_deriv_comp_cons i v hz, Φ.deriv_comp_cons i v hz, nonlin]
    have h1 : 𝔡 Φ i 𝔒 ≠ 0 :=
      (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hz)
    field_simp
    ring

/-! ## Lemma 2.5 -/

/-- Uniform bound for `H_w` on `cl B_ε` and the bound `2M c_max^m` for words sharing a prefix of
length `m`. -/
theorem exists_dualProj_bounds :
    ∃ M, ∀ (i j : Word N) (m : ℕ), (m : ℕ∞) ≤ i.commonPrefixLength j →
        ∀ z ∈ 𝔹 ε, ‖Φ.dualProj i z - Φ.dualProj j z‖ ≤ 2 * M * Φ.cmax ^ m := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  refine ⟨M, fun i j m hm z hz => ?_⟩
  obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
  rw [Φ.dualProj_prepend a i' hz, Φ.dualProj_prepend a j' hz, add_sub_add_left_eq_sub,
    ← mul_sub, norm_mul]
  have hz' := Φ.mapsTo_comp_closure a.reverse hz
  have h1 := Φ.norm_deriv_comp_le a.reverse hz
  rw [List.length_reverse, ha] at h1
  have h2 : ‖Φ.dualProj i' 𝔈 - Φ.dualProj j' 𝔈‖ ≤
      2 * M := by
    calc _ ≤ ‖Φ.dualProj i' 𝔈‖ + ‖Φ.dualProj j' 𝔈‖ := by bound
      _ ≤ M + M := by grind
      _ = 2 * M := by ring
  calc _ ≤ Φ.cmax ^ m * (2 * M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)
    _ = 2 * M * Φ.cmax ^ m := by ring

end IFS

end AnalyticESC
