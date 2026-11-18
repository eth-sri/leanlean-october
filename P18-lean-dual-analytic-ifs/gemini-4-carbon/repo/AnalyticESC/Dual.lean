module

public import AnalyticESC.Defs

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem dualTerm_of_get?_eq_none {w : Word N} {n : ℕ} (h : w.get? n = none) (z : ℂ) :
    Φ.dualTerm w n z = 0 := by simp [dualTerm, h]

theorem dualTerm_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N} (h : w.get? n = some i)
    (z : ℂ) :
    Φ.dualTerm w n z =
      Φ.nonlin i (Φ.comp (w.take n).reverse z) * deriv (Φ.comp (w.take n).reverse) z := by
  simp [dualTerm, h]

theorem length_take_of_get?_eq_some {w : Word N} {n : ℕ} {i : Fin N}
    (h : w.get? n = some i) : (w.take n).length = n := by
  cases w with
  | fin w =>
    have := (List.getElem?_eq_some_iff.1 h).1
    simp only [Word.take_fin, List.length_take]; omega
  | inf w => simp

theorem exists_dualTerm_bound : ∃ C, 0 ≤ C ∧ ∀ (w : Word N) (n : ℕ), ∀ z ∈ closure (nbhd ε),
    ‖Φ.dualTerm w n z‖ ≤ C * Φ.cmax ^ n := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_nonlin_bound
  refine ⟨C, hC0, fun w n z hz => ?_⟩
  cases h : w.get? n with
  | none => rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]; exact mul_nonneg hC0 (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have h2 := Φ.norm_deriv_comp_le (w.take n).reverse hz
    rw [List.length_reverse, length_take_of_get?_eq_some h] at h2
    exact mul_le_mul (hC i _ (Φ.mapsTo_comp_closure _ hz)) h2 (norm_nonneg _) hC0

theorem summable_dualTerm (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Summable fun n => Φ.dualTerm w n z := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C) fun n => hC w n z hz

theorem dualProj_fin_eq_sum (a : List (Fin N)) (z : ℂ) :
    Φ.dualProj (.fin a) z = ∑ n ∈ Finset.range a.length, Φ.dualTerm (.fin a) n z :=
  tsum_eq_sum fun n hn => Φ.dualTerm_of_get?_eq_none (by simp [Finset.mem_range.not.1 hn]) z

theorem dualProj_singleton (i : Fin N) (z : ℂ) : Φ.dualProj (.fin [i]) z = Φ.nonlin i z := by
  rw [dualProj_fin_eq_sum]; simp [dualTerm]

theorem differentiableOn_dualTerm (w : Word N) (n : ℕ) :
    DifferentiableOn ℂ (Φ.dualTerm w n) (nbhd ε) := by
  cases h : w.get? n with
  | none =>
    rw [show Φ.dualTerm w n = fun _ => 0 from funext (Φ.dualTerm_of_get?_eq_none h)]
    exact differentiableOn_const 0
  | some i =>
    rw [show Φ.dualTerm w n = fun z => Φ.nonlin i (Φ.comp (w.take n).reverse z) *
      deriv (Φ.comp (w.take n).reverse) z from funext (Φ.dualTerm_of_get?_eq_some h)]
    obtain ⟨U, -, hU, hnl⟩ := Φ.exists_differentiableOn_nonlin i
    obtain ⟨V, hVo, hV, hc⟩ := Φ.exists_differentiableOn_comp (w.take n).reverse
    exact (hnl.comp (Φ.differentiableOn_comp _) fun _ hz => hU (subset_closure (Φ.mapsTo_comp _ hz))).mul
      ((hc.deriv hVo).mono (subset_closure.trans hV))

theorem differentiableOn_dualProj (w : Word N) : DifferentiableOn ℂ (Φ.dualProj w) (nbhd ε) := by
  obtain ⟨C, -, hC⟩ := Φ.exists_dualTerm_bound
  exact Complex.differentiableOn_tsum_of_summable_norm
    ((summable_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
    (fun n => Φ.differentiableOn_dualTerm w n) (isOpen_nbhd ε) fun n z hz => hC w n z (subset_closure hz)

theorem im_dualProj_ofReal (w : Word N) {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (Φ.dualProj w t).im = 0 := by
  have h0 : ∀ n, (Φ.dualTerm w n t).im = 0 := fun n => by
    cases h : w.get? n with
    | none => simp [Φ.dualTerm_of_get?_eq_none h]
    | some i =>
      rw [Φ.dualTerm_of_get?_eq_some h]
      have h1 : Φ.comp (w.take n).reverse t = ((Φ.comp (w.take n).reverse t).re : ℂ) :=
        Complex.ext rfl (by simp [Φ.im_comp_ofReal _ ht])
      have h3 := Φ.im_nonlin_ofReal i (h1 ▸ Φ.mapsTo_comp _ ht)
      rw [← h1] at h3
      simp [Complex.mul_im, h3, Φ.im_deriv_comp_ofReal _ ht]
  rw [dualProj, Complex.im_tsum (Φ.summable_dualTerm w (subset_closure ht))]
  simp [h0]

theorem dualProj_prepend (a : List (Fin N)) (w : Word N) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.dualProj (w.prepend a) z =
      Φ.dualProj (.fin a) z + deriv (Φ.comp a.reverse) z * Φ.dualProj w (Φ.comp a.reverse z) := by
  rw [dualProj_fin_eq_sum]
  unfold dualProj
  rw [← (Φ.summable_dualTerm (w.prepend a) hz).sum_add_tsum_nat_add a.length, ← tsum_mul_left]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    simp only [dualTerm, Word.get?_prepend_of_lt a w hn', Word.take_prepend_of_le a w hn'.le,
      Word.get?_fin, Word.take_fin]
  · refine tsum_congr fun m => ?_
    have hg : (w.prepend a).get? (m + a.length) = w.get? m := add_comm m a.length ▸ Word.get?_prepend_add a w m
    have ht : (w.prepend a).take (m + a.length) = a ++ w.take m := add_comm m a.length ▸ Word.take_prepend_add a w m
    cases h : w.get? m with
    | none => rw [Φ.dualTerm_of_get?_eq_none (hg.trans h), Φ.dualTerm_of_get?_eq_none h, mul_zero]
    | some i =>
      rw [Φ.dualTerm_of_get?_eq_some (hg.trans h), Φ.dualTerm_of_get?_eq_some h, ht,
        List.reverse_append, Φ.deriv_comp_append _ _ hz, Φ.comp_append, Function.comp_apply]
      ring

theorem deriv_deriv_comp_cons (i : Fin N) (v : List (Fin N)) {z : ℂ}
    (hz : z ∈ closure (nbhd ε)) :
    deriv (deriv (Φ.comp (i :: v))) z =
      deriv (deriv (Φ.f i)) (Φ.comp v z) * deriv (Φ.comp v) z ^ 2 +
        deriv (Φ.f i) (Φ.comp v z) * deriv (deriv (Φ.comp v)) z := by
  obtain ⟨U, hUo, hU, hd⟩ := Φ.exists_differentiableOn_comp v
  have ho2 := isOpen_nbhd (2 * ε)
  have hfi := Φ.differentiableOn_f i
  have hW : IsOpen (U ∩ Φ.comp v ⁻¹' nbhd (2 * ε)) := hd.continuousOn.isOpen_inter_preimage hUo ho2
  have hzW : z ∈ U ∩ Φ.comp v ⁻¹' nbhd (2 * ε) := ⟨hU hz, closure_nbhd_subset_two (Φ.mapsTo_comp_closure v hz)⟩
  have heq : deriv (Φ.comp (i :: v)) =ᶠ[𝓝 z] fun u => deriv (Φ.f i) (Φ.comp v u) * deriv (Φ.comp v) u :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hzW) fun u hu =>
      deriv_comp u ((hfi _ hu.2).differentiableAt (ho2.mem_nhds hu.2)) ((hd u hu.1).differentiableAt (hUo.mem_nhds hu.1))
  rw [heq.deriv_eq]
  exact (((((hfi.deriv ho2) _ hzW.2).differentiableAt (ho2.mem_nhds hzW.2)).hasDerivAt.comp z
    ((hd z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)).hasDerivAt).mul
    (((hd.deriv hUo) z hzW.1).differentiableAt (hUo.mem_nhds hzW.1)).hasDerivAt).deriv.trans
    (by rw [Function.comp_apply]; ring)

theorem dualProj_fin_reverse (v : List (Fin N)) {z : ℂ} (hz : z ∈ closure (nbhd ε)) :
    Φ.dualProj (.fin v.reverse) z = deriv (deriv (Φ.comp v)) z / deriv (Φ.comp v) z := by
  induction v with
  | nil => simp [deriv_id', dualProj, dualTerm]
  | cons i v ih =>
    have hfin : (Word.fin [i]).prepend v.reverse = Word.fin (i :: v).reverse := by rw [List.reverse_cons]; rfl
    rw [← hfin, Φ.dualProj_prepend _ _ hz, ih, List.reverse_reverse, dualProj_singleton,
      Φ.deriv_deriv_comp_cons i v hz, Φ.deriv_comp_cons i v hz, nonlin]
    have h1 := (Φ.inClass i).deriv_ne_zero _ (Φ.mapsTo_comp_closure v hz)
    have h2 := Φ.deriv_comp_ne_zero v hz
    field_simp; ring

theorem exists_dualProj_bounds :
    ∃ M, 0 ≤ M ∧ (∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M) ∧
      ∀ (i j : Word N) (m : ℕ), (∀ k < m, (i.get? k).isSome ∧ i.get? k = j.get? k) →
        ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj i z - Φ.dualProj j z‖ ≤ 2 * M * Φ.cmax ^ m := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_dualTerm_bound
  set M := C * (1 - Φ.cmax)⁻¹
  have hM0 : 0 ≤ M := mul_nonneg hC0 (inv_nonneg.2 (sub_nonneg.2 Φ.cmax_lt_one.le))
  have hM : ∀ w : Word N, ∀ z ∈ closure (nbhd ε), ‖Φ.dualProj w z‖ ≤ M := fun w z hz =>
    tsum_of_norm_bounded ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left C)
      fun n => hC w n z hz
  refine ⟨M, hM0, hM, fun i j m hm z hz => ?_⟩
  obtain ⟨a, i', j', ha, rfl, rfl⟩ := Word.exists_eq_prepend hm
  rw [Φ.dualProj_prepend a i' hz, Φ.dualProj_prepend a j' hz, add_sub_add_left_eq_sub, ← mul_sub, norm_mul]
  have hz' := Φ.mapsTo_comp_closure a.reverse hz
  have h1 := Φ.norm_deriv_comp_le a.reverse hz
  rw [List.length_reverse, ha] at h1
  exact (mul_le_mul h1 ((norm_sub_le _ _).trans
    ((add_le_add (hM _ _ hz') (hM _ _ hz')).trans_eq (by ring : M + M = 2 * M)))
    (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)).trans_eq (mul_comm _ _)

theorem dualComp_apply (w : List (Fin N)) (h : ℂ → ℂ) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualComp w h z =
      deriv (Φ.comp w.reverse) z * h (Φ.comp w.reverse z) + Φ.dualProj (.fin w) z := by
  induction w generalizing z with
  | nil => simp [dualComp, dualProj, dualTerm]
  | cons i w ih =>
    have hcl : z ∈ closure (nbhd ε) := subset_closure hz
    have h1 : Φ.dualComp (i :: w) h z = deriv (Φ.f i) z * Φ.dualComp w h (Φ.f i z) + Φ.nonlin i z := rfl
    have h2 : (Word.fin w).prepend [i] = .fin (i :: w) := rfl
    rw [h1, ih (Φ.mapsTo_f i hz), List.reverse_cons, Φ.deriv_comp_append _ _ hcl,
      Φ.comp_append, show Φ.comp [i] = Φ.f i by simp, ← h2,
      Φ.dualProj_prepend [i] _ hcl, List.reverse_singleton, show Φ.comp [i] = Φ.f i by simp,
      Φ.dualProj_singleton, Function.comp_apply]
    ring

theorem not_dualSSC_of_comp_eq {a b : List (Fin N)} (hlen : a.length = b.length)
    (hlast : a.getLast? ≠ b.getLast?) (h : ∀ x ∈ I, Φ.comp a x = Φ.comp b x) : ¬ Φ.DualSSC := by
  intro hssc
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', p, rfl⟩
  · exact hlast (by rw [List.length_eq_zero_iff.1 hlen.symm])
  rcases List.eq_nil_or_concat' b with rfl | ⟨b', q, rfl⟩
  · simp at hlen
  have hpq : p ≠ q := fun hpq => hlast (by rw [List.getLast?_concat, List.getLast?_concat, hpq])
  let w₀ : ℕ → Fin N := fun _ => p
  let ext (u : List (Fin N)) (n : ℕ) : Fin N := if hn : n < u.length then u[n] else p
  have hprep : ∀ u, (Word.inf w₀).prepend u = .inf (ext u) := fun _ => rfl
  have h0_eq : ∀ (u : List (Fin N)) (c : Fin N), ext (u ++ [c]).reverse 0 = c := fun u c => by
    simp [ext]
  obtain ⟨x, hx, hne⟩ := hssc (ext (a' ++ [p]).reverse) (ext (b' ++ [q]).reverse)
    (by rw [h0_eq, h0_eq]; exact hpq)
  apply hne
  have hEq : EqOn (Φ.comp (a' ++ [p])) (Φ.comp (b' ++ [q])) (nbhd ε) :=
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp _) (Φ.differentiableOn_comp _)
      zero_lt_one subset_rfl h
  have hz : (x : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos hx
  have hEv : Φ.comp (a' ++ [p]) =ᶠ[𝓝 (x : ℂ)] Φ.comp (b' ++ [q]) :=
    Filter.eventuallyEq_of_mem ((isOpen_nbhd ε).mem_nhds hz) hEq
  have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure hz
  rw [← hprep, ← hprep, Φ.dualProj_prepend _ _ hcl, Φ.dualProj_prepend _ _ hcl,
    List.reverse_reverse, List.reverse_reverse,
    Φ.dualProj_fin_reverse _ hcl, Φ.dualProj_fin_reverse _ hcl,
    (hEv.deriv.deriv_eq), hEv.deriv_eq, hEq hz]

end IFS

private lemma norm_deriv_le_of_norm_le {ε : ℝ} (hε : 0 < ε) {D : ℂ → ℂ}
    (hD : DifferentiableOn ℂ D (nbhd ε)) {p q η M : ℝ} (hpq : Icc p q ⊆ I)
    (hη : 0 < η) (hM : 0 ≤ M) (hJ : 2 * Real.sqrt η < q - p)
    (hD0 : ∀ x ∈ Icc p q, ‖D x‖ ≤ η) (hD2 : ∀ x ∈ Icc p q, ‖deriv (deriv D) x‖ ≤ M)
    {x : ℝ} (hx : x ∈ Icc p q) : ‖deriv D x‖ ≤ (2 + M) * Real.sqrt η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Icc p q, |y - x| = Real.sqrt η :=
    if h : x + Real.sqrt η ≤ q then
      ⟨x + Real.sqrt η, ⟨by linarith [hx.1], h⟩, by simp [abs_of_pos hs]⟩
    else
      ⟨x - Real.sqrt η, ⟨by linarith, by linarith [hx.2]⟩,
        by rw [show x - Real.sqrt η - x = -Real.sqrt η by ring, abs_neg, abs_of_pos hs]⟩
  have hsub : uIcc x y ⊆ Icc p q := uIcc_subset_Icc hx hy
  have hmem : ∀ {t : ℝ}, t ∈ uIcc x y → nbhd ε ∈ 𝓝 (t : ℂ) :=
    fun ht => (isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε (hpq (hsub ht)))
  have hd1 : ∀ t ∈ uIcc x y, HasDerivAt (fun s : ℝ => D s) (deriv D t) t :=
    fun t ht => (hD.differentiableAt (hmem ht)).hasDerivAt.comp_ofReal
  have hd2 : ∀ t ∈ uIcc x y, HasDerivAt (fun s : ℝ => deriv D s) (deriv (deriv D) t) t :=
    fun t ht => ((hD.deriv (isOpen_nbhd ε)).differentiableAt (hmem ht)).hasDerivAt.comp_ofReal
  have hmvt1 : ∀ t ∈ uIcc x y, ‖deriv D t - deriv D x‖ ≤ M * Real.sqrt η := fun t ht => by
    have h1 := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd2 s hs).hasDerivWithinAt) (fun s hs => hD2 s (hsub hs)) left_mem_uIcc ht
    have htx : ‖t - x‖ ≤ Real.sqrt η := by
      rw [Real.norm_eq_abs]
      exact (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc left_mem_uIcc ht)).trans_eq hyx
    exact h1.trans (mul_le_mul_of_nonneg_left htx hM)
  let Ψ (t : ℝ) : ℂ := D t - deriv D x * t
  have hdΨ : ∀ t ∈ uIcc x y, HasDerivWithinAt Ψ (deriv D t - deriv D x) (uIcc x y) t := fun t ht =>
    ((hd1 t ht).fun_sub (((hasDerivAt_id t).ofReal_comp.const_mul (deriv D x)).congr_deriv
      (mul_one _))).hasDerivWithinAt
  have hmvt2 := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdΨ hmvt1 left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, hyx, mul_assoc, ← sq, Real.sq_sqrt hη.le] at hmvt2
  have hid : deriv D x * ((y : ℂ) - x) = D y - D x - (Ψ y - Ψ x) := by dsimp [Ψ]; ring
  have hn : ‖deriv D x‖ * Real.sqrt η ≤ (2 + M) * η := by
    rw [show ‖deriv D x‖ * Real.sqrt η = ‖deriv D x * ((y : ℂ) - x)‖ by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hyx], hid]
    linarith [norm_sub_le (D y - D x) (Ψ y - Ψ x), norm_sub_le (D y) (D x), hD0 y hy, hD0 x hx]
  exact le_of_mul_le_mul_right (by rwa [mul_assoc, ← sq, Real.sq_sqrt hη.le]) hs

private theorem norm_iteratedDeriv_sub_le {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε))
    (k : ℕ) {p q η Q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) (hQ : 0 ≤ Q)
    (hgQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j g x‖ ≤ Q)
    (hhQ : ∀ j ≤ k + 1, ∀ x ∈ Icc p q, ‖iteratedDeriv j h x‖ ≤ Q)
    (hJ : 2 * (2 + 2 * Q) * η ^ ((2 : ℝ)⁻¹ ^ k) < q - p)
    (hgh : ∀ x ∈ Icc p q, ‖g x - h x‖ ≤ η) :
    ∀ x ∈ Icc p q, ‖iteratedDeriv k g x - iteratedDeriv k h x‖ ≤
      (2 + 2 * Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ k) := by
  let D : ℂ → ℂ := fun z => g z - h z
  have hD : DifferentiableOn ℂ D (nbhd ε) := hg.sub hh
  have hpq : Icc p q ⊆ I := Icc_subset_Icc hp hq
  have hdiff : ∀ j, DifferentiableOn ℂ (iteratedDeriv j D) (nbhd ε) := fun j => by
    rw [iteratedDeriv_eq_iterate]; exact ((hD.analyticOnNhd (isOpen_nbhd ε)).iterated_deriv j).differentiableOn
  have hsub_eq : ∀ j, ∀ x ∈ Icc p q, iteratedDeriv j D x = iteratedDeriv j g x - iteratedDeriv j h x :=
    fun j x hx => by
      have hnhd := (isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε (hpq hx))
      exact iteratedDeriv_fun_sub ((hg.analyticAt hnhd).contDiffAt) ((hh.analyticAt hnhd).contDiffAt)
  suffices H : ∀ j ≤ k, ∀ x ∈ Icc p q,
      ‖iteratedDeriv j D x‖ ≤ (2 + 2 * Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j) from
    fun x hx => hsub_eq k x hx ▸ H k le_rfl x hx
  intro j; induction j with
  | zero =>
    intro _ x hx; simp only [iteratedDeriv_zero, pow_zero, Real.rpow_one, D]
    nlinarith [hgh x hx, sq_nonneg Q]
  | succ j ih =>
    intro hjk x hx
    have hsqrt : Real.sqrt ((2 + 2 * Q) ^ 2 * η ^ ((2 : ℝ)⁻¹ ^ j)) =
        (2 + 2 * Q) * η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hη.le, pow_succ, one_div]
    have hexp : η ^ ((2 : ℝ)⁻¹ ^ (j + 1)) ≤ η ^ ((2 : ℝ)⁻¹ ^ k) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk)
    rw [iteratedDeriv_succ]
    refine (norm_deriv_le_of_norm_le (M := 2 * Q) hε (hdiff j) hpq (by positivity) (by positivity)
      (by rw [hsqrt]; nlinarith) (ih (by omega)) (fun y hy => ?_) hx).trans_eq
      (by rw [hsqrt]; ring)
    rw [← iteratedDeriv_succ, ← iteratedDeriv_succ, hsub_eq (j + 2) y hy]
    exact (norm_sub_le _ _).trans (by linarith [hgQ (j + 2) (by omega) y hy, hhQ (j + 2) (by omega) y hy])

private theorem norm_iteratedDeriv_le_on_I {ε C : ℝ} (hε : 0 < ε) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hC : ∀ z ∈ nbhd ε, ‖g z‖ ≤ C)
    (k : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖iteratedDeriv k g x‖ ≤ k.factorial * C / (ε / 2) ^ k := by
  have hsub : closedBall (x : ℂ) (ε / 2) ⊆ nbhd ε :=
    (closedBall_subset_ball (half_lt_self hε)).trans (ball_subset_nbhd hx)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (half_pos hε)
    ⟨hg.mono (ball_subset_closedBall.trans hsub),
      (hg.continuousOn.mono hsub).mono closure_ball_subset_closedBall⟩
    fun z hz => hC z (hsub (sphere_subset_closedBall hz))

def SupExpSmall (n : ℕ → ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ θ > 0, ∀ᶠ k in atTop, η k ≤ θ ^ n k

namespace SupExpSmall

variable {n : ℕ → ℕ} {η : ℕ → ℝ}

theorem comp (h : SupExpSmall n η) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    SupExpSmall (n ∘ φ) (η ∘ φ) := fun θ hθ => hφ.eventually (h θ hθ)

theorem eventually_le (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, η k ≤ δ := by
  filter_upwards [h (min δ 1) (lt_min hδ one_pos)] with k hk
  exact hk.trans ((pow_le_of_le_one (le_min hδ.le zero_le_one) (min_le_right _ _) (by have := hn k; omega)).trans
    (min_le_left _ _))

theorem eventually_lt_pow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k in atTop, η k < c ^ n k := by
  filter_upwards [h (c / 2) (half_pos hc)] with k hk
  exact hk.trans_lt (pow_lt_pow_left₀ (half_lt_self hc) (half_pos hc).le (by have := hn k; omega))

theorem mul_pow_rpow (hn : ∀ k, 1 ≤ n k) (h : SupExpSmall n η) (hη : ∀ k, 0 ≤ η k) (K : ℝ)
    {A s : ℝ} (hA : 0 ≤ A) (hs : 0 < s) :
    SupExpSmall n fun k => K * A ^ n k * η k ^ s := by
  intro θ hθ
  set L := max K 1 * (A + 1) with hL_def
  have hL : 0 < L := by positivity
  have hθL : 0 < θ / L := div_pos hθ hL
  filter_upwards [h _ (Real.rpow_pos_of_pos hθL s⁻¹)] with k hk
  have hnk : n k ≠ 0 := by have := hn k; omega
  have h1 : η k ^ s ≤ (θ / L) ^ n k :=
    (Real.rpow_le_rpow (hη k) hk hs.le).trans_eq (by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hθL.le, ← Real.rpow_mul hθL.le,
        show s⁻¹ * (n k : ℝ) * s = n k by field_simp, Real.rpow_natCast])
  calc K * A ^ n k * η k ^ s ≤ max K 1 ^ n k * (A + 1) ^ n k * (θ / L) ^ n k :=
        mul_le_mul (mul_le_mul ((le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) hnk))
          (pow_le_pow_left₀ hA (by linarith) _) (by positivity) (by positivity))
          h1 (Real.rpow_nonneg (hη k) _) (by positivity)
    _ = θ ^ n k := by rw [← mul_pow, ← mul_pow, ← hL_def, mul_div_cancel₀ _ hL.ne']

end SupExpSmall

private theorem exists_frequently_eq_of_frequently_mem {α : Type*} {s : Set α} (hs : s.Finite)
    {f : ℕ → α} (h : ∃ᶠ k in atTop, f k ∈ s) : ∃ a ∈ s, ∃ᶠ k in atTop, f k = a := by
  by_contra! hcon
  exact h (((eventually_all_finite hs).2 fun a ha => hcon a ha).mono fun _ hk hks => hk _ hks rfl)

private theorem eqOn_nbhd_of_iteratedDeriv_close {ε : ℝ} (hε : 0 < ε) {g h : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (nbhd ε)) (hh : DifferentiableOn ℂ h (nbhd ε)) {p : ℕ → ℝ}
    {p₀ : ℝ} (hp₀ : p₀ ∈ I) (hp : Tendsto p atTop (𝓝 p₀))
    (hclose : ∀ r, ∀ δ > 0, ∀ᶠ k in atTop,
      ‖iteratedDeriv r g (p k) - iteratedDeriv r h (p k)‖ ≤ δ) :
    EqOn g h (nbhd ε) := by
  refine eqOn_nbhd_of_iteratedDeriv_eq hε hg hh hp₀ fun r => ?_
  have hmem : (p₀ : ℂ) ∈ nbhd ε := ofReal_mem_nbhd hε hp₀
  have hcont : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (nbhd ε) →
      Tendsto (fun k => iteratedDeriv r f (p k)) atTop (𝓝 (iteratedDeriv r f p₀)) := fun f hf => by
    have : ContinuousAt (iteratedDeriv r f) p₀ := by
      rw [iteratedDeriv_eq_iterate]
      exact ((hf.analyticOnNhd (isOpen_nbhd ε)).iterated_deriv r _ hmem).continuousAt
    exact this.tendsto.comp ((Complex.continuous_ofReal.tendsto p₀).comp hp)
  have hlim := ((hcont g hg).sub (hcont h hh)).norm
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  exact le_of_forall_pos_le_add fun δ hδ => by simpa using le_of_tendsto hlim (hclose r δ hδ)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem exists_iteratedDeriv_bounds :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ k, ∀ x ∈ I, ∀ w : Word N, ‖iteratedDeriv k (Φ.dualProj w) x‖ ≤ C k) ∧
      ∀ k, ∀ x ∈ I, ∀ (i j : Word N) (m : ℕ), (∀ l < m, (i.get? l).isSome ∧ i.get? l = j.get? l) →
        ‖iteratedDeriv k (Φ.dualProj i) x - iteratedDeriv k (Φ.dualProj j) x‖ ≤
          2 * C k * Φ.cmax ^ m := by
  obtain ⟨M, hM0, hM, hMd⟩ := Φ.exists_dualProj_bounds
  have hε := Φ.ε_pos
  let C (k : ℕ) : ℝ := k.factorial * M / (ε / 2) ^ k + 1
  refine ⟨C, fun k => by dsimp [C]; positivity, fun k x hx w => ?_, fun k x hx i j m hm => ?_⟩
  · exact (norm_iteratedDeriv_le_on_I hε (Φ.differentiableOn_dualProj w)
      (fun z hz => hM w z (subset_closure hz)) k hx).trans (le_add_of_nonneg_right zero_le_one)
  · have hnhd := (isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hx)
    rw [← iteratedDeriv_fun_sub (x := (x : ℂ)) (n := k)
      ((Φ.differentiableOn_dualProj i).analyticAt hnhd).contDiffAt
      ((Φ.differentiableOn_dualProj j).analyticAt hnhd).contDiffAt]
    calc ‖iteratedDeriv k (fun z => Φ.dualProj i z - Φ.dualProj j z) x‖
        ≤ k.factorial * (2 * M * Φ.cmax ^ m) / (ε / 2) ^ k :=
          norm_iteratedDeriv_le_on_I hε ((Φ.differentiableOn_dualProj i).sub (Φ.differentiableOn_dualProj j))
            (fun z hz => hMd i j m hm z (subset_closure hz)) k hx
      _ = 2 * (k.factorial * M / (ε / 2) ^ k) * Φ.cmax ^ m := by ring
      _ ≤ 2 * C k * Φ.cmax ^ m := by dsimp [C]; nlinarith [pow_nonneg Φ.cmax_nonneg m]

private theorem exists_dualProj_closeness :
    ∃ K η₀ : ℝ, 0 < η₀ ∧ ∀ a b u : List (Fin N), a.length = b.length → 0 < a.length →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        (∀ x ∈ I, ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ η) →
          ∀ x ∈ I, ‖Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)‖
            ≤ K * Φ.cmin⁻¹ ^ (2 * (a.length + u.length)) * η ^ ((1 : ℝ) / 4) := by
  obtain ⟨R, hR0, hR⟩ := Φ.exists_comp_bound
  let B (j : ℕ) : ℝ := j.factorial * R / (ε / 2) ^ j
  have hB0 : ∀ j, 0 ≤ B j := fun j => by have := Φ.ε_pos; dsimp [B]; positivity
  set Q := ∑ j ∈ Finset.range 4, B j
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => hB0 j
  have hQ : ∀ j ≤ 3, ∀ w : List (Fin N), ∀ x ∈ I, ‖iteratedDeriv j (Φ.comp w) x‖ ≤ Q := fun j hj w x hx =>
    (norm_iteratedDeriv_le_on_I Φ.ε_pos (Φ.differentiableOn_comp w)
      (fun z hz => hR w z (subset_closure hz)) j hx).trans
      (Finset.single_le_sum (fun i _ => hB0 i) (Finset.mem_range.2 (by omega)))
  obtain ⟨M, hM0, hM, -⟩ := Φ.exists_dualProj_bounds
  set c : ℝ := 1 / (4 * (2 + 2 * Q)) with hc_def
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc_def, div_le_one (by positivity)]; linarith
  refine ⟨(M + 1) * (2 + 2 * Q) ^ 2, c ^ 4, by positivity, fun a b u hab ha η hη hη0 hclose x hx => ?_⟩
  obtain ⟨i₀, -⟩ := List.exists_mem_of_length_pos ha
  have hN : 0 < N := i₀.pos
  have hcmin := Φ.cmin_pos hN
  have hcinv1 : 1 ≤ Φ.cmin⁻¹ := (one_le_inv₀ hcmin).2 ((Φ.cmin_le_cmax hN).trans Φ.cmax_lt_one.le)
  have hη1 : η ≤ 1 := hη0.trans (pow_le_one₀ hc0.le hc1)
  have h14 : η ^ ((1 : ℝ) / 4) ≤ c :=
    (Real.rpow_le_rpow hη.le hη0 (by norm_num)).trans_eq
      (by rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num)
  have h12 : η ^ ((1 : ℝ) / 2) ≤ η ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_ge hη hη1 (by norm_num)
  have hcQ : 2 * (2 + 2 * Q) * c = 1 / 2 := by rw [hc_def]; field_simp; ring
  have hJ1 : 2 * (2 + 2 * Q) * η ^ ((2 : ℝ)⁻¹ ^ 1) < 1 - 0 := by
    rw [show ((2 : ℝ)⁻¹ ^ 1) = 1 / 2 by norm_num]
    linarith [mul_le_mul_of_nonneg_left (h12.trans h14) (by positivity : (0 : ℝ) ≤ 2 * (2 + 2 * Q))]
  have hJ2 : 2 * (2 + 2 * Q) * η ^ ((2 : ℝ)⁻¹ ^ 2) < 1 - 0 := by
    rw [show ((2 : ℝ)⁻¹ ^ 2) = 1 / 4 by norm_num]
    linarith [mul_le_mul_of_nonneg_left h14 (by positivity : (0 : ℝ) ≤ 2 * (2 + 2 * Q))]
  set i := a ++ u; set j := b ++ u
  have hlen : j.length = i.length := by simp [i, j, hab]
  have hd1 := norm_iteratedDeriv_sub_le Φ.ε_pos (Φ.differentiableOn_comp i) (Φ.differentiableOn_comp j)
    1 le_rfl le_rfl hη hη1 hQ0 (fun l hl => hQ l (by omega) i) (fun l hl => hQ l (by omega) j) hJ1 hclose x hx
  have hd2 := norm_iteratedDeriv_sub_le Φ.ε_pos (Φ.differentiableOn_comp i) (Φ.differentiableOn_comp j)
    2 le_rfl le_rfl hη hη1 hQ0 (fun l hl => hQ l hl i) (fun l hl => hQ l hl j) hJ2 hclose x hx
  rw [iteratedDeriv_one, iteratedDeriv_one, show ((2 : ℝ)⁻¹ ^ 1) = 1 / 2 by norm_num] at hd1
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
    show ((2 : ℝ)⁻¹ ^ 2) = 1 / 4 by norm_num] at hd2
  have hz : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  set A := deriv (Φ.comp i) x; set B := deriv (Φ.comp j) x
  set A2 := deriv (deriv (Φ.comp i)) x; set B2 := deriv (deriv (Φ.comp j)) x
  have hBinv : ‖B‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length := by
    rw [inv_pow]; exact inv_anti₀ (pow_pos hcmin _) (hlen ▸ Φ.cmin_pow_le_norm_deriv_comp j hz)
  have hHi := Φ.dualProj_fin_reverse i hz; have hHj := Φ.dualProj_fin_reverse j hz
  set E := (2 + 2 * Q) ^ 2 * η ^ ((1 : ℝ) / 4)
  have hAB : ‖B - A‖ ≤ E := by rw [norm_sub_rev]; exact hd1.trans (mul_le_mul_of_nonneg_left h12 (by positivity))
  have hdist : ‖A2 / A - B2 / B‖ ≤ (M + 1) * E * Φ.cmin⁻¹ ^ i.length := by
    have hA : A ≠ 0 := Φ.deriv_comp_ne_zero i hz
    have hB : B ≠ 0 := Φ.deriv_comp_ne_zero j hz
    rw [show A2 / A - B2 / B = (A2 / A * (B - A) + (A2 - B2)) / B by field_simp; ring, norm_div, div_eq_mul_inv]
    refine (mul_le_mul ((norm_add_le _ _).trans (add_le_add (b := M * E) ?_ hd2)) hBinv
      (by positivity) (by positivity)).trans_eq (by ring)
    rw [norm_mul]; exact mul_le_mul (hHi ▸ hM _ _ hz) hAB (norm_nonneg _) hM0
  have hcoc : ∀ v : List (Fin N), Φ.dualProj (.fin (v ++ u).reverse) x =
      Φ.dualProj (.fin u.reverse) x + deriv (Φ.comp u) x * Φ.dualProj (.fin v.reverse) (Φ.comp u x) := fun v => by
    simpa [Word.prepend, List.reverse_append] using Φ.dualProj_prepend u.reverse (.fin v.reverse) hz
  have hdiff : A2 / A - B2 / B = deriv (Φ.comp u) x *
      (Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)) := by
    rw [← hHi, ← hHj, show i = a ++ u from rfl, show j = b ++ u from rfl, hcoc a, hcoc b]; ring
  have hu := Φ.cmin_pow_le_norm_deriv_comp u hz
  have huinv : ‖deriv (Φ.comp u) x‖⁻¹ ≤ Φ.cmin⁻¹ ^ i.length := by
    refine le_trans (b := Φ.cmin⁻¹ ^ u.length) ?_ (pow_le_pow_right₀ hcinv1 (by simp [i]))
    rw [inv_pow]; exact inv_anti₀ (pow_pos hcmin _) hu
  have hu0 : 0 < ‖deriv (Φ.comp u) x‖ := (pow_pos hcmin _).trans_le hu
  rw [show ‖Φ.dualProj (.fin a.reverse) (Φ.comp u x) - Φ.dualProj (.fin b.reverse) (Φ.comp u x)‖ =
      ‖A2 / A - B2 / B‖ * ‖deriv (Φ.comp u) x‖⁻¹ by rw [hdiff, norm_mul]; field_simp]
  exact (mul_le_mul hdist huinv (by positivity) (by positivity)).trans_eq
    (by rw [show i.length = a.length + u.length by simp [i], two_mul, pow_add]; ring)

structure CondSeq where
  a : ℕ → List (Fin N)
  b : ℕ → List (Fin N)
  u : ℕ → List (Fin N)
  η : ℕ → ℝ
  p₀ : ℝ
  length_eq : ∀ k, (a k).length = (b k).length
  length_pos : ∀ k, 0 < (a k).length
  getLast?_ne : ∀ k, (a k).getLast? ≠ (b k).getLast?
  η_pos : ∀ k, 0 < η k
  close : ∀ k, ∀ x ∈ I, ‖Φ.comp (a k ++ u k) x - Φ.comp (b k ++ u k) x‖ ≤ η k
  small : SupExpSmall (fun k => (a k).length + (u k).length) η
  length_tendsto : Tendsto (fun k => (a k).length + (u k).length) atTop atTop
  p₀_mem : p₀ ∈ I
  tendsto_p : Tendsto (fun k => Φ.compInf (u k)) atTop (𝓝 p₀)

theorem nonempty_condSeq (h : ¬ Φ.SESC) : Nonempty Φ.CondSeq := by
  have h₂ : ∀ k : ℕ, ∃ a b u : List (Fin N), a.length = b.length ∧ 0 < a.length ∧
      a.getLast? ≠ b.getLast? ∧ k ≤ a.length + u.length ∧ ∀ x ∈ I,
        ‖Φ.comp (a ++ u) x - Φ.comp (b ++ u) x‖ ≤ ((k : ℝ) + 2)⁻¹ ^ (a.length + u.length) := by
    intro k
    obtain ⟨n, hnk, i, j, hij, hlt⟩ := Φ.exists_close_pair_ge h (by positivity : 0 < ((k : ℝ) + 2)⁻¹) k
    obtain ⟨a, b, u, hi, hj, hlen, hpos, hlast⟩ :=
      List.exists_decomp_of_ne (i := List.ofFn i) (j := List.ofFn j) (by simp)
        fun h => hij (List.ofFn_injective h)
    have hn : a.length + u.length = n := by rw [← List.length_append, ← hi, List.length_ofFn]
    exact ⟨a, b, u, hlen, hpos, hlast, hn ▸ hnk, fun x hx => by
      rw [← hi, ← hj, hn]; exact (Φ.norm_le_supDist _ _ hx).trans hlt.le⟩
  choose a b u hlen hpos hlast hnk hclose using h₂
  have hsmall : SupExpSmall (fun k => (a k).length + (u k).length)
      fun k => ((k : ℝ) + 2)⁻¹ ^ ((a k).length + (u k).length) := fun θ hθ => by
    obtain ⟨m, hm⟩ := exists_nat_gt θ⁻¹
    filter_upwards [eventually_ge_atTop m] with k hk
    exact pow_le_pow_left₀ (by positivity)
      ((inv_le_comm₀ (by positivity) hθ).2 (by linarith [(by exact_mod_cast hk : (m : ℝ) ≤ k)])) _
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq (x := fun k => Φ.compInf (u k))
    fun k => by obtain ⟨hp0, hpq, hq1, -⟩ := Φ.image_comp_eq_Icc (u k); exact ⟨hp0, hpq.trans hq1⟩
  exact ⟨{
    a := a ∘ φ, b := b ∘ φ, u := u ∘ φ
    η := fun k => ((φ k : ℝ) + 2)⁻¹ ^ ((a (φ k)).length + (u (φ k)).length), p₀ := p₀
    length_eq := fun k => hlen (φ k), length_pos := fun k => hpos (φ k)
    getLast?_ne := fun k => hlast (φ k), η_pos := fun _ => by positivity
    close := fun k => hclose (φ k), small := hsmall.comp hφ.tendsto_atTop
    length_tendsto := tendsto_atTop_mono (fun k => (hφ.id_le k).trans (hnk (φ k))) tendsto_id
    p₀_mem := hp₀, tendsto_p := hlim }⟩

namespace CondSeq

variable {Φ}

noncomputable abbrev p (S : Φ.CondSeq) (k : ℕ) : ℝ := Φ.compInf (S.u k)
noncomputable abbrev q (S : Φ.CondSeq) (k : ℕ) : ℝ := Φ.compSup (S.u k)

def comp (S : Φ.CondSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) : Φ.CondSeq :=
  { a := S.a ∘ φ, b := S.b ∘ φ, u := S.u ∘ φ, η := S.η ∘ φ, p₀ := S.p₀
    length_eq := fun k => S.length_eq (φ k), length_pos := fun k => S.length_pos (φ k)
    getLast?_ne := fun k => S.getLast?_ne (φ k), η_pos := fun k => S.η_pos (φ k)
    close := fun k => S.close (φ k), small := S.small.comp hφ.tendsto_atTop
    length_tendsto := S.length_tendsto.comp hφ.tendsto_atTop
    p₀_mem := S.p₀_mem, tendsto_p := S.tendsto_p.comp hφ.tendsto_atTop }

theorem pos_N (S : Φ.CondSeq) : 0 < N :=
  ((S.a 0).head (List.ne_nil_of_length_pos (S.length_pos 0))).pos

theorem one_le_length (S : Φ.CondSeq) (k : ℕ) : 1 ≤ (S.a k).length + (S.u k).length := by
  have := S.length_pos k; omega

theorem pq_props (S : Φ.CondSeq) (k : ℕ) :
    0 ≤ S.p k ∧ S.p k < S.q k ∧ S.q k ≤ 1 ∧
      Φ.cmin ^ ((S.a k).length + (S.u k).length) ≤ S.q k - S.p k ∧
      S.q k - S.p k ≤ Φ.cmax ^ (S.u k).length := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hcmin1 : Φ.cmin ≤ 1 := (Φ.cmin_le_cmax S.pos_N).trans Φ.cmax_lt_one.le
  obtain ⟨hp0, -, hq1, hmin, hmax, -⟩ := Φ.image_comp_eq_Icc (S.u k)
  exact ⟨hp0, by linarith [pow_pos hcmin (S.u k).length], hq1,
    (pow_le_pow_of_le_one hcmin.le hcmin1 (Nat.le_add_left _ _)).trans hmin, hmax⟩

theorem mem_image (S : Φ.CondSeq) (k : ℕ) {y : ℝ} (hy : y ∈ Icc (S.p k) (S.q k)) :
    ∃ x ∈ I, (y : ℂ) = Φ.comp (S.u k) x := by
  rw [← (Φ.image_comp_eq_Icc (S.u k)).2.2.2.2.2] at hy
  obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, hx, (Φ.comp_ofReal _ hx).symm⟩

theorem comp_eq_comp (S : Φ.CondSeq) {a b : List (Fin N)} (ha : ∀ k, S.a k = a)
    (hb : ∀ k, S.b k = b) : ∀ x ∈ I, Φ.comp a x = Φ.comp b x := by
  have hcmin := Φ.cmin_pos S.pos_N
  have hz := ofReal_mem_nbhd Φ.ε_pos S.p₀_mem
  have hA := (Φ.differentiableOn_comp a).analyticOnNhd (isOpen_nbhd ε)
  have hB := (Φ.differentiableOn_comp b).analyticOnNhd (isOpen_nbhd ε)
  suffices heq : Φ.comp a =ᶠ[𝓝 (S.p₀ : ℂ)] Φ.comp b from
    fun x hx => hA.eqOn_of_preconnected_of_eventuallyEq hB (isPreconnected_nbhd ε) hz heq
      (ofReal_mem_nbhd Φ.ε_pos hx)
  by_contra hne
  have hne' : ¬ ∀ᶠ z in 𝓝 (S.p₀ : ℂ), Φ.comp a z - Φ.comp b z = 0 := by
    simpa only [Filter.EventuallyEq, sub_eq_zero] using hne
  obtain ⟨m, g, hg, hg0, hfactor⟩ :=
    ((hA _ hz).sub (hB _ hz)).exists_eventuallyEq_pow_smul_nonzero_iff.2 hne'
  let D := ‖g S.p₀‖ / 2
  have hD : 0 < D := half_pos (norm_pos_iff.2 hg0)
  have hgne : ∀ᶠ z in 𝓝 (S.p₀ : ℂ), D ≤ ‖g z‖ :=
    hg.continuousAt.norm.eventually (le_mem_nhds (half_lt_self (norm_pos_iff.2 hg0)))
  have hu : Tendsto (fun k => (S.u k).length) atTop atTop :=
    Filter.tendsto_atTop.2 fun B => (S.length_tendsto.eventually_ge_atTop (B + a.length)).mono
      fun k hk => by rw [ha k] at hk; omega
  have hwidth : Tendsto (fun k => S.q k - S.p k) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hu)
      (fun k => (sub_pos.2 (S.pq_props k).2.1).le) (fun k => (S.pq_props k).2.2.2.2)
  let r (k : ℕ) := if |S.q k - S.p₀| ≤ |S.p k - S.p₀| then S.p k else S.q k
  have hrmem : ∀ k, r k ∈ Icc (S.p k) (S.q k) := fun k => by
    dsimp [r]; split_ifs <;> exact ⟨by linarith [(S.pq_props k).2.1], by linarith [(S.pq_props k).2.1]⟩
  have hrlim : Tendsto (fun k => (r k : ℂ)) atTop (𝓝 (S.p₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_of_tendsto_of_tendsto_of_le_of_le S.tendsto_p (by simpa using hwidth.add S.tendsto_p)
        (fun k => (hrmem k).1) (fun k => (hrmem k).2))
  have hfar : ∀ k, (S.q k - S.p k) / 2 ≤ |r k - S.p₀| := fun k => by
    have ht : S.q k - S.p k ≤ |S.q k - S.p₀| + |S.p k - S.p₀| :=
      (by ring : S.q k - S.p k = (S.q k - S.p₀) + -(S.p k - S.p₀)).trans_le
        (add_le_add (le_abs_self _) (neg_le_abs _))
    dsimp [r]; split_ifs <;> linarith
  obtain ⟨k, hkfac, hkg, hksmall⟩ :=
    ((hrlim.eventually hfactor).and ((hrlim.eventually hgne).and
      ((S.small.mul_pow_rpow S.one_le_length (fun k => (S.η_pos k).le)
        ((2 : ℝ) ^ m / D) zero_le_one one_pos).eventually_lt_pow S.one_le_length (pow_pos hcmin m)))).exists
  obtain ⟨x, hx, hxy⟩ := S.mem_image k (hrmem k)
  have hclose : ‖Φ.comp a (r k) - Φ.comp b (r k)‖ ≤ S.η k := by
    rw [hxy]; simpa only [ha k, hb k, Φ.comp_append, Function.comp_apply] using S.close k x hx
  have hlower : D * (Φ.cmin ^ ((S.a k).length + (S.u k).length) / 2) ^ m ≤ S.η k := by
    refine (mul_le_mul hkg (pow_le_pow_left₀ (by positivity)
      ((div_le_div_of_nonneg_right (S.pq_props k).2.2.2.1 (by norm_num)).trans (hfar k)) _)
      (by positivity) (norm_nonneg _)).trans (le_trans (le_of_eq ?_) hclose)
    change ‖g (r k)‖ * |r k - S.p₀| ^ m = ‖(Φ.comp a - Φ.comp b) (r k)‖
    rw [hkfac, norm_smul, norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  simp only [one_pow, mul_one, Real.rpow_one] at hksmall
  rw [div_pow, ← mul_div_assoc] at hlower
  rw [← pow_mul, Nat.mul_comm, pow_mul] at hksmall
  have hlo := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).1 hlower
  have hhi := (div_lt_iff₀ hD).1 (show (2 ^ m * S.η k) / D < _ by simpa [div_mul_eq_mul_div] using hksmall)
  nlinarith

theorem exists_dualProj_eq (S₀ : Φ.CondSeq) (h : Tendsto (fun k => (S₀.a k).length) atTop atTop) :
    ∃ i j : ℕ → Fin N, i 0 ≠ j 0 ∧ ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  let d : Fin N := ⟨0, S₀.pos_N⟩
  let pad (w : List (Fin N)) (n : ℕ) : Fin N := if hn : n < w.length then w[n] else d
  obtain ⟨⟨i, j⟩, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun k => (pad (S₀.a k).reverse, pad (S₀.b k).reverse)
  have hcoord : ∀ n, ∀ᶠ k in atTop, pad (S₀.a (φ k)).reverse n = i n ∧ pad (S₀.b (φ k)).reverse n = j n := fun n => by
    have h1 := (((continuous_apply n).comp continuous_fst).tendsto (i, j)).comp hlim
    have h2 := (((continuous_apply n).comp continuous_snd).tendsto (i, j)).comp hlim
    rw [nhds_discrete, tendsto_pure] at h1 h2
    exact h1.and h2
  set S := S₀.comp φ hφ
  have hTlen : Tendsto (fun k => (S.a k).length) atTop atTop := h.comp hφ.tendsto_atTop
  have hpref : ∀ m, ∀ᶠ k in atTop, (∀ l < m, (Word.fin (S.a k).reverse).get? l = some (i l)) ∧
      (∀ l < m, (Word.fin (S.b k).reverse).get? l = some (j l)) := fun m => by
    filter_upwards [hTlen.eventually_ge_atTop m, eventually_all.2 fun l : Fin m => hcoord l] with k hk hc
    have hka : ∀ l < m, l < (S₀.a (φ k)).reverse.length := fun l hl => by
      have : m ≤ (S₀.a (φ k)).length := hk; simp; omega
    have hkb : ∀ l < m, l < (S₀.b (φ k)).reverse.length := fun l hl => by
      have : m ≤ (S₀.a (φ k)).length := hk; simp [← S₀.length_eq (φ k)]; omega
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have e := (hc ⟨l, hl⟩).1
      simp only [pad, hka l hl, ↓reduceDIte] at e
      exact (List.getElem?_eq_getElem (hka l hl)).trans (congrArg some e)
    · have e := (hc ⟨l, hl⟩).2
      simp only [pad, hkb l hl, ↓reduceDIte] at e
      exact (List.getElem?_eq_getElem (hkb l hl)).trans (congrArg some e)
  refine ⟨i, j, fun hij => ?_, ?_⟩
  · obtain ⟨k, hk1, hk2⟩ := (hpref 1).exists
    have e1 := hk1 0 one_pos; have e2 := hk2 0 one_pos
    simp only [Word.get?_fin, ← List.head?_eq_getElem?, List.head?_reverse] at e1 e2
    exact S.getLast?_ne k (by rw [e1, e2, hij])
  · have hcmin := Φ.cmin_pos S.pos_N
    have hn := S.one_le_length
    obtain ⟨K₀, η₀, hη₀, hK₀⟩ := Φ.exists_dualProj_closeness
    set η' : ℕ → ℝ := fun k => max K₀ 1 * (Φ.cmin⁻¹ ^ 2) ^ ((S.a k).length + (S.u k).length) *
      S.η k ^ ((1 : ℝ) / 4)
    have hη'pos : ∀ k, 0 < η' k := fun k => by
      have := S.η_pos k; have : 0 < max K₀ 1 := lt_max_of_lt_right one_pos; positivity
    have hη'nonneg : ∀ k, 0 ≤ η' k := fun k => (hη'pos k).le
    have hη'small : SupExpSmall (fun k => (S.a k).length + (S.u k).length) η' :=
      S.small.mul_pow_rpow hn (fun k => (S.η_pos k).le) _ (by positivity) (by norm_num)
    have hη'close : ∀ᶠ k in atTop, ∀ y ∈ Icc (S.p k) (S.q k),
        ‖Φ.dualProj (.fin (S.a k).reverse) y - Φ.dualProj (.fin (S.b k).reverse) y‖ ≤ η' k := by
      filter_upwards [S.small.eventually_le hn hη₀] with k hk y hy
      obtain ⟨x, hx, hxy⟩ := S.mem_image k hy
      rw [hxy]
      exact (hK₀ _ _ _ (S.length_eq k) (S.length_pos k) _ (S.η_pos k) hk
        (S.close k) x hx).trans (by
          rw [pow_mul]; have := S.η_pos k
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
            (by positivity))
    obtain ⟨C, hCpos, hCb, hC⟩ := Φ.exists_iteratedDeriv_bounds
    have heq : EqOn (Φ.dualProj (.inf i)) (Φ.dualProj (.inf j)) (nbhd ε) := by
      refine eqOn_nbhd_of_iteratedDeriv_close Φ.ε_pos (Φ.differentiableOn_dualProj _)
        (Φ.differentiableOn_dualProj _) S.p₀_mem S.tendsto_p fun r δ hδ => ?_
      set Q := ∑ l ∈ Finset.range (r + 2), C l
      have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun l _ => (hCpos l).le
      have hCQ : ∀ l ≤ r + 1, C l ≤ Q := fun l hl =>
        Finset.single_le_sum (fun m _ => (hCpos m).le) (Finset.mem_range.2 (by omega))
      have hs : (0 : ℝ) < (2 : ℝ)⁻¹ ^ r := by positivity
      have hδ3 : 0 < δ / 3 := by positivity
      obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 * C r * Φ.cmax ^ m ≤ δ / 3 := by
        have ht : Tendsto (fun m : ℕ => 2 * C r * Φ.cmax ^ m) atTop (𝓝 0) := by
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).const_mul (2 * C r)
        exact (ht.eventually (ge_mem_nhds hδ3)).exists
      filter_upwards [hη'small.eventually_le hn one_pos,
        (hη'small.mul_pow_rpow hn hη'nonneg (2 * (2 + 2 * Q)) zero_le_one hs).eventually_lt_pow hn hcmin,
        (hη'small.mul_pow_rpow hn hη'nonneg ((2 + 2 * Q) ^ 2) zero_le_one hs).eventually_le hn hδ3,
        hη'close, hpref m] with k h1 h2 h3 h4 ⟨h5, h6⟩
      simp only [one_pow, mul_one] at h2 h3
      obtain ⟨hp0, hpq, hq1, hcmin_le, -⟩ := S.pq_props k
      have hpI : S.p k ∈ I := ⟨hp0, hpq.le.trans hq1⟩
      have e1 := hC r _ hpI (.fin (S.a k).reverse) (.inf i) m (fun l hl => by simp [h5 l hl])
      have e2 := hC r _ hpI (.fin (S.b k).reverse) (.inf j) m (fun l hl => by simp [h6 l hl])
      have e3 := norm_iteratedDeriv_sub_le Φ.ε_pos (Φ.differentiableOn_dualProj _)
        (Φ.differentiableOn_dualProj _) r hp0 hq1 (hη'pos k) h1 hQ0
        (fun l hl x hx => (hCb l x (Icc_subset_Icc hp0 hq1 hx) _).trans (hCQ l hl))
        (fun l hl x hx => (hCb l x (Icc_subset_Icc hp0 hq1 hx) _).trans (hCQ l hl))
        (h2.trans_le hcmin_le) h4 (S.p k) (left_mem_Icc.2 hpq.le)
      set A := iteratedDeriv r (Φ.dualProj (.fin (S.a k).reverse)) (S.p k)
      set B := iteratedDeriv r (Φ.dualProj (.fin (S.b k).reverse)) (S.p k)
      set Hi := iteratedDeriv r (Φ.dualProj (.inf i)) (S.p k)
      set Hj := iteratedDeriv r (Φ.dualProj (.inf j)) (S.p k)
      calc ‖Hi - Hj‖ = ‖-(A - Hi) + (A - B) + (B - Hj)‖ := by congr 1; ring
        _ ≤ ‖-(A - Hi)‖ + ‖A - B‖ + ‖B - Hj‖ := norm_add₃_le
        _ = ‖A - Hi‖ + ‖A - B‖ + ‖B - Hj‖ := by rw [norm_neg]
        _ ≤ δ / 3 + δ / 3 + δ / 3 := by gcongr <;> linarith
        _ = δ := by ring
    exact fun x hx => heq (ofReal_mem_nbhd Φ.ε_pos hx)

end CondSeq

theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  obtain ⟨S⟩ := Φ.nonempty_condSeq hS
  by_cases hB : ∃ B, ∃ᶠ k in atTop, (S.a k).length ≤ B
  · obtain ⟨B, hB⟩ := hB
    obtain ⟨⟨a, b⟩, -, hab⟩ := exists_frequently_eq_of_frequently_mem
      ((List.finite_length_le (Fin N) B).prod (List.finite_length_le (Fin N) B))
      (f := fun k => (S.a k, S.b k))
      (hB.mono fun k hk => ⟨hk, (S.length_eq k ▸ hk : (S.b k).length ≤ B)⟩)
    obtain ⟨φ, hφ, hφab⟩ := extraction_of_frequently_atTop hab
    set T := S.comp φ hφ
    have ha : ∀ k, T.a k = a := fun k => congrArg Prod.fst (hφab k)
    have hb : ∀ k, T.b k = b := fun k => congrArg Prod.snd (hφab k)
    exact Φ.not_dualSSC_of_comp_eq (ha 0 ▸ hb 0 ▸ T.length_eq 0)
      (ha 0 ▸ hb 0 ▸ T.getLast?_ne 0) (T.comp_eq_comp ha hb) h
  · simp only [not_exists, not_frequently, not_le] at hB
    obtain ⟨i, j, hij, heq⟩ := S.exists_dualProj_eq (Filter.tendsto_atTop.2 fun B => (hB B).mono fun _ hk => hk.le)
    obtain ⟨x, hx, hne⟩ := h i j hij
    exact hne (heq x hx)

end IFS

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

noncomputable def beta : ℝ := ⨆ (x : I) (i : Fin N), ‖Φ.nonlin i ((x : ℝ) : ℂ)‖

theorem beta_nonneg : 0 ≤ Φ.beta :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_nonlin_le_beta (i : Fin N) {x : ℝ} (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  exact le_ciSup_of_le
    ⟨M, by rintro _ ⟨y, rfl⟩; exact Real.iSup_le (fun j => hM j _ (subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2))) hM0⟩
    ⟨x, hx⟩ (le_ciSup (f := fun j : Fin N => ‖Φ.nonlin j ((x : ℝ) : ℂ)‖) (finite_range _).bddAbove i)

theorem norm_dualProj_sub_nonlin_le {w : Word N} {a : Fin N} (h : w.get? 0 = some a) {x : ℝ}
    (hx : x ∈ I) : ‖Φ.dualProj w x - Φ.nonlin a x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
  have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have h0 : Φ.dualTerm w 0 x = Φ.nonlin a x := by rw [Φ.dualTerm_of_get?_eq_some h]; cases w <;> simp
  rw [dualProj, (Φ.summable_dualTerm w hxn).tsum_eq_zero_add, h0, add_sub_cancel_left, div_eq_mul_inv]
  refine tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left (Φ.beta * Φ.cmax)) fun n => ?_
  cases hn : w.get? (n + 1) with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none hn, norm_zero]
    exact mul_nonneg (mul_nonneg Φ.beta_nonneg Φ.cmax_nonneg) (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some hn, norm_mul]
    have h1 : ‖Φ.nonlin i (Φ.comp (w.take (n + 1)).reverse x)‖ ≤ Φ.beta := by
      rw [Φ.comp_ofReal _ hx]; exact Φ.norm_nonlin_le_beta i (Φ.re_comp_mem_I _ hx)
    have h2 := Φ.norm_deriv_comp_le (w.take (n + 1)).reverse hxn
    rw [List.length_reverse, length_take_of_get?_eq_some hn] at h2
    exact (mul_le_mul h1 h2 (norm_nonneg _) Φ.beta_nonneg).trans_eq (by rw [pow_succ']; ring)

theorem exists_dualProj_ne {α : ℝ} (hN : 0 < N)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} (hij : i ≠ j)
    (hlen : ∀ k, (i.get? k).isSome ↔ (j.get? k).isSome) :
    ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  classical
  have hex : ∃ k, i.get? k ≠ j.get? k := by by_contra! h; exact hij (Word.ext_get? h)
  set m := Nat.find hex
  have hm_ne : i.get? m ≠ j.get? m := Nat.find_spec hex
  have hm_some : (i.get? m).isSome ∧ (j.get? m).isSome := by
    by_contra h
    have hi0 : ¬ (i.get? m).isSome := fun h1 => h ⟨h1, (hlen m).1 h1⟩
    have hj0 : ¬ (j.get? m).isSome := fun h2 => h ⟨(hlen m).2 h2, h2⟩
    exact hm_ne ((Option.not_isSome_iff_eq_none.1 hi0).trans (Option.not_isSome_iff_eq_none.1 hj0).symm)
  obtain ⟨c, hc0⟩ := Option.isSome_iff_exists.1 hm_some.1
  obtain ⟨d, hd0⟩ := Option.isSome_iff_exists.1 hm_some.2
  have hcd : c ≠ d := fun h => hm_ne (by rw [hc0, hd0, h])
  have hm_eq : ∀ k < m, (i.get? k).isSome ∧ i.get? k = j.get? k := fun k hk =>
    ⟨Word.isSome_get?_of_lt hk hm_some.1, not_not.1 (Nat.find_min hex hk)⟩
  obtain ⟨u, i', j', hu, hi_eq, hj_eq⟩ := Word.exists_eq_prepend hm_eq
  subst hi_eq; subst hj_eq
  have hc : i'.get? 0 = some c := by have e := Word.get?_prepend_add u i' 0; rw [add_zero, hu] at e; exact e.symm.trans hc0
  have hd : j'.get? 0 = some d := by have e := Word.get?_prepend_add u j' 0; rw [add_zero, hu] at e; exact e.symm.trans hd0
  obtain ⟨y, hy, hαy⟩ := hsep c d hcd
  have hne : Φ.dualProj i' y ≠ Φ.dualProj j' y := fun heq => by
    have h1 := Φ.norm_dualProj_sub_nonlin_le hc hy
    have h2 := Φ.norm_dualProj_sub_nonlin_le hd hy
    have key := norm_sub_le_norm_sub_add_norm_sub (Φ.nonlin c y) (Φ.dualProj i' y) (Φ.nonlin d y)
    rw [norm_sub_rev (Φ.nonlin c y) (Φ.dualProj i' y), heq] at key
    rw [heq] at h1
    linarith [show 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) = 2 * (Φ.beta * Φ.cmax / (1 - Φ.cmax)) by ring]
  obtain ⟨hp, -, hq, hcmin, -, himg⟩ := Φ.image_comp_eq_Icc u.reverse
  have hpq : Φ.compInf u.reverse < Φ.compSup u.reverse :=
    sub_pos.1 ((pow_pos (Φ.cmin_pos hN) _).trans_le hcmin)
  by_contra! hall
  refine hne (eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj i')
    (Φ.differentiableOn_dualProj j') hpq (Icc_subset_Icc hp hq) (fun z hz => ?_)
    (ofReal_mem_nbhd Φ.ε_pos hy))
  rw [← himg] at hz; obtain ⟨x, hx, rfl⟩ := hz
  have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have h := hall x hx
  rw [Φ.dualProj_prepend u i' hxn, Φ.dualProj_prepend u j' hxn, add_right_inj] at h
  rw [← Φ.comp_ofReal u.reverse hx]
  exact mul_left_cancel₀ (Φ.deriv_comp_ne_zero u.reverse hxn) h

theorem proposition_1_8 (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖) :
    0 < Φ.beta ∧ (2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α →
      (∀ i j : Word N, i ≠ j → (∀ k, (i.get? k).isSome ↔ (j.get? k).isSome) →
        0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) ∧ Φ.SESC) := by
  have hbeta : 0 < Φ.beta := by
    obtain ⟨x, hx, hαx⟩ := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    linarith [Φ.norm_nonlin_le_beta ⟨0, by omega⟩ hx, Φ.norm_nonlin_le_beta ⟨1, by omega⟩ hx,
      norm_sub_le (Φ.nonlin ⟨0, by omega⟩ x) (Φ.nonlin ⟨1, by omega⟩ x)]
  refine ⟨hbeta, fun hlt => ?_⟩
  have hpos : ∀ i j : Word N, i ≠ j → (∀ k, (i.get? k).isSome ↔ (j.get? k).isSome) →
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖ := fun i j hij hlen => by
    obtain ⟨x, hx, hne⟩ := Φ.exists_dualProj_ne (by omega) hsep hlt hij hlen
    obtain ⟨M, -, hM, -⟩ := Φ.exists_dualProj_bounds
    exact (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le (le_ciSup
      (f := fun x : I => ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖)
      ⟨M + M, by rintro _ ⟨y, rfl⟩; have hyn := subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2)
                 exact (norm_sub_le _ _).trans (add_le_add (hM i _ hyn) (hM j _ hyn))⟩
      ⟨x, hx⟩)
  exact ⟨hpos, Φ.theorem_2_2 fun i j hij =>
    Φ.exists_dualProj_ne (by omega) hsep hlt (fun hw => hij (congrFun (Word.inf.inj hw) 0)) (fun _ => by simp)⟩

end IFS


lemma fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

lemma deriv_exampleMaps :
    deriv (exampleMaps 0) = (fun _ => 1 / 8) ∧
    deriv (exampleMaps 1) = (fun z => 1 / 8 + z / 16) ∧
    deriv (exampleMaps 2) = (fun z => 1 / 16 + z / 16) :=
  ⟨funext fun z => ((hasDerivAt_id' z).div_const 8).deriv,
   funext fun z => ((((hasDerivAt_id' z).div_const 8).fun_add
     (((hasDerivAt_id' z).fun_pow 2).div_const 32)).congr_deriv (by push_cast; ring)).deriv,
   funext fun z => (((((hasDerivAt_id' z).div_const 16).fun_add
     (((hasDerivAt_id' z).fun_pow 2).div_const 32)).add_const (29 / 32 : ℂ)).congr_deriv
     (by push_cast; ring)).deriv⟩

private lemma example_norm_deriv_le (i : Fin 3) {z : ℂ} (hz : z ∈ closure (nbhd (1 / 100))) :
    ‖deriv (exampleMaps i) z‖ ≤ 19 / 100 ∧ deriv (exampleMaps i) z ≠ 0 := by
  obtain ⟨x, hx, hzx⟩ := exists_mem_I_norm_sub_le (by norm_num) hz
  have h1 := norm_sub_norm_le z x
  have h2 := Complex.abs_re_le_norm (z - x)
  rw [Complex.norm_real, Real.norm_of_nonneg hx.1] at h1
  rw [Complex.sub_re, Complex.ofReal_re] at h2
  have hn : ‖z‖ ≤ 101 / 100 := by linarith [hx.2]
  have hre : -(1 / 100) ≤ z.re := by linarith [neg_abs_le (z.re - x), hx.1]
  obtain ⟨d0, d1, d2⟩ := deriv_exampleMaps
  have hbd : ∀ c : ℝ, 0 ≤ c → c ≤ 1 / 8 → ‖(c : ℂ) + z / 16‖ ≤ 19 / 100 := fun c hc0 hc => by
    calc ‖(c : ℂ) + z / 16‖ ≤ ‖(c : ℂ)‖ + ‖z / 16‖ := norm_add_le _ _
      _ = c + ‖z‖ / 16 := by rw [Complex.norm_real, Real.norm_of_nonneg hc0, norm_div]; norm_num
      _ ≤ 19 / 100 := by linarith
  have hne : ∀ c : ℝ, 1 / 1600 < c → (c : ℂ) + z / 16 ≠ 0 := fun c hc h => by
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.zero_re] at h'
    linarith
  rcases fin3 i with rfl | rfl | rfl
  · rw [d0]; constructor <;> norm_num
  · rw [d1]; exact ⟨by simpa using hbd (1 / 8) (by norm_num) le_rfl, by simpa using hne (1 / 8) (by norm_num)⟩
  · rw [d2]; exact ⟨by simpa using hbd (1 / 16) (by norm_num) (by norm_num), by simpa using hne (1 / 16) (by norm_num)⟩

theorem exampleMaps_inClass (i : Fin 3) : InClass (1 / 100) (exampleMaps i) :=
  inClass_of_deriv (by norm_num)
    (by rcases fin3 i with rfl | rfl | rfl <;> dsimp [exampleMaps] <;> fun_prop)
    (fun x _ => by rcases fin3 i with rfl | rfl | rfl <;> simp [exampleMaps, sq])
    (fun x hx => by
      obtain ⟨h0, h1⟩ := hx
      rcases fin3 i with rfl | rfl | rfl <;> simp [exampleMaps, sq] <;> constructor <;> nlinarith)
    (fun z hz => (example_norm_deriv_le i hz).2)
    (fun z hz => (example_norm_deriv_le i hz).1.trans_lt (by norm_num))

noncomputable def exampleIFS : IFS 3 (1 / 100) := ⟨exampleMaps, by norm_num, exampleMaps_inClass⟩

theorem exampleIFS_cmax_lt : exampleIFS.cmax < 1 / 5 := by
  have : Nonempty (closure (nbhd (1 / 100 : ℝ))) := ⟨⟨0, zero_mem_closure_nbhd (by norm_num)⟩⟩
  exact (ciSup_le fun i => ciSup_le fun z => (example_norm_deriv_le i z.2).1).trans_lt (by norm_num)

private lemma exampleIFS_nonlin_eq :
    (∀ z, exampleIFS.nonlin 0 z = 0) ∧
    (∀ z, exampleIFS.nonlin 1 z = 1 / 16 / (1 / 8 + z / 16)) ∧
    (∀ z, exampleIFS.nonlin 2 z = 1 / 16 / (1 / 16 + z / 16)) := by
  obtain ⟨d0, d1, d2⟩ := deriv_exampleMaps
  exact ⟨fun z => by simp [IFS.nonlin, exampleIFS, d0],
    fun z => by simp [IFS.nonlin, exampleIFS, d1],
    fun z => by simp [IFS.nonlin, exampleIFS, d2]⟩

theorem exampleIFS_beta_le : exampleIFS.beta ≤ 1 := by
  obtain ⟨n0, n1, n2⟩ := exampleIFS_nonlin_eq
  have : Nonempty I := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  refine ciSup_le fun x => ciSup_le fun i => ?_
  have hx0 := x.2.1
  rcases fin3 i with rfl | rfl | rfl
  · simp [n0]
  · rw [n1, show (1 / 16 : ℂ) / (1 / 8 + (x : ℂ) / 16) = ((1 / 16 / (1 / 8 + (x : ℝ) / 16) : ℝ) : ℂ)
      by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_le_one (by positivity)]
    linarith
  · rw [n2, show (1 / 16 : ℂ) / (1 / 16 + (x : ℂ) / 16) = ((1 / 16 / (1 / 16 + (x : ℝ) / 16) : ℝ) : ℂ)
      by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_le_one (by positivity)]
    linarith

theorem exampleIFS_sesc : exampleIFS.SESC := by
  obtain ⟨n0, n1, n2⟩ := exampleIFS_nonlin_eq
  have val : ∀ k : Fin 3, exampleIFS.nonlin k 0 = ((![0, 1 / 2, 1] k : ℝ) : ℂ) := fun k => by
    rcases fin3 k with rfl | rfl | rfl <;> [simp [n0]; (rw [n1]; norm_num); (rw [n2]; norm_num)]
  have hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ x ∈ I, (1 / 2 : ℝ) ≤ ‖exampleIFS.nonlin i x - exampleIFS.nonlin j x‖ := fun i j hij => by
    refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [Complex.ofReal_zero, val i, val j, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rcases fin3 i with rfl | rfl | rfl <;> rcases fin3 j with rfl | rfl | rfl <;>
      first | exact absurd rfl hij | norm_num
  obtain ⟨_, h⟩ := exampleIFS.proposition_1_8 (by norm_num) (by norm_num) hsep
  have hc := exampleIFS_cmax_lt
  have hc0 := exampleIFS.cmax_nonneg
  have hb := exampleIFS_beta_le
  exact (h ((div_lt_iff₀ (by linarith)).2 (by nlinarith))).2

end AnalyticESC
