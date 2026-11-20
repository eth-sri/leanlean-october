module

public import AnalyticESC.Separation
public import AnalyticESC.Main.Closeness

@[expose] public section

/-!
# Condensation

Remove the common suffix of a super-exponentially close pair, and extend both remainders
on the left so that their lengths tend to infinity. The finite dual projections then
converge along a subsequence, and their difference vanishes on the interval by analyticity.
-/

namespace AnalyticESC.IFS

open Set Metric Filter Topology

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Dual strong separation implies strong exponential separation. -/
theorem theorem_2_2 (h : Φ.DualSSC) : Φ.SESC := by
  by_contra hS
  have h₁ : ∀ c > 0, ∃ n, ∃ i j : Fin n → Fin N, i ≠ j ∧
      Φ.supDist (List.ofFn i) (List.ofFn j) < c ^ n := by simpa [SESC, Challenge.SESC, not_le] using hS
  have h₂ (k : ℕ) : ∃ (a b u : List (Fin N)) (c d : Fin N), c ≠ d ∧ k ≤ a.length ∧ k ≤ b.length ∧
      ∀ x ∈ I, ‖Φ.comp ((c :: a).reverse ++ u) x - Φ.comp ((d :: b).reverse ++ u) x‖ ≤
        (1 / ((k : ℝ) + 1)) ^ ((d :: b).length + u.length) := by
    let θ := 1 / ((k : ℝ) + 1)
    obtain ⟨n, i, j, hij, hlt⟩ := h₁ (θ^(k+1)) (by positivity)
    -- The common prefix of the reversed words is the suffix we cancel.
    let v := (List.ofFn i).reverse
    let w := (List.ofFn j).reverse
    obtain ⟨m, c, d, he, hc, hd, hcd⟩ := Word.exists_prefix_first_ne
      (v := .fin v) (w := .fin w) (by simpa [v, w] using hij) (Word.sameLength_fin (by simp [v, w]))
    let a := v.drop (m + 1)
    let b := w.drop (m + 1)
    let u := (v.take m).reverse
    have split (l : List (Fin N)) (c : Fin N) (h : l[m]? = some c) :
        l.reverse = (c :: l.drop (m + 1)).reverse ++ (l.take m).reverse := by
      obtain ⟨hl, hs⟩ := List.getElem?_eq_some_iff.1 h
      aesop
    have hi : List.ofFn i = (c :: a).reverse ++ u := by simpa [a, u, v] using split v c hc
    have hj : List.ofFn j = (d :: b).reverse ++ u := by
      change v.take m = w.take m at he
      simpa [b, u, w, ← he] using split w d hd
    have hl := congrArg List.length hj
    simp at hl
    have hk : k ≤ k*n := Nat.le_mul_of_pos_right k (by omega)
    let l := List.replicate (k*n) c
    refine ⟨a++l, b++l, u, c, d, hcd, ?_, ?_, fun x hx => ?_⟩
    · simp [l]; omega
    · simp [l]; omega
    · change ‖Φ.comp (((c::a)++l).reverse ++ u) x - Φ.comp (((d::b)++l).reverse ++ u) x‖ ≤ θ ^ _
      rw [show (d::(b++l)).length + u.length = (k+1)*n by simp [l, Nat.add_mul]; omega, pow_mul]
      simp only [List.reverse_append, List.append_assoc, ← hi, ← hj, Φ.comp_append, Function.comp_apply]
      have H := Φ.norm_comp_sub_le l.reverse
        (Φ.mapsTo_comp_closure (List.ofFn i) (Φ.real_mem_closed hx))
        (Φ.mapsTo_comp_closure (List.ofFn j) (Φ.real_mem_closed hx))
      exact (H.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ Φ.cmax_nonneg Φ.cmax_lt_one.le))).trans
        ((Φ.norm_le_supDist _ _ hx).trans hlt.le)
  choose a' b' u c d hcd ha hb hclose using h₂
  let a k := c k :: a' k
  let b k := d k :: b' k
  let n k := (b k).length + (u k).length
  have hn : Tendsto n atTop atTop := tendsto_atTop_mono (fun k => by have := hb k; simp [n, b]; omega) tendsto_id
  let pad (l : List (Fin N)) (k : ℕ) := l[k]?.getD (c 0)
  have hN := (c 0).pos
  let i k := pad (a k)
  let j k := pad (b k)
  choose p q hp hpq hq hwidth himg using fun k => Φ.exists_Icc_subset_image_comp (u k)
  obtain ⟨⟨v, w, x₀⟩, σ, hσ, hsubseq⟩ := CompactSpace.tendsto_subseq fun k =>
    (i k, j k, (⟨p k, hp k, (hpq k).trans (hq k)⟩ : I))
  simp only [nhds_prod_eq] at hsubseq
  have hv := hsubseq.fst
  have hw := hsubseq.snd.fst
  obtain ⟨k, hv₀, hw₀⟩ := ((Word.eventually_eq_letter hv 0).and (Word.eventually_eq_letter hw 0)).exists
  have hvw : v 0 ≠ w 0 := by grind
  obtain ⟨x, hx, hne⟩ := h v w hvw
  obtain ⟨R, hR₀, hR⟩ := Φ.exists_comp_bound
  obtain ⟨M, hM₀, hM⟩ := Φ.exists_norm_dualProj_le
  have width k : Φ.cmin ^ n k ≤ q k - p k :=
    (pow_le_pow_of_le_one Φ.cmin_nonneg (Φ.cmin_lt_one hN).le (Nat.le_add_left ..)).trans (hwidth k)
  have inside k  := Icc_subset_Icc (hp k) (hq k)
  let G k := Φ.comp (a k).reverse - Φ.comp (b k).reverse
  have hG k : DifferentiableOn ℂ (G k) (nbhd ε) :=
    (Φ.differentiableOn_comp _).sub (Φ.differentiableOn_comp _)
  have hs : SuperExpOn n (fun k => Icc (p k) (q k)) G := fun θ hθ => by
    refine ⟨1, zero_le_one, ?_⟩
    simp only [one_mul]
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hθ)] with k hk x hx
    obtain ⟨y, hy, rfl⟩ := himg k hx
    simpa only [G, Pi.sub_apply, ← Φ.comp_ofReal _ hy, comp_append, Function.comp_apply] using
      (hclose k y hy).trans (by bound)
  have jet := hs.jet Φ.ε_pos (Φ.cmin_pos hN) (by positivity) hG
    (fun k z hz => sub_le_twice (hR _ _ (subset_closure hz)) (hR _ _ (subset_closure hz))) inside width
  let F k := Φ.dualProj (.fin (a k)) - Φ.dualProj (.fin (b k))
  let g := Φ.dualProj (.inf v) - Φ.dualProj (.inf w)
  -- Passing to logarithmic derivatives costs at most an exponential factor.
  have hF : SuperExpOn n (fun k => Icc (p k) (q k)) F := by
    intro θ hθ
    have hc := Φ.cmin_pos hN
    let δ := θ * Φ.cmin
    have hδ : 0 < δ := by positivity
    obtain ⟨C₁, hC₁, H₁⟩ := jet 1 δ hδ
    obtain ⟨C₂, hC₂, H₂⟩ := jet 2 δ hδ
    refine ⟨C₂ + M * C₁, by positivity, ?_⟩
    filter_upwards [H₁, H₂] with k h₁ h₂ y hy
    let f := Φ.comp (a k).reverse
    let e := Φ.comp (b k).reverse
    let A := Φ.dualProj (.fin (a k)) y
    let B := Φ.dualProj (.fin (b k)) y
    have hz := Φ.real_mem_closed (inside k hy)
    have hj j : iteratedDeriv j (G k) y = iteratedDeriv j f y - iteratedDeriv j e y :=
      iteratedDeriv_sub (Φ.analyticAt_comp _ hz).contDiffAt (Φ.analyticAt_comp _ hz).contDiffAt
    specialize h₁ y hy
    specialize h₂ y hy
    simp only [hj, iteratedDeriv_succ, iteratedDeriv_zero] at h₁ h₂
    have he (v : List (Fin N)) : Φ.dualProj (.fin v) y * deriv (Φ.comp v.reverse) y =
        deriv (deriv (Φ.comp v.reverse)) y := by
      simpa using (eq_div_iff (Φ.deriv_comp_ne_zero _ hz)).1 (Φ.dualProj_fin_reverse v.reverse hz)
    have hab : ‖A - B‖ * ‖deriv e y‖ ≤ (C₂ + M * C₁) * (δ ^ n k) := by
      rw [← norm_mul, show (A - B) * deriv e y =
        (deriv (deriv f) y - deriv (deriv e) y) - A * (deriv f y - deriv e y) by
          linear_combination he (a k) - he (b k)]
      rw [add_mul, mul_assoc]
      refine (norm_sub_le ..).trans (add_le_add h₂ ?_)
      rw [norm_mul]
      bound
    have hp := (pow_le_pow_of_le_one Φ.cmin_nonneg (Φ.cmin_lt_one hN).le
      (show (b k).reverse.length ≤ n k by simp [n])).trans ((Φ.norm_deriv_comp_bounds (b k).reverse hz).1)
    apply (mul_le_mul_iff_left₀ (pow_pos hc (n k))).1
    change ‖A - B‖ * Φ.cmin ^ n k ≤ _
    rw [mul_assoc, ← mul_pow]
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans hab
  have hconv {a : ℕ → List (Fin N)} {v : ℕ → Fin N} (ha : ∀ k, k ≤ (a k).length)
      (h : Tendsto (fun k => pad (a (σ k))) atTop (𝓝 v)) :
      TendstoUniformlyOn (fun k => Φ.dualProj (.fin (a (σ k)))) (Φ.dualProj (.inf v)) atTop (closedNbhd ε) := by
    apply Φ.tendstoUniformlyOn_dualProj (a := fun k => .fin (a (σ k))) (w := v)
    intro l
    filter_upwards [eventually_all.2 fun i : Fin l => Word.eventually_eq_letter h i,
      hσ.tendsto_atTop.eventually (eventually_ge_atTop l)] with k hk hl
    apply Word.take_eq_of_get?_eq
    intro n hn
    simpa [pad, List.getElem?_eq_getElem (hn.trans_le (hl.trans (ha _)))] using congrArg some (hk ⟨n, hn⟩)
  have hlim := ((hconv (a := a) (by tauto) hv).sub
    (hconv (a := b) (by tauto) hw)).mono subset_closure
  have hd (k : ℕ) : DifferentiableOn ℂ (F k) (nbhd ε) :=
    (Φ.differentiableOn_dualProj _).sub (Φ.differentiableOn_dualProj _)
  have hg : DifferentiableOn ℂ g (nbhd ε) :=
    (Φ.differentiableOn_dualProj _).sub (Φ.differentiableOn_dualProj _)
  have hU := isOpen_nbhd ε
  have hl (j : ℕ) : TendstoLocallyUniformlyOn (fun k => iteratedDeriv j (F (σ k)))
      (iteratedDeriv j g) atTop (nbhd ε) := by
    induction j with
    | zero => exact hlim.tendstoLocallyUniformlyOn
    | succ j ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        (ih.deriv (.of_forall fun k => (hd (σ k)).iteratedDeriv_complex hU j) hU)
  have hx₀ := Φ.real_mem_open x₀.2
  have hp' : Tendsto (fun k => (p (σ k) : ℂ)) atTop (𝓝[nbhd ε] (x₀ : ℂ)) := by
    rw [hU.nhdsWithin_eq hx₀]
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.comp hsubseq.snd.snd
  have hj := hF.jet Φ.ε_pos (Φ.cmin_pos hN) (by positivity) hd
    (fun k z hz => sub_le_twice (hM _ _ (subset_closure hz)) (hM _ _ (subset_closure hz))) inside width
  have hvanish j : iteratedDeriv j g (x₀ : ℂ) = 0 := by
    obtain ⟨C, hC, hsmall⟩ := hj j (1 / 2) (by norm_num)
    have hz := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)).const_mul C).comp (hn.comp hσ.tendsto_atTop)
    have hle := le_of_tendsto_of_tendsto
      ((hl j).tendsto_comp ((hg.iteratedDeriv_complex hU j).continuousOn _ hx₀) hx₀ hp').norm
      (by simpa [Function.comp_def] using hz)
      ((hσ.tendsto_atTop.eventually hsmall).mono fun k hk => hk _ (left_mem_Icc.2 (hpq _)))
    simpa using hle
  have han := hg.analyticOnNhd hU
  have heq := analyticOrderAt_eq_top.1 (ENat.eq_top_iff_forall_ge.2 fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han _ hx₀)).2 fun j _ => hvanish j)
  exact hne (sub_eq_zero.1 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_nbhd ε) hx₀ heq (Φ.real_mem_open hx)))

end AnalyticESC.IFS
