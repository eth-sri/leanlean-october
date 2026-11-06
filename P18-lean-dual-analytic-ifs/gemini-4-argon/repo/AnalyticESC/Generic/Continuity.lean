module

public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Lemma 2.7

The dual natural projection depends Lipschitz-continuously on the system in the `𝒞²` metric,
uniformly in the word (2.6), so the strong separation of the dual is an open condition.

We write `f_i = Φ.f i`, `g_i = Ψ.f i` and `d = d₂(Φ, Ψ)`, with `Φ ∈ 𝔖_N(ε)` and `Ψ ∈ 𝔖_N(ε')`
for arbitrary `ε, ε' > 0`; all constants depend on `Φ` only. The estimates (2.3)–(2.5) are proved
at the real points of `I`, where all compositions take values in `I`. Since `d₂(Φ, Ψ)` small does
not give `|g_i'| ≤ c_max`, the contraction ratio of `Ψ` on `I` is bounded by `c' = c_max + δ₀ < 1`
and `|g_i'|` from below by `c_min / 2`. Auxiliary results are in the namespace `IFS.Continuity`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS.Continuity

/-! ## The real points of `I` in `ℂ` -/

theorem image_I_subset_nbhd {δ : ℝ} (hδ : 0 < δ) : ((↑) : ℝ → ℂ) '' I ⊆ nbhd δ := by
  rintro _ ⟨y, hy, rfl⟩
  exact ofReal_mem_nbhd hδ hy

theorem ofReal_mem_closure {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : x ∈ I) :
    (x : ℂ) ∈ closure (nbhd δ) :=
  subset_closure (ofReal_mem_nbhd hδ hx)

/-- `f_i''/f_i'` is uniformly Lipschitz on `I`. -/
private theorem exists_lipschitz_nonlin {N : ℕ} {ε : ℝ} (Φ : IFS N ε) :
    ∃ L, 0 ≤ L ∧ ∀ i, ∀ a ∈ I, ∀ b ∈ I,
      ‖Φ.nonlin i (a : ℂ) - Φ.nonlin i (b : ℂ)‖ ≤ L * ‖(a : ℂ) - b‖ := by
  have hIU : ((↑) : ℝ → ℂ) '' I ⊆ nbhd ε := image_I_subset_nbhd Φ.ε_pos
  have hd (i : Fin N) : DifferentiableOn ℂ (Φ.nonlin i) (nbhd ε) :=
    fun _ hz => (Φ.differentiableAt_nonlin i (subset_closure hz)).differentiableWithinAt
  choose L hL using fun i => isCompact_image_I.exists_bound_of_continuousOn
    (((hd i).deriv (isOpen_nbhd ε)).continuousOn.mono hIU)
  refine ⟨∑ i, max (L i) 0, Finset.sum_nonneg fun _ _ => le_max_right _ _, fun i a ha b hb => ?_⟩
  exact (Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => Φ.differentiableAt_nonlin i (subset_closure (hIU hz)))
    (fun z hz => (hL i z hz).trans (le_max_left _ _))
    ((convex_Icc (0 : ℝ) 1).linear_image Complex.ofRealCLM.toLinearMap)
    (mem_image_of_mem _ hb) (mem_image_of_mem _ ha)).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => max (L j) 0) (fun _ _ => le_max_right _ _)
        (Finset.mem_univ i)) (norm_nonneg _))

theorem bddAbove_range_norm_sub {F G : ℂ → ℂ}
    (hF : ContinuousOn F (((↑) : ℝ → ℂ) '' I)) (hG : ContinuousOn G (((↑) : ℝ → ℂ) '' I)) :
    BddAbove (range fun x : I => ‖F ((x : ℝ) : ℂ) - G ((x : ℝ) : ℂ)‖) := by
  have hU (x : I) : ((x : ℝ) : ℂ) ∈ ((↑) : ℝ → ℂ) '' I := mem_image_of_mem _ x.2
  have h1 : Continuous fun x : I => ((x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  exact (isCompact_range ((hF.comp_continuous h1 hU).sub (hG.comp_continuous h1 hU)).norm).bddAbove

variable {N : ℕ} {ε ε' : ℝ}

theorem continuousOn_f_deriv (Φ : IFS N ε) (i : Fin N) :
    ContinuousOn (Φ.f i) (((↑) : ℝ → ℂ) '' I) ∧
      ContinuousOn (deriv (Φ.f i)) (((↑) : ℝ → ℂ) '' I) ∧
      ContinuousOn (deriv (deriv (Φ.f i))) (((↑) : ℝ → ℂ) '' I) := by
  have hIU := image_I_subset_nbhd (by linarith [Φ.ε_pos] : 0 < 2 * ε)
  have hO := isOpen_nbhd (2 * ε)
  have hf := Φ.differentiableOn_f i
  exact ⟨hf.continuousOn.mono hIU, (hf.deriv hO).continuousOn.mono hIU,
    ((hf.deriv hO).deriv hO).continuousOn.mono hIU⟩

/-! ## Pointwise bounds from `d₂` -/

theorem d2_nonneg (Φ : IFS N ε) (Ψ : IFS N ε') : 0 ≤ d2 Φ Ψ :=
  Real.iSup_nonneg fun _ => add_nonneg (add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_nonneg fun _ => norm_nonneg _)) (Real.iSup_nonneg fun _ => norm_nonneg _)

/-- At a point of `I`, the maps, their derivatives and their second derivatives differ by at
most `d₂(Φ, Ψ)`. -/
theorem norm_sub_le_d2 (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.f i x - Ψ.f i x‖ ≤ d2 Φ Ψ ∧ ‖deriv (Φ.f i) x - deriv (Ψ.f i) x‖ ≤ d2 Φ Ψ ∧
      ‖deriv (deriv (Φ.f i)) x - deriv (deriv (Ψ.f i)) x‖ ≤ d2 Φ Ψ := by
  obtain ⟨hf0, hf1, hf2⟩ := continuousOn_f_deriv Φ i
  obtain ⟨hg0, hg1, hg2⟩ := continuousOn_f_deriv Ψ i
  have key {F G : ℂ → ℂ} (hF : ContinuousOn F (((↑) : ℝ → ℂ) '' I))
      (hG : ContinuousOn G (((↑) : ℝ → ℂ) '' I)) :
      ‖F x - G x‖ ≤ ⨆ y : I, ‖F ((y : ℝ) : ℂ) - G ((y : ℝ) : ℂ)‖ :=
    le_ciSup (f := fun y : I => ‖F ((y : ℝ) : ℂ) - G ((y : ℝ) : ℂ)‖)
      (bddAbove_range_norm_sub hF hG) ⟨x, hx⟩
  have e0 := key hf0 hg0
  have e1 := key hf1 hg1
  have e2 := key hf2 hg2
  have n0 := (norm_nonneg _).trans e0
  have n1 := (norm_nonneg _).trans e1
  have n2 := (norm_nonneg _).trans e2
  have hd : d2Map (Φ.f i) (Ψ.f i) ≤ d2 Φ Ψ :=
    le_ciSup (f := fun i => d2Map (Φ.f i) (Ψ.f i)) (finite_range _).bddAbove i
  unfold d2Map at hd
  exact ⟨by linarith, by linarith, by linarith⟩

/-! ## The estimates (2.3)–(2.5) -/

/-- (2.4): `|f_v(x) - g_v(x)| ≤ d / (1 - c_max)` on `I`. -/
private theorem norm_comp_sub_comp_le (Φ : IFS N ε) (Ψ : IFS N ε') (v : List (Fin N)) {x : ℝ}
    (hx : x ∈ I) :
    ‖((Φ.comp v x).re : ℂ) - (Ψ.comp v x).re‖ ≤ d2 Φ Ψ / (1 - Φ.cmax) := by
  have hc := Φ.cmax_lt_one
  have hc0 := Φ.cmax_nonneg
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  induction v with
  | nil => simp only [comp_nil, id, sub_self, norm_zero]; positivity
  | cons i u ih =>
    set a := (Φ.comp u x).re
    set b := (Ψ.comp u x).re
    have ha := Φ.re_comp_mem_I u hx
    have hb := Ψ.re_comp_mem_I u hx
    rw [ ← Φ.comp_ofReal (i :: u) hx, ← Ψ.comp_ofReal (i :: u) hx, comp_cons, comp_cons,
      Function.comp_apply, Function.comp_apply, Φ.comp_ofReal u hx, Ψ.comp_ofReal u hx]
    have h1 : ‖Φ.f i a - Φ.f i b‖ ≤ Φ.cmax * ‖(a : ℂ) - b‖ := by
      simpa [comp_cons, comp_nil] using
        Φ.norm_comp_sub_le [i] (ofReal_mem_nbhd Φ.ε_pos ha) (ofReal_mem_nbhd Φ.ε_pos hb)
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add (h1.trans (mul_le_mul_of_nonneg_left ih hc0))
        (norm_sub_le_d2 Φ Ψ i hb).1).trans_eq (by field_simp; ring))

private theorem norm_mul_sub_mul_le {u₁ u₂ v₁ v₂ : ℂ} {A B C D : ℝ} (hA : 0 ≤ A)
    (hu : ‖u₁‖ ≤ A) (huv : ‖u₁ - u₂‖ ≤ B) (hv : ‖v₁ - v₂‖ ≤ C) (hv₂ : ‖v₂‖ ≤ D) :
    ‖u₁ * v₁ - u₂ * v₂‖ ≤ A * C + B * D := by
  rw [show u₁ * v₁ - u₂ * v₂ = u₁ * (v₁ - v₂) + (u₁ - u₂) * v₂ by ring]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_mul u₁ _ ▸ mul_le_mul hu hv (norm_nonneg _) hA)
    (norm_mul _ v₂ ▸ mul_le_mul huv hv₂ (norm_nonneg _) ((norm_nonneg _).trans huv)))

/-- `|g_v'(x)| ≤ c'^{|v|}` on `I` if `|g_i'| ≤ c'` on `I` for all `i`. -/
private theorem norm_deriv_comp_le_pow (Ψ : IFS N ε) {c' : ℝ} (hc'0 : 0 ≤ c')
    (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c') (v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Ψ.comp v) x‖ ≤ c' ^ v.length := by
  induction v with
  | nil => simp [comp_nil]
  | cons i u ih =>
    rw [Ψ.deriv_comp_cons i u (ofReal_mem_closure Ψ.ε_pos hx), Ψ.comp_ofReal u hx, norm_mul,
      List.length_cons, pow_succ']
    exact mul_le_mul (hc' i _ (Ψ.re_comp_mem_I u hx)) ih (norm_nonneg _) hc'0

/-- (2.5): `|f_v'(x) - g_v'(x)| ≤ |v| c'^{|v|} K d` on `I`, with
`K = (M / (1 - c_max) + 1) / c'` and `M` a bound on `f_i''/f_i'` on `cl B_ε`. -/
private theorem norm_deriv_comp_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {c' M : ℝ} (hc'0 : 0 < c')
    (hcc' : Φ.cmax ≤ c') (hc' : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c') (hM0 : 0 ≤ M)
    (hM : ∀ i, ∀ z ∈ closure (nbhd ε), ‖Φ.nonlin i z‖ ≤ M)
    (v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖deriv (Φ.comp v) x - deriv (Ψ.comp v) x‖ ≤
      v.length * c' ^ v.length * ((M / (1 - Φ.cmax) + 1) / c') * d2 Φ Ψ := by
  have hc := Φ.cmax_lt_one
  have hd := d2_nonneg Φ Ψ
  have hc1 : 0 < 1 - Φ.cmax := by linarith
  have hxc := ofReal_mem_closure Φ.ε_pos hx
  have hxc' := ofReal_mem_closure Ψ.ε_pos hx
  induction v with
  | nil => simp [comp_nil]
  | cons i u ih =>
    set a := (Φ.comp u x).re
    set b := (Ψ.comp u x).re
    have ha := Φ.re_comp_mem_I u hx
    have hb := Ψ.re_comp_mem_I u hx
    rw [Φ.deriv_comp_cons i u hxc, Ψ.deriv_comp_cons i u hxc', Φ.comp_ofReal u hx, Ψ.comp_ofReal u hx]
    set K := (M / (1 - Φ.cmax) + 1) / c' with hK
    have hA : ‖deriv (Φ.f i) a‖ ≤ c' :=
      (Φ.norm_deriv_le_cmax i (ofReal_mem_closure Φ.ε_pos ha)).trans hcc'
    have hB : ‖deriv (Φ.f i) a - deriv (Ψ.f i) b‖ ≤ K * c' * d2 Φ Ψ :=
      (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        ((add_le_add ((Φ.norm_deriv_f_sub_le (hM i) ha hb).trans
          (mul_le_mul_of_nonneg_left (norm_comp_sub_comp_le Φ Ψ u hx) hM0))
          (norm_sub_le_d2 Φ Ψ i hb).2.1).trans_eq (by rw [hK]; field_simp))
    exact (norm_mul_sub_mul_le hc'0.le hA hB ih
      (norm_deriv_comp_le_pow Ψ hc'0.le hc' u hx)).trans_eq
      (by simp only [List.length_cons]; push_cast; ring)

/-- (2.3): `|f_i''/f_i' - g_i''/g_i'| ≤ (1 + M) / m · d` on `I`, if `|g_i'| ≥ m > 0` on `I` and
`M` bounds `f_i''/f_i'` on `I`. -/
private theorem norm_nonlin_sub_le (Φ : IFS N ε) (Ψ : IFS N ε') {m M : ℝ} (hm : 0 < m) (hM0 : 0 ≤ M)
    (hgm : ∀ i, ∀ y ∈ I, m ≤ ‖deriv (Ψ.f i) (y : ℂ)‖)
    (hM : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M) (i : Fin N) {y : ℝ} (hy : y ∈ I) :
    ‖Φ.nonlin i y - Ψ.nonlin i y‖ ≤ (1 + M) / m * d2 Φ Ψ := by
  have hf := (Φ.inClass i).deriv_ne_zero _ (ofReal_mem_closure Φ.ε_pos hy)
  have hg := (Ψ.inClass i).deriv_ne_zero _ (ofReal_mem_closure Ψ.ε_pos hy)
  obtain ⟨-, h1, h2⟩ := norm_sub_le_d2 Φ Ψ i hy
  have hnum : ‖(deriv (deriv (Φ.f i)) y - deriv (deriv (Ψ.f i)) y) +
      Φ.nonlin i y * (deriv (Ψ.f i) y - deriv (Φ.f i) y)‖ ≤ (1 + M) * d2 Φ Ψ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_sub_rev (deriv (Ψ.f i) y)]
    exact (add_le_add h2 (mul_le_mul (hM i y hy) h1 (norm_nonneg _) hM0)).trans_eq (by ring)
  rw [show Φ.nonlin i y - Ψ.nonlin i y =
    ((deriv (deriv (Φ.f i)) y - deriv (deriv (Ψ.f i)) y) +
      Φ.nonlin i y * (deriv (Ψ.f i) y - deriv (Φ.f i) y)) / deriv (Ψ.f i) y by
    simp only [nonlin]; field_simp; ring, norm_div]
  exact (div_le_div₀ (by have := d2_nonneg Φ Ψ; positivity) hnum hm (hgm i y hy)).trans_eq (by ring)

end IFS.Continuity

namespace IFS

variable {N : ℕ} {ε : ℝ}

/-- (2.6): `|H_w(x) - Ĥ_w(x)| ≤ C' d₂(Φ, Ψ)` on `I`, for all words, when `Ψ` is close to `Φ`. -/
theorem exists_dualProj_sub_le_d2 (Φ : IFS N ε) (hN : 0 < N) :
    ∃ C' δ₀ : ℝ, 0 < δ₀ ∧ ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ₀ → ∀ (w : Word N), ∀ x ∈ I,
      ‖Φ.dualProj w x - Ψ.dualProj w x‖ ≤ C' * d2 Φ Ψ := by
  have hc0 := Φ.cmax_nonneg
  have hc1 := Φ.cmax_lt_one
  have hm := Φ.cmin_pos hN
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  have hM' : ∀ i, ∀ y ∈ I, ‖Φ.nonlin i (y : ℂ)‖ ≤ M := fun i y hy =>
    hM i _ (Continuity.ofReal_mem_closure Φ.ε_pos hy)
  obtain ⟨L₂, hL₂0, hL₂⟩ := Continuity.exists_lipschitz_nonlin Φ
  set c := Φ.cmax
  set m := Φ.cmin
  set δ₀ := min ((1 - c) / 2) (m / 2)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith) (by linarith)
  have hδ₀1 : δ₀ ≤ (1 - c) / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ m / 2 := min_le_right _ _
  set c' := c + δ₀
  have hc'0 : 0 < c' := by linarith
  have hc'1 : c' < 1 := by linarith
  set K := (M / (1 - c) + 1) / c'
  set B := L₂ / (1 - c) + (1 + M) / (m / 2)
  have hsum : Summable fun n : ℕ => (M * K * n + B) * c' ^ n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * c' ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_pos hc'0]; exact hc'1)
    convert (h1.mul_left (M * K)).add
      ((summable_geometric_of_lt_one hc'0.le hc'1).mul_left B) using 1
    ext n; ring
  refine ⟨∑' n : ℕ, (M * K * n + B) * c' ^ n, δ₀, hδ₀, fun {ε'} Ψ hΨ w x hx => ?_⟩
  have hP1 : ∀ i, ∀ y ∈ I, ‖deriv (Ψ.f i) (y : ℂ)‖ ≤ c' := fun i y hy => by
    have h3 := norm_sub_norm_le (deriv (Ψ.f i) y) (deriv (Φ.f i) y)
    rw [norm_sub_rev] at h3
    linarith [(Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1,
      Φ.norm_deriv_le_cmax i (Continuity.ofReal_mem_closure Φ.ε_pos hy)]
  have hP2 : ∀ i, ∀ y ∈ I, m / 2 ≤ ‖deriv (Ψ.f i) (y : ℂ)‖ := fun i y hy => by
    linarith [(Continuity.norm_sub_le_d2 Φ Ψ i hy).2.1,
      Φ.cmin_le_norm_deriv i (Continuity.ofReal_mem_closure Φ.ε_pos hy),
      norm_sub_norm_le (deriv (Φ.f i) y) (deriv (Ψ.f i) y)]
  rw [dualProj, dualProj, ← (Φ.summable_dualTerm w
    (Continuity.ofReal_mem_closure Φ.ε_pos hx)).tsum_sub
    (Ψ.summable_dualTerm w (Continuity.ofReal_mem_closure Ψ.ε_pos hx))]
  refine tsum_of_norm_bounded (hsum.hasSum.mul_right _) fun n => ?_
  have hd := Continuity.d2_nonneg Φ Ψ
  have hc1' : 0 < 1 - c := by linarith
  have hK0 : 0 ≤ K := by positivity
  unfold dualTerm
  cases h : w.get? n with
  | none => simp only [sub_self, norm_zero]; positivity
  | some i =>
    set v := (w.take n).reverse
    have hlen : v.length = n := by rw [List.length_reverse, length_take_of_get?_eq_some h]
    rw [← hlen, Φ.comp_ofReal v hx, Ψ.comp_ofReal v hx]
    have ha := Φ.re_comp_mem_I v hx
    have hb := Ψ.re_comp_mem_I v hx
    have hBn : ‖Φ.nonlin i (Φ.comp v x).re - Ψ.nonlin i (Ψ.comp v x).re‖ ≤ B * d2 Φ Ψ :=
      (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        ((add_le_add ((hL₂ i _ ha _ hb).trans
          (mul_le_mul_of_nonneg_left (Continuity.norm_comp_sub_comp_le Φ Ψ v hx) hL₂0))
          (Continuity.norm_nonlin_sub_le Φ Ψ (by linarith) hM0 hP2 hM' i hb)).trans_eq (by ring))
    exact (Continuity.norm_mul_sub_mul_le hM0 (hM' i _ ha) hBn
      (Continuity.norm_deriv_comp_sub_le Φ Ψ hc'0 (by linarith) hP1 hM0 hM v hx)
      (Continuity.norm_deriv_comp_le_pow Ψ hc'0.le hP1 v hx)).trans_eq (by ring)

/-- Lemma 2.7 for `𝔖_N`: if the dual of `Φ` satisfies the SSC, so does the dual of every
`Ψ ∈ 𝔖_N` close to `Φ` in the `𝒞²` metric. -/
theorem lemma_2_7_union (Φ : IFS N ε) (hN : 0 < N) (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < δ → Ψ.DualSSC := by
  obtain ⟨δ, hδ, hsep⟩ := Φ.exists_delta_of_dualSSC h
  obtain ⟨C', δ₀, hδ₀, hC'⟩ := Φ.exists_dualProj_sub_le_d2 hN
  refine ⟨min δ₀ (δ / (3 * (|C'| + 1))), lt_min hδ₀ (by positivity), fun {ε'} Ψ hΨ i j hij => ?_⟩
  have hΨδ₀ : d2 Φ Ψ < δ₀ := hΨ.trans_le (min_le_left _ _)
  have hsmall : C' * d2 Φ Ψ < δ / 3 := by
    have h1 : d2 Φ Ψ < δ / (3 * (|C'| + 1)) := hΨ.trans_le (min_le_right _ _)
    have h2 := mul_le_mul_of_nonneg_right (le_abs_self C') (Continuity.d2_nonneg Φ Ψ)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg C']
  obtain ⟨x, hx, hxδ⟩ := hsep i j hij
  refine ⟨x, hx, fun heq => ?_⟩
  have hi := hC' Ψ hΨδ₀ (.inf i) x hx
  have hj := hC' Ψ hΨδ₀ (.inf j) x hx
  have tri := norm_sub_le_norm_sub_add_norm_sub (Φ.dualProj (.inf i) x)
    (Ψ.dualProj (.inf i) x) (Φ.dualProj (.inf j) x)
  rw [heq, norm_sub_rev (Ψ.dualProj (.inf j) x)] at tri
  rw [heq] at hi
  linarith [norm_nonneg (Φ.dualProj (.inf i) x - Ψ.dualProj (.inf j) x)]

end IFS

end AnalyticESC
