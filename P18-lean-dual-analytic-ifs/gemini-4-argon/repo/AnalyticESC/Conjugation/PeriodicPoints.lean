module

public import AnalyticESC.Conjugation.ExactOverlaps
public import AnalyticESC.Conjugation.Zeros

@[expose] public section

/-!
# Theorem 1.12 (a) along periodic points

The paper's proof of Theorem 1.12 (a). Let `g` be analytic and injective on `[0,1]` with
`g ∘ f_k = λ_k g + t_k` there for every letter `k`, so that `g ∘ f_w = λ_w g + t_w` for every
finite word `w`.

1. Differentiating gives `g'(f_k(x)) f_k'(x) = λ_k g'(x)`, so every `f_k` maps the zero set of
   `g'` in `[0,1]` into itself. This set is closed and `π(i) = lim f_{i₁ ⋯ iₙ}(x)` for every
   `x ∈ [0,1]`, so it contains the attractor once it is nonempty. A non-singleton attractor is
   infinite, and the identity theorem would give `g' ≡ 0`, against injectivity. Hence `g' ≠ 0`
   on `[0,1]`.
2. At the fixed point `p` of `f_w`, `f_w'(p) = λ_w`, and differentiating twice with (2.7) gives
   `g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`.
3. For `i, j ∈ Σ` let `kₙ = i₁ ⋯ iₙ jₙ ⋯ j₁`. The fixed point `p_{kₙ}` lies in
   `f_{i₁ ⋯ iₙ}([0,1])`, so `p_{kₙ} → π(i)`; `f_{kₙ}'(p_{kₙ}) → 0`; and
   `H_{j₁ ⋯ jₙ iₙ ⋯ i₁}(p_{kₙ}) → H_j(π(i))` by `exists_dualProj_bounds`, used to prove Lemma 2.5, uniformly on
   `cl B_ε` and holds for a finite and an infinite word with a common prefix, and the continuity
   of `H_j`. As `g''/g'` is continuous at `π(i)`, `g''/g' = H_j` on the attractor for every `j`,
   and the identity theorem gives `H_j = H_k` on `[0,1]`.

The converse follows the paper as well: `H = H_{k^∞} = Ĥ_{f_k}` for every letter `k`, Lemma 5.1
gives an invertible `g` with `g'' = H g'`, and the second part of Lemma 5.1 conjugates each `f_k`
to `y ↦ f_k'(p_k) y + g(p_k)(1 - f_k'(p_k))`. `theorem_1_12` states Theorem 1.12 (a) and (b) for
systems whose attractor is not a singleton.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Analytic maps on `[0,1]` -/

/-- Maps that agree on `[0,1]` and have derivatives at a point of `[0,1]` have the same
derivative there. -/
private theorem periodic_hasDerivAt_unique {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Compositions on `[0,1]` -/

/-- `f_{k w} = f_k ∘ f_w` on `[0,1]`, for the real maps. -/
private theorem periodic_re_comp_cons (k : Fin N) (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    (Φ.comp (k :: w) x).re = Φ.realMap k (Φ.comp w x).re := by
  show (Φ.f k (Φ.comp w x)).re = (Φ.f k ((Φ.comp w x).re : ℂ)).re
  rw [← Φ.comp_ofReal w hx]

/-- `π(i) = lim f_{i₁ ⋯ i_{mₙ}}(zₙ)` for points `zₙ ∈ [0,1]` and lengths `mₙ → ∞`. -/
theorem tendsto_re_comp_natProj (i : ℕ → Fin N) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {z : ℕ → ℝ} (hz : ∀ n, z n ∈ I) :
    Tendsto (fun n => (Φ.comp (List.ofFn fun k : Fin (m n) => i k) (z n)).re) atTop
      (𝓝 (Φ.natProj i)) := by
  refine ((Φ.tendsto_natProj i).comp hm).congr_dist (squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp hm))
  simpa [Real.dist_eq] using
    Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin (m n) => i k) (left_mem_Icc.2 zero_le_one) (hz n)

/-- `g ∘ f_w = λ_w g + t_w` on `[0,1]` for every finite word `w` if `g ∘ f_k = λ_k g + t_k` on
`[0,1]` for every letter `k`. -/
theorem exists_conj_comp {g : ℝ → ℝ} {lam t : Fin N → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (Φ.realMap k x) = lam k * g x + t k) (w : List (Fin N)) :
    ∃ a b : ℝ, ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b := by
  induction w with
  | nil => exact ⟨1, 0, fun x _ => by simp⟩
  | cons k w ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨lam k * a, lam k * b + t k, fun x hx => ?_⟩
    rw [Φ.periodic_re_comp_cons k w hx, hconj k _ (Φ.re_comp_mem_I w hx), h x hx]; ring

/-! ## The first step: `g'` has no zero -/

/-- Theorem 1.12 (a), first step of the proof: if `g` is analytic and injective on `[0,1]`,
`g ∘ f_k = λ_k g + t_k` on `[0,1]` for every `k`, and the attractor is not a singleton, then `g'`
has no zero in `[0,1]`. -/
theorem deriv_ne_zero_of_conj_of_nonsingleton (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x})
    {g : ℝ → ℝ} (hg : IsAnalyticCoord g) {lam t : Fin N → ℝ}
    (hconj : ∀ k, ∀ x ∈ I, g (Φ.realMap k x) = lam k * g x + t k) :
    ∀ x ∈ I, deriv g x ≠ 0 := by
  obtain ⟨hga, hinj⟩ := hg
  intro z hz hgz
  set Z := I ∩ deriv g ⁻¹' {0}
  have hZc : IsClosed Z := ContinuousOn.preimage_isClosed_of_isClosed
    (fun x hx => (hga x hx).deriv.continuousAt.continuousWithinAt) isClosed_Icc isClosed_singleton
  have hinv (k : Fin N) : MapsTo (Φ.realMap k) Z Z := by
    rintro x ⟨hx, hx0⟩
    have hFx : Φ.realMap k x ∈ I := (Φ.inClass k).re_mem_I x hx
    have hd : HasDerivAt (Φ.realMap k) (deriv (Φ.f k) x).re x :=
      hasDerivAt_re_ofReal (Φ.differentiableAt_f k (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)))
    have hid := periodic_hasDerivAt_unique hx ((hga _ hFx).differentiableAt.hasDerivAt.comp x hd)
      (((hga x hx).differentiableAt.hasDerivAt.const_mul (lam k)).add_const (t k)) (hconj k)
    simp only [mem_preimage, mem_singleton_iff] at hx0 ⊢
    rw [hx0, mul_zero] at hid
    exact ⟨hFx, (mul_eq_zero.1 hid).resolve_right
      (char_re_deriv_ne_zero_abs_lt_one Φ.ε_pos (Φ.inClass k) hx).1⟩
  have hinvw (w : List (Fin N)) : MapsTo (fun x : ℝ => (Φ.comp w x).re) Z Z := by
    induction w with
    | nil => intro x hx; simpa using hx
    | cons k w ih =>
      intro x hx
      show (Φ.comp (k :: w) x).re ∈ Z
      rw [Φ.periodic_re_comp_cons k w hx.1]
      exact hinv k (ih hx)
  obtain ⟨x₀, hx₀, hacc⟩ := ((Φ.attractor_infinite hN hnd).mono (by
    rintro _ ⟨i, rfl⟩
    exact hZc.mem_of_tendsto (Φ.tendsto_re_comp_natProj i tendsto_id fun _ => hz)
      (Eventually.of_forall fun _ => hinvw _ ⟨hz, hgz⟩))).exists_accPt_of_subset_isCompact
    isCompact_Icc inter_subset_left
  have hd0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun y hy => (hga y hy).deriv) isPreconnected_Icc hx₀
    ((accPt_iff_frequently_nhdsNE.1 hacc).mono fun _ hz => hz.2)
  exact one_ne_zero (hinj (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)
    (eq_of_hasDerivAt_zero_I (fun x hx => (hga x hx).differentiableAt.hasDerivAt.congr_deriv (hd0 hx))
      (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)))

/-! ## The second step: periodic points -/

/-- Theorem 1.12 (a), second step of the proof: if `g ∘ f_w = λ g + t` on `[0,1]` for a nonempty
word `w` and `g'` does not vanish at the fixed point `p` of `f_w`, then `f_w'(p) = λ` and
`g''(p)/g'(p) = H_{w^←}(p)/(1 - f_w'(p))`. -/
theorem deriv_deriv_div_deriv_eq_of_fixedPoint {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g I)
    {w : List (Fin N)} (hw : w ≠ []) {a b : ℝ}
    (hconj : ∀ x ∈ I, g (Φ.comp w x).re = a * g x + b) {p : ℝ} (hp : p ∈ I)
    (hfp : Φ.comp w p = p) (hgp : deriv g p ≠ 0) :
    ((deriv (deriv g) p / deriv g p : ℝ) : ℂ) =
      Φ.dualProj (.fin w.reverse) p / (1 - deriv (Φ.comp w) p) := by
  have hmem {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd ε := ofReal_mem_nbhd Φ.ε_pos hx
  set F : ℝ → ℝ := fun y => (Φ.comp w y).re
  set F₁ : ℝ → ℝ := fun y => (deriv (Φ.comp w) y).re with hF₁
  set F₂ : ℝ → ℝ := fun y => (deriv (deriv (Φ.comp w)) y).re with hF₂
  have hFd : ∀ x ∈ I, HasDerivAt F (F₁ x) x := fun _ => Φ.hasDerivAt_re_comp w
  have hF₁d : ∀ x ∈ I, HasDerivAt F₁ (F₂ x) x := fun _ hx =>
    hasDerivAt_re_ofReal (((Φ.differentiableOn_comp w).deriv (isOpen_nbhd ε)).differentiableAt
      ((isOpen_nbhd ε).mem_nhds (hmem hx)))
  have hFI : ∀ x ∈ I, F x ∈ I := fun _ hx => Φ.re_comp_mem_I w hx
  have hgd : ∀ y ∈ I, HasDerivAt g (deriv g y) y := fun y hy =>
    (hg y hy).differentiableAt.hasDerivAt
  have hg₁d : ∀ y ∈ I, HasDerivAt (deriv g) (deriv (deriv g) y) y := fun y hy =>
    (hg y hy).deriv.differentiableAt.hasDerivAt
  have hA : ∀ x ∈ I, deriv g (F x) * F₁ x = a * deriv g x := fun x hx =>
    periodic_hasDerivAt_unique hx ((hgd _ (hFI x hx)).comp x (hFd x hx))
      (((hgd x hx).const_mul a).add_const b) hconj
  have hB : deriv (deriv g) (F p) * F₁ p * F₁ p + deriv g (F p) * F₂ p =
      a * deriv (deriv g) p :=
    periodic_hasDerivAt_unique hp (((hg₁d _ (hFI p hp)).comp p (hFd p hp)).mul (hF₁d p hp))
      ((hg₁d p hp).const_mul a) hA
  have hFp : F p = p := by show (Φ.comp w p).re = p; rw [hfp, Complex.ofReal_re]
  have hF₁p : F₁ p = a := by
    have h := hA p hp; rw [hFp] at h; exact mul_left_cancel₀ hgp (by rw [h, mul_comm])
  have hcl : (p : ℂ) ∈ closure (nbhd ε) := subset_closure (hmem hp)
  have h₁ : deriv (Φ.comp w) p = (F₁ p : ℂ) :=
    Complex.ext (by simp [hF₁]) (by simp [hF₁, Φ.im_deriv_comp_ofReal w (hmem hp)])
  have h₂ : deriv (deriv (Φ.comp w)) p = (F₂ p : ℂ) :=
    Complex.ext (by simp [hF₂]) (by simp [hF₂, im_deriv_eq_zero (isOpen_nbhd ε)
      ((Φ.differentiableOn_comp w).deriv (isOpen_nbhd ε))
      (fun s hs => Φ.im_deriv_comp_ofReal w hs) (hmem hp)])
  have hne : F₁ p ≠ 0 := fun h0 =>
    Φ.deriv_comp_ne_zero w hcl (by rw [h₁, h0, Complex.ofReal_zero])
  have hne' : 1 - F₁ p ≠ 0 := sub_ne_zero.2 <| ne_of_gt <| (le_abs_self _).trans_lt <|
    (Complex.abs_re_le_norm _).trans_lt <| (Φ.norm_deriv_comp_le w hcl).trans_lt <|
      pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  rw [Φ.dualProj_fin_reverse w (hmem hp), h₁, h₂,
    show (F₂ p : ℂ) / (F₁ p : ℂ) / (1 - (F₁ p : ℂ)) = ((F₂ p / F₁ p / (1 - F₁ p) : ℝ) : ℂ) by
      push_cast; ring]
  congr 1
  rw [hFp, ← hF₁p] at hB
  rw [div_div, div_eq_div_iff hgp (mul_ne_zero hne hne')]
  linear_combination -hB

/-! ## The third step: the limit along periodic points -/

/-- Theorem 1.12 (a), third step of the proof: if `Φ` is conjugated to a self-similar IFS and its
attractor is not a singleton, then all dual natural projections agree on `[0,1]`. -/
theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬ ∃ x, Φ.attractor = {x})
    (h : ConjSelfSimilar Φ.realMap) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  intro i₀ j₀
  have hN : 0 < N := (i₀ 0).pos
  have hε := Φ.ε_pos
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  have hconj' : ∀ k, ∀ x ∈ I, g (Φ.realMap k x) = lam k * g x + t k := fun k => (hconj k).2.2
  have hg' := Φ.deriv_ne_zero_of_conj_of_nonsingleton hN hnd hg hconj'
  obtain ⟨M, -, -, hM⟩ := Φ.exists_dualProj_bounds
  have hc : Tendsto (fun n : ℕ => Φ.cmax ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).comp
      (tendsto_add_atTop_nat 1)
  have key (i j : ℕ → Fin N) :
      ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ) =
        Φ.dualProj (.inf j) (Φ.natProj i) := by
    have hπ : Φ.natProj i ∈ I := Φ.attractor_subset_I ⟨i, rfl⟩
    set u : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => i m with hu
    set v : ℕ → List (Fin N) := fun n => List.ofFn fun m : Fin (n + 1) => j m with hv
    set k : ℕ → List (Fin N) := fun n => u n ++ (v n).reverse with hk
    have hkne (n : ℕ) : k n ≠ [] := by simp [hk, hu]
    choose p hp hfp using fun n =>
      exists_fixedPoint (by linarith) (Φ.inClass_comp (hkne n))
    have hpcl (n : ℕ) : (p n : ℂ) ∈ closure (nbhd ε) :=
      subset_closure (ofReal_mem_nbhd hε (hp n))
    have hid (n : ℕ) : ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ) =
        Φ.dualProj (.fin (k n).reverse) (p n) / (1 - deriv (Φ.comp (k n)) (p n)) :=
      let ⟨_, _, hab⟩ := Φ.exists_conj_comp hconj' (k n)
      Φ.deriv_deriv_div_deriv_eq_of_fixedPoint hg.1 (hkne n) hab (hp n) (hfp n) (hg' _ (hp n))
    have hplim : Tendsto p atTop (𝓝 (Φ.natProj i)) := by
      refine (Φ.tendsto_re_comp_natProj i (tendsto_add_atTop_nat 1)
        (z := fun n => (Φ.comp (v n).reverse (p n)).re)
        fun n => Φ.re_comp_mem_I _ (hp n)).congr fun n => ?_
      show (Φ.comp (u n) ((Φ.comp (v n).reverse (p n)).re : ℂ)).re = p n
      rw [← Φ.comp_append_ofReal _ _ (hp n)]
      show (Φ.comp (k n) (p n)).re = p n
      rw [hfp n, Complex.ofReal_re]
    have hL : Tendsto (fun n => ((deriv (deriv g) (p n) / deriv g (p n) : ℝ) : ℂ)) atTop
        (𝓝 ((deriv (deriv g) (Φ.natProj i) / deriv g (Φ.natProj i) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        (((hg.1 _ hπ).deriv.deriv.continuousAt.div
          (hg.1 _ hπ).deriv.continuousAt (hg' _ hπ)).tendsto.comp hplim)
    have hD : Tendsto (fun n => deriv (Φ.comp (k n)) (p n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => (Φ.norm_deriv_comp_le _ (hpcl n)).trans
        (pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le ?_)) hc
      simp only [hk, hu, hv, List.length_append, List.length_reverse, List.length_ofFn]; omega
    have hH₁ : Tendsto (fun n => Φ.dualProj (.fin (k n).reverse) (p n) -
        Φ.dualProj (.inf j) (p n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => hM _ _ (n + 1) ?_ _ (hpcl n))
        (by simpa using hc.const_mul (2 * M))
      rw [Word.le_commonPrefixLength_iff]
      intro l hl
      have hl' : l < (v n).length := by simp only [hv, List.length_ofFn]; exact hl
      rw [Word.get?_fin, hk, List.reverse_append, List.reverse_reverse,
        List.getElem?_append_left hl', congrFun hv n]
      simp only [List.getElem?_ofFn, hl, ↓reduceDIte, Word.get?_inf, true_and, Option.isSome_some]
    have hH₂ : Tendsto (fun n => Φ.dualProj (.inf j) (p n)) atTop
        (𝓝 (Φ.dualProj (.inf j) (Φ.natProj i))) :=
      (((Φ.differentiableOn_dualProj _).differentiableAt ((isOpen_nbhd ε).mem_nhds
        (ofReal_mem_nbhd hε hπ))).continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.tendsto _).comp hplim)
    have hR : Tendsto (fun n => Φ.dualProj (.fin (k n).reverse) (p n) /
        (1 - deriv (Φ.comp (k n)) (p n))) atTop (𝓝 (Φ.dualProj (.inf j) (Φ.natProj i))) := by
      simpa only [Pi.div_def, zero_add, sub_zero, div_one, sub_add_cancel] using (hH₁.add hH₂).div
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).sub hD)
        (by rw [sub_zero]; exact one_ne_zero)
    exact tendsto_nhds_unique hL (hR.congr fun n => (hid n).symm)
  intro x hx
  by_contra hne
  refine Φ.attractor_infinite hN hnd ((finite_zeros hε ((Φ.differentiableOn_dualProj (.inf i₀)).sub
    (Φ.differentiableOn_dualProj (.inf j₀))) ⟨x, hx, sub_ne_zero.2 hne⟩).subset ?_)
  rintro _ ⟨i, rfl⟩
  refine ⟨Φ.attractor_subset_I ⟨i, rfl⟩, ?_⟩
  show Φ.dualProj (.inf i₀) (Φ.natProj i) - Φ.dualProj (.inf j₀) (Φ.natProj i) = 0
  rw [← key i i₀, ← key i j₀, sub_self]

/-! ## The converse -/

/-- `Ĥ_{f_k} = H_{k^∞}` on `[0,1]`. -/
private theorem periodic_hatH_f_eq_dualProj_const (k : Fin N) :
    ∀ x ∈ I, hatH (Φ.f k) x = Φ.dualProj (.inf fun _ => k) x := fun x hx => by
  have h := Φ.hatH_comp_eq_dualProj one_pos ![k] x hx
  have hw : periodic one_pos (![k] ∘ Fin.rev) = fun _ => k :=
    funext fun _ => by unfold periodic; exact Matrix.cons_val_fin_one k ![] _
  rwa [hw, show Φ.comp (List.ofFn ![k]) = Φ.f k by simp] at h

/-- Theorem 1.12 (a), the converse: if all dual natural projections agree on `[0,1]`, then
`char_re_koenigs_spec` for `f_{k₀}` and `char_exists_conj_of_ode` conjugate each `f_k` to a
similarity. -/
theorem conjSelfSimilar_of_dualProj_eq
    (h : ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) :
    ConjSelfSimilar Φ.realMap := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun j => j.elim0⟩
  have hε := Φ.ε_pos
  set k₀ : Fin N := ⟨0, hN⟩
  obtain ⟨g, hco, -, hode⟩ := char_re_koenigs_spec hε (Φ.inClass k₀)
  choose lam t hlam using fun k => char_exists_conj_of_ode hε (Φ.inClass k) hco.1
    fun x hx => by
      rw [Φ.periodic_hatH_f_eq_dualProj_const k x hx, h _ (fun _ => k₀) x hx,
        ← Φ.periodic_hatH_f_eq_dualProj_const k₀ x hx]
      exact hode x hx
  exact ⟨g, hco, lam, t, hlam⟩

/-- Theorem 1.12 (b), for every system. -/
theorem subConjSelfSimilar_iff :
    Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x := by
  have hε4 : 0 < ε / 4 := by linarith [Φ.ε_pos]
  have hne {m : ℕ} (w : Fin m → Fin N) (hm : 0 < m) : List.ofFn w ≠ [] := fun h =>
    hm.ne' (List.ofFn_eq_nil_iff.1 h)
  have hrev {m : ℕ} (w : Fin m → Fin N) : (w ∘ Fin.rev) ∘ Fin.rev = w := funext fun _ => by simp
  have hrev_ne {m : ℕ} {u v : Fin m → Fin N} (huv : u ≠ v) : u ∘ Fin.rev ≠ v ∘ Fin.rev :=
    fun h => huv (by rw [← hrev u, h, hrev])
  constructor
  · rintro ⟨m, i, j, hij, g, ⟨hg, hinj⟩, lam, t, hconj⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun h => hij (by subst h; exact Subsingleton.elim _ _)
    have hf₁ := Φ.inClass_comp (hne i hm)
    have hf₂ := Φ.inClass_comp (hne j hm)
    let Ψ : IFS 2 (ε / 4) := ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)], hε4,
      Fin.forall_fin_two.2 ⟨hf₁, hf₂⟩⟩
    by_cases hnd : ∃ x, Ψ.attractor = {x}
    · obtain ⟨p, hp⟩ := hnd
      have hcomm := comp_comm_of_conj hinj (fun x hx => hf₁.re_mem_I x hx)
        (fun x hx => hf₂.re_mem_I x hx) (hconj 0).2.2 (hconj 1).2.2
        (Ψ.attractor_subset_I (hp ▸ mem_singleton p))
        (Ψ.fixedPoint_of_attractor_singleton hp 0)
        (Ψ.fixedPoint_of_attractor_singleton hp 1)
      have hm' : 0 < m + m := by omega
      have hcomp {u v : Fin m → Fin N} {y : ℝ} (hy : y ∈ I) :
          Φ.comp (List.ofFn (Fin.append u v)) y =
          ((Φ.comp (List.ofFn u) ((Φ.comp (List.ofFn v) y).re : ℂ)).re : ℂ) := by
        rw [List.ofFn_fin_append, Φ.comp_append_ofReal _ _ hy]
        exact Φ.comp_ofReal _ (Φ.re_comp_mem_I _ hy)
      have hH := hatH_eq_of_eqOn_I hε4 (Φ.inClass_comp (hne (Fin.append i j) hm'))
        (Φ.inClass_comp (hne (Fin.append j i) hm')) fun y hy => by
          rw [hcomp hy, hcomp hy]; exact congrArg _ (hcomm y hy)
      refine ⟨m + m, hm', Fin.append i j ∘ Fin.rev, Fin.append j i ∘ Fin.rev,
        hrev_ne fun h => hij (funext fun k => by simpa using congrFun h (Fin.castAdd m k)),
        fun x hx => ?_⟩
      rw [← Φ.hatH_comp_eq_dualProj hm' _ x hx, ← Φ.hatH_comp_eq_dualProj hm' _ x hx]
      exact hH x hx
    · have hall := Ψ.dualProj_eq_of_conjSelfSimilar hnd ⟨g, ⟨hg, hinj⟩, lam, t,
        Fin.forall_fin_two.2 ⟨by simpa [Ψ, realMap] using hconj 0,
          by simpa [Ψ, realMap] using hconj 1⟩⟩
      refine ⟨m, hm, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, fun x hx => ?_⟩
      have h := hall (fun _ => 0) (fun _ => 1) x hx
      rw [← Ψ.periodic_hatH_f_eq_dualProj_const 0 x hx,
        ← Ψ.periodic_hatH_f_eq_dualProj_const 1 x hx] at h
      rw [← Φ.hatH_comp_eq_dualProj hm _ x hx, ← Φ.hatH_comp_eq_dualProj hm _ x hx]
      simpa [Ψ] using h
  · rintro ⟨m, hm, i, j, hij, h⟩
    have hH : ∀ x ∈ I, hatH (Φ.comp (List.ofFn (i ∘ Fin.rev))) x =
        hatH (Φ.comp (List.ofFn (j ∘ Fin.rev))) x := fun x hx => by
      rw [Φ.hatH_comp_eq_dualProj hm _ x hx, Φ.hatH_comp_eq_dualProj hm _ x hx, hrev, hrev]
      exact h x hx
    have hf₁ := Φ.inClass_comp (hne (i ∘ Fin.rev) hm)
    have hf₂ := Φ.inClass_comp (hne (j ∘ Fin.rev) hm)
    obtain ⟨g, hco, -, hode⟩ := char_re_koenigs_spec hε4 hf₁
    obtain ⟨l₁, t₁, c₁⟩ := char_exists_conj_of_ode hε4 hf₁ hco.1 hode
    obtain ⟨l₂, t₂, c₂⟩ := char_exists_conj_of_ode hε4 hf₂ hco.1 fun x hx => by
      rw [← hH x hx]; exact hode x hx
    exact ⟨m, i ∘ Fin.rev, j ∘ Fin.rev, hrev_ne hij, g, hco, ![l₁, l₂], ![t₁, t₂],
      Fin.forall_fin_two.2 ⟨c₁, c₂⟩⟩

/-! ## Theorem 1.12 -/

/-- Theorem 1.12 (a) and (b), for systems whose attractor is not a singleton. -/
theorem theorem_1_12 (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    (ConjSelfSimilar Φ.realMap ↔
      ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x) ∧
    (Φ.SubConjSelfSimilar ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x ∈ I, Φ.dualProj (.inf (periodic hm i)) x = Φ.dualProj (.inf (periodic hm j)) x) :=
  ⟨⟨Φ.dualProj_eq_of_conjSelfSimilar hnd, Φ.conjSelfSimilar_of_dualProj_eq⟩,
    Φ.subConjSelfSimilar_iff⟩

end IFS

end AnalyticESC
