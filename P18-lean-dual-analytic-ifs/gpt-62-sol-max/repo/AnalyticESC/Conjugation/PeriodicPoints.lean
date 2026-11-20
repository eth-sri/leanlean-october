module

public import AnalyticESC.Conjugation.Composite

@[expose] public section

/-! A common linearizing coordinate has logarithmic derivative fixed by every dual operator.
Contraction identifies it with all infinite dual projections. For two compositions the
corresponding projections are the reversed periodic words. -/

namespace AnalyticESC.IFS

open Set Metric Filter Topology

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- A zero of the coordinate derivative would give a nonempty finite invariant set of zeros,
hence a common fixed point. -/
private theorem deriv_ne_zero_of_conj (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x})
    {g : ℝ → ℝ} (hg : IsAnalyticCoord g) {lam t : Fin N → ℝ}
    (hlam : ∀ i, lam i ≠ 0)
    (hconj : ∀ i, ∀ x ∈ I, g (Φ.realMaps i x) = lam i * g x + t i) : ∀ x ∈ I, deriv g x ≠ 0 := by
  intro x hx hzero
  let Z := I ∩ deriv g ⁻¹' {0}
  have hxZ : x ∈ Z := ⟨hx, hzero⟩
  have hfin : Z.Finite := by
    by_contra! hInf
    obtain ⟨p, hp, ha⟩ := hInf.exists_accPt_of_subset_isCompact isCompact_Icc inter_subset_left
    have han : AnalyticOnNhd ℝ (deriv g) I := fun y hy => (hg.1 y hy).deriv
    have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Icc hp
      ((accPt_iff_frequently_nhdsNE.1 ha).mono fun _ hy => hy.2)
    have hz (y : ℝ) (hy : y ∈ I) : HasDerivAt g 0 y := by
      have he : deriv g y = 0 := hzero hy
      rw [← he]
      exact (hg.1 y hy).differentiableAt.hasDerivAt
    exact one_ne_zero (hg.2 (by simp) (by simp) (eq_of_hasDerivAt_zero_I hz (by simp) (by simp)))
  have hinv (i : Fin N) : MapsTo (Φ.realMaps i) Z Z := by
    rintro y ⟨hy, hy0⟩
    have he := conj_deriv_eq Φ.ε_pos (Φ.inClass i) hg.1 (hconj i) hy
    change deriv g y = 0 at hy0
    rw [hy0, mul_zero] at he
    exact ⟨(Φ.inClass i).re_mem_I y hy, (mul_eq_zero.1 he).resolve_right
      ((Φ.inClass i).re_deriv_ne_zero Φ.ε_pos hy)⟩
  let i : Fin N := ⟨0, hN⟩
  have hi : InjOn (Φ.realMaps i) Z := by
    intro y hy z hz h
    apply hg.2 hy.1 hz.1
    grind
  have hs := ((hfin.injOn_iff_bijOn_of_mapsTo (hinv i)).1 hi).surjOn
  have hd := diam_le_of_forall_dist_le (s := Z) (C := Φ.cmax * diam Z)
    (mul_nonneg Φ.cmax_nonneg diam_nonneg) (fun z hz w hw => by
      obtain ⟨y, hy, rfl⟩ := hs hz
      obtain ⟨v, hv, rfl⟩ := hs hw
      have h := Φ.abs_re_comp_sub_le_mul [i] hy.1 hv.1
      simp only [List.length_singleton, pow_one, ← Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem hfin.isBounded hy hv) Φ.cmax_nonneg))
  have hsub : Z.Subsingleton := not_nontrivial_iff.1 fun h =>
    (mul_lt_of_lt_one_left (diam_pos h hfin.isBounded) Φ.cmax_lt_one).not_ge hd
  exact hnd ⟨x, (Φ.attractor_eq_singleton_iff hN).2 ⟨hx, fun i => hsub (hinv i hxZ) hxZ⟩⟩

theorem dualProj_eq_of_conjSelfSimilar (hnd : ¬ ∃ x, Φ.attractor = {x})
    (h : ConjSelfSimilar Φ.realMaps) :
    ∀ i j : ℕ → Fin N, ∀ x ∈ I, Φ.dualProj (.inf i) x = Φ.dualProj (.inf j) x := by
  obtain ⟨g, hg, lam, t, hconj⟩ := h
  intro u v x hx
  have hg' := Φ.deriv_ne_zero_of_conj (u 0).pos hnd hg (fun i => (hconj i).1) (fun i => (hconj i).2.2)
  let G (y : ℝ)  := (logDeriv g y : ℂ)
  have hgc : ContinuousOn (logDeriv g) I := by
    apply ContinuousOn.div
    · exact fun y hy => (hg.1 y hy).deriv.deriv.continuousAt.continuousWithinAt
    · exact fun y hy => (hg.1 y hy).deriv.continuousAt.continuousWithinAt
    assumption
  have hfix (i : Fin N) : IsDualFixed (Φ.f i) G := by
    intro y hy
    have hf := Φ.inClass i
    have hA := conj_deriv_eq Φ.ε_pos hf hg.1 (hconj i).2.2 hy
    have hd x (hx : x ∈ I) := (hg.1 x hx).deriv.differentiableAt.hasDerivAt
    have hp := ((hd _ (hf.re_mem_I y hy)).comp y (hf.hasDerivAt_re Φ.ε_pos hy)).fun_mul
      (hf.hasDerivAt_re_deriv Φ.ε_pos hy)
    simp only [Function.comp_apply] at hp
    have hB := hasDerivAt_unique_of_eqOn_I hy hp ((hd y hy).const_mul (lam i))
      (fun _ => conj_deriv_eq Φ.ε_pos hf hg.1 (hconj i).2.2)
    have he : logDeriv g y = (deriv (deriv (Φ.f i)) y).re / (deriv (Φ.f i) y).re +
        (deriv (Φ.f i) y).re * logDeriv g (Φ.f i y).re := by
      unfold logDeriv
      field_simp [hg' y hy, hg' _ (hf.re_mem_I y hy), hf.re_deriv_ne_zero Φ.ε_pos hy]
      grind
    dsimp only [G]
    rw [he, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_mul,
      ← hf.deriv_eq_ofReal_re Φ.ε_pos hy, ← hf.deriv_deriv_eq_ofReal_re Φ.ε_pos hy]
  have h w := Φ.eq_dualProj_of_cocycle (Complex.continuous_ofReal.comp_continuousOn hgc) w
    (fun k => hfix (w k)) x hx
  grind

theorem conjSelfSimilar_of_const_dual_eq
    (h : ∀ i j : Fin N, ∀ x ∈ I, Φ.dualProj (.inf fun _ => i) x = Φ.dualProj (.inf fun _ => j) x) :
    ConjSelfSimilar Φ.realMaps := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨id, ⟨analyticOnNhd_id, injOn_id _⟩, 0, 0, fun i => i.elim0⟩
  let i : Fin N := ⟨0, hN⟩
  obtain ⟨g, hg, hg', hode⟩ := exists_coord_of_logDeriv Φ.ε_pos
    (Φ.differentiableOn_dualProj (.inf fun _ => i))
  choose lam t hl hl' he using fun j => Φ.exists_conj_of_dual_fixed j hg.1 hg'
    (Φ.dualProj_const_fixed j) (fun x hx => by rw [hode x hx, h i j x hx])
  exact ⟨g, hg, lam, t, fun j => ⟨hl j, hl' j, he j⟩⟩

private def pairSystem {m : ℕ} (hm : 0 < m) (i j : Fin m → Fin N) : IFS 2 (ε / 4) :=
  ⟨![Φ.comp (List.ofFn i), Φ.comp (List.ofFn j)], by positivity [Φ.ε_pos],
    Fin.forall_fin_two.2 ⟨Φ.inClass_comp (by aesop), Φ.inClass_comp (by aesop)⟩⟩

private theorem realMaps_pairSystem {m : ℕ} (hm : 0 < m) (i j : Fin m → Fin N) :
    (Φ.pairSystem hm i j).realMaps = ![fun x : ℝ => (Φ.comp (List.ofFn i) x).re,
      fun x : ℝ => (Φ.comp (List.ofFn j) x).re] := funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)

end AnalyticESC.IFS

namespace Challenge
open AnalyticESC Set
variable {N : ℕ}

/-- Theorem 1.12 (a). If the attractor of `Φ` is not a singleton, then `Φ` is conjugated to a
self-similar IFS if and only if `H_i ≡ H_j` on `[0,1]` for all `i, j ∈ Σ`. -/
theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x := by
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  simp only [Subtype.forall]
  exact ⟨Φ.dualProj_eq_of_conjSelfSimilar hnd,
    fun h => Φ.conjSelfSimilar_of_const_dual_eq fun _ _ => h _ _⟩

/-- Theorem 1.12 (b). If the attractor of `Φ` is not a singleton, then `Φ` is sub-conjugated to a
self-similar IFS, that is, `(f_i, f_j)` is conjugated to a self-similar IFS for some distinct
`i, j ∈ Σ_*` of the same length, if and only if `H_{(i)^∞} ≡ H_{(j)^∞}` on `[0,1]` for some distinct
`i, j ∈ Σ_*` of the same length. -/
theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (_hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x => (comp f (List.ofFn i) x).re,
        fun x => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x := by
  simp only [Subtype.forall]
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  constructor
  · rintro ⟨m, i, j, hij, h⟩
    have hm : 0 < m := Nat.pos_of_ne_zero fun he => hij (by subst m; exact Subsingleton.elim _ _)
    let Ψ := Φ.pairSystem hm i j
    have hΨ : ConjSelfSimilar Ψ.realMaps := by rwa [Φ.realMaps_pairSystem]
    by_cases hnd : ∃ p, Ψ.attractor = {p}
    · obtain ⟨p, hp⟩ := hnd
      obtain ⟨hpI, hfix⟩ := (Ψ.attractor_eq_singleton_iff (by decide)).1 hp
      obtain ⟨g, hg, lam, t, hconj⟩ := hΨ
      have hcenter i x (hx : x ∈ I) : g (Ψ.realMaps i x) - g p = lam i * (g x - g p) := by
        have h := (hconj i).2.2 p hpI
        grind
      have hc x (hx : x ∈ I) : Ψ.realMaps 0 (Ψ.realMaps 1 x) = Ψ.realMaps 1 (Ψ.realMaps 0 x) := by
        have h0 := (Ψ.inClass 0).re_mem_I _ hx
        have h1 := (Ψ.inClass 1).re_mem_I _ hx
        apply hg.2 ((Ψ.inClass 0).re_mem_I _ h1) ((Ψ.inClass 1).re_mem_I _ h0)
        apply (sub_left_inj (a := g p)).1
        simp only [AnalyticESC.IFS.realMaps] at hcenter
        grind
      have hm₂ : 0 < m + m := by omega
      have hh := Φ.dualProj_periodic_eq_of_eqOn_I hm₂ (u := Fin.append i j) (v := Fin.append j i)
        fun x hx => by
          simp only [List.ofFn_fin_append, Φ.comp_ofReal _ hx, Φ.reComp_append _ _ hx]
          tauto
      exact ⟨m + m, hm₂, _, _, Fin.rev_surjective.injective_comp_right.ne (fun h => hij (funext fun k => by
        simpa using congrFun h (Fin.castAdd m k))), hh⟩
    · refine ⟨m, hm, _, _, Fin.rev_surjective.injective_comp_right.ne hij, fun x hx => ?_⟩
      have H := Ψ.dualProj_eq_of_conjSelfSimilar hnd hΨ (fun _ => 0) (fun _ => 1) x hx
      rwa [Φ.dualProj_const_eq_periodic Ψ 0 (w := i) hm rfl x hx,
        Φ.dualProj_const_eq_periodic Ψ 1 (w := j) hm rfl x hx] at H
  · rintro ⟨m, hm, i, j, hij, h⟩
    let Ψ := Φ.pairSystem hm (i ∘ Fin.rev) (j ∘ Fin.rev)
    have hh : ∀ x ∈ I, Ψ.dualProj (.inf fun _ => 0) x = Ψ.dualProj (.inf fun _ => 1) x := by
      intro x hx
      rw [Φ.dualProj_const_eq_periodic Ψ 0 (w := i ∘ Fin.rev) hm rfl x hx,
        Φ.dualProj_const_eq_periodic Ψ 1 (w := j ∘ Fin.rev) hm rfl x hx, Function.comp_assoc]; simp [Function.comp_def]
      tauto
    have hc := Ψ.conjSelfSimilar_of_const_dual_eq (by
      simp_all)
    exact ⟨m, _, _, Fin.rev_surjective.injective_comp_right.ne hij, by rwa [Φ.realMaps_pairSystem] at hc⟩

end Challenge
