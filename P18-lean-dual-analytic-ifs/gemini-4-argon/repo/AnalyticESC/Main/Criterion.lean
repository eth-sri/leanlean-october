module

public import AnalyticESC.Main.Dichotomy

@[expose] public section

/-!
# Proposition 1.8

An explicit sufficient condition for the hypothesis of Theorem 1.5: if the distortions
`f_i''/f_i'` of different maps are `α`-apart somewhere on `[0,1]` and `α > 2β c_max/(1 - c_max)`,
then dual natural projections of distinct words of equal length differ, and `Φ` satisfies the
SESC.

The first term of the series (1.4) for `H_w` is `f_a''/f_a'`, where `a` is the first letter of
`w`, and the remaining terms sum to at most `β c_max/(1 - c_max)` on `I`. Hence words with
different first letters have different dual projections at a point of `I`, and, by the identity
theorem, on every nondegenerate subinterval of `I`. Distinct words of equal length are reduced to
this case by the cocycle identity for their longest common prefix.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta : ℝ := ⨆ (x : I) (i : Fin N), ‖Φ.nonlin i ((x : ℝ) : ℂ)‖

theorem beta_nonneg : 0 ≤ Φ.beta :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

private theorem norm_nonlin_le_beta (i : Fin N) {x : ℝ} (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
  refine le_ciSup_of_le (f := fun x : I => ⨆ i : Fin N, ‖Φ.nonlin i ((x : ℝ) : ℂ)‖) ⟨M, ?_⟩ ⟨x, hx⟩
    (le_ciSup (f := fun i : Fin N => ‖Φ.nonlin i ((x : ℝ) : ℂ)‖) (finite_range _).bddAbove i)
  rintro _ ⟨y, rfl⟩
  exact Real.iSup_le (fun j => hM j _ (subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2))) hM0

/-- The term with index `n` of (1.4) is at most `β c_max^n` at the points of `I`. -/
private theorem norm_dualTerm_le_beta (w : Word N) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.dualTerm w n x‖ ≤ Φ.beta * Φ.cmax ^ n := by
  cases h : w.get? n with
  | none =>
    rw [Φ.dualTerm_of_get?_eq_none h, norm_zero]
    exact mul_nonneg Φ.beta_nonneg (pow_nonneg Φ.cmax_nonneg n)
  | some i =>
    rw [Φ.dualTerm_of_get?_eq_some h, norm_mul]
    have h2 := Φ.norm_deriv_comp_le (w.take n).reverse
      (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))
    rw [List.length_reverse, length_take_of_get?_eq_some h] at h2
    exact mul_le_mul (by rw [Φ.comp_ofReal _ hx]; exact Φ.norm_nonlin_le_beta i (Φ.re_comp_mem_I _ hx))
      h2 (norm_nonneg _) Φ.beta_nonneg

/-- If `w` begins with `a`, then `|H_w(x) - (f_a''/f_a')(x)| ≤ β c_max/(1 - c_max)` on `I`. -/
private theorem norm_dualProj_sub_nonlin_le {w : Word N} {a : Fin N} (h : w.get? 0 = some a) {x : ℝ}
    (hx : x ∈ I) : ‖Φ.dualProj w x - Φ.nonlin a x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
  have h0 : Φ.dualTerm w 0 x = Φ.nonlin a x := by
    rw [Φ.dualTerm_of_get?_eq_some h]; cases w <;> simp
  rw [dualProj, (Φ.summable_dualTerm w
    (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))).tsum_eq_zero_add,
    h0, add_sub_cancel_left, div_eq_mul_inv]
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left (Φ.beta * Φ.cmax)) fun n =>
    (Φ.norm_dualTerm_le_beta w (n + 1) hx).trans_eq (by ring)

/-- Words with different first letters have different dual projections at a point of `I`. -/
private theorem exists_dualProj_ne_of_get?_zero {α : ℝ}
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} {a b : Fin N}
    (hi : i.get? 0 = some a) (hj : j.get? 0 = some b) (hab : a ≠ b) :
    ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨x, hx, hαx⟩ := hsep a b hab
  refine ⟨x, hx, fun heq => ?_⟩
  have h1 := Φ.norm_dualProj_sub_nonlin_le hi hx
  have h2 := Φ.norm_dualProj_sub_nonlin_le hj hx
  have key := norm_sub_le (Φ.dualProj j x - Φ.nonlin b x) (Φ.dualProj j x - Φ.nonlin a x)
  rw [sub_sub_sub_cancel_left] at key
  rw [heq] at h1
  have : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) = 2 * (Φ.beta * Φ.cmax / (1 - Φ.cmax)) := by ring
  linarith

/-- Distinct words of equal length have different dual projections at a point of `I`. -/
private theorem exists_dualProj_ne {α : ℝ} (hN : 0 < N)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} (hij : i ≠ j)
    (hlen : i.length = j.length) : ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  classical
  have hex : ∃ n, i.get? n ≠ j.get? n := by by_contra! h; exact hij (Word.ext_get? h)
  set m := Nat.find hex
  have hm : i.get? m ≠ j.get? m := Nat.find_spec hex
  have his : (i.get? m).isSome ↔ (j.get? m).isSome := by
    rw [Word.isSome_get?_iff, hlen, Word.isSome_get?_iff]
  cases hc : i.get? m with
  | none => cases hd : j.get? m <;> simp_all
  | some c =>
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (his.1 (by simp [hc]))
    have hmlt : (m : ℕ∞) < i.length := (Word.isSome_get?_iff i m).1 (by simp [hc])
    obtain ⟨u, i', j', hu, rfl, rfl⟩ := Word.exists_eq_prepend (n := m)
      (Word.le_commonPrefixLength_iff.2 fun k hk =>
        ⟨(Word.isSome_get?_iff i k).2 (( Nat.cast_lt.2 hk).trans hmlt),
          Decidable.not_not.1 (Nat.find_min hex hk)⟩)
    simp only [Word.get?_prepend, hu, lt_irrefl, ↓reduceIte, Nat.sub_self] at hc hd hm
    obtain ⟨y, hy, hne⟩ := Φ.exists_dualProj_ne_of_get?_zero hsep hlt hc hd
      fun hcd => hm (by rw [hc, hd, hcd])
    obtain ⟨p, q, hp, hq, hcmin, -, himg⟩ := Φ.exists_image_comp_eq_Icc u.reverse
    have hpq : p < q := sub_pos.1 ((pow_pos (Φ.cmin_pos hN) _).trans_le hcmin)
    by_contra! hall
    refine hne (eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj i')
      (Φ.differentiableOn_dualProj j') hpq (Icc_subset_Icc hp hq) (fun z hz => ?_)
      (ofReal_mem_nbhd Φ.ε_pos hy))
    obtain ⟨x, hx, hxz⟩ := himg z hz
    have hxn : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
    have h := hall x hx
    rw [Φ.dualProj_prepend u i' hxn, Φ.dualProj_prepend u j' hxn, add_right_inj] at h
    rw [hxz]
    exact mul_left_cancel₀ (Φ.deriv_comp_ne_zero u.reverse hxn) h

/-- Proposition 1.8. -/
theorem proposition_1_8 (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x ∈ I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖) :
    0 < Φ.beta ∧ (2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α →
      (∀ i j : Word N, i ≠ j → i.length = j.length →
        0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖) ∧ Φ.SESC) := by
  have hbeta : 0 < Φ.beta := by
    obtain ⟨x, hx, hαx⟩ := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
    linarith [Φ.norm_nonlin_le_beta ⟨0, by omega⟩ hx, Φ.norm_nonlin_le_beta ⟨1, by omega⟩ hx,
      norm_sub_le (Φ.nonlin ⟨0, by omega⟩ x) (Φ.nonlin ⟨1, by omega⟩ x)]
  refine ⟨hbeta, fun hlt => ?_⟩
  have hpos (i j : Word N) (hij : i ≠ j) (hlen : i.length = j.length) :
      0 < ⨆ x : I, ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖ := by
    obtain ⟨x, hx, hne⟩ := Φ.exists_dualProj_ne (by omega) hsep hlt hij hlen
    obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
    refine (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le
      (le_ciSup (f := fun x : I => ‖Φ.dualProj i ((x : ℝ) : ℂ) - Φ.dualProj j ((x : ℝ) : ℂ)‖)
        ⟨M + M, ?_⟩ ⟨x, hx⟩)
    rintro _ ⟨y, rfl⟩
    have hyn : ((y : ℝ) : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos y.2)
    exact (norm_sub_le _ _).trans (add_le_add (hM i _ hyn) (hM j _ hyn))
  exact ⟨hpos, Φ.theorem_1_5 hpos⟩

end IFS

end AnalyticESC
