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

variable {N : ℕ} (Φ : IFS N)

/-- `β = sup_{x ∈ [0,1], i} |f_i''/f_i'(x)|` (Proposition 1.8). -/
noncomputable def beta : ℝ := ⨆ (x : I) (i : Fin N), ‖Φ.nonlin i ((x : ℝ) : ℂ)‖

theorem beta_nonneg : 0 ≤ Φ.beta :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

lemma norm_nonlin_le_beta (i : Fin N) {x : ℝ} (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta := by
  have c : ContinuousOn (fun t : ℝ => fun j => Φ.nonlin j t) I := continuousOn_pi.mpr fun j =>
    (Φ.analytic_nonlin j).continuousOn.comp Complex.continuous_ofReal.continuousOn fun _ => Φ.closedReal
  simpa only [beta,Pi.norm_def,Finset.sup_univ_eq_ciSup,NNReal.coe_iSup,coe_nnnorm] using
    (norm_le_pi_norm (fun j => Φ.nonlin j x) i).trans (le_sup isCompact_Icc c.norm hx)

abbrev Spread (α : ℝ) := ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖

/-- Dropping the first term leaves a geometrically bounded tail. -/
lemma head_error {l : ℕ∞} (hl : 0 < l) (w : Address N) (x : I) :
    ‖Φ.dualProj l w x - Φ.nonlin (w 0) x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
  rw [dualProj,(Φ.summable_dualTerm l w (Φ.closedReal x.2)).tsum_eq_zero_add,
    show Φ.dualTerm l w 0 x = Φ.nonlin (w 0) x by simp [dualTerm,hl,block], add_sub_cancel_left]
  simpa using Φ.tail_bound (m := 1) fun n => Φ.term_bound Φ.beta_nonneg l w n (Φ.closedReal x.2) fun i a => by
    rw [Φ.comp_ofReal a x.2]; exact Φ.norm_nonlin_le_beta i (Φ.re_comp_mem_I a x.2)

/-- Agreement of projections persists when a common prefix is canceled:
the tail projections agree on its image, hence on the entire interval. -/
lemma cancel_prefix {l : ℕ∞} {m : ℕ} (hm : (m:ℕ∞) ≤ l) {v w} (he : block m v = block m w)
    (e : ∀ x : I, Φ.dualProj l v x = Φ.dualProj l w x) (y : I) :
    Φ.dualProj (l-m) (shift m v) y = Φ.dualProj (l-m) (shift m w) y := by
  have an u := real_slice ((Φ.analytic_dual (l-m) u).mono (image_subset_iff.mpr fun _ => Φ.real_mem))
  let a := (block m w).reverse
  apply agree_Icc (an _) (an _) ((Icc_infinite zero_lt_one).image (Φ.regular_R a).injOn)
    (image_subset_iff.mpr (Φ.re_comp_mem_I a)) _ y.2
  rintro _ ⟨x,hx,rfl⟩
  have h := e ⟨x,hx⟩
  rw [Φ.expand _ v hm (Φ.closedReal hx),Φ.expand _ w hm (Φ.closedReal hx),he,add_right_inj] at h
  dsimp only [Function.comp_apply,R]; rw [← Φ.comp_ofReal a hx]
  exact mul_left_cancel₀ (Φ.deriv_comp_ne_zero a (Φ.closedReal hx)) h

lemma criterion {α : ℝ} (hsep : Φ.Spread α) (hlt : 2*Φ.beta*Φ.cmax/(1-Φ.cmax) < α)
    {l v w} (h : ∃ n : ℕ, (n:ℕ∞) < l ∧ v n ≠ w n) : 0 < dev (Φ.dualProj l v) (Φ.dualProj l w) := by
  obtain ⟨m,hm,he,ne⟩ := first_difference h
  obtain ⟨x,hα⟩ := hsep _ _ ne
  by_contra! hz
  have H (y : I) := sub_eq_zero.mp <| norm_le_zero_iff.mp <|
    (Φ.le_real_sup (((Φ.analytic_dual l v).continuousOn.sub (Φ.analytic_dual l w).continuousOn).norm) y.2).trans hz
  have e := Φ.cancel_prefix hm.le he H x
  have hl := tsub_pos_of_lt hm
  have h₁ := Φ.head_error hl (shift m v) x; have h₂ := Φ.head_error hl (shift m w) x
  rw [← e] at h₂; rw [norm_sub_rev] at h₁
  grind [norm_sub_le_norm_sub_add_norm_sub (Φ.nonlin (v m) x) (Φ.dualProj (l-m) (shift m v) x) (Φ.nonlin (w m) x)]

lemma infinite_criterion {α} (hsep : Φ.Spread α) (hlt : 2*Φ.beta*Φ.cmax/(1-Φ.cmax) < α)
    {v w : Address N} (h : v ≠ w) : 0 < dev (Φ.dualProj ⊤ v) (Φ.dualProj ⊤ w) :=
  Φ.criterion hsep hlt (by simp_all <;> grind)

lemma beta_pos_of_spread {α} (hsep : Φ.Spread α) (hα : 0 < α) (hN : 2 ≤ N) : 0 < Φ.beta := by
  have H (i j : Fin N) (hne : i ≠ j) : 0 < Φ.beta := by
    obtain ⟨x,hx⟩ := hsep i j hne
    linarith [norm_sub_le (Φ.nonlin i x) (Φ.nonlin j x),Φ.norm_nonlin_le_beta i x.2,Φ.norm_nonlin_le_beta j x.2]
  exact H ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp)

end IFS

end AnalyticESC
