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

theorem norm_nonlin_le_beta (i : Fin N) {x : ℝ} (hx : x ∈ I) : ‖Φ.nonlin i x‖ ≤ Φ.beta := by
  obtain ⟨M, hM₀, hM⟩ := Φ.exists_nonlin_bound
  refine le_ciSup_of_le (f := fun t : I => ⨆ i : Fin N, ‖Φ.nonlin i (t : ℝ)‖)
    ⟨M, forall_mem_range.2 fun t => Real.iSup_le (fun i => hM i _ (Φ.real_mem_closed t.2)) hM₀⟩ ⟨x, hx⟩ ?_
  exact le_ciSup (f := fun i => ‖Φ.nonlin i x‖) (finite_range _).bddAbove i

/-- Words with different first letters have different dual projections at a point of `I`. -/
theorem exists_dualProj_ne_of_get?_zero {α : ℝ}
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} {a b : Fin N}
    (hi : i.get? 0 = some a) (hj : j.get? 0 = some b) (hab : a ≠ b) :
    ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨⟨x, hx⟩, hαx⟩ := hsep a b hab
  refine ⟨x, hx, fun heq => ?_⟩
  have htail {w : Word N} {c : Fin N} (h : w.get? 0 = some c) :
      ‖Φ.dualProj w x - Φ.nonlin c x‖ ≤ Φ.beta * Φ.cmax / (1 - Φ.cmax) := by
    have hxn  := Φ.real_mem_closed hx
    have h0 : Φ.dualTerm w 0 x = Φ.nonlin c x := by
      cases w <;> simp_all [dualTerm]
    rw [dualProj, (Φ.summable_dualTerm w hxn).tsum_eq_zero_add, h0, add_sub_cancel_left,
      div_eq_mul_inv]
    have hg : HasSum (fun n : ℕ => Φ.beta * Φ.cmax * Φ.cmax ^ n)
        (Φ.beta * Φ.cmax * (1 - Φ.cmax)⁻¹) :=
      (hasSum_geometric_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one).mul_left _
    refine tsum_of_norm_bounded hg fun n => ?_
    simpa [pow_succ', mul_assoc] using Φ.norm_dualTerm_le Φ.cmax_nonneg Φ.beta_nonneg w (n + 1) x
      (fun v => (Φ.norm_deriv_comp_bounds v hxn).2)
      (fun i v => Φ.comp_ofReal v hx ▸ Φ.norm_nonlin_le_beta i (Φ.re_comp_mem_I v hx))
  have key := dist_triangle (Φ.nonlin a x) (Φ.dualProj i x) (Φ.nonlin b x)
  rw [dist_comm (Φ.nonlin a x) (Φ.dualProj i x), heq] at key
  simp only [dist_eq_norm] at key
  grind

/-- Distinct words of equal length have different dual projections at a point of `I`. -/
theorem exists_dualProj_ne {α : ℝ}
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖Φ.nonlin i x - Φ.nonlin j x‖)
    (hlt : 2 * Φ.beta * Φ.cmax / (1 - Φ.cmax) < α) {i j : Word N} (hij : i ≠ j)
    (hlen : i.SameLength j) : ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨n, c, d, hp, hc, hd, hcd⟩ := Word.exists_prefix_first_ne hij hlen
  let i' := i.drop n
  let j' := j.drop n
  obtain ⟨y, hy, hne⟩ := Φ.exists_dualProj_ne_of_get?_zero hsep hlt
    (i := i') (j := j') (by aesop) (by aesop) hcd
  by_contra! hall
  obtain ⟨p, q, hp', hpq, hq, hlen', hEq⟩ := Φ.exists_Icc_subset_image_comp (i.take n).reverse
  apply hne
  apply eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_dualProj i') (Φ.differentiableOn_dualProj j')
    (sub_pos.1 ((pow_pos (Φ.cmin_pos c.pos) _).trans_le hlen')) (Icc_subset_Icc hp' hq) _ (Φ.real_mem_open hy)
  intro t ht
  obtain ⟨x, hx, rfl⟩ := hEq ht
  have hz := Φ.real_mem_closed hx
  have h := hall x hx
  rw [Φ.dualProj_split i n (Word.length_take_of_get?_eq_some hc) hz,
    Φ.dualProj_split j n (Word.length_take_of_get?_eq_some hd) hz, ← hp, add_right_inj,
    Φ.comp_ofReal _ hx] at h
  exact mul_left_cancel₀ (Φ.deriv_comp_ne_zero _ hz) h

theorem pos_sup_dualProj_sub_iff (i j : Word N) :
    (0 < ⨆ x : I, ‖Φ.dualProj i (x : ℝ) - Φ.dualProj j (x : ℝ)‖) ↔
      ∃ x ∈ I, Φ.dualProj i x ≠ Φ.dualProj j x := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  have : Nonempty I := ⟨⟨0, by simp⟩⟩
  rw [lt_ciSup_iff ⟨2 * M, forall_mem_range.2 fun y =>
    sub_le_twice (hM i _ (Φ.real_mem_closed y.2)) (hM j _ (Φ.real_mem_closed y.2))⟩]
  simp [norm_pos_iff, sub_ne_zero, Subtype.exists]

end IFS

end AnalyticESC

namespace Challenge

open AnalyticESC Set

variable {N : ℕ}

/-- Proposition 1.8. Let `Φ = (f_i)_{i ∈ Fin N}` be an analytic IFS in `𝔖_N` with `N ≥ 2` maps.
Suppose that there is `α > 0` such that for all `i ≠ j` there is `x ∈ [0,1]` with
`|f_i''/f_i'(x) - f_j''/f_j'(x)| ≥ α`. Then `β > 0`, and if `α > 2β c_max/(1 - c_max)`, then
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with `|i| = |j|`, and `Φ`
satisfies the strong exponential separation condition. The hypothesis `N ≥ 2` ensures `β > 0`,
which can fail for a singleton IFS. -/
theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hc : 1 - cmax ε f ≠ 0)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧ (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
          dualProjFin f hd (List.ofFn j) x‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧
      SESC f) := by
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  have hβ : 0 < Φ.beta := by
    obtain ⟨x, h⟩ := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    have h₁ := Φ.norm_nonlin_le_beta ⟨0, by omega⟩ x.2
    have h₂ := Φ.norm_nonlin_le_beta ⟨1, by omega⟩ x.2
    change α ≤ ‖Φ.nonlin _ x - Φ.nonlin _ x‖ at h
    grind [norm_sub_le]
  refine ⟨hβ, fun hlt => ?_⟩
  have hpos i j hij hlen :=
    (Φ.pos_sup_dualProj_sub_iff i j).2 (Φ.exists_dualProj_ne hsep hlt hij hlen)
  refine ⟨fun n i j hij => ?_, fun i j hij => hpos (.inf i) (.inf j) (fun e => hij (Word.inf.inj e)) (fun _ => rfl),
    Φ.theorem_2_2 fun i j hij => Φ.exists_dualProj_ne_of_get?_zero hsep hlt (i := .inf i) (j := .inf j) rfl rfl hij⟩
  have he (w : List (Fin N)) (x : I) : dualProjFin f hd w x = Φ.dualProj (.fin w) x := by
    rw [dualProjFin, Φ.dualProj_fin_eq_sum, ← Fin.sum_univ_eq_sum_range]
    simp [IFS.dualTerm, Word.get?, Word.take, nonlin, IFS.nonlin, IFS.comp, Φ]
  simpa only [← he] using hpos (.fin (List.ofFn i)) (.fin (List.ofFn j))
    (fun e => hij (List.ofFn_injective (Word.fin.inj e))) (Word.sameLength_fin (by simp))

/-- Positive uniform distances between the infinite dual projections imply strong exponential
separation. -/
theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (_hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x -
        dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) : SESC f :=
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  Φ.theorem_2_2 fun i j hij => (Φ.pos_sup_dualProj_sub_iff (.inf i) (.inf j)).1
    (hinf i j (fun h => hij (congrFun h 0)))

end Challenge
