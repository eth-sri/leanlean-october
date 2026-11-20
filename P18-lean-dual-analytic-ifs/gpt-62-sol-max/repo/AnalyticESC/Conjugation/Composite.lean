module

public import AnalyticESC.Conjugation.Linearisation
public import AnalyticESC.Generic.Class
public import AnalyticESC.Analysis

@[expose] public section

/-! The logarithmic derivative of a composition is the dual projection of its reversed
periodic word, by uniqueness of the contracting affine recursion. -/

namespace AnalyticESC

open Set Metric Filter Topology

/-- `List.ofFn (w ∘ Fin.rev) = (List.ofFn w)^←`. -/
private theorem composite_ofFn_comp_rev {α : Type*} {m : ℕ} (w : Fin m → α) :
    List.ofFn (w ∘ Fin.rev) = (List.ofFn w).reverse := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  grind

private theorem continuousOn_onReal {ε : ℝ} {h : ℂ → ℂ} (hε : 0 < ε)
    (hh : DifferentiableOn ℂ h (nbhd ε)) : ContinuousOn (fun x : ℝ => h x) I :=
  hh.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun _ => ofReal_mem_nbhd hε)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

theorem inClass_comp {w : List (Fin N)} (hw : w ≠ []) : InClass (ε / 4) (Φ.comp w) := by
  have hε := Φ.ε_pos
  have hsub : nbhd (2 * (ε / 4)) ⊆ nbhd ε := nbhd_mono (by linarith)
  have hcl : closedNbhd (ε / 4) ⊆ closedNbhd ε := closure_mono (nbhd_mono (by linarith))
  refine Challenge.InClass.of_deriv (by positivity) ((Φ.differentiableOn_comp w).mono hsub)
    (fun _ hx => Φ.im_comp_ofReal w (subset_closure (hsub hx))) (fun _ hx => Φ.re_comp_mem_I w hx)
    (fun _ hz => Φ.deriv_comp_ne_zero w (hcl hz)) (fun _ hz => ?_)
  exact ((Φ.norm_deriv_comp_bounds w (hcl hz)).2).trans_lt
    (pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne')

/-- The reversed periodic word is fixed by the dual operator of the composition. -/
private theorem dualProj_periodic_fixed {m : ℕ} (hm : 0 < m) (w : Fin m → Fin N) :
    IsDualFixed (Φ.comp (List.ofFn w))
      (fun x => Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x) := by
  let v := periodic hm (w ∘ Fin.rev)
  have ht : (Word.inf v).take m = (List.ofFn w).reverse := by
    rw [← composite_ofFn_comp_rev]
    simp [v, periodic, Nat.mod_eq_of_lt, Function.comp_def]
  have hd : (Word.inf v).drop m = .inf v := by
    simp only [Word.drop, Word.inf.injEq]
    funext k
    simp [Word.shift, v, periodic]
  intro y hy
  dsimp only
  have hz := Φ.real_mem_closed hy
  conv_lhs => rw [Φ.dualProj_split (.inf v) m (by simp) hz, ht, hd,
    Φ.dualProj_fin_reverse _ hz, List.reverse_reverse, Φ.comp_ofReal _ hy]

theorem dualProj_const_eq_periodic {M m : ℕ} {δ : ℝ} (Ψ : IFS M δ) (i : Fin M) {w : Fin m → Fin N}
    (hm : 0 < m) (hi : Ψ.f i = Φ.comp (List.ofFn w)) :
    ∀ x ∈ I, Ψ.dualProj (.inf fun _ => i) x = Φ.dualProj (.inf (periodic hm (w ∘ Fin.rev))) x := by
  intro x hx
  exact (Ψ.eq_dualProj_of_cocycle (continuousOn_onReal Φ.ε_pos (Φ.differentiableOn_dualProj _))
    (fun _ => i) (fun _ => hi.symm ▸ Φ.dualProj_periodic_fixed hm w) x hx).symm

theorem dualProj_periodic_eq_of_eqOn_I {m : ℕ} (hm : 0 < m) {u v : Fin m → Fin N}
    (h : ∀ x ∈ I, Φ.comp (List.ofFn u) x = Φ.comp (List.ofFn v) x) :
    ∀ x ∈ I, Φ.dualProj (.inf (periodic hm (u ∘ Fin.rev))) x =
      Φ.dualProj (.inf (periodic hm (v ∘ Fin.rev))) x := by
  let Ψ : IFS 1 (ε / 4) := ⟨fun _ => Φ.comp (List.ofFn v), by positivity [Φ.ε_pos],
    fun _ => Φ.inClass_comp (by aesop)⟩
  let W := fun x : ℝ => Φ.dualProj (.inf (periodic hm (u ∘ Fin.rev))) x
  have h₁ : IsDualFixed (Ψ.f 0) W := by
    have he := eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp _) (Φ.differentiableOn_comp _)
      zero_lt_one subset_rfl h
    intro x hx
    have hz := Φ.real_mem_open hx
    have hd := he.deriv (isOpen_nbhd ε)
    simpa only [Ψ, he hz, hd hz, (hd.deriv (isOpen_nbhd ε)) hz] using Φ.dualProj_periodic_fixed hm u x hx
  intro x hx
  exact (Ψ.eq_dualProj_of_cocycle (continuousOn_onReal Φ.ε_pos (Φ.differentiableOn_dualProj _))
    (fun _ => 0) (fun _ => h₁) x hx).trans (Φ.dualProj_const_eq_periodic Ψ 0 hm rfl x hx)

end IFS
end AnalyticESC
