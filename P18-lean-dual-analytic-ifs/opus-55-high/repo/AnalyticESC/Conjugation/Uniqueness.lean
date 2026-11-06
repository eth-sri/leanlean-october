module

public import AnalyticESC.Conjugation.Linearisation
public import AnalyticESC.Conjugation.Basic

public section

/-!
# Uniqueness of linearisations of a single map

For a map `f` of the class: `Ĥ_f` satisfies the fixed-point equation of the dual operator of `f`;
a linearisation `φ` of `f` with `φ' ≠ 0` satisfies `φ'' = Ĥ_f φ'`; solutions of `φ'' = Ĥ_f φ'`
are affine functions of the linearising map `ĝ` of (5.2); and `Ĥ_f` depends only on `f` on `[0,1]`.
-/

namespace AnalyticESC

variable {g : ℂ → ℂ}

open Set

variable {f : ℂ → ℂ}

/-- The real restriction of a map holomorphic on `B_ε` is analytic near `[0,1]`. -/
theorem analyticOnNhd_re_ofReal (hε : 0 < ε) (hg : DifferentiableOn ℂ g (nbhd ε)) :
    AnalyticOnNhd ℝ (fun x : ℝ => (g x).re) I := by
  intro x hx
  have ha : AnalyticAt ℝ g x :=
    (hg.analyticOnNhd isOpen_nbhd x (ofReal_mem_nbhd hε hx)).restrictScalars
  exact (Complex.reCLM.analyticAt _).comp (ha.comp (Complex.ofRealCLM.analyticAt x))

/-- `Ĥ_f` depends only on `f` on `[0,1]`. -/
theorem hatH_eq_of_eqOn_I (hε : 0 < ε) (hf : InClass ε f) (hε' : 0 < ε')
    (hg : InClass ε' g) (h : Ɐ f x = g x) : Ɐ hatH f x = hatH g x := by
  -- `δ = min ε ε'`
  obtain ⟨δ, hδ, hδε, hδε', hcase⟩ : ∃ δ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ ε' ∧ (δ = ε ∨ δ = ε') := by grind
  have hδ2 : nbhd δ ⊆ 𝔑 δ := nbhd_mono (by linarith)
  -- `f = g` on `B_{2δ}` by the identity theorem
  have hfg : EqOn f g (𝔑 δ) :=
    eqOn_nbhd_of_eqOn_Icc (by linarith) (hf.differentiableOn.mono (nbhd_mono (by linarith)))
      (hg.differentiableOn.mono (nbhd_mono (by linarith))) zero_lt_one subset_rfl h
  -- `f` maps `B_δ` into itself: for `δ = ε` by (B), and for `δ = ε'` since `f = g` there
  have hmaps : MapsTo f (nbhd δ) (nbhd δ) := by
    rcases hcase with rfl | rfl
    · exact fun z hz => hf.mapsTo (subset_closure hz)
    · intro z hz
      exact hfg (hδ2 hz) ▸ hg.mapsTo (subset_closure hz)
  have hiter : ∀ k, ∀ z ∈ nbhd δ, f^[k] z = g^[k] z ∧ f^[k] z ∈ nbhd δ := by
    intro k
    induction k with
    | zero => exact fun z hz => ⟨rfl, hz⟩
    | succ k ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := ih (f z) (hmaps hz)
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg (hδ2 hz)]
      exact ⟨h1, h2⟩
  have hd1 := hfg.deriv isOpen_nbhd
  have hd2 := hd1.deriv isOpen_nbhd
  have hdk : ∀ k, EqOn (deriv (f^[k])) (deriv (g^[k])) (nbhd δ) :=
    fun k => EqOn.deriv (fun z hz => (hiter k z hz).1) isOpen_nbhd
  intro x hx
  have hxδ := ofReal_mem_nbhd hδ hx
  refine tsum_congr fun k => ?_
  grind

end AnalyticESC
