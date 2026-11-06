module

public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Separation

@[expose] public section

/-!
# Lemma 5.1

A map of the class has a unique fixed point `p ∈ [0,1]`. For `a, b ∈ ℝ` with `b ≠ 0` there is an
invertible `g ∈ C^ω_ε([0,1])` with `g'' = Ĥ_f g'`, `g(p) = a` and `g'(p) = b`; and every solution
`g` of `g'' = Ĥ_f g'` on `[0,1]` conjugates `f` to the affine map `y ↦ f'(p) y + g(p)(1 - f'(p))`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

variable {ε : ℝ} {f : ℂ → ℂ}

/-- A map of the class has a fixed point in `[0,1]`. -/
theorem exists_fixedPoint (hε : 0 < ε) (hf : InClass ε f) :
    ∃ p ∈ I, f p = p := by
  let Ψ := koenigsIFS hε hf
  set p := Ψ.natProj fun _ => 0
  have hp : p ∈ I := Ψ.attractor_subset_I ⟨_, rfl⟩
  exact ⟨p, hp, (Ψ.comp_ofReal [0] hp).trans (congrArg _ (Ψ.natProj_eq_realMap fun _ => 0).symm)⟩

end AnalyticESC
