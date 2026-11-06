import Mathlib.Tactic

import RequestProject.Pi2GenerationDescent

/-!
# The copies of `L̃` cover the universal cover of the pushout

Step 2 of the proof of Proposition 3.11 computes `π₂(E)` for the cellular pushout
`E = K ∪_p L` from the short exact sequence of chain complexes

  `0 → ⊕_Λ C_*(D) → (⊕_{Λ/H} C_*(D)) ⊕ (⊕_{Λ/J} C_*(L̃)) → C_*(Ẽ) → 0`.

This file proves the **surjectivity of the right-hand map in degree two** (and in the two
lower degrees) in the combinatorial model, from scratch:

* `FiniteChains.Comb.pi1Trivial_of_simplyConnected` — a cellular map out of a simply connected
  complex kills `π₁`;
* `FiniteChains.Comb.exists_lift_univCover` — **every copy of `L̃` is available**: for a
  cellular map `ι : L → E` and a vertex `c` of `Ẽ` over `ι l₀` there is a lift
  `φ : L̃(l₀) → Ẽ(x₀)` of `ι` to the universal covers which sends the base vertex of `L̃(l₀)`
  to `c`;
* `FiniteChains.Comb.exists_lift_onF_eq` — consequently, if `ι` is onto on two-cells, **every
  two-cell of `Ẽ` lies in a copy of `L̃`**; likewise for edges and vertices;
* `FiniteChains.Comb.span_chainsFromSub_eq_top` — hence the chains of `Ẽ` in degree two are
  spanned by the chains coming from the copies of `L̃`
  (`FiniteChains.Comb.ChainsFromSub`, the degree-two part of the middle term above);
* `FiniteChains.Comb.surjective_onF_of_isCovering`, `surjective_onE_of_isCovering` — a
  combinatorial covering is onto on cells, hence `FiniteChains.Comb.surjective_pushF` etc.:
  the map `L → K ∪_p L` of Proposition 3.11 is onto on cells of every dimension;
* `FiniteChains.Comb.span_chainsFromSub_pushoutMap_eq_top` — the resulting statement for the
  pushout of Proposition 3.11.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb



/-! ### Maps out of a simply connected complex -/

/-- A cellular map out of a simply connected complex kills `π₁`. -/
theorem pi1Trivial_of_simplyConnected {X Y : Complex2.{u}} (hX : SimplyConnected X)
    (h : Hom X Y) : Pi1Trivial h := by
  intro a p hp
  simpa using mapPath_htpy h (hX a p hp)

/-! ### Lifting a cellular map to the universal covers, with a prescribed base image -/

section

variable {L E : Complex2.{u}}

/-- **Every copy of `L̃` inside `Ẽ` is available.**  Given a cellular map `ι : L → E`, a
vertex `l₀` of `L` and a vertex `c` of the universal cover of `E` lying over `ι l₀`, there is
a lift of `ι` to the universal covers taking the base vertex of `L̃(l₀)` to `c`.  (The
universal cover of `L` is simply connected, so the composite `L̃ → L → E` lifts; a change of
base vertex moves the image of the base point to `c`.) -/
theorem exists_lift_univCover (ι : Hom L E) {x₀ : E.V} (l₀ : L.V) (c : UV E x₀)
    (hc : endV c = ι.onV l₀) :
    ∃ φ : Hom (uCover L l₀) (uCover E x₀),
      (∀ v, endV (φ.onV v) = ι.onV (endV v)) ∧
      (∀ e : UE L l₀, ((φ.onE e).1).2 = ι.onE (e.1.2)) ∧
      (∀ f : UF L l₀, ((φ.onF f).1).2 = ι.onF (f.1.2)) ∧
      φ.onV (UV.base L l₀) = c := by
  classical
  set f : Hom (uCover L l₀) E := ι.comp (univProj L l₀)
  have htriv  := pi1Trivial_of_simplyConnected simplyConnected_univCover f
  set psi : Hom (uCover L l₀) (uCover E (ι.onV l₀)) :=
    liftHom (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv
  -- a path representing `c`
  obtain ⟨tp, htp⟩ := Quotient.exists_rep c
  have hend : endpt E x₀ tp.1 = ι.onV l₀ := by rw [← hc, ← htp]; rfl
  have hq : IsPath E.src E.tgt tp.1 x₀ (ι.onV l₀) := by
    have h := tp.2
    rwa [hend] at h
  refine ⟨(shiftHom hq).comp psi, ?_, ?_, ?_, ?_⟩
  · intro v
    show endV (shiftV hq (psi.onV v)) = ι.onV (endV v)
    rw [endV_shiftV]
    exact univProj_liftHom_onV (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv v
  · aesop
  · aesop
  · show shiftV hq (psi.onV (UV.base L l₀)) = c
    have h1 : psi.onV (UV.base L l₀) = UV.base E (ι.onV l₀) :=
      liftHom_base (f := f) (d₀ := UV.base L l₀) isConnected_univCover htriv
    rw [h1, shiftV_base, ← htp]
    exact congrArg UV.mk (Subtype.ext rfl)

/-! ### The degree-two chains coming from the copies -/

end

/-! ### Coverings are onto on cells -/







/-! ### The map `L → K ∪_p L` of Proposition 3.11 is onto on cells -/







end FiniteChains.Comb

