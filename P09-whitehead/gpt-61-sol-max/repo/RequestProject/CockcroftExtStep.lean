import Mathlib.Tactic

import RequestProject.Pi2ExtensionInjective

/-!
# The extension steps of rule 1 preserve the Cockcroft property

Lemma 3.9 concludes, from the generation statement (3.3), that the operation `T` preserves
Cockcroftness: "If `P` is Cockcroft, Hurewicz kills each structural image, by naturality, and
each translate, since the fundamental-group action becomes trivial in ordinary homology."

In the combinatorial model the Hurewicz map is the augmentation `ℤ[G] → ℤ` applied to each
coordinate of a Fox cycle (`RequestProject/Cockcroft.lean`), so the argument becomes: the
augmentation of a `ℤ[G']`-combination of images of Fox cycles of `P` is the corresponding
integer combination of the augmentations of those cycles, hence zero.  Together with
`RequestProject/Pi2Generation.lean` this proves, for the two extensions used in rule 1:

* `FiniteChains.isCockcroft_extRel` — the enlarged presentation is Cockcroft whenever the old
  one is;
* `FiniteChains.isCockcroft_tietze`, `FiniteChains.isCockcroft_hnn` — the two instances, with
  no hypothesis on the fundamental groups beyond the infinite-order condition of the paper.
-/



namespace FiniteChains

open MonoidAlgebra


variable {α : Type u} [Fintype α] [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable (ρ : J → FreeGroup α) (w₀ : FreeGroup (Option α))

omit [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The augmentation is unchanged by pushing coefficients along a homomorphism of groups. -/
theorem augQ_mapDomain {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (x : MonoidAlgebra ℤ G) :
    (MonoidAlgebra.lift ℤ ℤ G' 1).toRingHom (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g m =>
      simp_all

end FiniteChains
