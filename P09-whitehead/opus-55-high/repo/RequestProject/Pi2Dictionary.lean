import RequestProject.UniversalCoverPi2
import RequestProject.CycleLifting
import RequestProject.Tac


/-!
# The condition "the inclusion is zero on `π₂`" in cellular and in Fox coordinates

Condition (1) of Theorem A is topological: for a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of
two-complexes the inclusion `X_r ⊂ X_{r+1}` is zero on `π₂`.  For a presentation complex
`π₂` is the module of cellular two-cycles of the universal cover
(`FiniteChains.Comb.univCover_bdry2_eq_zero_iff`), and the inclusion of complexes lifts to
the universal covers as the map of two-cells `(q, c) ↦ (Φ q, g c)`, where `Φ` is the map
induced on fundamental groups and `g` is the inclusion of the sets of two-cells.

This file proves that the resulting condition on cellular chains of the universal cover is
*equivalent* to the algebraic condition used in Section 2 (a Fox cycle over `ℤ[π₁(X_r)]`
has zero image in the chain module of `X_{r+1}`):
`FiniteChains.Comb.univCover_zero_pi2_iff`.

Thus the hypothesis carried by `FiniteChains.PresChain` is exactly condition (1) of the
paper, read in the combinatorial model, and nothing more.
-/

bwd

namespace FiniteChains.Comb

open MonoidAlgebra

universe u

variable {α : Type u} [DecidableEq α] {J : Type u} [Fintype J] [DecidableEq J]
variable {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q : Type u} [Group Q] {K : Type u}



omit [DecidableEq α] [Fintype J] [DecidableEq J] in
/-- The same statement in Fox coordinates: the image of a coefficient vector vanishes iff
each coefficient dies in the group ring of the next stage. -/
theorem mapDomain_mapRange_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (v : J →₀ CoverRing Nsub) :
    Finsupp.mapDomain g
        (Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v) = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (v j) = 0 := by
  classical
  constructor
  · intro h j
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      refine Finsupp.mapDomain_injective hg ?_
      simp_all
    have := congrArg (· j) h0
    simpa using this
  · intro h
    have h0 : Finsupp.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _) v = 0 := by
      grind
    simp_all

variable [Fintype α]
