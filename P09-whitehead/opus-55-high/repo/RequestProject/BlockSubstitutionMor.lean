import RequestProject.GenerationStep
import RequestProject.FoxNaturality
import RequestProject.CockcroftExtStep


/-!
# Rule 3 as a structural map

`RequestProject/BlockSubstitutionPi1.lean` computes the fundamental group of the substituted
presentation (3.4) of rule 3.  This file produces the *structural map* of rule 3 in the sense
of `RequestProject/GenerationStep.lean`, i.e. it equips the substitution with its induced map
on the two-chains of the universal covers and proves that this map is semilinear, carries Fox
cycles to Fox cycles and preserves zero augmentations.  After that, rule 3 enters the
composite operation `T` on exactly the same footing as rules 1 and 2: `Generates.comp`,
`isCockcroft_of_generates` and `cells_eq_zero_of_generates` apply to it verbatim, and the
*only* thing that the block still has to supply is the generation property (B2) itself.

The set-up is the indexed form of (3.4).  The source presentation is
`ρ : Option J → FreeGroup α`, where `ρ none = r` is the replaced entry and the `ρ (some j)`
are the retained ones; the target is

  `substPres ρ bsub : J ⊕ M → FreeGroup (α ⊕ Z)`,
  `inl j ↦ r_j` (read in the larger free group),  `inr m ↦ β_m(u, v, Z)`.

Two things are assumed, and both are the algebraic shadow of the chosen filling of (B1):

* `hfill` — the replaced relator `r` dies in the group of (3.4).  This is proved from the
  filling in `FiniteChains.BlockSubst.mk_map_inl_relator_eq_one`;
* the two-chain `c : M → ℤ[G']` carried by the filling, whose cellular boundary is the
  boundary of the replaced two-cell (`hbdry_base`) and which involves no internal generator
  in a spurious way (`hbdry_int`).  In the pushout of the paper this chain is the image of
  the fundamental class of `Σ_q` under `b_q`.

Nothing here assumes anything about the block beyond these identities; in particular the
generation property (B2) is *not* proved, and by
`FiniteChains.BlockSubst.baseHom_not_injective` it cannot be, from presentations alone.
-/


namespace FiniteChains.BlockMor



variable {α Z J M : Type u}




variable (ρ : Option J → FreeGroup α) (bsub : M → FreeGroup (α ⊕ Z))






section Fox

variable [Fintype α] [DecidableEq α] [Fintype Z] [DecidableEq Z]
  [Fintype J] [DecidableEq J] [Fintype M] [DecidableEq M]

/-! ### Naturality of the Fox matrix -/

theorem mapDomainRingHom_comp' {G H K} [Group G] [Group H] [Group K]
    (g : H →* K) (f : G →* H) x :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x := by
  simp




/-! ### The structural map on two-chains -/






variable {ρ bsub hfill c}



variable (ρ bsub hfill c)



/-! ### The hypotheses are satisfiable

The data assumed above do occur: the *trivial block*, whose single relator is the replaced
one and whose filling chain is the corresponding single two-cell, satisfies them.  (It is of
course not a surface block: it has no internal generators and does not change the
presentation.  The point of the example is only that `IsFilling` is not vacuous.) -/
