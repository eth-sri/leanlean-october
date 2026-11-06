import Mathlib.Tactic

import RequestProject.WedgeCockcroft

/-!
# An arbitrary wedge of Cockcroft complexes is Cockcroft

The last paragraph of Lemma 3.10 collapses the acyclic core of the terminal extension and
identifies the quotient with a wedge

  `Q(P)/D ≃ ⋁_r K⟨Z_r | β_{q(r),j}(1,…,1,Z_r)⟩`

*indexed by the extra relator labels* `r`, and then argues: "A wedge of Cockcroft complexes
is Cockcroft: its `H₂` is the direct sum of those of the factors, and the factor retractions
detect every coordinate of a Hurewicz image."

`RequestProject/WedgeCockcroft.lean` proves this for a wedge of two factors.  This file proves
it for a wedge of an arbitrary finite family of presentations, which is the form the lemma
uses: the generators (resp. the two-cells) of the wedge are the disjoint union of the
generators (resp. two-cells) of the factors, and the retraction onto the `s`-th factor kills
the generators of all other factors.

* `FiniteChains.sigmaWedgeRel` — the presentation of the wedge of a family;
* `FiniteChains.isBlock_sigmaWedge` — every factor is a retract block of the wedge;
* `FiniteChains.isCockcroft_sigmaWedgeRel` — **a wedge of Cockcroft complexes is
  Cockcroft**.
-/

namespace FiniteChains




variable {S : Type u} {α : S → Type u} {J : S → Type u} (ρ : ∀ s, J s → FreeGroup (α s))

/-- The presentation of the wedge of a family of presentations: the generators and the
relators of all the factors, side by side. -/
def sigmaWedgeRel : (Σ s, J s) → FreeGroup (Σ s, α s) :=
  fun p => FreeGroup.map (Sigma.mk p.1) (ρ p.1 p.2)

@[simp] theorem sigmaWedgeRel_mk (s : S) (j : J s) :
    sigmaWedgeRel ρ ⟨s, j⟩ = FreeGroup.map (Sigma.mk s) (ρ s j) := rfl

variable [DecidableEq S]

/-- The retraction of the ambient free group onto the `s`-th factor: it kills the generators
of all the other factors. -/
def killOther (s : S) : FreeGroup (Σ t, α t) →* FreeGroup (α s) :=
  FreeGroup.lift fun p => if h : p.1 = s then FreeGroup.of (h ▸ p.2) else 1

@[simp] theorem killOther_map_self (s : S) (w : FreeGroup (α s)) :
    killOther (α := α) s (FreeGroup.map (Sigma.mk s) w) = w := by
  have h : ((killOther (α := α) s).comp (FreeGroup.map (Sigma.mk s))
      : FreeGroup (α s) →* FreeGroup (α s)) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ fun a => by
      simp [killOther]
  exact congrArg (fun F : FreeGroup (α s) →* FreeGroup (α s) => F w) h

@[simp] theorem killOther_map_other {s t : S} (hst : t ≠ s) (w : FreeGroup (α t)) :
    killOther (α := α) s (FreeGroup.map (Sigma.mk t) w) = 1 := by
  have h : ((killOther (α := α) s).comp (FreeGroup.map (Sigma.mk t))
      : FreeGroup (α t) →* FreeGroup (α s)) = 1 :=
    FreeGroup.ext_hom _ _ fun a => by
      simp [killOther, hst]
  exact congrArg (fun F : FreeGroup (α t) →* FreeGroup (α s) => F w) h

variable [∀ s, DecidableEq (α s)]

/-- **Every factor is a retract block of the wedge.** -/
theorem isBlock_sigmaWedge (s : S) :
    IsBlock (ρ s) (sigmaWedgeRel ρ) (Sigma.mk s) (Sigma.mk s) (killOther s) where
  gen_injective := sigma_mk_injective
  cell_injective := sigma_mk_injective
  rel_eq _ := rfl
  fox_outside i l hl := by
    aesop (add unsafe apply [FiniteChains.fox_map_of_not_mem_range])
  retract_map w := killOther_map_self s w
  retract_rel l := by
    obtain ⟨t, j⟩ := l
    by_cases hts : t = s
    · subst hts
      rw [sigmaWedgeRel_mk, killOther_map_self]
      exact Subgroup.subset_normalClosure (Set.mem_range_self _)
    · simp_all



end FiniteChains
