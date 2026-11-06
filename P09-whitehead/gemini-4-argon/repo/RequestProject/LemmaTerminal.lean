module

public import RequestProject.CoverChainComplex
public import RequestProject.PresentationDictionary
public import RequestProject.ExponentCorrection
public import RequestProject.Cockcroft
public import RequestProject.GenerationStep
public import RequestProject.CockcroftExtStep
public import RequestProject.BlockSubstitutionMor
public import RequestProject.WedgeSigma

@[expose] public section

/-!
# Lemma 3.10: the terminal extension `Q`

Lemma 3.10 of the paper reads:

> Suppose `P` is Cockcroft and all core generators `x_i` are trivial in `G(P)`.  Then `Q(P)`
> is Cockcroft and `T(P) ⊂ Q(P)` is zero on `π₂`.  The core group remains trivial in both new
> groups.

Here `T` is the structural operation of Lemma 3.9 (`RequestProject/LemmaStructural.lean`) and
the *terminal extension* `Q(P)` of (3.6) is `T(P)` with the letters `a_z, b_z` added as
individual relators.

Its proof has two halves.

**First half** (the `π₂` statement).  "The structural map fixes the `x_i`, so they remain
trivial.  The composite `P → T(P) → Q(P)` kills all of `G(P)`: every extra generator maps to a
commutator of two capped loops.  A map from a Cockcroft complex that kills its fundamental
group is zero on `π₂`: lift to the simply connected target cover and use naturality of
Hurewicz.  This applies to the composite.  Equation (3.3) then makes the inclusion
`T(P) → Q(P)` zero on all of `π₂`."  This half is proved here **in full**, in the
presentation model of the project:

* `FiniteChains.addRels`, `FiniteChains.addRelsMor`, `FiniteChains.PresPoint.addRels` — the
  terminal extension: adjoining relators, with its structural map;
* `FiniteChains.cells_eq_zero_of_isCockcroft_of_hom_trivial` — **a map out of a Cockcroft
  complex which kills the fundamental group is zero on `π₂`** (the augmentation argument: on
  a trivial fundamental group the coefficient ring acts through the augmentation, so the
  image of a chain only depends on the Hurewicz image of that chain, which vanishes);
* `FiniteChains.cells_eq_zero_of_generates_comp` — the passage "equation (3.3) then makes the
  inclusion zero on *all* of `π₂`";
* `FiniteChains.terminal_cells_eq_zero` — **`T(P) ⊂ Q(P)` is zero on `π₂`**;
* `FiniteChains.terminal_core_trivial` — **the core group remains trivial in both new
  groups**;
* `FiniteChains.terminal_cells_eq_zero_ruleOne` — the same conclusion for rule 1 with one
  extra generator, with no hypothesis beyond Cockcroftness of `P` and the triviality of the
  core generators: there the composite kills `G(P)` because the stable-letter relator makes
  the extra generator equal to `[a,b]`, and `a` and `b` are killed by `Q`.

**Second half** (Cockcroftness of `Q(P)`).  The paper collapses the acyclic core `D`, so that
`H₂(Q(P)) ≅ H₂(Q(P)/D)`, identifies the quotient with a wedge of block complexes, and quotes
property **(B3)** of Theorem 3.2 for each factor.  The wedge step is proved in
`RequestProject/WedgeSigma.lean`; here it is combined with the two inputs the paper quotes —
(B3) and the isomorphism induced by the collapse on second homology — into

* `FiniteChains.isCockcroft_of_collapse_to_wedge` — **if the collapse is injective on
  Hurewicz images and every block factor is Cockcroft, then the complex is Cockcroft**.

The collapse isomorphism and (B3) are exactly the inputs that Lemma 3.10 imports from
Theorem 3.2, just as (B2) is the one input carried by the moves of Lemma 3.9.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open MonoidAlgebra

universe u

/-! ### A map which kills the fundamental group is zero on Hurewicz-trivial chains -/

variable {α J α' J' : Type u} {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'}

/-- If a homomorphism of fundamental groups is trivial, then pushing coefficients along it is
the augmentation: the group ring acts on the target through `ℤ`. -/
theorem mapDomainRingHom_eq_single_augPres (h : PresGroup ρ →* PresGroup ρ')
    (htriv : ∀ g, h g = 1) (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ h c = MonoidAlgebra.single 1 (augPres ρ c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, MonoidAlgebra.single_add]
  | single g m =>
      show MonoidAlgebra.mapDomain h (MonoidAlgebra.single g m) = _
      rw [MonoidAlgebra.mapDomain_single, htriv g]
      exact congrArg (MonoidAlgebra.single (1 : PresGroup ρ') ·) (augQ_single _ _ _).symm

/-- A homomorphism out of a presented group is trivial as soon as it kills the generators. -/
theorem hom_eq_one_of_gens {H : Type u} [Group H] (h : PresGroup ρ →* H)
    (hgen : ∀ a : α, h (QuotientGroup.mk (FreeGroup.of a)) = 1) (x : PresGroup ρ) : h x = 1 := by
  have hcomp : (h.comp (QuotientGroup.mk' (relSub ρ)) : FreeGroup α →* H) = 1 :=
    FreeGroup.ext_hom _ _ hgen
  induction x using QuotientGroup.induction_on with
  | H w => exact congrArg (· w) hcomp

variable {L : Type u} (ρ : J → FreeGroup α) (ν : L → FreeGroup α)

def addRels : J ⊕ L → FreeGroup α := Sum.elim ρ ν

theorem relSub_le_relSub_addRels : relSub ρ ≤ relSub (addRels ρ ν) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  exact Subgroup.subset_normalClosure ⟨Sum.inl j, rfl⟩

def addRelsHom : PresGroup ρ →* PresGroup (addRels ρ ν) :=
  QuotientGroup.map _ _ (MonoidHom.id _) fun _ hw =>
    Subgroup.mem_comap.2 (relSub_le_relSub_addRels ρ ν hw)

@[simp] theorem addRelsHom_mk (w : FreeGroup α) :
    addRelsHom ρ ν (QuotientGroup.mk w) = QuotientGroup.mk w := rfl

noncomputable def addRelsRingHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup (addRels ρ ν)) :=
  MonoidAlgebra.mapDomainRingHom ℤ (addRelsHom ρ ν)

theorem quot_addRelsRingHom (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub (addRels ρ ν)) x = addRelsRingHom ρ ν (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      rw [quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain (addRelsHom ρ ν) (quotRingHom ℤ (relSub ρ) (single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, addRelsHom_mk]

theorem foxMatrix_addRels_inl [DecidableEq α] (i : α) (j : J) :
    foxMatrixPres (addRels ρ ν) i (Sum.inl j) = addRelsRingHom ρ ν (foxMatrixPres ρ i j) :=
  quot_addRelsRingHom ρ ν (fox i (ρ j))

theorem augPres_addRelsRingHom (z : MonoidAlgebra ℤ (PresGroup ρ)) :
    augPres (addRels ρ ν) (addRelsRingHom ρ ν z) = augPres ρ z :=
  augQ_mapDomain (addRelsHom ρ ν) z
