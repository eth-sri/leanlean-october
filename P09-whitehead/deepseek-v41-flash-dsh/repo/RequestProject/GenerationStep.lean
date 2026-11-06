module

public import RequestProject.Pi2Generation

@[expose] public section

/-!
# Structural maps with the generation property, and their composites

Lemma 3.9 of the paper states the generation equation

  `π₂(T(P)) = ℤ[G(T(P))] · η_{P*} π₂(P)`                                          (3.3)

for the operation `T`, and then *composes*: `T` is a finite sequence of elementary moves
(rules 1–3), each of which has the generation property, and the paper concludes with
"Composing proves (3.3)".  The two consequences drawn from (3.3) are also formal:
Cockcroftness is inherited by the target, and a map which is zero on `π₂` upstairs stays
zero on `π₂` after applying `T`.

This file isolates that formal layer.  A **structural map** `PresMor ρ ρ'` between two
presentations is a homomorphism of the presented groups together with the induced map of
two-chains, semilinear over it and carrying Fox cycles to Fox cycles and zero augmentations
to zero augmentations.  `FiniteChains.Generates` is equation (3.3) for such a map.  The
results are:

* `FiniteChains.Generates.comp` — the generation property is stable under composition,
  which is exactly the step "composing proves (3.3)";
* `FiniteChains.isCockcroft_of_generates` — a structural map with the generation property
  transports the Cockcroft property (`P` Cockcroft ⟹ `T(P)` Cockcroft);
* `FiniteChains.cells_eq_zero_of_generates` — the last paragraph of Lemma 3.9: for a
  commuting square `T(j) ∘ η_P = η_{P'} ∘ j`, if `j` is zero on `π₂` and (3.3) holds for
  `η_P`, then `T(j)` is zero on all of `π₂(T(P))`.

The elementary move of rule 1 is packaged as a `PresMor` in
`RequestProject/GenerationIterate.lean`, where the composite of finitely many moves is
treated.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open MonoidAlgebra


section

variable {α J α' J' α'' J'' : Type u}
  [Fintype α] [DecidableEq α] [Fintype J]
  [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J'']

/-- A **structural map** between presentation complexes: the induced homomorphism of
fundamental groups together with the induced map on two-chains of the universal covers.
The map on chains is additive, semilinear over the group homomorphism, carries Fox cycles
(elements of `π₂`) to Fox cycles, and carries chains with zero augmentation to chains with
zero augmentation (naturality of the Hurewicz map). -/
structure PresMor (ρ : J → FreeGroup α) (ρ' : J' → FreeGroup α') where
  /-- The induced map of fundamental groups. -/
  hom : PresGroup ρ →* PresGroup ρ'
  /-- The induced map of two-chains. -/
  cells : (J → MonoidAlgebra ℤ (PresGroup ρ)) → (J' → MonoidAlgebra ℤ (PresGroup ρ'))
  cells_add : ∀ y z, cells (y + z) = cells y + cells z
  cells_smul : ∀ (c : MonoidAlgebra ℤ (PresGroup ρ)) (y : J → MonoidAlgebra ℤ (PresGroup ρ)),
    cells (c • y) = MonoidAlgebra.mapDomainRingHom ℤ hom c • cells y
  /-- The map carries `π₂` into `π₂`. -/
  cells_cycle : ∀ y, IsFoxCycle ρ y → IsFoxCycle ρ' (cells y)
  /-- Naturality of the Hurewicz map: zero augmentations go to zero augmentations. -/
  cells_aug : ∀ y, (∀ j, augPres ρ (y j) = 0) → ∀ j', augPres ρ' (cells y j') = 0

namespace PresMor

variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}

omit [Fintype α] [Fintype α'] in
@[simp] theorem cells_zero (f : PresMor ρ ρ') : f.cells 0 = 0 := by
  have h := f.cells_smul 0 0
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

omit [Fintype α] [DecidableEq α] [Fintype J] [Fintype α'] [DecidableEq α'] [Fintype J']
  [Fintype α''] [DecidableEq α''] [Fintype J''] in
/-- Pushing coefficients along a composite of group homomorphisms. -/
theorem mapDomainRingHom_comp (g : PresGroup ρ' →* PresGroup ρ'') (f : PresGroup ρ →* PresGroup ρ')
    (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) c
      = MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f c) := by
  change MonoidAlgebra.mapDomain (g.comp f) c = MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f c)
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl

/-- The composite of two structural maps. -/
def comp (g : PresMor ρ' ρ'') (f : PresMor ρ ρ') : PresMor ρ ρ'' where
  hom := g.hom.comp f.hom
  cells := fun y => g.cells (f.cells y)
  cells_add := fun y z => by rw [f.cells_add, g.cells_add]
  cells_smul := fun c y => by
    rw [f.cells_smul, g.cells_smul, mapDomainRingHom_comp]
  cells_cycle := fun y hy => g.cells_cycle _ (f.cells_cycle _ hy)
  cells_aug := fun y hy => g.cells_aug _ (f.cells_aug _ hy)

omit [Fintype α] [Fintype α'] [Fintype α''] in
@[simp] theorem comp_cells (g : PresMor ρ' ρ'') (f : PresMor ρ ρ')
    (y : J → MonoidAlgebra ℤ (PresGroup ρ)) : (g.comp f).cells y = g.cells (f.cells y) := rfl

end PresMor

variable {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}

end

end FiniteChains
