module

public import RequestProject.CockcroftExtStep

@[expose] public section

/-!
# Subpresentations that are retracts: their Fox cycles have zero augmentation

This file isolates the mechanism behind the last step of Lemma 3.10 ("a wedge of Cockcroft
complexes is Cockcroft: the factor retractions detect every coordinate of a Hurewicz image").

Suppose a presentation `τ` contains a presentation `ρ` as a *block*: the generators and the
relators of `ρ` sit inside those of `τ` (injectively, and old relators are read as the same
words), no relator outside the block involves a generator of the block, and there is a
retraction of the ambient free group onto the free group of the block which carries the
relators of `τ` into the relator subgroup of `ρ`.  Then every Fox cycle of `τ` has, in the
coordinates of the block, zero augmentation as soon as `ρ` is Cockcroft
(`FiniteChains.augPres_block_eq_zero`).

The proof is the one used throughout Section 3.4: the block equations say that the block
coordinates form a cycle of the Fox matrix of `ρ`, read in the group ring of the image of
`π₁` of the block; that image is a faithful copy of `π₁` of the block because of the
retraction, so the base change statement of `RequestProject/BaseChangeCycles.lean` writes the
block coordinates as a combination of images of Fox cycles of `ρ`, whose augmentations vanish.
-/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

open MonoidAlgebra

universe u

variable {α γ : Type u} [DecidableEq γ]
variable {J L : Type u}
variable (ρ : J → FreeGroup α) (τ : L → FreeGroup γ) (f : α → γ) (g : J → L)
variable (r : FreeGroup γ →* FreeGroup α)

/-- The data expressing that the presentation `ρ` is a retract block of the presentation `τ`.
-/
structure IsBlock : Prop where
  /-- the generators of the block are included injectively -/
  gen_injective : Function.Injective f
  /-- the two-cells of the block are included injectively -/
  cell_injective : Function.Injective g
  /-- an old relator is read as the same word -/
  rel_eq : ∀ j, τ (g j) = FreeGroup.map f (ρ j)
  /-- no relator outside the block involves a generator of the block -/
  fox_outside : ∀ (i : α) (l : L), l ∉ Set.range g → @fox γ _ (f i) (τ l) = 0
  /-- the retraction restricts to the identity on the block -/
  retract_map : ∀ w : FreeGroup α, r (FreeGroup.map f w) = w
  /-- the retraction carries relators to relators -/
  retract_rel : ∀ l, r (τ l) ∈ relSub ρ

variable {ρ τ f g r} (hb : IsBlock ρ τ f g r)

include hb

theorem IsBlock.relSub_le_comap : relSub ρ ≤ (relSub τ).comap (FreeGroup.map f) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨j, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  rw [← hb.rel_eq j]
  exact Subgroup.subset_normalClosure (Set.mem_range_self _)

/-- The map of fundamental groups induced by the inclusion of the block. -/
def IsBlock.hom : PresGroup ρ →* PresGroup τ :=
  QuotientGroup.map _ _ (FreeGroup.map f) hb.relSub_le_comap

@[simp] theorem IsBlock.hom_mk (w : FreeGroup α) :
    hb.hom (QuotientGroup.mk w) = QuotientGroup.mk (FreeGroup.map f w) := rfl

theorem IsBlock.relSub_le_comap_retract : relSub τ ≤ (relSub ρ).comap r := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨l, rfl⟩
  exact Subgroup.mem_comap.2 (hb.retract_rel l)

/-- The retraction of the ambient presented group onto the block. -/
def IsBlock.retract : PresGroup τ →* PresGroup ρ :=
  QuotientGroup.map _ _ r hb.relSub_le_comap_retract

/-- The ring map of group rings induced by the inclusion of the block. -/
noncomputable def IsBlock.ringHom :
    MonoidAlgebra ℤ (PresGroup ρ) →+* MonoidAlgebra ℤ (PresGroup τ) :=
  MonoidAlgebra.mapDomainRingHom ℤ hb.hom

theorem IsBlock.quot_freeRingMap (x : FreeGroupRing α) :
    quotRingHom ℤ (relSub τ) (freeRingMap f x) = hb.ringHom (quotRingHom ℤ (relSub ρ) x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w m =>
      show quotRingHom ℤ (relSub τ)
          (MonoidAlgebra.mapDomain (FreeGroup.map f) (MonoidAlgebra.single w m)) = _
      rw [MonoidAlgebra.mapDomain_single, quotRingHom_single]
      show _ = MonoidAlgebra.mapDomain hb.hom (quotRingHom ℤ (relSub ρ) (MonoidAlgebra.single w m))
      rw [quotRingHom_single, MonoidAlgebra.mapDomain_single, IsBlock.hom_mk]



variable [DecidableEq α]

/-- Inside the block the Fox matrix of `τ` is the image of the Fox matrix of `ρ`. -/
theorem IsBlock.foxMatrix_block (i : α) (j : J) :
    foxMatrixPres τ (f i) (g j) = hb.ringHom (foxMatrixPres ρ i j) := by
  have hfox : @fox γ _ (f i) (τ (g j)) = freeRingMap f (fox i (ρ j)) := by
    rw [hb.rel_eq j]
    exact fox_map f hb.gen_injective i (ρ j)
  show quotRingHom ℤ (relSub τ) (fox (f i) (τ (g j))) = _
  rw [hfox, hb.quot_freeRingMap]
  rfl
