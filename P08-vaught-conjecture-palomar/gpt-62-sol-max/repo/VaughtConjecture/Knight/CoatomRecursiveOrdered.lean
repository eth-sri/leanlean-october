/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomRecursiveApex
public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

@[expose] public section

namespace VaughtConjecture.Knight.CoatomRecursiveOrdered

open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan

open SemSchemeBoundaryInput CoatomRecursiveApex

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι} {s : Step A} {m n : ℕ}

variable (I : Input s m (n + 3) (n + 3)) {α : Ordinal.{0}}
  {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
  (O : Display I α p q)

abbrev boundary (d : Cell I.boundary) := old I (CoatomRecursiveDisplay.boundary I d)

theorem boundary_index (d : Cell I.boundary) : (scheme I).cell (boundary I d) =
    I.boundary.cell d :=
  (MaximalFullLayer.old_index _ _ _ _ _ _).trans
    (CanonicalRecursiveInventory.boundary_cell _ _ _ d)

theorem boundary_order : StrictMono (boundary I) :=
  (SourceLayerCarrier.old_order _ _ _ _ _).comp
    (CoatomRecursiveDisplay.boundary I).strictMono

theorem boundary_exhaustive (hB : ¬ A ⊆ B) (z : Cell (scheme I))
    (hz : (scheme I).scope z ⊆ B) :
    ∃ d, boundary I d = z := by
  have hn : (scheme I).cell z ≠ (A, n + 4) := by aesop
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (CoatomRecursiveInput.scheme I)
    Unit (n + 4) (by omega) (finalHeight I) z hn
  have hx : (CoatomRecursiveInput.scheme I).scope x ⊆ B := by
    change ((scheme I).cell (old I x)).1 ⊆ B at hz
    rwa [MaximalFullLayer.old_index] at hz
  obtain ⟨d, hd⟩ := CanonicalRecursiveInventory.proper_occurrence I.rows (n + 3)
    (CoatomRecursiveInput.height_le I) x (fun h => hB (h.trans hx))
  exact ⟨d, congrArg (old I) hd⟩

theorem boundary_row (c : Cell I.boundary) (d : I.boundary.below (I.boundary.cell c)) :
    O.rows.E (boundary I c) ⟨boundary I d.1, by rw [boundary_index, boundary_index]; grind⟩ =
      I.rows.E c d := by
  let cb := CoatomRecursiveDisplay.boundary I c
  let db : (CoatomRecursiveInput.scheme I).below ((CoatomRecursiveInput.scheme I).cell cb) :=
    ⟨CoatomRecursiveDisplay.boundary I d.1, by
      rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
      exact d.2⟩
  exact (O.old_row cb db).trans
    (CanonicalRecursiveBoundaryTransport.row I.rows I.proper n (CoatomRecursiveInput.height_le I) c d)

def face {D : CellScheme B} {sem : Semantics D} (F : ExactSemanticFace sem I.rows)
    (hB : ¬ A ⊆ B) : ExactSemanticFace sem O.rows :=
  F.through ⟨boundary I, (boundary_order I).injective⟩ (boundary_index I)
    (boundary_exhaustive I hB) (boundary_row I O)

end

end VaughtConjecture.Knight.CoatomRecursiveOrdered

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

noncomputable section

/-- Exact physical rows, exhaustive occurrence order, plan, and labels suffice
for literal ordered restriction; no relabelling or equivalence of types. -/
theorem typeMap_of_pointImage_face {α : Ordinal.{0}} {m n : ℕ}
    (t : S α n) (p : S α m) (f : Fin m ↪ Fin n) {B : Finset (Fin n)}
    (hB : Finset.univ.image f = B)
    (F : ExactSemanticFace (PointImageSemantics.rows p.scheme.scheme f hB p.scheme.rows)
      t.scheme.rows) (hmono : StrictMono F.map)
    (hplan : Plan.restrictPlan t.scheme.scheme.plan B = p.scheme.scheme.plan.image (Finset.image f))
    (hlabel : ∀ d, t.label (F.map d) = p.label d) : typeMap f t = some p := by
  have hv : Finset.univ.image f ∈ t.scheme.scheme.plan := by
    have hh : B ∈ Plan.restrictPlan t.scheme.scheme.plan B := by
      rw [hplan, ← hB]
      exact Finset.mem_image.mpr ⟨_, p.scheme.scheme.isPlan.domain_mem, rfl⟩
    exact hB ▸ (Finset.mem_inter.mp hh).1
  have hvis (c : Cell p.scheme.scheme) : t.scheme.scheme.scope (F.map c) ⊆ Finset.univ.image f := by
    change (t.scheme.scheme.cell (F.map c)).1 ⊆ _
    rw [F.index c]
    exact Finset.image_subset_image (Finset.subset_univ _)
  apply typeMap_eq_some_of_emb f t p hv F.map hmono hvis
    (fun d hd => F.exhaustive d (hB ▸ hd))
  · apply Finset.image_injective (Finset.image_injective f.injective)
    rw [image_restrictFace_plan, hB, hplan]
  · intro c
    apply Prod.ext
    · apply Finset.image_injective f.injective
      rw [CellScheme.image_pullCell_fst _ _ (hvis c)]
      exact congrArg Prod.fst (F.index c)
    · exact show t.scheme.scheme.grade (F.map c) = p.scheme.scheme.grade c from
        congrArg Prod.snd (F.index c)
  · exact hlabel
  · intro c d d' hd
    have hh := F.row c (PointImageSemantics.belowEquiv p.scheme.scheme f hB c d)
    exact (congrArg (t.scheme.rows.E (F.map c)) (Subtype.ext hd)).trans hh

end

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.CoatomRecursiveOrdered

open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan

open SemSchemeBoundaryInput CoatomRecursiveApex

noncomputable section

variable {n m : ℕ} {α : Ordinal.{0}}
  {s : Step (Finset.univ : Finset (Fin (n + 4)))}
  (I : Input s m (n + 3) (n + 3))
  {p : Cell I.left.scheme → ExtOrd} {q : Cell I.right.scheme → ExtOrd}
  (O : Display I α p q)

private theorem face_typeMap {k : ℕ} (t : S α k) (f : Fin k ↪ Fin (n + 4))
    {B : Finset (Fin (n + 4))} (hf : Finset.univ.image f = B)
    (hn : ¬ Finset.univ ⊆ B)
    (F : ExactSemanticFace (PointImageSemantics.rows t.scheme.scheme f hf t.scheme.rows) I.rows)
    (hmono : StrictMono F.map)
    (hplan : Plan.restrictPlan s.plan B = t.scheme.scheme.plan.image (Finset.image f))
    (hlabel : ∀ d, O.toType.label ((face I O F hn).map d) = t.label d) :
    typeMap f O.toType = some t := by
  apply typeMap_of_pointImage_face O.toType t f hf (face I O F hn)
    ((boundary_order I).comp hmono) _ hlabel
  exact (congrArg (fun R => Plan.restrictPlan R B)
    (CanonicalRecursiveBoundaryTransport.plan_eq I.rows (n + 3) (CoatomRecursiveInput.height_le I))).trans hplan

/-- The complete supplier for coatom input arities at least three. -/
theorem exists_amalgam (hα : Order.IsSuccLimit α) (C : CoatomPair (n + 2))
    {pa pb : S α (n + 3)} (h : C.Compatible pa pb) :
    ∃ t : S α (n + 4), C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  let I := (CoatomBoundaryPresentation.of_compatible C h).input
  let O := ofCompatible hα C h
  exact ⟨O.toType,
    ⟨face_typeMap I O pa I.placeLeft I.imageLeft (by simp) I.leftFace I.left_order I.planLeft O.left_read,
      face_typeMap I O pb I.placeRight I.imageRight (by simp) I.rightFace I.right_order I.planRight O.right_read⟩,
    O.maximal⟩

end

end VaughtConjecture.Knight.CoatomRecursiveOrdered
