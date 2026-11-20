/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.CoatomSeedInstallation

@[expose] public section

namespace VaughtConjecture.Knight.SmallCoatomSeeds

open Transform Value ExtOrd AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput

open CoatomBoundaryExtension CoatomSeedInstallation

noncomputable section

section One

variable {s : Step (Finset.univ : Finset (Fin 2))} {m : ℕ} (I : Input s m 1 1)

abbrev oneHeight : 1 ≤ (Finset.univ : Finset (Fin 2)).card := by simp

theorem oneGrade (d : Cell I.boundary) : I.boundary.grade d ≤ 1 := by
  simpa only [max_self] using I.grade_le d

def one : Seed I where
  scheme := CanonicalOneCoatom.scheme I.rows oneHeight
  rows := CanonicalOneCoatom.rows I.rows oneHeight I.proper (oneGrade I)
  plan := rfl
  boundary := OrderEmbedding.ofStrictMono (CanonicalOneCoatom.old I.rows oneHeight)
    (SourceLayerCarrier.old_order _ _ _ _ _)
  index d := SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)
  exhaustive B hB z hz := by
    rcases CanonicalOneCoatom.coverage I.rows oneHeight z with h | he
    · exact h
    · exact (hB (he ▸ hz)).elim
  row c d := CanonicalFieldLayer.inherited_row I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) c d
  consistent := CanonicalFieldLayer.consistent I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) I.consistent
  coded := CanonicalSeedCoding.fieldLayer I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight I.proper (oneGrade I) I.coded
  bountiful := by
    apply CanonicalOneCoatom.bountiful I.rows oneHeight I.proper (oneGrade I)
      (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
      (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
      (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
      (by rw [I.left_card]) (by rw [I.right_card]) I.intersection_visible
      (fun _ hC hCA => proper_scope_cover s hC hCA)
    intro C hC hCA hCc
    exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, (by decide : 0 < 1), hCc⟩) hCA
  grade := CanonicalFieldLayer.max_grade I.rows 1 (Cell I.boundary) id (by decide)
    oneHeight (oneGrade I)
  complete := CanonicalOneCoatom.complete I.rows oneHeight
    (fun _ hJ hp => I.complete_proper hJ hp)
  extend_whole _ hp := CanonicalOneCoatom.exists_whole I.rows oneHeight I.proper (oneGrade I) hp

end One

section Two

variable {s : Step (Finset.univ : Finset (Fin 3))} {m : ℕ} (I : Input s m 2 2)

abbrev twoHeight : 2 ≤ (Finset.univ : Finset (Fin 3)).card := by simp

theorem twoGrade (d : Cell I.boundary) : I.boundary.grade d ≤ 2 := by
  simpa only [max_self] using I.grade_le d

def two : Seed I where
  scheme := CanonicalPairLocalSections.carrier I.rows twoHeight
  rows := CanonicalPairLocalSections.semantics I.rows twoHeight I.proper
  plan := rfl
  boundary := CanonicalRecursiveInventory.boundary I.rows 2 twoHeight
  index := CanonicalRecursiveInventory.boundary_cell I.rows 2 twoHeight
  exhaustive B hB z hz := by
    rcases CanonicalRecursiveCoverage.coverage I.rows 2 twoHeight z with h | he
    · exact h
    · exact (hB (he ▸ hz)).elim
  row c d := GradeCutPairRows.old_row I.boundary _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide)
    I.rows (CanonicalPairLocalSections.smallRows I.rows twoHeight I.proper) c d
  consistent := CanonicalPairBoundary.consistent I.rows 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide)
    I.consistent
  coded := CanonicalSeedCoding.pair I.rows twoHeight I.proper I.coded
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound I.rows 2 twoHeight (twoGrade I)) (by decide : 0 < 2)
    intro C B j hC hB hj hCB
    apply CanonicalPairLowerLifting.lower_lift I.rows I.proper twoHeight
      (CoatomRecursiveInput.oldLifts I) I.left_visible I.right_visible
      (fun h => Finset.notMem_erase s.a Finset.univ (h.symm ▸ s.ha))
      (fun h => Finset.notMem_erase s.b Finset.univ (h.symm ▸ s.hb))
      (by rw [I.left_card]) (by rw [I.right_card]) I.intersection_visible
      (fun _ hC hCA => proper_scope_cover s hC hCA) _ hC hB ⟨hCB, le_rfl⟩ hj
    intro C hC hCA i hi hiC _
    exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, hi, hiC⟩) hCA
  grade := CanonicalRecursiveCoverage.grade_bound I.rows 2 twoHeight (twoGrade I)
  complete := CanonicalRecursiveCoverage.complete_through I.rows 2 twoHeight
    (fun _ hJ hproper => I.complete_proper hJ hproper)
  extend_whole _ hp := CanonicalPairBoundary.exists_whole I.rows 1 2 (by decide)
    (CanonicalPairLocalSections.one_le twoHeight) (by decide) twoHeight I.proper (by decide) hp

end Two

end

end VaughtConjecture.Knight.SmallCoatomSeeds
