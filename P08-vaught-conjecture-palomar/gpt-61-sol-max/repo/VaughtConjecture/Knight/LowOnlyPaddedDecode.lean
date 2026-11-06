/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedSuccessor

/-! # Protected decoding on the actual padded LOW successor

Both physical source sections are constructed lawfully by the successor.
The protected inverse then retains every actual coordinate at the native cut,
including unused rungs and long tips. Its decoded output is lawful without a
shortness assumption on the inherited rows.

The two source-repair corollaries accept a lawful original-face prescription
at this native cut. They are not arbitrary-ambient lifting: constructing that
prescription from an external physical chart, and restoring above an owner,
are separate obligations.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedDecode
open   ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedSuccessor LowOnlyOrderedLadder
noncomputable section

section
variable {n K j b : ℕ} {P C : SemScheme n} {F : LowOnly.Family P C K}
  {a : Field P C → ExtOrd} {S : State P C}

theorem grid_fixed_below (r : F.ProtectedRepair a S j b)
    {z} (hz : z ∈ PairedSlotComparison.sourceGrid j (Fintype.card (Field P C)))
    (hlt : z < grid j b) : r.decoder z = z := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact r.witness.bot
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    apply r.grid_fixed
    by_contra hn
    have hi  := Nat.le_of_not_gt hn
    exact (not_le_of_gt hlt) (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl))

end

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I F hroot hA hB hC

local notation "source₀" => source I F hroot hA hB hC

def protected_caps {b} {a : F.Anchor 2} {S}
    (r : F.ProtectedRepair a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    d :=  OrbitPrefixSupport.decode_agree r.witness (grid_visible 2 b)
    (by exact?) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported a)
    (source_prefix I F hroot hA hB hC r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)

def protected_lawful {b} {a : F.Anchor 2} {S}
    (r : F.ProtectedRepair a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1) := (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful I F hroot hA hB hC a) (source_lawful I F hroot hA hB hC r.anchor)
    (fun d => d.2.2) (grid_visible 2 b) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported a d.1)
    (fun d => source_prefix I F hroot hA hB hC r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

local notation "original₀" => original I F hroot hA hB hC

theorem original_decode {b} {a : F.Anchor 2} {S}
    (r : F.ProtectedRepair a.val S 2 b) d :
    r.decoder (source₀ r.anchor (original₀ d)) =
      S.profile (field I d) := by
  rw [original_readback]
  exact r.readback _

/-- Physical private occurrences in the grade-two target. -/
def privateAt (d : I.right.scheme.below (effC n 2)) :
    (carrier₀).below (A, 2) :=
  ⟨original₀ (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    change I.boundary.grade (I.rightFace.map d.1) = I.right.scheme.grade d.1 at hg
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

/-- Physical donor occurrences in the same target. -/
def donorAt (d : I.left.scheme.below (effC n 2)) :
    (carrier₀).below (A, 2) :=
  ⟨original₀ (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    change I.boundary.grade (I.leftFace.map d.1) = I.left.scheme.grade d.1 at hg
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

theorem private_source_repair {b} {S}
    (hS : F.Admissible 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {v}
    (hv : RespectsSemanticsBelow I.right.rows (effC n 2) v)
    (hag : ∀ d, min (v d) (grid 2 b) = min (S.lowerC 2 d) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (privateAt I F hroot hA hB hC d) = v d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.private_protected_repair (by decide) hS hc hv hag
  refine ⟨_, protected_lawful I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I F hroot hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.rightFace.map d.1)).trans
    ((field_private hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS') d.1).trans
        (congrFun he d))

theorem donor_source_repair {b} {S}
    (hS : F.Admissible 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {u}
    (hu : RespectsSemanticsBelow I.left.rows (effC n 2) u)
    (hag : ∀ d, min (u d) (grid 2 b) = min (S.lowerP 2 d) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (donorAt I F hroot hA hB hC d) = u d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by decide) hS hc hu hag
  refine ⟨_, protected_lawful I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I F hroot hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode I F hroot hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.leftFace.map d.1)).trans
    ((field_read I).trans
      ((I.paste_left S'.u S'.v d.1).trans (congrFun he d)))

