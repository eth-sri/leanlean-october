/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedSuccessor

/-! # Protected decoding on the actual padded growth successor

Both physical source sections are constructed lawfully by the successor.
The protected inverse then retains every actual coordinate at the native cut,
including unused rungs and long tips. Its decoded output is lawful without a
shortness assumption on the inherited rows.

The two source-repair corollaries accept a lawful original-face prescription
at this native cut. They are not arbitrary-ambient lifting: constructing that
prescription from an external physical chart, and restoring above an owner,
are separate obligations. Adapted from `LowOnlyPaddedDecode`, consuming the
actual growth fibres rather than substituting LOW.
-/

namespace VaughtConjecture.Knight.GrowthPaddedDecode
open   ExtOrd  Growth CanonicalPairedInverse
open GrowthPaddedSuccessor GrowthOrderedBase
noncomputable section

section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  {X : RelativeData DA semA DQ semQ} {j b : ℕ}
  {a : Field DA DQ → ExtOrd} {S : State DA DQ}

/-- The replacement indexes the existing fixed catalogue. -/
def repairAnchor (r : ProtectedRepair X a S j b) : Catalogue X j :=
  ⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩

theorem grid_fixed_below (r : ProtectedRepair X a S j b)
    {z} (hz : z ∈ PairedSlotComparison.sourceGrid j (Fintype.card (Field DA DQ)))
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
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "source₀" => source I X T hA hB hC

def protected_caps {b} {a : Catalogue X 2} {S}
    (r : ProtectedRepair X a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    d :=  OrbitPrefixSupport.decode_agree r.witness (grid_visible 2 b)
    (by exact?) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported a)
    (source_prefix I X T hA hB hC (repairAnchor r) a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)

def protected_lawful {b} {a : Catalogue X 2} {S}
    (r : ProtectedRepair X a.val S 2 b)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1) := (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful I X T hA hB hC a) (source_lawful I X T hA hB hC (repairAnchor r))
    (fun d => d.2.2) (grid_visible 2 b) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported a d.1)
    (fun d => source_prefix I X T hA hB hC (repairAnchor r) a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

local notation "original₀" => original I X T hA hB hC

theorem original_decode {b} {a : Catalogue X 2} {S}
    (r : ProtectedRepair X a.val S 2 b) d :
    r.decoder (source₀ (repairAnchor r) (original₀ d)) =
      S.profile (field I d) := by
  rw [original_readback]
  exact r.readback _

/-- Physical private occurrences in the grade-two target. -/
def privateAt (d : I.right.scheme.below (Finset.univ, 2)) :
    (carrier₀).below (A, 2) :=
  ⟨original₀ (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    change I.boundary.grade (I.rightFace.map d.1) = I.right.scheme.grade d.1 at hg
    exact hg.le.trans d.2.2⟩

/-- Physical donor occurrences in the same target. -/
def donorAt (d : I.left.scheme.below (Finset.univ, 2)) :
    (carrier₀).below (A, 2) :=
  ⟨original₀ (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    change I.boundary.grade (I.leftFace.map d.1) = I.left.scheme.grade d.1 at hg
    exact hg.le.trans d.2.2⟩

theorem private_source_repair {b} {S}
    (hS : Admitted X 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {v}
    (hv : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) v)
    (hag : ∀ d, min (v d) (grid 2 b) = min (S.privateValues d.1) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (privateAt I X T hA hB hC d) = v d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, _, ⟨r⟩⟩ := T.private_protected_all (by decide) hS hc hv hag
  refine ⟨_, protected_lawful I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I X T hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.rightFace.map d.1)).trans
    ((field_private T hS' d.1).trans
        (he d))

theorem donor_source_repair (hN : 2 < X.req.N) {b} {S}
    (hS : Admitted X 2 S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) 2)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {u}
    (hu : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) u)
    (hag : ∀ d, min (u d) (grid 2 b) = min (S.donorValues d.1) (grid 2 b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (donorAt I X T hA hB hC d) = u d) ∧
      ∀ d, min (w d) (grid 2 b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1) (grid 2 b) := by
  obtain ⟨S', hS', he, _, _, _, ⟨r⟩⟩ := T.donor_protected_before (by decide) hN hS hc hu hag
  refine ⟨_, protected_lawful I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps I X T hA hB hC
      (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode I X T hA hB hC
    (a := ⟨S.profile, hc, S, hS, rfl⟩) r (I.leftFace.map d.1)).trans
    ((field_donor I).trans (he d))

