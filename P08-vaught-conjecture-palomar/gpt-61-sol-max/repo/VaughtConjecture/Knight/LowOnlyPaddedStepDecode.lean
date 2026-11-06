/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedIteration
import VaughtConjecture.Knight.LowOnlyPaddedDecode

/-! # Protected repair on every constructed padded LOW successor

The scalar repair's fixed grid and orbit receipts imply cap agreement at
every actual installed coordinate. Both source sections are lawful by the
constructed recursion, so positive-cut transport gives lawful decoding even
at long inherited rows. The input is a lawful prescription at the native
source cut, not an arbitrary external ambient.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedStepDecode
open   ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedStepRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def original (d : Cell I.boundary) : Cell (carrier P hnext) :=
  old P hnext (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d))

theorem original_index d :
    (carrier P hnext).cell (original P hnext d) = I.boundary.cell d := by
  rw [original, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index,
    P.base_index, RelativeLadderLayer.old_index]

local notation "source₀" => source P hk hnext

theorem source_original a d :
    source₀ a (original P hnext d) = F.fields (k + 1) a (field I d) := by
  rw [original, source_old]
  exact (P.original_readback I F hroot hA hB hC (Nat.le_succ k)
    (state F a) (state_admissible a) (state_proper F a)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f) d).trans
    (congrFun (state_profile F a) (field I d))

theorem leaf_row a
    d :
    (rows P hk hnext).E (controller P hnext a).1 d = source₀ a d.1 :=
  (data P hk hnext).row_new _ _

local notation "grid₀" => CanonicalPairedInverse.grid (k + 1)

def protected_caps {b} {a : F.Anchor (k + 1)} {S}
    (r : F.ProtectedRepair a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    d := OrbitPrefixSupport.decode_agree r.witness (CanonicalPairedInverse.grid_visible _ _)
    (by simp_all [VaughtConjecture.Knight.gTop]) r.reaches
    (fun _ hz hlt => LowOnlyPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (source_supported P hk hnext a)
    (source_agreement P hk hnext r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq) d

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)

def protected_lawful {b} {a : F.Anchor (k + 1)} {S}
    (r : F.ProtectedRepair a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1) := (OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful P hk hnext a) (source_lawful P hk hnext r.anchor)
    (fun d => d.2.2) (CanonicalPairedInverse.grid_visible _ _) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => LowOnlyPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported P hk hnext a d.1)
    (fun d => source_agreement P hk hnext r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)).1

theorem original_decode {b} {a : F.Anchor (k + 1)} {S}
    (r : F.ProtectedRepair a.val S (k + 1) b) d :
    r.decoder (source₀ r.anchor (original P hnext d)) =
      S.profile (field I d) := by
  rw [source_original]
  exact r.readback _

local notation "effC₀" => effC n (k + 1)

def privateAt (d : I.right.scheme.below (effC₀)) :
    (carrier P hnext).below (A, k + 1) :=
  ⟨original P hnext (I.rightFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.rightFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

def donorAt (d : I.left.scheme.below (effC₀)) :
    (carrier P hnext).below (A, k + 1) :=
  ⟨original P hnext (I.leftFace.map d.1), by
    rw [original_index]
    refine ⟨I.boundary.scope_subset _, ?_⟩
    have hg := congrArg Prod.snd (I.leftFace.index d.1)
    exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

theorem private_source_repair {b} {S}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {v}
    (hv : RespectsSemanticsBelow I.right.rows (effC₀) v)
    (hag : ∀ d, min (v d) (grid₀ b) =
      min (S.lowerC (k + 1) d) (grid₀ b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (privateAt P hnext d) = v d) ∧
      ∀ d, min (w d) (grid₀ b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (grid₀ b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.private_protected_repair (by omega) hS hc hv hag
  refine ⟨_, protected_lawful P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r
    (I.rightFace.map d.1)).trans
    ((field_private hroot
      (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS') d.1).trans
      (congrFun he d))

theorem donor_source_repair {b} {S}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {u}
    (hu : RespectsSemanticsBelow I.left.rows (effC₀) u)
    (hag : ∀ d, min (u d) (grid₀ b) =
      min (S.lowerP (k + 1) d) (grid₀ b)) :
    ∃ w, RespectsSemanticsBelow₀ w ∧
      (∀ d, w (donorAt P hnext d) = u d) ∧
      ∀ d, min (w d) (grid₀ b) =
        min (source₀ ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (grid₀ b) := by
  obtain ⟨S', _hS', he, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by omega) hS hc hu hag
  refine ⟨_, protected_lawful P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb, ?_,
    fun d => protected_caps P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb d.1⟩
  intro d
  
  exact (original_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r
    (I.leftFace.map d.1)).trans
    ((field_read I).trans
      ((I.paste_left S'.u S'.v d.1).trans (congrFun he d)))

