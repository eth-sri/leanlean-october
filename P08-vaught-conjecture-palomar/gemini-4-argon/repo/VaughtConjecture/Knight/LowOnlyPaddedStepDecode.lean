/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyPaddedDecode

/-! # Protected repair on every constructed padded LOW successor

The scalar repair's fixed grid and orbit receipts imply cap agreement at
every actual installed coordinate. Both source sections are lawful by the
constructed recursion, so positive-cut transport gives lawful decoding even
at long inherited rows. The input is a lawful prescription at the native
source cut, not an arbitrary external ambient.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepDecode
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract LowOnlyPaddedStepRows

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "Car" => carrier P hnext
local notation "Ccell" => CellScheme.cell (carrier P hnext)
local notation "Cbelow" => CellScheme.below (carrier P hnext)
local notation "Rws" => rows P hk hnext
local notation "src" => source P hk hnext

def original (d : Cell I.boundary) : Cell Car :=
  old P hnext (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d))

local notation "orig" => original P hnext

theorem original_index (d : Cell I.boundary) : Ccell (orig d) = I.boundary.cell d := by
  rw [original, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index,
    P.base_index, RelativeLadderLayer.old_index]

theorem source_original (a : F.Anchor (k + 1)) (d : Cell I.boundary) :
    src a (orig d) = F.fields (k + 1) a (field I d) := by
  rw [original, source_old]
  exact (P.original_readback I F hroot hA hB hC (Nat.le_succ k)
    (state F a) (state_admissible F a) (state_proper F a)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f) d).trans
    (congrFun (state_profile F a) (field I d))

theorem leaf_row (a : F.Anchor (k + 1))
    (d : Cbelow (Ccell (controller P hnext a).1)) :
    Semantics.E Rws (controller P hnext a).1 d = src a d.1 :=
  (data P hk hnext).row_new _ _

theorem protected_decode {b : ℕ} {a : F.Anchor (k + 1)} {S : State I.left I.right}
    (r : F.ProtectedRepair a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1) :
    RespectsSemanticsBelow Rws (A, k + 1) (fun d => r.decoder (src r.anchor d.1)) ∧
      ∀ d : Cbelow (A, k + 1),
        min (r.decoder (src r.anchor d.1)) (CanonicalPairedInverse.grid (k + 1) b) =
          min (src a d.1) (CanonicalPairedInverse.grid (k + 1) b) :=
  OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful P hk hnext a) (source_lawful P hk hnext r.anchor)
    (fun d => d.2.2) (CanonicalPairedInverse.grid_visible _ _) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => LowOnlyPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported P hk hnext a d.1)
    (fun d => source_agreement P hk hnext r.anchor a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)

def privateAt (d : I.right.scheme.below (effC n (k + 1))) : Cbelow (A, k + 1) :=
  ⟨orig (I.rightFace.map d.1), by
    rw [original_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩⟩

def donorAt (d : I.left.scheme.below (effC n (k + 1))) : Cbelow (A, k + 1) :=
  ⟨orig (I.leftFace.map d.1), by
    rw [original_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩⟩

theorem private_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {v : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    (hv : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) v)
    (hag : ∀ d, min (v d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.lowerC (k + 1) d) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow Rws (A, k + 1) w ∧
      (∀ d, w (privateAt P hnext d) = v d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (src ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', hS', he, _, _, ⟨r⟩⟩ := F.private_protected_repair (by omega) hS hc hv hag
  obtain ⟨hl, hcap⟩ := protected_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb
  refine ⟨_, hl, fun d => ?_, hcap⟩
  change r.decoder (src r.anchor (orig (I.rightFace.map d.1))) = v d
  rw [source_original]
  exact (r.readback _).trans ((field_private I F hroot
    (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS') d.1).trans
    (congrFun he d))

theorem donor_source_repair {b : ℕ} {S : State I.left I.right}
    (hS : F.Admissible (k + 1) S)
    (hc : S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.left I.right) + 1)
    {u : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    (hu : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) u)
    (hag : ∀ d, min (u d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.lowerP (k + 1) d) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow Rws (A, k + 1) w ∧
      (∀ d, w (donorAt P hnext d) = u d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (src ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', _hS', he, _, _, ⟨r⟩⟩ := F.donor_protected_repair (by omega) hS hc hu hag
  obtain ⟨hl, hcap⟩ := protected_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb
  refine ⟨_, hl, fun d => ?_, hcap⟩
  change r.decoder (src r.anchor (orig (I.leftFace.map d.1))) = u d
  rw [source_original]
  exact (r.readback _).trans ((field_read I S' (I.leftFace.map d.1)).trans
    ((I.paste_left S'.u S'.v d.1).trans (congrFun he d)))
