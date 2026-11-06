/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedIteration
public import VaughtConjecture.Knight.GrowthPaddedDecode

/-! # Protected repair on every constructed padded growth successor

The scalar repair's fixed grid and orbit receipts imply cap agreement at
every actual installed coordinate. Both source sections are lawful by the
constructed recursion, so positive-cut transport gives lawful decoding even
at long inherited rows. The input is a lawful prescription at the native
source cut, not an arbitrary external ambient.
-/

/- Adapted from the corresponding LOW physical endgame; scalar admission
and source sections here are exclusively the growth producers. -/
@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedStepDecode
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthPaddedContract GrowthPaddedStepRows

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

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

theorem source_original (a : Catalogue X (k + 1)) (d : Cell I.boundary) :
    src a (orig d) = GrowthHigherSources.fields X (k + 1) a (field I d) := by
  rw [original, source_old]
  exact (P.original_readback I X T hA hB hC (Nat.le_succ k)
    (GrowthHigherSources.state X a) (GrowthHigherSources.state_admitted X a)
    (GrowthHigherSources.state_proper X a)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by
      rw [GrowthHigherSources.state_profile]
      exact GrowthHigherSources.anchor_bound X a f) d).trans
    (congrFun (GrowthHigherSources.state_profile X a) (field I d))

theorem protected_decode {b : ℕ} {a : Catalogue X (k + 1)} {S : State I.right.scheme I.left.scheme}
    (r : ProtectedRepair X a.val S (k + 1) b)
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1) :
    RespectsSemanticsBelow Rws (A, k + 1)
      (fun d => r.decoder (src (GrowthPaddedDecode.repairAnchor r) d.1)) ∧
      ∀ d : Cbelow (A, k + 1),
        min (r.decoder (src (GrowthPaddedDecode.repairAnchor r) d.1))
          (CanonicalPairedInverse.grid (k + 1) b) =
        min (src a d.1) (CanonicalPairedInverse.grid (k + 1) b) :=
  OrbitPrefixSupport.decode_respects_of_positive_cut r.witness
    (source_lawful P hk hnext a) (source_lawful P hk hnext (GrowthPaddedDecode.repairAnchor r))
    (fun d => d.2.2) (CanonicalPairedInverse.grid_visible _ _) (ofOrd_ne_bot _) r.reaches
    (fun _ hz hlt => GrowthPaddedDecode.grid_fixed_below r hz hlt) r.boundary_fixed
    (fun d => source_supported P hk hnext a d.1)
    (fun d => source_agreement P hk hnext (GrowthPaddedDecode.repairAnchor r) a
      (PairedSlotComparison.sourceGrid_endpoint hb) r.prefix_eq d.1)

def privateAt (d : I.right.scheme.below (Finset.univ, k + 1)) : Cbelow (A, k + 1) :=
  ⟨orig (I.rightFace.map d.1), by
    rw [original_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩⟩

def donorAt (d : I.left.scheme.below (Finset.univ, k + 1)) : Cbelow (A, k + 1) :=
  ⟨orig (I.leftFace.map d.1), by
    rw [original_index]
    exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩⟩

theorem private_source_repair {b : ℕ} {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X (k + 1) S)
    (hc : S.profile ∈
      CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {v : I.right.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hv : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) v)
    (hag : ∀ d, min (v d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.privateValues d.1) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow Rws (A, k + 1) w ∧
      (∀ d, w (privateAt P hnext d) = v d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (src ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', hS', he, _, _, _, ⟨r⟩⟩ := T.private_protected_all (by omega) hS hc hv hag
  obtain ⟨hl, hcap⟩ := protected_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb
  refine ⟨_, hl, fun d => ?_, hcap⟩
  change r.decoder (src (GrowthPaddedDecode.repairAnchor r) (orig (I.rightFace.map d.1))) = v d
  rw [source_original]
  exact (r.readback _).trans ((GrowthOrderedBase.field_private I X T hS' d.1).trans (he d))

theorem donor_source_repair (hN : k + 1 < X.req.N) {b : ℕ} {S : State I.right.scheme I.left.scheme}
    (hS : Admitted X (k + 1) S)
    (hc : S.profile ∈
      CanonicalPairedProfiles.inventory (Field I.right.scheme I.left.scheme) (k + 1))
    (hb : b ≤ 2 * Fintype.card (Field I.right.scheme I.left.scheme) + 1)
    {u : I.left.scheme.below (Finset.univ, k + 1) → ExtOrd}
    (hu : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) u)
    (hag : ∀ d, min (u d) (CanonicalPairedInverse.grid (k + 1) b) =
      min (S.donorValues d.1) (CanonicalPairedInverse.grid (k + 1) b)) :
    ∃ w, RespectsSemanticsBelow Rws (A, k + 1) w ∧
      (∀ d, w (donorAt P hnext d) = u d) ∧
      ∀ d, min (w d) (CanonicalPairedInverse.grid (k + 1) b) =
        min (src ⟨S.profile, hc, S, hS, rfl⟩ d.1)
          (CanonicalPairedInverse.grid (k + 1) b) := by
  obtain ⟨S', _hS', he, _, _, _, ⟨r⟩⟩ := T.donor_protected_before (by omega) hN hS hc hu hag
  obtain ⟨hl, hcap⟩ := protected_decode P hk hnext (a := ⟨S.profile, hc, S, hS, rfl⟩) r hb
  refine ⟨_, hl, fun d => ?_, hcap⟩
  change r.decoder (src (GrowthPaddedDecode.repairAnchor r) (orig (I.leftFace.map d.1))) = u d
  rw [source_original]
  exact (r.readback _).trans ((GrowthOrderedBase.field_donor I S' d.1).trans (he d))
