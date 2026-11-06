
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveSemantics
import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Supported source-prefix completion on the recursive seed

The proper old-boundary repair is normalized and decoded by a constructed
supported inverse. Every seed controller and every retained old occurrence
keeps its source-grid cap. Lawfulness concerns the actual current lower domain;
retained proper owners above it are not incorrectly assumed to have low grade.
-/

namespace VaughtConjecture.Knight.CanonicalSeedPrefix
open   ExtOrd  CanonicalRecursiveSeedRows
open CanonicalPairedInverse PairedSlotEncoding


variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : AvoidsValue D.scope A)

/-- The repair is an old-boundary input; its whole recursive extension,
supported inverse and all auxiliary source-cap equations are constructed. -/
theorem exists_section
    (a : Profile sem)
    {p : CellLabels D}
    (hpr : RespectsSemanticsBelow sem (A, 3) (fun d => p d.1)) (ht : AvoidsValue p ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : CappedEq a.val p (CanonicalPairedInverse.grid 3 B)) :
    ∃ r : CellLabels (carrier sem hA),
      RespectsSemanticsBelow (rows sem hA hp) (A, 3) (fun d => r d.1) ∧
      (∀ d, r (boundary sem hA d) = p d) ∧
      (∀ d, min (r d) (CanonicalPairedInverse.grid 3 B) =
        min (source sem hA hp a d) (CanonicalPairedInverse.grid 3 B)) := by
  let F := data sem hA hp
  let b := CanonicalRecursiveInventory.encode sem hpr ht
  have hb : CappedEq b.val a.val (CanonicalPairedInverse.grid 3 B) :=
    CanonicalPairedProfiles.normalize_cap a.property.2 hag
  have hgrid : CanonicalPairedInverse.grid 3 B ∈
      CanonicalRecursiveSeedRows.grid (D := D) :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hsource := source_agreement_all sem hA hp
    b a hgrid hb
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ :=
    CanonicalPairedInverse.exists_supported_inverse a.property.2 ht hag
  have hfixGrid : ∀ z ∈ CanonicalRecursiveSeedRows.grid (D := D),
      z < CanonicalPairedInverse.grid 3 B → κ z = z := by
    
    intro z hz hzB
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hw.bot
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hz
      apply hfix b
      by_contra hn
      have hBn  := Nat.le_of_not_gt hn
      have he : CanonicalPairedInverse.grid 3 B ≤
          CanonicalPairedInverse.grid 3 b :=
        ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
      exact (not_le_of_gt hzB) he
  have hfixBoundary : ∀ d, a.val d < CanonicalPairedInverse.grid 3 B →
      κ (a.val d) = a.val d := by
    intro d hd
    have hba  := eq_of_cap_eq_lt (hb d).symm hd
    have hpa  := eq_of_cap_eq_lt (hag d) hd
    calc
      κ (a.val d) = κ (b.val d) := congrArg κ hba
      _ = p d := hread d
      _ = a.val d := hpa.symm
  have hguard : CanonicalPairedInverse.grid 3 B ≤ gTop 3 3 := by
    exact?
  have hcaps := OrbitPrefixSupport.decode_agree hw (grid_visible 3 B) hguard hreach
    hfixGrid hfixBoundary (source_supported sem hA hp a)
    hsource
  have hpos : CanonicalPairedInverse.grid 3 B ≠ ⊥ := ofOrd_ne_bot _
  have hwhole := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    (F.profile_respects (controller sem hA b))
    (F.profile_respects (controller sem hA a))
    (fun d => d.2.2) (SharpWitnessComposition.boundedMap_of_witness hw)
    hpos (fun d => hcaps d.1)
  refine ⟨fun d => κ (source sem hA hp b d),
    hwhole, ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_boundary]
  exact hread d


