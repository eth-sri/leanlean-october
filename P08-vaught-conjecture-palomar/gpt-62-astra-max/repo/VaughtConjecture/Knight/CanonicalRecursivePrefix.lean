/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Supported source-prefix completion on the recursive successor

The proper old-boundary repair is normalized and decoded by a constructed
supported inverse. Every recursive controller and every retained old occurrence
keeps its source-grid cap. Lawfulness concerns the actual current lower domain;
retained proper owners above it are not incorrectly assumed to have low grade.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursivePrefix
open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows
open CanonicalPairedInverse PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

/-- The repair is an old-boundary input; its whole recursive extension,
supported inverse and all auxiliary source-cap equations are constructed. -/
theorem exists_section
    a
    {p : D.Labelling}
    (hpr : RespectsSemanticsBelow sem (A, (n + 1)) (fun d => p d.1))
    {B} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val d) (CanonicalPairedInverse.grid (n + 1) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 1) B)) :
    ∃ r : (carrier sem n hA).Labelling,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, (n + 1)) (fun d => r d.1) ∧
      (∀ d, r (boundary sem n hA d) = p d) ∧
      (∀ d, min (r d) (CanonicalPairedInverse.grid (n + 1) B) =
        min (source sem n hA hp P a d) (CanonicalPairedInverse.grid (n + 1) B)) := by
  let F := data sem n hA hp P
  let j := n + 1
  let G := CanonicalFieldLayer.family (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) (GradeCutBoundary.grade_bound D j)
  have hs : G.admitted p := (GradeCutBoundary.pullback_respects D j sem le_rfl hpr).toRespects
    (fun d => ⟨D.scope_subset _, GradeCutBoundary.grade_bound D j d⟩)
  obtain ⟨r⟩ := ProfileCatalogue.exists_repair G (Nat.succ_pos n) a.property.2 hs hag
  let b : Profile sem n := ⟨r.encoded,r.admitted,r.canonical⟩
  have hgrid : CanonicalPairedInverse.grid (n + 1) B ∈
      CanonicalRecursiveSuccessorRows.grid (D := D) n :=
    PairedSlotComparison.sourceGrid_endpoint hB
  have hsource := source_agreement_all sem n hA hp P b a hgrid r.prefix_eq
  have hguard : CanonicalPairedInverse.grid (n + 1) B ≤ gTop (n + 1) (n + 1) := by
    rw [gTop_of_le le_rfl]
    exact le_top
  have hcaps := OrbitPrefixSupport.decode_agree r.witness (grid_visible (n + 1) B) hguard r.reaches
    (fun _ => r.fixedBelow) r.boundary_fixed (source_supported sem n hA hp P a)
    hsource
  have hpos : CanonicalPairedInverse.grid (n + 1) B ≠ ⊥ := ofOrd_ne_bot _
  have hwhole := SharpWitnessComposition.map_respects_of_positive_cap_agreement
    (F.profile_respects (controller sem n hA b))
    (F.profile_respects (controller sem n hA a))
    (fun d => d.2.2) (SharpWitnessComposition.boundedMap_of_witness r.witness)
    hpos (fun d => hcaps d.1)
  refine ⟨fun d => r.decoder (source sem n hA hp P b d),
    hwhole, ?_, hcaps⟩
  intro d
  dsimp only
  rw [source_boundary]
  exact r.readback d

end
end VaughtConjecture.Knight.CanonicalRecursivePrefix
