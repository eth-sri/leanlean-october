
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalSeedPrefix
import VaughtConjecture.Knight.CanonicalSeedAmbient

/-! # Current-boundary repair with the complete persistent field inventory

Only the actual grade cut participates in old-face completion. Every other
original field is retained before normalization, so controller caps continue
to refer to the same full inventory.
-/

namespace VaughtConjecture.Knight.CanonicalSeedCutPrefix
open    CanonicalRecursiveSeedRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card)
variable (hp : AvoidsValue D.scope A)

abbrev cut := GradeCutBoundary.scheme D 3
abbrev cutRows := GradeCutBoundary.rows D 3 sem
abbrev occurrence := GradeCutBoundary.toCell D 3

local notation "Cell₀" => Cell (cut (D := D))

local notation "occurrence₀" => occurrence (D := D)

def oldTarget (d : Cell₀) : CanonicalSeedAmbient.target sem hA :=
  ⟨boundary sem hA (occurrence₀ d), by
    have he : (carrier sem hA).cell (boundary sem hA (occurrence₀ d)) =
        D.cell (occurrence₀ d) :=
      CanonicalRecursiveInventory.boundary_cell sem 3 hA _
    rw [he]
    exact ⟨D.scope_subset _, GradeCutBoundary.grade_bound d⟩⟩

theorem oldTarget_cell (d : Cell₀) :
    (carrier sem hA).cell (oldTarget sem hA d).1 = (cut (D := D)).cell d :=
  CanonicalRecursiveInventory.boundary_cell sem 3 hA _

theorem exists_section (a : Profile sem)
    {p : Cell₀ → ExtOrd} (hpr : RespectsSemantics (cutRows sem) p)
    (ht : AvoidsValue p ⊤) {B} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val (occurrence₀ d)) (CanonicalPairedInverse.grid 3 B) =
      min (p d) (CanonicalPairedInverse.grid 3 B)) :
    ∃ r : CellLabels (carrier sem hA),
      RespectsSemanticsBelow (rows sem hA hp) (A, 3) (fun d => r d.1) ∧
      (∀ d, r (oldTarget sem hA d).1 = p d) ∧
      ∀ d, min (r d) (CanonicalPairedInverse.grid 3 B) =
        min (source sem hA hp a d) (CanonicalPairedInverse.grid 3 B) := by
  classical
  let occ := occurrence₀
  let v := Function.extend occ p a.val
  have hv (d) : v (occ d) = p d := occ.injective.extend_apply p a.val d
  have hvp : RespectsSemantics (cutRows sem) (v ∘ occ) := by
    simpa only [Function.comp_def, hv] using hpr
  have hl := (GradeCutBoundary.respects_iff sem (A, 3) le_rfl _).mp
    (hvp.toBelow (A, 3))
  have hvl : RespectsSemanticsBelow sem (A, 3) (fun d => v d.1) := by
    convert hl using 1
    funext d
    exact (congrArg v (congrArg Subtype.val
      ((GradeCutBoundary.belowEquiv D (A, 3) le_rfl).apply_symm_apply d))).symm
  have hvt : AvoidsValue v ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact ht d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      exact a.property.2.2 x
  have hva : CappedEq a.val v (CanonicalPairedInverse.grid 3 B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · obtain ⟨d, rfl⟩ := hx
      rw [hv]; exact hag d
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ :=
    CanonicalSeedPrefix.exists_section sem hA hp a hvl hvt hB hva
  exact ⟨r, hr, fun d => (hread (occ d)).trans (hv d), hcap⟩

