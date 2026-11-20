/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursivePrefix
public import VaughtConjecture.Knight.CanonicalRecursiveAmbient

/-! # Current-boundary repair with the complete persistent field inventory

Only the actual grade cut participates in old-face completion. Every other
original field is retained before normalization, so controller caps continue
to refer to the same full inventory.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
open Transform Value ExtOrd CanonicalRecursiveSuccessorRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

abbrev cut := GradeCutBoundary.scheme D (n + 1)
abbrev cutRows := GradeCutBoundary.rows D (n + 1) sem
abbrev occurrence := GradeCutBoundary.toCell D (n + 1)

def oldTarget (d : Cell (cut (D := D) n)) : CanonicalRecursiveAmbient.target sem n hA :=
  ⟨boundary sem n hA (occurrence n d), by
    have he : (carrier sem n hA).cell (boundary sem n hA (occurrence n d)) =
        D.cell (occurrence n d) :=
      CanonicalRecursiveInventory.boundary_cell sem (n + 1) hA _
    rw [he]
    exact ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D _ d⟩⟩

theorem oldTarget_cell (d : Cell (cut n)) :
    (carrier sem n hA).cell (oldTarget sem n hA d).1 = (cut n).cell d :=
  CanonicalRecursiveInventory.boundary_cell sem (n + 1) hA _

theorem exists_section a
    {p : Cell (cut n) → ExtOrd} (hpr : RespectsSemantics (cutRows sem n) p)
    {B} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val (occurrence n d)) (CanonicalPairedInverse.grid (n + 1) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 1) B)) :
    ∃ r : (carrier sem n hA).Labelling,
      RespectsSemanticsBelow (rows sem n hA hp P) (A, n + 1) (fun d => r d.1) ∧
      (∀ d, r (oldTarget sem n hA d).1 = p d) ∧
      ∀ d, min (r d) (CanonicalPairedInverse.grid (n + 1) B) =
        min (source sem n hA hp P a d) (CanonicalPairedInverse.grid (n + 1) B) := by
  classical
  let occ := occurrence (D := D) n
  let v := Function.extend occ p a.val
  have hv (d) : v (occ d) = p d := occ.injective.extend_apply p a.val d
  have hvp : RespectsSemantics (cutRows sem n) (v ∘ occ) := by
    simpa [Function.comp_def, hv] using hpr
  have hl := (GradeCutBoundary.respects_iff D (n + 1) sem (A, n + 1) le_rfl _).mp
    (hvp.toBelow (A, n + 1))
  have hvl : RespectsSemanticsBelow sem (A, n + 1) (fun d => v d.1) := by
    convert hl using 1
    funext d
    exact (congrArg v (congrArg Subtype.val
      ((GradeCutBoundary.belowEquiv D (n + 1) (A, n + 1) le_rfl).apply_symm_apply d))).symm
  have hva : ∀ x, min (a.val x) (CanonicalPairedInverse.grid (n + 1) B) =
      min (v x) (CanonicalPairedInverse.grid (n + 1) B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ :=
    CanonicalRecursivePrefix.exists_section sem n hA hp P a hvl hB hva
  exact ⟨r, hr, fun d => (hread (occ d)).trans (hv d), hcap⟩

end
end VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
