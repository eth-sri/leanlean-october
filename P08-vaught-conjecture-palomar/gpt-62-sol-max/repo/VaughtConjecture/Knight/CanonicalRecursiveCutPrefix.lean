/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursivePrefix

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCutPrefix

open Transform Value ExtOrd CanonicalRecursiveSuccessorRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card)

abbrev cut := GradeCutBoundary.scheme D (n + 3)

abbrev cutRows := GradeCutBoundary.rows D (n + 3) sem

abbrev occurrence := GradeCutBoundary.toCell D (n + 3)

abbrev target := (carrier sem n hA).below (A, n + 3)

def oldTarget (d : Cell (cut (D := D) n)) : target sem n hA :=
  ⟨boundary sem n hA (occurrence (D := D) n d), by
    have he : (carrier sem n hA).cell (boundary sem n hA (occurrence (D := D) n d)) =
        D.cell (occurrence (D := D) n d) :=
      CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA _
    rw [he]
    exact ⟨D.scope_subset _, GradeCutBoundary.grade_bound D _ d⟩⟩

theorem oldTarget_cell (d : Cell (cut (D := D) n)) :
    (carrier sem n hA).cell (oldTarget sem n hA d).1 = (cut (D := D) n).cell d :=
  CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA _

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

theorem exists_section (a : Profile sem n)
    {p : Cell (cut (D := D) n) → ExtOrd} (hpr : RespectsSemantics (cutRows sem n) p)
    (ht : ∀ d, p d ≠ ⊤) {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val (occurrence (D := D) n d)) (CanonicalPairedInverse.grid (n + 3) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 3) B)) :
    ∃ r : Cell (carrier sem n hA) → ExtOrd,
      RespectsSemanticsBelow (rows S) (A, n + 3) (fun d => r d.1) ∧
      (∀ d, r (oldTarget sem n hA d).1 = p d) ∧
      ∀ d, min (r d) (CanonicalPairedInverse.grid (n + 3) B) =
        min (source S a d) (CanonicalPairedInverse.grid (n + 3) B) := by
  classical
  let occ := occurrence (D := D) n
  let v := Function.extend occ p a.val
  have hv (d) : v (occ d) = p d := occ.injective.extend_apply p a.val d
  have hvp : RespectsSemantics (cutRows sem n) (v ∘ occ) := by
    simpa only [Function.comp_def, hv] using hpr
  have hl := (GradeCutBoundary.respects_iff D (n + 3) sem (A, n + 3) le_rfl _).mp
    (hvp.toBelow (A, n + 3))
  have hvl : RespectsSemanticsBelow sem (A, n + 3) (fun d => v d.1) := by
    convert hl using 1
    funext d
    exact (congrArg v (congrArg Subtype.val
      ((GradeCutBoundary.belowEquiv D (n + 3) (A, n + 3) le_rfl).apply_symm_apply d))).symm
  have hvt : ∀ x, v x ≠ ⊤ := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
      apply a.property.2.2
  have hva : ∀ x, min (a.val x) (CanonicalPairedInverse.grid (n + 3) B) =
      min (v x) (CanonicalPairedInverse.grid (n + 3) B) := by
    intro x
    by_cases hx : ∃ d, occ d = x
    · grind
    · rw [show v x = a.val x from Function.extend_apply' p a.val x hx]
  obtain ⟨r, hr, hread, hcap⟩ :=
    CanonicalRecursivePrefix.exists_section S a hvl hvt hB hva
  exact ⟨r, hr, fun d => (hread (occ d)).trans (hv d), hcap⟩

end

end VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
