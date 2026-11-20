/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

/-! # Exact proper-boundary transport through the recursive semantics -/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

theorem plan_eq m (hm : m ≤ A.card) :
    (CanonicalRecursiveInventory.scheme sem m hm).plan = D.plan := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (Nat.le_of_succ_le hm)

def properEquiv : (n : ℕ) → (hA : n ≤ A.card) →
    (J : Finset ι × ℕ) → ¬ A ⊆ J.1 → D.below J ≃ (carrier sem n hA).below J
  | 0, _, _, _ => Equiv.refl _
  | n + 1, hA, J, hJ =>
    (properEquiv n (Nat.le_of_succ_le hA) J hJ).trans
      (CanonicalRecursiveSuccessorSections.equiv sem n hA J (fun h => hJ h.1))

theorem properEquiv_val n (hA : n ≤ A.card)
    J (hJ : ¬ A ⊆ J.1) d :
    (properEquiv sem n hA J hJ d).1 = boundary sem n hA d.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (CanonicalRecursiveSuccessorRows.old sem n hA)
      (ih (Nat.le_of_succ_le hA))

theorem proper_respects_iff (hp : D.AvoidsScope A)
    n (hA : n ≤ A.card) J (hJ : ¬ A ⊆ J.1)
    p :
    sem.Lawful p ↔
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) J
        (p ∘ (properEquiv sem n hA J hJ).symm) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (ih (Nat.le_of_succ_le hA)).trans
      (CanonicalRecursiveSuccessorSections.respects_iff sem n hA hp
        (CanonicalRecursiveSemantics.state sem hp n (Nat.le_of_succ_le hA)) J
        (fun h => hJ h.1) _)

theorem pullback_respects (hp : D.AvoidsScope A)
    n (hA : n ≤ A.card) J (hJ : ¬ A ⊆ J.1)
    {p}
    (hpr : RespectsSemanticsBelow (CanonicalRecursiveSemantics.rows sem hp n hA) J p) :
    RespectsSemanticsBelow sem J (p ∘ properEquiv sem n hA J hJ) := by
  apply (proper_respects_iff sem hp n hA J hJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hpr

/-- Proper targets retain all original rows and all original lifting clauses. -/
theorem proper_lift (hp : D.AvoidsScope A)
    n (hA : n ≤ A.card) {I J}
    (h : GradedLe I J) (hJ : ¬ A ⊆ J.1)
    (hl : CoatomBoundaryExtension.CappedLift sem h) :
    CoatomBoundaryExtension.CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h := by
  have hI : ¬ A ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  let eI := properEquiv sem n hA I hI
  let eJ := properEquiv sem n hA J hJ
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := by
    apply Subtype.ext
    exact (properEquiv_val sem n hA J hJ _).trans
      (properEquiv_val sem n hA I hI d).symm
  exact (CoatomBoundaryExtension.CappedLift.equiv_iff eI eJ hm rfl
    (proper_respects_iff sem hp n hA I hI) (proper_respects_iff sem hp n hA J hJ)).mp hl

end
end VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
