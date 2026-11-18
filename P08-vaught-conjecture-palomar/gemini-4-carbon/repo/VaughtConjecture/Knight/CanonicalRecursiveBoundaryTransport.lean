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

theorem plan_eq (m : ℕ) (hm : m ≤ A.card) :
    (CanonicalRecursiveInventory.scheme sem m hm).plan = D.plan := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (Nat.le_of_succ_le hm)

def properEquivAt : (m : ℕ) → (hA : m + 2 ≤ A.card) →
    (J : Finset ι × ℕ) → ¬ A ⊆ J.1 → D.below J ≃ (carrierAt sem m hA).below J
  | 0, hA, J, hJ =>
    GradeCutPairCarrier.properEquiv D
      (CanonicalPairBoundary.firstProfiles sem 1 2)
      (CanonicalPairBoundary.secondProfiles sem 2)
      1 2 (by decide) (CanonicalPairLocalSections.one_le hA) (by decide) hA J hJ
  | m + 1, hA, J, hJ =>
    (properEquivAt m (Nat.le_of_succ_le hA) J hJ).trans
      (CanonicalRecursiveSemantics.equiv sem m hA J (fun h => hJ h.1))

theorem properEquiv_valAt (m : ℕ) (hA : m + 2 ≤ A.card)
    (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) (d : D.below J) :
    (properEquivAt sem m hA J hJ d).1 = boundaryAt sem m hA d.1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    exact congrArg (CanonicalRecursiveSemantics.old sem m hA)
      (ih (Nat.le_of_succ_le hA))

theorem proper_respects_iffAt (hp : ∀ d : Cell D, D.scope d ≠ A)
    (m : ℕ) (hA : m + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    (p : D.below J → ExtOrd) :
    RespectsSemanticsBelow sem J p ↔
      RespectsSemanticsBelow (CanonicalRecursiveSemantics.rowsAt sem hp m hA) J
        (p ∘ (properEquivAt sem m hA J hJ).symm) := by
  induction m with
  | zero =>
    exact GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
      (CanonicalPairLocalSections.one_le hA) (by decide) hA hp (by decide)
      sem (CanonicalPairLocalSections.smallRows sem hA hp) J hJ p
  | succ m ih =>
    exact (ih (Nat.le_of_succ_le hA)).trans
      (CanonicalRecursiveSemantics.respects_iff sem m hA hp
        (CanonicalRecursiveSemantics.stateAt sem hp m (Nat.le_of_succ_le hA)) J
        (fun h => hJ h.1) _)

theorem pullback_respectsAt (hp : ∀ d : Cell D, D.scope d ≠ A)
    (m : ℕ) (hA : m + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    {p : (carrierAt sem m hA).below J → ExtOrd}
    (hpr : RespectsSemanticsBelow (CanonicalRecursiveSemantics.rowsAt sem hp m hA) J p) :
    RespectsSemanticsBelow sem J (p ∘ properEquivAt sem m hA J hJ) := by
  apply (proper_respects_iffAt sem hp m hA J hJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hpr

theorem proper_liftAt (hp : ∀ d : Cell D, D.scope d ≠ A)
    (m : ℕ) (hA : m + 2 ≤ A.card) {I J : Finset ι × ℕ}
    (h : GradedLe I J) (hJ : ¬ A ⊆ J.1)
    (hl : CoatomBoundaryExtension.CappedLift sem h) :
    CoatomBoundaryExtension.CappedLift (CanonicalRecursiveSemantics.rowsAt sem hp m hA) h := by
  intro p q γ hpr hqr hγ hag
  have hI : ¬ A ⊆ I.1 := fun hi => hJ (hi.trans h.1)
  let eI := properEquivAt sem m hA I hI
  let eJ := properEquivAt sem m hA J hJ
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) :=
    Subtype.ext ((properEquiv_valAt sem m hA J hJ _).trans
      (properEquiv_valAt sem m hA I hI d).symm)
  obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
    (pullback_respectsAt sem hp m hA I hI hpr)
    (pullback_respectsAt sem hp m hA J hJ hqr) hγ
    (fun d => by simpa only [Function.comp_apply, hm] using hag (eI d))
  refine ⟨r ∘ eJ.symm, (proper_respects_iffAt sem hp m hA J hJ r).mp hr, ?_, ?_⟩
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc (eJ.symm d)
  · intro d
    have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)


abbrev proper_lift (hp : ∀ d : Cell D, D.scope d ≠ A) (n : ℕ) (hA : n + 3 ≤ A.card)
    {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : ¬ A ⊆ J.1)
    (hl : CoatomBoundaryExtension.CappedLift sem h) :=
  proper_liftAt sem hp (n + 1) hA h hJ hl

end
end VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
