/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyCompleteFields
public import VaughtConjecture.Knight.FullScopeBountiful

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd AmalgamationPlan CappedDonor

variable {n : ℕ} {P C : SemScheme n}

/-- The common-face equivalence at a lower grade. -/
def rootCut {A B : Finset (Fin n)}
    (e : P.scheme.below (A, A.card) ≃ C.scheme.below (B, B.card))
    (hg : ∀ a, P.scheme.grade a.1 = C.scheme.grade (e a).1) (j : ℕ) :
    P.scheme.below (faceIndex A j) ≃ C.scheme.below (faceIndex B j) :=
  P.scheme.restrictBelowEquiv e (min_le_left ..) (min_le_left ..) (fun a => by
    have h : P.scheme.grade a.1 ≤ A.card := a.2.2
    have h' : C.scheme.grade (e a).1 ≤ B.card := (e a).2.2
    rw [le_min_iff, le_min_iff, and_iff_right h, and_iff_right h', hg a])

/-- The complete common root, with exact original source rows. -/
structure CommonRoot (P C : SemScheme n) where
  A : Finset (Fin n)
  B : Finset (Fin n)
  A_mem : A ∈ P.scheme.plan
  B_mem : B ∈ C.scheme.plan
  face : P.scheme.below (A, A.card) ≃ C.scheme.below (B, B.card)
  grade : ∀ a, P.scheme.grade a.1 = C.scheme.grade (face a).1
  respects_iff : ∀ {j : ℕ} (v : C.scheme.below (faceIndex B j) → ExtOrd),
    RespectsSemanticsBelow C.rows (faceIndex B j) v ↔
      RespectsSemanticsBelow P.rows (faceIndex A j) (v ∘ rootCut face grade j)

namespace CommonRoot

variable (R : CommonRoot P C)

def fullP {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    P.scheme.below (R.A, R.A.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

abbrev faceAt (j : ℕ) := rootCut R.face R.grade j

def Shared (u : Cell P.scheme → ExtOrd) (v : Cell C.scheme → ExtOrd) : Prop :=
  ∀ a, u a.1 = v (R.face a).1

theorem shared_at {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    u a.1 = v (R.faceAt j a).1 := h (R.fullP a)

/-- Installing the present vector keeps the entire common root, including its future part. -/
theorem shared_complete {j : ℕ} {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (h : R.Shared u v) (u' : P.scheme.below (effC n j) → ExtOrd)
    (v' : C.scheme.below (effC n j) → ExtOrd)
    (hface : ∀ a : P.scheme.below (faceIndex R.A j),
      u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) :
    R.Shared (CellScheme.complete u u') (CellScheme.complete v v') := by
  intro a
  by_cases hj : P.scheme.grade a.1 ≤ j
  · let a' : P.scheme.below (faceIndex R.A j) := ⟨a.1, a.2.1, le_min a.2.2 hj⟩
    exact (CellScheme.complete_present u u' (CellScheme.below.mono (faceIndex_le R.A j) a')).trans
      ((hface a').trans
        (CellScheme.complete_present v v' (CellScheme.below.mono (faceIndex_le R.B j)
          (R.faceAt j a'))).symm)
  · rw [completeAt_future u u' a.1 (not_le.mp hj),
      completeAt_future v v' (R.face a).1 (by simp_all [← R.grade])]
    exact h a

/-- Prescribe the private root in the original donor, preserving all donor caps.
Empty roots and nominal grade zero need no bountifulness call. -/
theorem installP {j : ℕ} {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ =
        min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ) :
    ∃ u', RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (∀ d, min (u' d) γ = min (u d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        u' (CellScheme.below.mono (faceIndex_le R.A j) a) =
          v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) := by
  exact P.bountiful.extend R.A_mem P.scheme.isPlan.domain_mem (faceIndex_le R.A j)
    ((R.respects_iff _).mp (hv.mono (faceIndex_le R.B j))) hu hγ hag

/-- The reverse original-face installation uses the inverse actual root map. -/
theorem installC {j : ℕ} {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {γ : ExtOrd} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a : P.scheme.below (faceIndex R.A j),
      min (v (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a))) γ =
        min (u (CellScheme.below.mono (faceIndex_le R.A j) a)) γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (∀ d, min (v' d) γ = min (v d) γ) ∧
      ∀ a : P.scheme.below (faceIndex R.A j),
        v' (CellScheme.below.mono (faceIndex_le R.B j) (R.faceAt j a)) =
          u (CellScheme.below.mono (faceIndex_le R.A j) a) :=
  C.bountiful.extend_inverse R.B_mem C.scheme.isPlan.domain_mem (faceIndex_le R.B j)
    (R.faceAt j) R.respects_iff hv (hu.mono (faceIndex_le R.A j)) hγ hag

end CommonRoot

end VaughtConjecture.Knight.LowOnly
