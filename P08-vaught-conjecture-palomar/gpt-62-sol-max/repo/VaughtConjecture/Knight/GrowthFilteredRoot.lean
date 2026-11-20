/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCompleteFields
public import VaughtConjecture.Knight.CappedDonorFace
public import VaughtConjecture.Knight.CappedDonorReceiving
public import VaughtConjecture.Knight.FullScopeBountiful

@[expose] public section

namespace VaughtConjecture.Knight.Growth

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  (F : SemScheme r) (fP : Fin r ↪ Fin (n + 1))
  (hvP : Finset.univ.image fP ∈ P.scheme.plan) (hP : P.restrictFace fP hvP = F)
  (fC : Fin r ↪ Fin J) (hvC : Finset.univ.image fC ∈ C.scheme.plan)
  (hC : C.restrictFace fC hvC = F)

abbrev rootMap (j : ℕ) := commonFace fP hvP hP fC hvC hC j

theorem rootMap_grade (j : ℕ) (a : P.scheme.below (Finset.univ.image fP, j)) :
    C.scheme.grade (rootMap F fP hvP hP fC hvC hC j a).1 = P.scheme.grade a.1 :=
  commonFace_grade fP hvP hP fC hvC hC j a

theorem rootMap_lawful (j : ℕ) (p : C.scheme.below (Finset.univ.image fC, j) → ExtOrd) :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, j) p ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, j)
        (fun a => p (rootMap F fP hvP hP fC hvC hC j a)) :=
  commonFace_respects fP hvP hP fC hvC hC j p

/-- The actual relative-data occurrence map, constructed from literal face
restrictions and containment of the private root in the cap's lower domain. -/
def literalKappa (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c)) :
    P.scheme.below (Finset.univ.image fP, r) → C.scheme.below (C.scheme.cell c) :=
  fun a => CellScheme.below.mono hc (rootMap F fP hvP hP fC hvC hC r a)

theorem literalKappa_lawful (c : Cell C.scheme)
    (hc : GradedLe (Finset.univ.image fC, r) (C.scheme.cell c))
    {s : C.scheme.below (C.scheme.cell c) → ExtOrd}
    (hs : RespectsSemanticsBelow C.rows (C.scheme.cell c) s) :
    RespectsSemanticsBelow P.rows (Finset.univ.image fP, r)
      (fun a => s (literalKappa F fP hvP hP fC hvC hC c hc a)) :=
  (rootMap_lawful F fP hvP hP fC hvC hC r _).mp (hs.mono hc)

/-- Only actual literal geometry is supplied. Grade preservation and all
filtered transports below are derived, not fields of this record. -/
structure RootAttachment (X : RelativeData C.scheme C.rows P.scheme P.rows) where
  root_eq : X.root = (Finset.univ.image fP, r)
  occurrence : ∀ a : P.scheme.below X.root,
    (X.κ a).1 = (rootMap F fP hvP hP fC hvC hC r
      ⟨a.1, root_eq ▸ a.2⟩).1

namespace RootAttachment

variable {F fP hvP hP fC hvC hC}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

include R in
theorem grade (a : P.scheme.below X.root) : C.scheme.grade (X.κ a).1 = P.scheme.grade a.1 := by
  rw [R.occurrence a]
  apply rootMap_grade

def full {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    P.scheme.below X.root :=
  ⟨a.1, R.root_eq.symm ▸ show GradedLe (P.scheme.cell a.1)
      (Finset.univ.image fP, r) from ⟨a.2.1, by
    change P.scheme.grade a.1 ≤ r
    have h := (P.scheme.grade_le_card_scope a.1).trans (Finset.card_le_card a.2.1)
    simp_all [Finset.card_image_of_injective _ fP.injective, Finset.card_univ,]⟩⟩

theorem at_occurrence {j : ℕ} (a : P.scheme.below (Finset.univ.image fP, j)) :
    (rootMap F fP hvP hP fC hvC hC j a).1 = (X.κ (R.full a)).1 := by
  rw [R.occurrence]
  exact commonFace_val_congr _ _ _ _ _ _ _ _ _ rfl

def filtered {j : ℕ} (a : P.scheme.below X.root) (hj : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (Finset.univ.image fP, j) :=
  ⟨a.1, (show GradedLe (P.scheme.cell a.1) (Finset.univ.image fP, r) from
    R.root_eq ▸ a.2).1, hj⟩

end RootAttachment

end

end VaughtConjecture.Knight.Growth
