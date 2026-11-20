/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

@[expose] public section

namespace VaughtConjecture.Knight

open CellScheme.restrictFace

namespace CappedDonor

/-- Transport of a lower set along an equality of domains. -/
def castBelow {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ) :
    X.scheme.below BJ ≃ Y.scheme.below BJ :=
  Equiv.cast (by tauto)

theorem castBelow_val {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ)
    (d : X.scheme.below BJ) : (castBelow h BJ d).1 = SemScheme.castCell h d.1 := by aesop

theorem castBelow_castBelow_symm {n : ℕ} {X Y : SemScheme n} (h : X = Y)
    (BJ : Finset (Fin n) × ℕ) (d : Y.scheme.below BJ) :
    castBelow h BJ (castBelow h.symm BJ d) = d := by aesop

/-- Restricted lawfulness transports along an equality of domains. -/
theorem castBelow_respects {n : ℕ} {X Y : SemScheme n} (h : X = Y) (BJ : Finset (Fin n) × ℕ)
    (r : Y.scheme.below BJ → ExtOrd) :
    RespectsSemanticsBelow Y.rows BJ r ↔
      RespectsSemanticsBelow X.rows BJ (fun d => r (castBelow h BJ d)) := by aesop

/-- Transport of a cell along an equality of domains keeps its grade. -/
theorem castCell_grade {n : ℕ} {X Y : SemScheme n} (h : X = Y) (c : Cell X.scheme) :
    Y.scheme.grade (SemScheme.castCell h c) = X.scheme.grade c := by aesop

section CommonFace

variable {n nP J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J} {F : SemScheme n}
  (fP : Fin n ↪ Fin (nP + 1)) (hvP : Finset.univ.image fP ∈ P.scheme.plan)
  (hP : P.restrictFace fP hvP = F)
  (fC : Fin n ↪ Fin J) (hvC : Finset.univ.image fC ∈ C.scheme.plan)
  (hC : C.restrictFace fC hvC = F) (KA : ℕ)

/-- The face bijection on the request side. -/
noncomputable abbrev bP :
    (P.restrictFace fP hvP).scheme.below (Finset.univ, KA) ≃
      P.scheme.below (Finset.univ.image fP, KA) :=
  belowEquiv P.scheme fP hvP (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fP, KA)) rfl

/-- The face bijection on the private side. -/
noncomputable abbrev bC :
    (C.restrictFace fC hvC).scheme.below (Finset.univ, KA) ≃
      C.scheme.below (Finset.univ.image fC, KA) :=
  belowEquiv C.scheme fC hvC (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fC, KA)) rfl

/-- **The identification of the two copies of a literally common face**: through the common
restriction `F`, along the bijections `belowEquiv` of the face restrictions. -/
noncomputable def commonFace :
    P.scheme.below (Finset.univ.image fP, KA) ≃ C.scheme.below (Finset.univ.image fC, KA) :=
  (bP fP hvP KA).symm.trans
    ((castBelow hP (Finset.univ, KA)).trans
      ((castBelow hC.symm (Finset.univ, KA)).trans (bC fC hvC KA)))

theorem commonFace_apply (a : P.scheme.below (Finset.univ.image fP, KA)) :
    commonFace fP hvP hP fC hvC hC KA a =
      bC fC hvC KA (castBelow hC.symm (Finset.univ, KA)
        (castBelow hP (Finset.univ, KA) ((bP fP hvP KA).symm a))) := rfl

/-- The underlying cell of the identification. -/
theorem commonFace_val (a : P.scheme.below (Finset.univ.image fP, KA)) :
    (commonFace fP hvP hP fC hvC hC KA a).1 =
      toCell C.scheme fC hvC (SemScheme.castCell hC.symm (SemScheme.castCell hP
        ((bP fP hvP KA).symm a).1)) := by
  change (toCell C.scheme fC hvC (castBelow hC.symm (Finset.univ, KA)
    (castBelow hP (Finset.univ, KA) ((bP fP hvP KA).symm a))).1) = _
  rw [castBelow_val, castBelow_val]

/-- The identification preserves grades. -/
theorem commonFace_grade (a : P.scheme.below (Finset.univ.image fP, KA)) :
    C.scheme.grade (commonFace fP hvP hP fC hvC hC KA a).1 = P.scheme.grade a.1 := by
  rw [commonFace_val]
  change (C.restrictFace fC hvC).scheme.grade (SemScheme.castCell hC.symm
    (SemScheme.castCell hP ((bP fP hvP KA).symm a).1)) = _
  rw [castCell_grade, castCell_grade]
  exact congrArg P.scheme.grade (toCell_belowEquiv_symm_val P.scheme fP hvP
    (BJ' := (Finset.univ, KA)) (BJ := (Finset.univ.image fP, KA)) rfl a)

/-- The identifications at two grades agree on a common cell. -/
theorem commonFace_val_congr {KA' : ℕ} (a : P.scheme.below (Finset.univ.image fP, KA))
    (a' : P.scheme.below (Finset.univ.image fP, KA')) (h : a.1 = a'.1) :
    (commonFace fP hvP hP fC hvC hC KA a).1 = (commonFace fP hvP hP fC hvC hC KA' a').1 := by
  have e1 : toCell P.scheme fP hvP ((bP fP hvP KA).symm a).1 = a.1 :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA))
      (BJ := (Finset.univ.image fP, KA)) rfl a
  have e2 : toCell P.scheme fP hvP ((bP fP hvP KA').symm a').1 = a'.1 :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA'))
      (BJ := (Finset.univ.image fP, KA')) rfl a'
  have e : ((bP fP hvP KA).symm a).1 = ((bP fP hvP KA').symm a').1 :=
    toCell_injective P.scheme fP hvP (e1.trans (h.trans e2.symm))
  rw [commonFace_val, commonFace_val, e]

private theorem restrict_iff {m n : ℕ} (D : SemScheme n) (f : Fin m ↪ Fin n)
    (hf : Finset.univ.image f ∈ D.scheme.plan) (k : ℕ)
    (r : D.scheme.below (Finset.univ.image f, k) → ExtOrd) :
    RespectsSemanticsBelow D.rows (Finset.univ.image f, k) r ↔
      RespectsSemanticsBelow (D.restrictFace f hf).rows (Finset.univ, k) (r ∘ bC f hf k) := by
  refine ⟨fun h => h.restrictFace rfl, fun h => ?_⟩
  let e := bC f hf k
  have hl : RespectsSemanticsBelow D.rows (Finset.univ.image f, k) ((r ∘ e) ∘ e.symm) :=
    h.of_restrictFace (f := f) (hr := hf) rfl
  rwa [show (r ∘ e) ∘ e.symm = r from funext fun x => congrArg r (e.apply_symm_apply x)] at hl

/-- Restricted lawfulness transports along the common-face identification. -/
theorem commonFace_respects (r : C.scheme.below (Finset.univ.image fC, KA) → ExtOrd) :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, KA) r ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, KA)
        (fun a => r (commonFace fP hvP hP fC hvC hC KA a)) := by
  rw [restrict_iff C fC hvC KA, castBelow_respects hC.symm, castBelow_respects hP,
    restrict_iff P fP hvP KA]
  apply Iff.of_eq
  congr 1
  funext d
  change _ = r (bC fC hvC KA (castBelow hC.symm _
    (castBelow hP _ ((bP fP hvP KA).symm (bP fP hvP KA d)))))
  rw [Equiv.symm_apply_apply]
  rfl

end CommonFace

end CappedDonor

end VaughtConjecture.Knight
