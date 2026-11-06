import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.Model

/-! # Literal common faces

The face identification of the capped-donor reference data (`CappedDonor.Ref.face`, with its
lawfulness transport `face_respects`) derived from **literal face restrictions**: when the
request scheme `P` restricted along `fP` and the private scheme `C` restricted along `fC` are the
same domain `F` (as `SemScheme`s), the lower sets `(fP[univ], KA)` of `P` and `(fC[univ], KA)`
of `C` are identified through `F` (`commonFace`), and restricted lawfulness transports along the
identification in both directions (`commonFace_respects`), by the existing transport of respect
along a face restriction (`RespectsSemanticsBelow.restrictFace` / `.of_restrictFace`) and the
transport along an equality of domains (`castBelow_respects`).  The underlying cell of the
identification is computed by `commonFace_val`; the identification preserves grades
(`commonFace_grade`) and the identifications at two grades agree on a common cell
(`commonFace_val_congr`), which is what makes it a graded identification of the whole literal
root; labels transport along an equality of stage types by `StageType.label_castCell`. -/

namespace VaughtConjecture.Knight

open CellScheme.restrictFace

/-- Labels transport along an equality of stage types. -/
theorem StageType.label_castCell {α : Ordinal₀} {n : ℕ} {X Y : S α n} (h : X = Y)
    (c : Cell X.scheme.scheme) :
    Y.label (SemScheme.castCell (congrArg StageType.scheme h) c) = X.label c := by
  subst h; rfl

namespace CappedDonor

/-- Transport of a lower set along an equality of domains. -/
def castBelow {n} {X Y} (h : X = Y) BJ :=
  Equiv.cast (congrArg (fun Z : SemScheme n => Z.scheme.below BJ) h)

theorem castBelow_val {n : ℕ} {X Y : SemScheme n} (h : X = Y) BJ
    d : (castBelow h BJ d).1 = SemScheme.castCell h d.1 := by
  subst h; rfl

theorem castBelow_castBelow_symm {n : ℕ} {X Y : SemScheme n} (h : X = Y)
    BJ d :
    castBelow h BJ (castBelow h.symm BJ d) = d := by
  subst h; rfl



theorem castBelow_symm {n : ℕ} {X Y : SemScheme n} (h : X = Y) BJ :
    (castBelow h BJ).symm = castBelow h.symm BJ := by
  subst h; rfl

/-- Restricted lawfulness transports along an equality of domains. -/
theorem castBelow_respects {n : ℕ} {X Y : SemScheme n} (h : X = Y) {BJ : GradedIndex (Fin n)}
    r :
    RespectsSemanticsBelow Y.rows BJ r ↔
      RespectsSemanticsBelow X.rows BJ (fun d => r (castBelow h BJ d)) := by
  subst h; exact Iff.rfl

/-- Transport of a cell along an equality of domains keeps its grade. -/
theorem castCell_grade {n : ℕ} {X Y : SemScheme n} (h : X = Y) (c : Cell X.scheme) :
    Y.scheme.grade (SemScheme.castCell h c) = X.scheme.grade c := by
  subst h; rfl

section

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

local notation "bC₀" => bC fC hvC KA

local notation "bP₀" => bP fP hvP KA

local notation "castBelow₀₀₀" => castBelow hP (Finset.univ, KA)

local notation "castBelow₀₀₀₀" => castBelow hC.symm (Finset.univ, KA)

/-- **The identification of the two copies of a literally common face**: through the common
restriction `F`, along the bijections `belowEquiv` of the face restrictions. -/
noncomputable def commonFace :=
  (bP₀).symm.trans
    ((castBelow₀₀₀).trans
      ((castBelow₀₀₀₀).trans (bC₀)))

local notation "commonFace₀" => commonFace fP hvP hP fC hvC hC KA

theorem commonFace_apply a :
    commonFace₀ a =
      bC₀ (castBelow₀₀₀₀
        (castBelow₀₀₀ ((bP₀).symm a))) := rfl

local notation "castBelow₀" => castBelow hP.symm (Finset.univ, KA)

local notation "castBelow₀₀" => castBelow hC (Finset.univ, KA)

theorem commonFace_symm_apply e :
    (commonFace₀).symm e =
      bP₀ (castBelow₀
        (castBelow₀₀ ((bC₀).symm e))) := by
  simp  [commonFace,   castBelow_symm]

/-- The underlying cell of the identification. -/
theorem commonFace_val a :
    (commonFace₀ a).1 =
      toCell C.scheme fC hvC (SemScheme.castCell hC.symm (SemScheme.castCell hP
        ((bP₀).symm a).1)) := by
  change (toCell C.scheme fC hvC (castBelow₀₀₀₀
    (castBelow₀₀₀ ((bP₀).symm a))).1) = _
  rw [castBelow_val, castBelow_val]

/-- The identification preserves grades. -/
theorem commonFace_grade (a : P.scheme.below (Finset.univ.image fP, KA)) :
    C.scheme.grade (commonFace₀ a).1 = P.scheme.grade a.1 := by
  rw [commonFace_val]
  change (C.restrictFace fC hvC).scheme.grade (SemScheme.castCell hC.symm
    (SemScheme.castCell hP ((bP₀).symm a).1)) = _
  rw [castCell_grade, castCell_grade]
  exact congrArg P.scheme.grade (toCell_belowEquiv_symm_val P.scheme fP hvP
     (BJ := (Finset.univ.image fP, KA)) rfl a)

/-- The identifications at two grades agree on a common cell. -/
theorem commonFace_val_congr {KA'} (a : P.scheme.below (Finset.univ.image fP, KA))
    (a' : P.scheme.below (Finset.univ.image fP, KA')) (h : a.1 = a'.1) :
    (commonFace₀ a).1 = (commonFace fP hvP hP fC hvC hC KA' a').1 := by
  have e1  :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA))
       rfl a
  have e2  :=
    toCell_belowEquiv_symm_val P.scheme fP hvP (BJ' := (Finset.univ, KA'))
       rfl a'
  have e : ((bP₀).symm a).1 = ((bP fP hvP KA').symm a').1 :=
    toCell_injective P.scheme fP hvP (e1.trans (h.trans e2.symm))
  rw [commonFace_val, commonFace_val, e]

/-- **Restricted lawfulness transports along the identification**, in both directions. -/
theorem commonFace_respects r :
    RespectsSemanticsBelow C.rows (Finset.univ.image fC, KA) r ↔
      RespectsSemanticsBelow P.rows (Finset.univ.image fP, KA)
        (fun a => r (commonFace₀ a)) := by
  constructor
  · intro hr
    have h1 := hr.restrictFace  (hr := hvC) (BJ' := (Finset.univ, KA)) rfl
    have h2 := (castBelow_respects hC.symm _).mp h1
    have h3 := (castBelow_respects hP _).mp h2
    have h4 := h3.of_restrictFace    rfl
    exact h4
  · intro hr
    have h1 : RespectsSemanticsBelow (P.restrictFace fP hvP).rows (Finset.univ, KA)
        (fun d => r (commonFace₀ (bP₀ d))) :=
      hr.restrictFace   (BJ' := (Finset.univ, KA)) rfl
    
    have h2 : RespectsSemanticsBelow F.rows (Finset.univ, KA)
        (fun d => r (commonFace₀
          (bP₀ (castBelow₀ d)))) := by
      aesop
    have e2 : (fun d => r (commonFace₀ (bP₀
        (castBelow₀ (castBelow₀₀
          (castBelow₀₀₀₀ d)))))) =
        fun d => r (commonFace₀
          (bP₀ (castBelow₀ d))) :=
      funext fun d => by rw [castBelow_castBelow_symm]
    have h3 : RespectsSemanticsBelow (C.restrictFace fC hvC).rows (Finset.univ, KA)
        (fun d => r (commonFace₀ (bP₀
          (castBelow₀ (castBelow₀₀ d))))) := by
      refine (castBelow_respects hC.symm _).mpr ?_
      rw [e2]
      exact h2
    have h4  :=
      h3.of_restrictFace    rfl
    have he : (fun e => r (commonFace₀ (bP₀
        (castBelow₀ (castBelow₀₀
          ((bC₀).symm e)))))) = r := by
      funext e
      rw [← commonFace_symm_apply fP hvP hP fC hvC hC KA e, Equiv.apply_symm_apply]
    rw [← he]
    exact h4



