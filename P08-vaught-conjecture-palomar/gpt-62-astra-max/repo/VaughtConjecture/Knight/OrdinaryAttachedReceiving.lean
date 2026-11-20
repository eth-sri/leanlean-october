/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingProbe
public import VaughtConjecture.Knight.WholeDonorAttachment
public import VaughtConjecture.Knight.CappedDonorFace

/-! # The legal ordinary receiver from literal common-face reference data

KVC's attachment (`daefcbe`) supplies the input plan, occurrences and union.
V-C's literal `commonFace` receipt supplies the catalogue face identification.
Thus the probe requires no attached-plan or shared-source premise from the
model consumer. Its remaining inputs are the actual two schemes, their literal
root restrictions and the acquired reference data. Model realization is separate.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryAttachedReceiving
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CellScheme.restrictFace SemSchemeBoundaryInput
noncomputable section

private theorem faceMap_cast {m k} D Q
    (f : Fin m ↪ Fin k) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (he : D.restrictFace f hv = Q) d :
    faceMap D Q f hv he d = toCell D.scheme f hv (SemScheme.castCell he.symm d) := by
  subst Q
  rfl

private theorem common_alignment {m N} C P
    Q (e : Fin m ↪ Fin N)
    (hvC : Finset.univ.image e ∈ C.scheme.plan)
    (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
    (hC : C.restrictFace e hvC = Q) (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
    {AP} {AC} {k}
    (φ : P.scheme.below (AP, k) ≃ C.scheme.below (AC, k))
    (hAP : AP = Finset.univ.image Fin.castSuccEmb) (hAC : AC = Finset.univ.image e)
    (hk : k = m) (hφ : HEq φ (commonFace Fin.castSuccEmb hvP hP e hvC hC m))
    i :
    ∃ d,
      d.1 = faceMap P Q Fin.castSuccEmb hvP hP i ∧
      (φ d).1 = faceMap C Q e hvC hC i := by
  subst AP AC k
  have he : φ = commonFace Fin.castSuccEmb hvP hP e hvC hC m := eq_of_heq hφ
  subst φ
  let q : Q.Native m := ⟨i, Finset.subset_univ _, gradeC_le i⟩
  let d := bP Fin.castSuccEmb hvP m (castBelow hP.symm (Finset.univ, m) q)
  refine ⟨d, ?_, ?_⟩
  · change toCell P.scheme Fin.castSuccEmb hvP
      (castBelow hP.symm (Finset.univ, m) q).1 = _
    rw [castBelow_val]
    exact (faceMap_cast P Q Fin.castSuccEmb hvP hP i).symm
  · rw [commonFace_apply, Equiv.symm_apply_apply, castBelow_castBelow_symm]
    change toCell C.scheme e hvC (castBelow hC.symm (Finset.univ, m) q).1 = _
    rw [castBelow_val]
    exact (faceMap_cast C Q e hvC hC i).symm

variable {I : Type*} [Fintype I] {nP n : ℕ}
variable (C : SemScheme (n + 4)) (P : SemScheme (nP + 1)) (Q : SemScheme nP)
variable (e : Fin nP ↪ Fin (n + 4))
variable (hvC : Finset.univ.image e ∈ C.scheme.plan)
variable (hvP : Finset.univ.image Fin.castSuccEmb ∈ P.scheme.plan)
variable (hC : C.restrictFace e hvC = Q) (hP : P.restrictFace Fin.castSuccEmb hvP = Q)
variable (R : Ref I nP (n + 4) (n + 4) P C)
variable (hA : R.A = Finset.univ.image Fin.castSuccEmb) (hA' : R.A' = Finset.univ.image e)
variable (hK : R.KA = nP)
variable (hface : HEq R.face (commonFace Fin.castSuccEmb hvP hP e hvC hC nP))

abbrev boundary := WholeDonorAttachment.input e C P Q hvC hvP hC hP

include hA hA' hK hface in
/-- The source-face equation is derived from the literal reference identification. -/
theorem alignment i :
    ∃ d,
      d.1 = (boundary C P Q e hvC hvP hC hP).shared.g i ∧
      (R.face d).1 = (boundary C P Q e hvC hvP hC hP).shared.f i :=
  common_alignment C P Q e hvC hvP hC hP R.face hA hA' hK hface i

end
end VaughtConjecture.Knight.OrdinaryAttachedReceiving
