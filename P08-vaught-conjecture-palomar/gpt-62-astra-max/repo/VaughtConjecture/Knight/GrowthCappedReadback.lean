/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthReplicatedOccurrences

/-! # Physical correctness with a positive, possibly proper private cap

Recognition at the activation grade gives a capped admitted state. It need
not be the uncapped vector. Every original agrees with that state below the
grade maximum, which dominates the actual private cap. Correctness depends
only on these cap readings, so it transfers back to the actual originals.
No top-cap or supplied-admission hypothesis is needed.
-/

@[expose] public section

namespace VaughtConjecture.Knight
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherMixed
noncomputable section

namespace Requests
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  (r : Requests DA DQ)

/-- Correctness depends only on the donor cap readings, active references and
the marker when a high request is present. Internal source choices need not agree. -/
theorem correct_of_observed_readings
    {s s'} {v v'}
    (hobs : ∀ d, d ∈ r.Z ∨ d ∈ r.F ∨ d ∈ r.T →
      min (v d) (s r.capCell) = min (v' d) (s' r.capCell))
    (href : ∀ d ∈ r.F, r.tOf s d = r.tOf s' d)
    (hmark : r.T.Nonempty → r.dOf s = r.dOf s')
    (h : r.Correct s v) : r.Correct s' v' := by
  refine ⟨?_, ?_, ?_⟩
  · simp_all [Correct]
  · simp_all [Correct]
  · intro d hd
    calc
      r.dOf s' = r.dOf s := (hmark ⟨d, hd⟩).symm
      _ ≤ min (v d) (s r.capCell) := h.2.2 d hd
      _ = min (v' d) (s' r.capCell) := hobs d (Or.inr (Or.inr hd))

/-- Correctness reads only the private and donor vectors below its own
visible cap. Agreement is required on the actual cap domain, not future cells. -/
theorem correct_of_cap_agreement
    {s s'} {v v'}
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N)
    (hvis : SelfVis r.N (s' r.capCell)) (hc : s r.capCell = s' r.capCell)
    (hs : CappedEq s s' (s' r.capCell))
    (hv : CappedEq v v' (s' r.capCell))
    (h : r.Correct s v) : r.Correct s' v' := by
  have href (f) (hf : f ∈ r.F) : r.tOf s f = r.tOf s' f := by
    unfold tOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl (hoff f hf), hs,
      evr_min_of_selfVis hvis le_rfl (hoff f hf)]
  have hmark : r.dOf s = r.dOf s' := by
    unfold dOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl r.R_lt_N.le, hs,
      evr_min_of_selfVis hvis le_rfl r.R_lt_N.le]
  exact r.correct_of_observed_readings (fun d _ => by grind)
    href (fun _ => hmark) h

end Requests

namespace GrowthCappedReadback
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)
  (t : ℕ) (ht : t + 2 ≤ A.card)
  (U : Finset ι) (j : ℕ) (hBU : B ⊆ U) (hCU : C ⊆ U)
  (hU : U ∈ R) (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hj : j ≤ U.card) (hj0 : 1 ≤ j) (hjt : j ≤ t + 2)
  (hsmall : n + 1 < X.req.N) (hN : X.req.N ≤ j)
  {p : CellScheme.below (carrier frame t ht) (U, j) → ExtOrd}

open GrowthReplicatedReadback
local notation "Rows" => rows frame t ht
local notation "H" => gradeMax frame t ht U j p X.req.N

include hU hm hj hjt hsmall hN in
/-- Lower original heights dominate the activation-grade maximum. -/
theorem maximum_le_height (hp : RespectsSemanticsBelow Rows (U, j) p)
    k (hk : k ≤ X.req.N) :
    H ≤ height frame t ht U j p k := by
  have he : height frame t ht U j p X.req.N = H := by
    simp [height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]
  rw [← he]
  exact height_antitone frame t ht U hU hm j hj hp hjt hk

include hU hm hj hj0 hjt hsmall in
theorem cap_le_maximum (hp : RespectsSemanticsBelow Rows (U, j) p) :
    p (privateAt frame t ht U j hCU X.req.C (Eq.trans_le X.grade_C hN)) ≤ H := by
  rw [private_readback frame t ht U j hCU hU hm hj hj0 hjt hp,
    X.grade_C, height, ite_eq_right (by omega : ¬ X.req.N ≤ 1), ite_eq_left hN]
  simp

section State
variable {S : State I.right.scheme I.left.scheme} (hS : Admitted X X.req.N S)
  (hprof : ∀ f, S.profile f = min
    (shadowSup frame t ht U hU hm j hj hj0 p f)
    (gradeMax frame t ht U j p X.req.N))

include hjt hsmall hS hprof in
theorem private_capped (hp : RespectsSemanticsBelow Rows (U, j) p)
    d (hd : I.right.scheme.grade d ≤ X.req.N) :
    S.privateValues d =
      min (p (privateAt frame t ht U j hCU d (hd.trans hN))) H := by
  rw [private_readback frame t ht U j hCU hU hm hj hj0 hjt hp,
    min_assoc, min_eq_right (maximum_le_height frame t ht U j hU hm hj hjt
      hsmall hN hp _ hd)]
  exact (GrowthOrderedBase.field_private I X frame.attachment hS d).symm.trans (hprof _)

include hjt hsmall hprof in
theorem donor_capped (hp : RespectsSemanticsBelow Rows (U, j) p)
    d :
    S.donorValues d =
      min (p (donorAt frame t ht U j hBU d
        ((donor_grade_le I X d).trans hN))) H := by
  rw [donor_readback_height frame t ht U j hBU hU hm hj hj0 hjt hp,
    min_assoc, min_eq_right (maximum_le_height frame t ht U j hU hm hj hjt
      hsmall hN hp _ (donor_grade_le I X d))]
  exact (GrowthOrderedBase.field_donor I S d).symm.trans (hprof _)

end State

include hU hm hj hj0 hjt hsmall in
/-- The actual private and donor readings satisfy correctness whenever the
private cap is positive and its bottom class is the template class. -/
theorem physical_correct (hp : RespectsSemanticsBelow Rows (U, j) p)
    (hcap : p (privateAt frame t ht U j hCU X.req.C
      (Eq.trans_le X.grade_C hN)) ≠ ⊥)
    (hclass : ∀ d : I.right.scheme.RowDomain X.req.C,
      p (privateAt frame t ht U j hCU d.1
        ((grade_le_of_below_cap I X d).trans hN)) = ⊥ ↔ d ∈ X.ZA) :
    X.req.Correct
      (fun d => p (privateAt frame t ht U j hCU d.1
        ((grade_le_of_below_cap I X d).trans hN)))
      (fun d => p (donorAt frame t ht U j hBU d
        ((donor_grade_le I X d).trans hN))) := by
  obtain ⟨S, hS, he⟩ := exists_admitted_at frame t ht U hU hm j hj hj0 hp
    X.req.N (by omega) hN (hN.trans hjt)
  have hbound := cap_le_maximum frame t ht U j hCU hU hm hj hj0 hjt hsmall hN hp
  have hpos := fun hz => hcap (le_bot_iff.mp (hbound.trans_eq hz))
  have hpriv := private_capped frame t ht U j hCU hU hm hj hj0 hjt
    hsmall hN hS he hp
  have hdon := donor_capped frame t ht U j hBU hU hm hj hj0 hjt
    hsmall hN he hp
  have hc : S.privateValues X.req.C =
      p (privateAt frame t ht U j hCU X.req.C (Eq.trans_le X.grade_C hN)) := by
    rw [hpriv _ X.grade_C.le, min_eq_left hbound]
  have hin : InClass X.ZA S.privateValues := by
    intro d
    rw [hpriv d.1 (grade_le_of_below_cap I X d)]
    constructor
    · grind
    · grind
  have hvis : SelfVis X.req.N
      (p (privateAt frame t ht U j hCU X.req.C (Eq.trans_le X.grade_C hN))) := by
    rw [← hc]
    have ho := (hS.private_lawful.orderly (Growth.capAt X le_rfl X.req.capCell)).symm
    change SelfVis (I.right.scheme.grade X.req.C) (S.privateValues X.req.C) at ho
    rwa [X.grade_C] at ho
  apply X.req.correct_of_cap_agreement X.off_lt hvis hc _ _ (hS.correct le_rfl hin)
  · intro d
    change min (S.privateValues d.1)
      (p (privateAt frame t ht U j hCU X.req.C (Eq.trans_le X.grade_C hN))) = _
    rw [hpriv d.1 (grade_le_of_below_cap I X d), min_assoc, min_eq_right hbound]
    rfl
  · intro d
    change min (S.donorValues d)
      (p (privateAt frame t ht U j hCU X.req.C (Eq.trans_le X.grade_C hN))) = _
    rw [hdon d, min_assoc, min_eq_right hbound]
    rfl

section Full
variable {v : Cell (carrier frame t ht) → ExtOrd}

include hsmall in
/-- Correctness on the full physical carrier with any positive retained
private cap. The cap may be proper in an independently lawful stable labelling. -/
theorem full_correct (hfull : A.card ≤ t + 2)
    (hv : RespectsSemantics (rows frame t ht) v)
    lab (hclass : InClass X.ZA lab)
    (hcap : lab X.req.C ≠ ⊥)
    (hpriv : ∀ d, v ((GrowthReplicatedRows.privateFace frame t ht).map d) = lab d) :
    X.req.Correct (X.req.sec lab)
      (fun d => v ((GrowthReplicatedRows.donorFace frame t ht).map d)) := by
  have hN := threshold_le_card I X frame.rightProper
  have hprivate (d : Cell I.right.scheme) (hd : I.right.scheme.grade d ≤ A.card) :
      v (privateAt frame t ht A A.card frame.rightProper.subset d hd).1 = lab d := by
    rw [← privateFace_map frame t ht d hd]
    exact hpriv d
  have h := physical_correct frame t ht A A.card frame.leftProper.subset frame.rightProper.subset
    (A_mem frame t ht) (Or.inl rfl) le_rfl (by omega) hfull hsmall hN
    (hv.toBelow (A, A.card)) (by grind)
    (fun d => by rw [hprivate]; exact hclass d)
  have hps : (fun d =>
      v (privateAt frame t ht A A.card frame.rightProper.subset d.1
        ((grade_le_of_below_cap I X d).trans hN)).1) = X.req.sec lab :=
    funext fun d => hprivate d.1 _
  have hds : (fun d : Cell I.left.scheme =>
      v (donorAt frame t ht A A.card frame.leftProper.subset d
        ((donor_grade_le I X d).trans hN)).1) =
      fun d => v ((GrowthReplicatedRows.donorFace frame t ht).map d) :=
    funext fun d => congrArg v (donorFace_map frame t ht d _).symm
  rw [hps, hds] at h
  exact h

end Full
end GrowthCappedReadback
end
end VaughtConjecture.Knight
