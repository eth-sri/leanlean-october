/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthReplicatedOccurrences

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
    {s s' : DA.below (DA.cell r.C) → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hobs : ∀ d, d ∈ r.Z ∨ d ∈ r.F ∨ d ∈ r.T →
      min (v d) (s r.capCell) = min (v' d) (s' r.capCell))
    (href : ∀ d ∈ r.F, r.tOf s d = r.tOf s' d)
    (hmark : r.T.Nonempty → r.dOf s = r.dOf s')
    (h : r.Correct s v) : r.Correct s' v' := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (hobs d (Or.inl hd)).symm.trans (h.1 d hd)
  · intro d hd
    exact (hobs d (Or.inr (Or.inl hd))).symm.trans
      ((h.2.1 d hd).trans (href d hd))
  · intro d hd
    calc
      r.dOf s' = r.dOf s := by tauto
      _ ≤ min (v d) (s r.capCell) := h.2.2 d hd
      _ = min (v' d) (s' r.capCell) := by grind

/-- Correctness reads only the private and donor vectors below its own
visible cap. Agreement is required on the actual cap domain, not future cells. -/
theorem correct_of_cap_agreement
    {s s' : DA.below (DA.cell r.C) → ExtOrd} {v v' : Cell DQ → ExtOrd}
    (hoff : ∀ f ∈ r.F, r.off f ≤ r.N)
    (hvis : SelfVis r.N (s' r.capCell)) (hc : s r.capCell = s' r.capCell)
    (hs : ∀ d, min (s d) (s' r.capCell) = min (s' d) (s' r.capCell))
    (hv : ∀ d, min (v d) (s' r.capCell) = min (v' d) (s' r.capCell))
    (h : r.Correct s v) : r.Correct s' v' := by
  have href (f) (hf : f ∈ r.F) : r.tOf s f = r.tOf s' f := by
    unfold tOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl (hoff f hf), hs,
      evr_min_of_selfVis hvis le_rfl (hoff f hf)]
  have hmark : r.dOf s = r.dOf s' := by
    unfold dOf
    rw [hc, ← evr_min_of_selfVis hvis le_rfl r.R_lt_N.le, hs,
      evr_min_of_selfVis hvis le_rfl r.R_lt_N.le]
  exact r.correct_of_observed_readings (fun d _ => by rw [hc]; exact hv d)
    href (fun _ => hmark) h

end Requests

namespace GrowthCappedReadback

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)
  (hsmall : n + 1 < G.X.req.N)

open GrowthReplicatedReadback

local notation "Rows" => rows G

section Readback

variable {G} (W : Cut G) (hBU : B ⊆ W.scope) (hCU : C ⊆ W.scope)
  (hN : G.X.req.N ≤ W.grade) {p : CellScheme.below (carrier G) W.index → ExtOrd}

local notation "H" => gradeMax W p G.X.req.N

include hsmall hN in
/-- Lower original heights dominate the activation-grade maximum. -/
theorem maximum_le_height (hp : RespectsSemanticsBelow Rows W.index p)
    (k : ℕ) (hk : k ≤ G.X.req.N) :
    H ≤ height W p k := by
  have he : height W p G.X.req.N = H := by
    grind [height]
  rw [← he]
  exact height_antitone W hp hk

include hsmall in
theorem cap_le_maximum (hp : RespectsSemanticsBelow Rows W.index p) :
    p (privateAt G W.scope W.grade hCU G.X.req.C (cap_grade_le G W.grade hN)) ≤ H := by
  rw [private_readback W hCU hp,
    G.X.grade_C, height, ite_eq_right (by omega), ite_eq_left hN]
  simp

section State

variable {S : State G.I.right.scheme G.I.left.scheme} (hS : Admitted G.X G.X.req.N S)
  (hprof : ∀ f, S.profile f = min
    (shadowSup W p f)
    (gradeMax W p G.X.req.N))

include hsmall hS hprof in
theorem private_capped (hp : RespectsSemanticsBelow Rows W.index p)
    (d : Cell G.I.right.scheme) (hd : G.I.right.scheme.grade d ≤ G.X.req.N) :
    S.privateValues d =
      min (p (privateAt G W.scope W.grade hCU d (hd.trans hN))) H := by
  rw [private_readback W hCU hp,
    min_assoc, min_eq_right (maximum_le_height hsmall W hN hp _ hd)]
  exact (GrowthOrderedBase.field_private G.I G.X G.attach hS d).symm.trans (hprof _)

include hsmall hprof in
theorem donor_capped (hp : RespectsSemanticsBelow Rows W.index p)
    (d : Cell G.I.left.scheme) :
    S.donorValues d =
      min (p (donorAt G W.scope W.grade hBU d
        ((donor_grade_le G d).trans hN))) H := by
  rw [donor_readback_height W hBU hp,
    min_assoc, min_eq_right (maximum_le_height hsmall W hN hp _ (donor_grade_le G d))]
  exact (GrowthOrderedBase.field_donor G.I S d).symm.trans (hprof _)

end State

include hsmall in
/-- The actual private and donor readings satisfy correctness whenever the
private cap is positive and its bottom class is the template class. -/
theorem physical_correct (hp : RespectsSemanticsBelow Rows W.index p)
    (hcap : p (privateAt G W.scope W.grade hCU G.X.req.C
      (cap_grade_le G W.grade hN)) ≠ ⊥)
    (hclass : ∀ d : G.I.right.scheme.below (G.I.right.scheme.cell G.X.req.C),
      p (privateAt G W.scope W.grade hCU d.1
        ((grade_le_of_below_cap G d).trans hN)) = ⊥ ↔ d ∈ G.X.ZA) :
    G.X.req.Correct
      (fun d => p (privateAt G W.scope W.grade hCU d.1
        (by grind)))
      (fun d => p (donorAt G W.scope W.grade hBU d
        ((donor_grade_le G d).trans hN))) := by
  obtain ⟨S, hS, he⟩ := exists_admitted_at W hp
    G.X.req.N (by omega) hN
  have hbound := cap_le_maximum hsmall W hCU hN hp
  have hpos : H ≠ ⊥ := by grind
  have hpriv := private_capped hsmall W hCU hN hS he hp
  have hdon := donor_capped hsmall W hBU hN he hp
  have hc : S.privateValues G.X.req.C =
      p (privateAt G W.scope W.grade hCU G.X.req.C (cap_grade_le G W.grade hN)) := by
    rw [hpriv _ G.X.grade_C.le, min_eq_left hbound]
  have hin : InClass G.X.ZA S.privateValues := by
    intro d
    rw [hpriv d.1 (grade_le_of_below_cap G d)]
    constructor
    · intro h
      exact (hclass d).mp (eq_of_min_eq_of_lt' h (bot_lt_iff_ne_bot.mpr hpos))
    · intro h
      rw [(hclass d).mpr h, min_eq_left bot_le]
  have hvis : SelfVis G.X.req.N
      (p (privateAt G W.scope W.grade hCU G.X.req.C (cap_grade_le G W.grade hN))) := by
    rw [← hc]
    have ho := (hS.private_lawful.orderly (Growth.capAt G.X le_rfl G.X.req.capCell)).symm
    change SelfVis (G.I.right.scheme.grade G.X.req.C) (S.privateValues G.X.req.C) at ho
    rwa [G.X.grade_C] at ho
  apply G.X.req.correct_of_cap_agreement G.X.off_lt hvis hc _ _ (hS.correct le_rfl hin)
  · intro d
    change min (S.privateValues d.1)
      (p (privateAt G W.scope W.grade hCU G.X.req.C (cap_grade_le G W.grade hN))) = _
    rw [hpriv d.1 (grade_le_of_below_cap G d), min_assoc, min_eq_right hbound]
    rfl
  · intro d
    change min (S.donorValues d)
      (p (privateAt G W.scope W.grade hCU G.X.req.C (cap_grade_le G W.grade hN))) = _
    rw [hdon d, min_assoc, min_eq_right hbound]
    rfl

end Readback

section Full

variable {v : Cell (carrier G) → ExtOrd}

include hsmall in
/-- Correctness on the full physical carrier with any positive retained
private cap. The cap may be proper in an independently lawful stable labelling. -/
theorem full_correct (hfull : A.card ≤ G.depth + 2)
    (hv : RespectsSemantics (rows G) v)
    (lab : Cell G.I.right.scheme → ExtOrd) (hclass : InClass G.X.ZA lab)
    (hcap : lab G.X.req.C ≠ ⊥)
    (hpriv : ∀ d, v ((GrowthReplicatedRows.privateFace G).map d) = lab d) :
    G.X.req.Correct (G.X.req.sec lab)
      (fun d => v ((GrowthReplicatedRows.donorFace G).map d)) := by
  have hN := threshold_le_card G
  have hprivate (d : Cell G.I.right.scheme) (hd : G.I.right.scheme.grade d ≤ A.card) :
      v (privateAt G A A.card G.rightProper.subset d hd).1 = lab d := by
    rw [← privateFace_map G d hd]
    exact hpriv d
  let W : Cut G := ⟨A, A.card, G.I.isPlan.domain_mem, Or.inl rfl, le_rfl, G.pos, hfull⟩
  have h := physical_correct hsmall W G.leftProper.subset G.rightProper.subset hN
    (hv.toBelow (A, A.card)) (by rw [hprivate]; exact hcap)
    (fun d => by rw [hprivate]; exact hclass d)
  have hps : (fun d : G.I.right.scheme.below (G.I.right.scheme.cell G.X.req.C) =>
      v (privateAt G A A.card G.rightProper.subset d.1
        ((grade_le_of_below_cap G d).trans hN)).1) = G.X.req.sec lab :=
    funext fun d => hprivate d.1 _
  have hds : (fun d : Cell G.I.left.scheme =>
      v (donorAt G A A.card G.leftProper.subset d
        ((donor_grade_le G d).trans hN)).1) =
      fun d => v ((GrowthReplicatedRows.donorFace G).map d) :=
    funext fun d => congrArg v (donorFace_map G d _).symm
  rwa [hps, hds] at h

end Full

end GrowthCappedReadback

end

end VaughtConjecture.Knight
