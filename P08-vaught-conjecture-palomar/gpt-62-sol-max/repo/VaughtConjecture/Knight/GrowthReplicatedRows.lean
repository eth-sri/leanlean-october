/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationLifting
public import VaughtConjecture.Knight.GrowthPaddedIteration
public import VaughtConjecture.Knight.PaddedInstallation
public import VaughtConjecture.Knight.PaddedSourceTable

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedRows

open AmalgamationPlan Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration ScopeReplicationCarrier

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {attach : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}
  {k : ℕ} (P : Layer I X attach hA hB hC k)

/-- Every proper old owner lies inside an original face. This concerns
occupied cells, not a two-face cover of the whole plan. -/
theorem proper_covered (c : Cell P.carrier) (hc : P.carrier.scope c ≠ A) :
    P.carrier.scope c ⊆ B ∨ P.carrier.scope c ⊆ C := by
  rcases P.cases c with ⟨d, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary (by omega : 0 < A.card) d with
      ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hi := (P.base_index (RelativeLadderLayer.old I.boundary (by omega) e)).trans
        (RelativeLadderLayer.old_index I.boundary (by omega) e)
      have he := (I.occupied_iff (I.boundary.cell_mem e)).mp ⟨e, rfl⟩
      simp_all
    · exact (hc ((congrArg Prod.fst (P.base_index _)).trans
        (congrArg Prod.fst (RelativeLadderLayer.added_index I.boundary (by omega) v)))).elim
  trivial

abbrev frame : Frame A := ⟨P.carrier, B, C, proper_covered P, P.rows⟩

abbrev carrier := ScopeReplicationCarrier.scheme (frame P)

abbrev old := ScopeReplicationCarrier.old (frame P)

abbrev erase := ScopeReplicationCarrier.erase (frame P)

def rows : Semantics (carrier P) :=
  ScopeReplicationSemantics.rows (frame P)

theorem consistent : (rows P).IsConsistent :=
  ScopeReplicationSemantics.consistent (frame P) P.consistent

theorem coded (hp : P.rows.IsCoded) : (rows P).IsCoded := by
  intro c d
  change IsCodedLabel ((carrier P).grade c) (P.rows.E (erase P c) _)
  rw [← ScopeReplicationCarrier.erase_grade (frame P) c]
  exact hp _ _

def face {T : Finset ι} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE P.rows) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows P) :=
  ScopeReplicationSemantics.face (frame P) F hT

theorem copy_eq {V : Finset ι × ℕ} {p : (carrier P).below V → ExtOrd}
    (hp : RespectsSemanticsBelow (rows P) V p) (a b : (carrier P).below V)
    (hs : (carrier P).scope a.1 ⊆ (carrier P).scope b.1) (he : erase P a.1 = erase P b.1) :
    p a = p b :=
  ScopeReplicationSemantics.copy_eq (frame P) hp a b hs he

/-- Replication consumes the single-scope lift, not a selected rendering or
an assumed extension of the replicated ambient. -/
theorem lift_to_full {U : Finset ι × ℕ} {j : ℕ} (h : GradedLe U (A, j))
    (hside : U.1 ⊆ B ∨ U.1 ⊆ C) (hl : CoatomBoundaryExtension.CappedLift P.rows h) :
    CoatomBoundaryExtension.CappedLift (rows P) h :=
  ScopeReplicationLifting.lift_to_full (frame P) h hside hl

section Constructed

variable (G : BuildContext A B C R m n J)

local notation "Q" => G.tower

theorem build_coded : (rows Q).IsCoded :=
  coded _ (Padded.build_coded G.I.consistent G.I.coded G.depth G.fits)

def donorFace : ExactSemanticFace G.I.leftRows (rows Q) :=
  face _ ((Q).face G.I.leftFace G.leftProper.not_ge) (Or.inl le_rfl)

def privateFace : ExactSemanticFace G.I.rightRows (rows Q) :=
  face _ ((Q).face G.I.rightFace G.rightProper.not_ge) (Or.inr le_rfl)

theorem donor_order : StrictMono (donorFace G).map :=
  (old_order (frame Q)).comp ((Q).face_mono _ G.leftProper.not_ge G.I.left_order)

theorem private_order : StrictMono (privateFace G).map :=
  (old_order (frame Q)).comp ((Q).face_mono _ G.rightProper.not_ge G.I.right_order)

/-- All plan scopes, including mixed ones, are occupied through the installed height. -/
theorem complete_through {V : Finset ι × ℕ} (hV : V ∈ Plan.gradedPlan R)
    (hv : V.2 ≤ G.depth + 2) : ∃ d, (carrier Q).cell d = V := by
  classical
  by_cases hside : V.1 ⊆ B ∨ V.1 ⊆ C
  · obtain ⟨d, hd⟩ := (G.I.occupied_iff hV).mpr hside
    exact ⟨old Q ((Q).original d), (old_index _ _).trans (((Q).original_index d).trans hd)⟩
  · obtain ⟨c, hc⟩ := (Q).full_occupied (by omega) V.2 (Plan.mem_gradedPlan.mp hV).2.1 hv
    have hg := congrArg Prod.snd hc
    change (Q).carrier.grade c = V.2 at hg
    have hm : V.1 = A ∨ Mixed B C V.1 := by tauto
    have hplan : V.1 ∈ (Q).carrier.plan := by
      rw [GrowthPaddedIteration.build_plan]; exact (Plan.mem_gradedPlan.mp hV).1
    refine ⟨atScope (frame Q) V.1 hplan hm c (congrArg Prod.fst hc)
      (hg ▸ (Plan.mem_gradedPlan.mp hV).2.2), ?_⟩
    exact (atScope_index _ _ _ _ _ _ _).trans (by rw [hg])

/-- At full installed height this includes the whole graded plan. -/
theorem complete (hfull : A.card ≤ G.depth + 2) : (carrier Q).IsComplete := by
  intro V hV
  have hp : (carrier Q).plan = R := GrowthPaddedIteration.build_plan ..
  rw [hp] at hV
  exact complete_through G hV ((Plan.mem_gradedPlan.mp hV).2.2.trans
    ((Finset.card_le_card (G.I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV).1)).trans hfull))

/-- Targets inside either original face use that face's bountifulness. -/
theorem inherited_lift {U V : Finset ι × ℕ}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) : CoatomBoundaryExtension.CappedLift (rows Q) h :=
  G.I.installed_lift (donorFace G) (privateFace G) hU hV h hv

end Constructed

end

end VaughtConjecture.Knight.GrowthReplicatedRows
