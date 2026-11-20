/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.ScopeReplicationLifting
public import VaughtConjecture.Knight.GrowthPaddedInstallation

/-! # The actual growth rows on every mixed scope

Instantiate scope replication on the constructed one-scope growth layers.
The catalogue and the full padded grade-one base are unchanged. Every mixed
scope receives each eligible full-scope prototype, with actual enlarged rows.
Consistency, coding, selected lawfulness, prefix agreement and support are
derived. Original faces remain literal and ordered. Completeness through the
installed height no longer assumes that proper scopes lie in an original face.
This does not yet prove arbitrary mixed-section extension or bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthReplicatedRows
open AmalgamationPlan Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration ScopeReplicationCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {frame : I.GrowthFrame X}
  {k : ℕ} (P : Layer frame k)

/-- Every proper old owner lies inside an original face. This concerns
occupied cells, not a two-face cover of the whole plan. -/
theorem proper_covered c (hc : P.carrier.scope c ≠ A) :
    P.carrier.scope c ⊆ B ∨ P.carrier.scope c ⊆ C := by
  rcases P.cases c with ⟨d, rfl⟩ | ⟨hs, _, _⟩
  · rcases RelativeLadderLayer.cell_cases I.boundary frame.positive d with
      ⟨e, rfl⟩ | ⟨v, rfl⟩
    · have hi := (P.base_index (RelativeLadderLayer.old I.boundary frame.positive e)).trans
        (RelativeLadderLayer.old_index I.boundary frame.positive e)
      have he := (I.occupied_iff (I.boundary.cell_mem e)).mp ⟨e, rfl⟩
      simp_all
    · exact (hc ((congrArg Prod.fst (P.base_index _)).trans
        (congrArg Prod.fst (RelativeLadderLayer.added_index I.boundary frame.positive v)))).elim
  simp_all

abbrev carrier := ScopeReplicationCarrier.scheme P.carrier B C
abbrev old := ScopeReplicationCarrier.old P.carrier B C
abbrev erase := ScopeReplicationCarrier.erase P.carrier B C

def rows : Semantics (carrier P) :=
  ScopeReplicationSemantics.rows P.carrier B C (proper_covered P) P.rows

theorem consistent : (rows P).IsConsistent :=
  ScopeReplicationSemantics.consistent P.carrier B C (proper_covered P) P.rows P.consistent

theorem coded (hp : P.rows.IsCoded) : (rows P).IsCoded := by
  intro c d
  rw [← ScopeReplicationCarrier.erase_grade P.carrier B C c]
  solve_by_elim

def face {T} {E : CellScheme T} {semE : Semantics E}
    (F : ExactSemanticFace semE P.rows) (hT : T ⊆ B ∨ T ⊆ C) :
    ExactSemanticFace semE (rows P) :=
  ScopeReplicationSemantics.face P.carrier B C (proper_covered P) P.rows F hT

theorem copy_eq {V} {p}
    (hp : RespectsSemanticsBelow (rows P) V p) a b
    (hs : (carrier P).scope a.1 ⊆ (carrier P).scope b.1) (he : erase P a.1 = erase P b.1) :
    p a = p b :=
  ScopeReplicationSemantics.copy_eq P.carrier B C (proper_covered P) P.rows hp a b hs he

/-- Replication consumes the single-scope lift, not a selected rendering or
an assumed extension of the replicated ambient. -/
theorem lift_to_full {U} {j} (h : GradedLe U (A, j))
    (hside : U.1 ⊆ B ∨ U.1 ⊆ C) (hl : CoatomBoundaryExtension.CappedLift P.rows h) :
    CoatomBoundaryExtension.CappedLift (rows P) h :=
  ScopeReplicationLifting.lift_to_full P.carrier B C (proper_covered P) P.rows h hside hl

section Constructed
variable (frame) (t : ℕ) (ht : t + 2 ≤ A.card)

abbrev built := build frame t ht

theorem build_consistent : (rows (built frame t ht)).IsConsistent :=
  consistent _

theorem build_coded : (rows (built frame t ht)).IsCoded :=
  coded _ (GrowthPaddedInstallation.build_coded frame t ht)

def donorFace : ExactSemanticFace I.leftRows (rows (built frame t ht)) :=
  face _ (GrowthPaddedInstallation.donorFace frame t ht) (Or.inl le_rfl)

def privateFace : ExactSemanticFace I.rightRows (rows (built frame t ht)) :=
  face _ (GrowthPaddedInstallation.privateFace frame t ht) (Or.inr le_rfl)

theorem donor_order : StrictMono (donorFace frame t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.donor_order frame t ht)

theorem private_order : StrictMono (privateFace frame t ht).map :=
  (old_order _ B C).comp (GrowthPaddedInstallation.private_order frame t ht)

/-- All actual plan scopes, mixed ones included, are occupied through the
installed height. No two-face coverage hypothesis remains. -/
theorem complete_through {V} (hV : V ∈ Plan.gradedPlan R)
    (hv : V.2 ≤ t + 2) :
    ∃ d, (carrier (built frame t ht)).cell d = V := by
  classical
  let P := built frame t ht
  by_cases hside : V.1 ⊆ B ∨ V.1 ⊆ C
  · obtain ⟨d, hd⟩ := (I.occupied_iff hV).mpr hside
    refine ⟨old P (P.baseMap (RelativeLadderLayer.old I.boundary frame.positive d)), ?_⟩
    exact (old_index _ B C _).trans ((P.base_index _).trans
      ((RelativeLadderLayer.old_index I.boundary frame.positive d).trans hd))
  · obtain ⟨c, hc⟩ := GrowthPaddedInstallation.full_occupied frame t ht
      V.2 (Plan.mem_gradedPlan.mp hV).2.1 hv
    have hs := congrArg Prod.fst hc
    have hg := congrArg Prod.snd hc
    change P.carrier.grade c = V.2 at hg
    have hm : V.1 = A ∨ Mixed B C V.1 := Or.inr
      ⟨fun h => hside (Or.inl h), fun h => hside (Or.inr h)⟩
    have hplan : V.1 ∈ P.carrier.plan := by
      rw [GrowthPaddedIteration.build_plan]; exact (Plan.mem_gradedPlan.mp hV).1
    refine ⟨atScope P.carrier B C V.1 hplan hm c hs
      (hg ▸ (Plan.mem_gradedPlan.mp hV).2.2), ?_⟩
    exact (atScope_index P.carrier B C _ _ _ _ _ _).trans (by simp_all)

end Constructed

/-- At full installed height every graded-plan index is occupied, including
all mixed scopes. This is completeness, not bountifulness. -/
theorem complete :
    (carrier (built frame (A.card - 2) frame.fullHeight.le)).IsComplete := by
  intro V hV
  have hp : (carrier (built frame (A.card - 2) frame.fullHeight.le)).plan = R :=
    GrowthPaddedIteration.build_plan frame (A.card - 2) frame.fullHeight.le
  have hV' : V ∈ Plan.gradedPlan R := by rwa [hp] at hV
  have hg := (Plan.mem_gradedPlan.mp hV').2.2
  have hc := Finset.card_le_card (I.boundary.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hV').1)
  exact complete_through frame (A.card - 2) frame.fullHeight.le hV' (by have := frame.fullHeight; omega)

/-- Targets inside either literal original face use that face's existing
bountifulness, with no mixed-target extension premise. -/
theorem inherited_lift t (ht : t + 2 ≤ A.card) {U V}
    (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) :
    CoatomBoundaryExtension.CappedLift (rows (built frame t ht)) h := by
  by_cases he : U = V
  · subst V; exact CoatomBoundaryExtension.lift_refl
  rcases hv with hb | hc
  · exact (donorFace frame t ht).lift hb
      (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact (privateFace frame t ht).lift hc
      (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

end
end VaughtConjecture.Knight.GrowthReplicatedRows
