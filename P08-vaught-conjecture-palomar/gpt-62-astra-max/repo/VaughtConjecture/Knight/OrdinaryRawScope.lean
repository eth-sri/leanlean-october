/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryPlanScopeStep
public import VaughtConjecture.Knight.CanonicalRecursiveCoverage

/-! # The ordinary producer on its actual raw boundary

Factor the existing canonical constructors over their old-boundary premises.
No second enumeration, independently chosen facet, or output lifting theorem
is supplied. The binary facets and their common plan come from this plan.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryRawScope
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open OrdinaryScopeOperator AmalgamatedBoundaryPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

/-- Properties of the existing proper boundary, not of a prospective output. -/
structure Ready : Prop where
  proper : D.AvoidsScope A
  consistent : sem.IsConsistent
  coded : sem.IsCoded
  lifts : CoatomBoundaryExtension.OldLifts sem
  complete : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d, D.cell d = J

variable (H : Ready sem) (s : Step A) (hplan : D.plan = s.plan)

include hplan in
theorem left_mem : A.erase s.a ∈ D.plan := by
  rw [hplan]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.left_plan.domain_mem)

include hplan in
theorem right_mem : A.erase s.b ∈ D.plan := by
  rw [hplan]
  exact Finset.mem_union_left _ (Finset.mem_union_right _ s.right_plan.domain_mem)

include hplan in
theorem overlap_mem : A.erase s.a ∩ A.erase s.b ∈ D.plan := by
  rw [hplan, erased_inter]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.common_left)

include hplan in
theorem coverage (C : Finset ι) (hC : C ∈ D.plan) (hCA : C ≠ A) :
    C ⊆ A.erase s.a ∨ C ⊆ A.erase s.b :=
  OrdinaryPlanScopeStep.coverage s C (hplan ▸ hC) hCA

include H in
theorem boundary_grade {k : ℕ} (hA : A.card ≤ k + 1) (d : Cell D) : D.grade d ≤ k := by
  have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), H.proper d⟩)
  have hg := D.grade_le_card_scope d
  omega

def core (n : ℕ) (hn : 0 < n) (hA : n ≤ A.card) (hg : ∀ d : Cell D, D.grade d ≤ n)
    (hL : n ≤ (A.erase s.a).card) (hR : n ≤ (A.erase s.b).card) :
    OrdinaryScopeOperator.Core sem n where
  carrier := CanonicalRecursiveContract.carrier sem n hA
  rows := CanonicalRecursiveSemantics.rows sem H.proper n hA
  plan := CanonicalRecursiveBoundaryTransport.plan_eq sem n hA
  original := CanonicalRecursiveInventory.boundary sem n hA
  index := CanonicalRecursiveInventory.boundary_cell sem n hA
  coverage d := by
    rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem)
      n hA d with ⟨c, rfl⟩ | ⟨j, _, _, he⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr (congrArg Prod.fst he)
  row := CanonicalRecursiveLiteralRows.row sem H.proper n hA
  consistent := CanonicalRecursiveSemantics.consistent sem H.proper H.consistent n hA
  coded := CanonicalRecursiveCoding.coded sem H.proper H.coded n hA
  bountiful := by
    apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
      (CanonicalRecursiveCoverage.grade_bound sem n hA hg) hn
    intro C T j hC hT hj hCT
    rw [CanonicalRecursiveBoundaryTransport.plan_eq] at hC hT
    exact CanonicalRecursiveInitialized.lift sem H.proper H.lifts
      (left_mem s hplan) (right_mem s hplan)
      (OrdinaryPlanScopeStep.left_proper s) (OrdinaryPlanScopeStep.right_proper s)
      (overlap_mem s hplan) (coverage s hplan) n hA hL hR
      (fun C hC hCA j hj hjC _ => H.complete (C, j) (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA)
      hC hT ⟨hCT, le_rfl⟩ hj
  grade := CanonicalRecursiveCoverage.grade_bound sem n hA hg
  complete := CanonicalRecursiveCoverage.complete_through sem n hA H.complete
  short := (CanonicalRecursiveSemantics.state sem H.proper n hA).full_short
  render := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).sectionOf
    hA (hp.toBelow (A, A.card)) ht
  readback := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_boundary
    hA (hp.toBelow (A, A.card)) ht
  lawful := by
    intro p hp ht G θ hG hθ
    apply ((CanonicalRecursiveSemantics.state sem H.proper n hA).section_lawful
      hA (hp.toBelow (A, A.card)) ht hG hθ).toRespects
    intro d
    exact ⟨(CanonicalRecursiveContract.carrier sem n hA).isPlan.subset_of_mem
      ((CanonicalRecursiveContract.carrier sem n hA).scope_mem_plan d),
      (CanonicalRecursiveCoverage.grade_bound sem n hA hg d).trans hA⟩
  bound := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_bound
    hA (hp.toBelow (A, A.card)) ht
  support := fun hp ht => (CanonicalRecursiveSemantics.state sem H.proper n hA).section_supported
    hA (hp.toBelow (A, A.card)) ht
  agreement := fun hp ht hq htq =>
    (CanonicalRecursiveSemantics.state sem H.proper n hA).section_agreement
    hA (hp.toBelow (A, A.card)) ht (hq.toBelow (A, A.card)) htq

/-- Construct the operation on this raw boundary; derive the binary facets
from its actual plan, rather than requesting legal copies of those facets. -/
def build (k : ℕ) (hk : 0 < k) (hcard : A.card = k + 1) :
    OrdinaryScopeOperator.Core sem k := by
  let s := Classical.choose (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hplan := Classical.choose_spec (exists_step D.isPlan (by omega : 2 ≤ A.card))
  have hL := (OrdinaryPlanScopeStep.left_height s hcard).ge
  have hR := (OrdinaryPlanScopeStep.right_height s hcard).ge
  have hg := boundary_grade sem H hcard.le
  exact core sem H s hplan.symm k hk (by omega) hg hL hR

end

section Mute
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {k : ℕ} (S : OrdinaryScopeOperator.Core sem k)

theorem completed_highest_row (hk : 0 < k) (hcard : A.card = k + 1)
    (c : Cell (S.finish hk hcard).carrier)
    (hc : (S.finish hk hcard).carrier.grade c = k + 1)
    (d : (S.finish hk hcard).carrier.RowDomain c) :
    (S.finish hk hcard).rows.E c d = ⊥ := by
  rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c with
    ⟨c, rfl⟩ | rfl
  · have he := congrArg Prod.snd
      (MaximalFullLayer.old_index S.carrier k (k + 1) (Nat.lt_succ_self k) hcard.ge c)
    have hg : S.carrier.grade c = k + 1 := he.symm.trans hc
    have := S.grade c
    omega
  · exact OrdinaryScopeMute.apex_row S.carrier S.rows k (k + 1) S.grade
      (Nat.lt_succ_self k) hcard.ge d

end Mute
end VaughtConjecture.Knight.OrdinaryRawScope
