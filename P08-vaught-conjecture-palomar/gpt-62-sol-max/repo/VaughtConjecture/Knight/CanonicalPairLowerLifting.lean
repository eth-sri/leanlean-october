/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairBoundary
public import VaughtConjecture.Knight.CanonicalCoatomBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPairLowerLifting

open Transform Value ExtOrd CanonicalPairBoundary CoatomBoundaryExtension AmalgamationPlan

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (j k : ℕ)

variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

theorem transport_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k)
    (hl : CappedLift (lowerRows sem j k hj hkA hp hjk) h) :
    CappedLift (rows sem j k hj hjA hk hkA hp hjk) h := by
  let e (B : Finset ι × ℕ) (hB : B.2 ≤ k) :=
    GradeCutPairCarrier.belowEquiv D (firstProfiles sem j k) (secondProfiles sem k)
      j k hj hjA hk hkA B hB
  let hr := GradeCutPairRows.lower_respects_iff D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk)
  exact CappedLift.of_equiv (e I (h.2.trans hJ)) (e J hJ) (fun _ => rfl) le_rfl
    (hr I (h.2.trans hJ)) (hr J hJ) hl

include hk in
/-- Grade restriction obtains its proper-target clauses from the old schemes.
Nominal indices above the cut are handled at the effective grade, without
changing the external cap. -/
theorem cut_oldLifts (hold : CanonicalCoatomBountiful.OldLifts sem) :
    CanonicalCoatomBountiful.OldLifts (boundaryRows sem k) := by
  intro I J hI hJ hJA h
  apply EffectiveGradeLifting.lift (GradeCutBoundary.grade_bound D k) h
  apply (GradeCutLifting.lift_iff sem k (EffectiveGradeLifting.cut_le h) (min_le_right _ _)).mpr
  have mem (B : Finset ι × ℕ) (hB : B ∈ Plan.gradedPlan D.plan) :
      EffectiveGradeLifting.cut (K := k) B ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hB
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hk, (min_le_left _ _).trans hc⟩
  aesop

variable (hA : 2 ≤ A.card) (hold : CanonicalCoatomBountiful.OldLifts sem)

variable {L R : Finset ι}

variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)

variable (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)

variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
  ∃ d : Cell D, D.cell d = (C, i))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Bountifulness of the actual grade-one/two lower carrier is constructed
from the two old schemes' clauses even when their proper owners have grade three
or higher. All original occurrences through grade two are retained. -/
theorem lower_bountiful :
    (lowerRows sem 1 2 (by decide) hA hp (by decide)).IsBountiful := by
  apply CanonicalCoatomBountiful.bountiful (boundaryRows sem 2) hA
    (GradeCutBoundary.proper D 2 hp) (GradeCutBoundary.grade_bound D 2)
    (cut_oldLifts sem 2 (by decide) hold) hL hR hLA hRA hLc hRc hO hcover
  intro C hC hCA i hi hiC hi2
  obtain ⟨d, hd⟩ := hcomplete C hC hCA i hi hiC hi2
  have hg : D.grade d ≤ 2 := by aesop
  refine ⟨GradeCutBoundary.fromCell D 2 d hg, ?_⟩
  exact (congrArg D.cell (GradeCutBoundary.to_from D 2 d hg)).trans hd

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- One arbitrary lawful prescribed face, one arbitrary lawful lower ambient,
and the original permitted cap. The conclusion preserves the entire auxiliary
vector through grade two; no conditions on a future grade-three row are inputs. -/
theorem lower_lift {I J : Finset ι × ℕ}
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I J) (hJ2 : J.2 ≤ 2) :
    CappedLift (rows sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
      (by decide) hA hp (by decide)) h := by
  apply transport_lift sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
    (by decide) hA hp (by decide) h hJ2
  have hb := lower_bountiful sem hp hA hold hL hR hLA hRA hLc hRc hO hcover hcomplete
  by_cases he : I = J
  · subst J; exact lift_refl
  solve_by_elim

end

end VaughtConjecture.Knight.CanonicalPairLowerLifting
