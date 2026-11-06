/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedDonorRepair
public import VaughtConjecture.Knight.GradeSplice
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedDonorLift
open Transform Value ExtOrd CappedDonor Growth GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts GrowthPaddedDonorRepair
open GradeTailRestoration AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem restore (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {u : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hu : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) u)
    {M : ExtOrd} (hM : SelfVis 2 M)
    (hread : ∀ d, u (donorAt I X T hA hB hC d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M :=
  AmbientGradeCharts.restore_of_lower
    (show GradedLe (Finset.univ, 1) (Finset.univ, 2) from ⟨Finset.Subset.refl _, Nat.le_succ 1⟩)
    (donor_grade I X T hA hB hC) (fun d => d.2.2)
    (lowerEquiv I X T hA hB hC) (lower_respects_iff I X T hA hB hC)
    (fun d hd => ⟨d.1, Finset.subset_univ _, hd⟩)
    hp hu hM (fun hp₀ hq₀ => GrowthOrderedBase.donor_lift I X T (by omega) hB hC hN hp₀ hq₀)
    hread hbound hmax

theorem active_donor_lift (hN : 2 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 2) → ExtOrd}
    {q : (carrier I X T hA hB hC).below (A, 2) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) q)
    {γ : ExtOrd} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt I X T hA hB hC d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2) r ∧
      (∀ d, r (donorAt I X T hA hB hC d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn : 2 ≤ n + 1 := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (Finset.univ, 2)
    (Plan.mem_gradedPlan.mpr ⟨I.left.scheme.isPlan.domain_mem, by omega,
      by simpa only [Finset.card_univ, Fintype.card_fin] using hn⟩)
  exact AmbientGradeCharts.active_lift_of_restore hp hq hγ hpos hd hpd c₀ hc₀ rfl
    (fun c hci hg hpc => owner_capped I X T hA hB hC hN c hci hg hp hq hγ hpos hpc hag)
    (fun hu hM hread hbound hmax =>
      restore I X T hA hB hC (by omega) hp hu hM hread hbound hmax)
