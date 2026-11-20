/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSections
public import VaughtConjecture.Knight.CanonicalLowerLift
public import VaughtConjecture.Knight.FullFaceLifting

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalOriginalLift

open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift

open CoatomBoundaryExtension GradeTailRestoration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 2 ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ 2)

local notation "M" => Frame.two sem hA hproper hg

local notation "topRows" => rows M

local notation "oldTop" => oldTarget M

local notation "oldLow" => CanonicalLowerLift.oldLow sem 2 hA (by decide) hproper hg

/-- At grade one, use the lower-layer lift for a positive cap and a section at bottom. -/
theorem lift_one {C : Finset ι} (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (W : CutCover sem (C, 1) 2) (W₁ : CutCover sem (C, 1) 1) :
    PaddedFaceLift.Lift sem topRows (fun e : D.below (C, 1) => oldLow e.1 e.2.2) := by
  intro p q hp hq γ hγ hag
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := CanonicalSections.exists_section M W hp
    let h12 : GradedLe (A, 1) (A, 2) := ⟨Finset.Subset.refl _, Nat.le_succ 1⟩
    exact ⟨r ∘ CellScheme.below.mono h12, hr.mono h12, hread, fun _ => by simp [hz]⟩
  · exact CanonicalLowerLift.exists_positive_lift sem 2 hA (by decide) hproper hg hfull hp hq hγ hz (fun d => (hag d).symm) W₁

/-- The owner repair and the grade-one lift give the ordinary two-grade face lift. -/
theorem lift_two {C : Finset ι}
    (hfull₁ : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    (hfull₂ : ∃ c : D.below (C, 2), D.cell c.1 = (C, 2))
    (W : CutCover sem (C, 2) 2) (W₁ : CutCover sem (C, 1) 1) :
    PaddedFaceLift.Lift sem topRows (fun e : D.below (C, 2) => oldTop e.1) := by
  let h12 : GradedLe (C, 1) (C, 2) := ⟨Finset.Subset.refl _, Nat.le_succ 1⟩
  have lower : PaddedFaceLift.Lift sem topRows (fun e : D.below (C, 1) => oldLow e.1 e.2.2) :=
    lift_one sem hA hproper hg hfull₁ (W.precomp h12 (bountiful_same_scope sem h12)) W₁
  intro p q
  refine PaddedFaceLift.lift_of_capped (fun _ _ => ?_) (fun _ {p} hp => ?_) (fun _ => ?_)
    (PaddedFaceLift.restore_of_lower h12 le_rfl (fun d h => ⟨d.2.1, h⟩)
      (fun d => oldTarget_grade M d.1)
      (Equiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) lower)
  · obtain ⟨c, hc⟩ := hfull₂
    exact ⟨c.1, hc, rfl⟩
  · exact CanonicalSections.exists_section M W hp
  · intro c hc hg' p q hp hq γ hγ hpos hpc hag
    have hcle : GradedLe (D.cell c.1) (C, 2) := by rw [hc]; exact GradedLe.refl _
    have Wc : CutCover sem (D.cell c.1) 2 := hc.symm ▸ W
    obtain ⟨u, hu, hr, hcap⟩ := exists_owner_capped_lift M c.1 hg' (hp.mono hcle) hq hγ (ne_of_gt hpos)
      (fun e => (hag (CellScheme.below.mono hcle e)).symm) hpc Wc
    have hM : SelfVis 2 (p c) := by simpa only [hg'] using (hp.orderly c).symm
    refine ⟨fun d => min (u d) (p c), hu.cap hM, ?_, ?_, fun _ => min_le_right _ _⟩
    · intro d
      change min (u (oldTop d.1)) (p c) = _
      rw [hr ⟨d.1, hc.symm ▸ d.2⟩]
      change min (min (p d) (p c)) (p c) = _
      simp [min_assoc]
    · intro d
      simpa only [min_assoc, min_eq_right hpc.le] using hcap d

end

end VaughtConjecture.Knight.CanonicalOriginalLift
