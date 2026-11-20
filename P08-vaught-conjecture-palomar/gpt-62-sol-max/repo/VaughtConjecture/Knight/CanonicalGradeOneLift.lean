/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldOwnerLift

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalGradeOneLift

open Transform Value ExtOrd CanonicalFieldLayer CanonicalFieldOwnerLift

open CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (X : Type*) [Fintype X] (occ : Cell D → X)

variable (hA : 1 ≤ A.card) (hproper : ∀ d : Cell D, D.scope d ≠ A)

variable (hg : ∀ d : Cell D, D.grade d ≤ 1) (hinj : Function.Injective occ)

include hinj

/-- Positive original-cap lifting from an actual proper grade-one face. The
ambient is arbitrary on the actual full grade-one target; only OLD face
lifting clauses are consumed. The inactive branch also covers literal top cap. -/
theorem exists_positive_lift {C : Finset ι}
    (hfull : ∃ c : D.below (C, 1), D.cell c.1 = (C, 1))
    {p : D.below (C, 1) → ExtOrd} (hp : RespectsSemanticsBelow sem (C, 1) p)
    {q : target sem 1 X occ (by decide) hA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e : D.below (C, 1), min (p e) γ =
      min (q (oldTarget sem 1 X occ (by decide) hA hg e.1)) γ)
    (W : CutCover sem (C, 1) 1) :
    ∃ r : target sem 1 X occ (by decide) hA → ExtOrd,
      RespectsSemanticsBelow (rows sem 1 X occ (by decide) hA hproper hg) (A, 1) r ∧
      (∀ e : D.below (C, 1), r (oldTarget sem 1 X occ (by decide) hA hg e.1) = p e) ∧
      ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨c, hci, hmax⟩ := AmbientGradeCharts.exists_maximizer hp hfull
  have hdom (e : D.below (C, 1)) : p e ≤ p c :=
    hmax e (Nat.le_antisymm (hg e.1) (D.grade_pos e.1))
  by_cases hactive : γ < p c
  · have hc : D.grade c.1 = 1 := congrArg Prod.snd hci
    have hcle : GradedLe (D.cell c.1) (C, 1) := by rw [hci]; exact GradedLe.refl _
    let pc : D.below (D.cell c.1) → ExtOrd := fun e => p ⟨e.1, e.2.trans hcle⟩
    have hpc : RespectsSemanticsBelow sem (D.cell c.1) pc := hp.mono hcle
    have Wc : CutCover sem (D.cell c.1) 1 := hci.symm ▸ W
    obtain ⟨r, hr, hread, hcap⟩ := exists_owner_capped_lift sem 1 X occ (by decide) hA
      hproper hg hinj c.1 hc hpc hq hγ hγb (fun e => hag ⟨e.1, e.2.trans hcle⟩)
      hactive Wc
    refine ⟨r, hr, ?_, hcap⟩
    intro e
    have he : GradedLe (D.cell e.1) (D.cell c.1) := by grind
    exact (hread ⟨e.1, he⟩).trans (min_eq_left (hdom e))
  · refine ⟨fun d => min (q d) γ, hq.cap hγ, ?_, ?_⟩
    all_goals grind

end

end VaughtConjecture.Knight.CanonicalGradeOneLift
