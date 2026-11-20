/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.MixedGradeInterpolation

@[expose] public section

namespace VaughtConjecture.Knight.GradePrefixProjection

open Transform Value ExtOrd AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {ρ : Cell D → ExtOrd} {H : ℕ → ExtOrd}

/-- At an owner the projected locality target is exactly the target of its
lawful grade prefix; availability also stays within that single grade. -/
theorem respectsBelow (ha : Antitone H)
    (hp : ∀ j ≤ BJ.2, RespectsSemanticsBelow sem (BJ.1, j)
      (fun d => min (ρ d.1) (H j))) :
    RespectsSemanticsBelow sem BJ (fun d => min (ρ d.1) (H (D.grade d.1))) where
  orderly d := (hp (D.grade d.1) d.2.2).orderly ⟨d.1, d.2.1, le_rfl⟩
  locality c := by
    have ht := (hp (D.grade c.1) c.2.2).locality ⟨c.1, c.2.1, le_rfl⟩
    refine transformsTo_congr rfl rfl ?_ ht
    funext d
    change min (min (ρ d.1) (H (D.grade c.1))) (min (ρ c.1) (H (D.grade c.1))) =
      min (min (ρ d.1) (H (D.grade d.1))) (min (ρ c.1) (H (D.grade c.1)))
    have hdc : H (D.grade c.1) ≤ H (D.grade d.1) := ha d.2.2
    grind
  availability c e hs hg := by
    obtain ⟨w, hw, hle⟩ := (hp (D.grade c.1) c.2.2).availability
      ⟨c.1, c.2.1, le_rfl⟩ ⟨e.1, e.2.1, hg.symm.le⟩ hs hg
    refine ⟨⟨w.1, w.2.1, w.2.2.trans c.2.2⟩, hw, ?_⟩
    aesop

end VaughtConjecture.Knight.GradePrefixProjection
