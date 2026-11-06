/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CapReceivingPositive
import VaughtConjecture.Knight.NonHollowGrowthReceivingCore

/-! # Stable modelhood through cap receiving

The source is a model; the stable candidate is only known consistent and covering.
All-donor positive-root receiving supplies its cap requests. Empty roots are
completed by finite singleton attachment, then the four old model clauses follow.
This is the modelhood producer used by `NonHollowGrowthProlongation`; the
selected-family occurrence-package route remains a separate application.
-/

namespace VaughtConjecture.Knight.CapStableModel
open  StageType KnightRealization  ExtOrd
universe w
variable {M : Type w} {α : LimitStage} {W : KnightRealization α M}

theorem finiteCutReceiving (hM : W.IsModel) (hh : ¬ W.IsHollow)
    (hg : W.HasTopGradeGrowth) : FiniteCutReceiving (stableLift hM) := by
  apply FiniteCutReceiving.of_positive hM.nonempty
    (stableLiftOf_consistent hM.consistent hM.covering)
    (stableLiftOf_covering hM.consistent hM.covering)
  intro n hn t p hp q hqp δ hδ hδα
  obtain ⟨p₀, hp₀, rfl⟩ := stableLift_eval_eq_some hM hp
  obtain ⟨ν, rfl, hν⟩ : ∃ ν , δ = ofOrd ν ∧ ν < α.nextBlock.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    · exact False.elim (lt_irrefl _ hδ)
    · simp_all
    · simp_all
  obtain ⟨y, hy, s, hs, he, hproper, htop⟩ :=
    NonHollowGrowthReceiving.receives_positive hM hh hg hn t p₀ hp₀ q hqp ν hν
  refine ⟨y, hy, stableLiftType hM hs, stableLift_eval_some hM hs, he.symm, ?_⟩
  intro d
  change min (W.stableValue (snoc t y hy) s d) (ofOrd ν) =
    min (q.label (SemScheme.castCell he.symm d)) (ofOrd ν)
  by_cases hd : q.label (SemScheme.castCell he.symm d) = ⊤
  · have hh := htop (SemScheme.castCell he.symm d) hd
    rw [hd, ]
    exact min_eq_right hh.le
  · have hh := hproper (SemScheme.castCell he.symm d) hd
    exact congrArg (fun x => min x (ofOrd ν)) hh

/-- Alternative constructed stable modelhood, without assuming the stable candidate
is a model or using its occurrence package as an input. -/
def isModel (hM : W.IsModel) (hh : ¬ W.IsHollow) (hg : W.HasTopGradeGrowth) :=
  FiniteCutReceiving.isModel (finiteCutReceiving hM hh hg) hM.nonempty
    (stableLiftOf_consistent hM.consistent hM.covering)
    (stableLiftOf_covering hM.consistent hM.covering)

