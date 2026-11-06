/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutBoundary
import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Exact lifting transport across an actual grade cut -/

namespace VaughtConjecture.Knight.GradeCutLifting
open    CoatomBoundaryExtension GradeCutBoundary
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ)

theorem lift_iff {I J} (h : GradedLe I J) (hJ : J.2 ≤ k) :
    CappedLift (rows D k sem) h ↔ CappedLift sem h := by
  let eI := belowEquiv D I (h.2.trans hJ)
  let eJ := belowEquiv D J hJ
  have hm (d : (scheme D k).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  have hi (d : D.below I) :
      eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
    grind
  constructor
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
      (pullback_respects (h.2.trans hJ) hp)
      (pullback_respects hJ hq) hγ (fun d => hag (eI d))
    refine ⟨r ∘ eJ.symm, (respects_iff sem J hJ r).mp hr, ?_, ?_⟩
    · simp_all
    · simp_all
  · intro hl p q γ hp hq hγ hag
    obtain ⟨r, hr, hc, hread⟩ := hl (p ∘ eI.symm) (q ∘ eJ.symm) γ
      ((respects_iff sem I (h.2.trans hJ) p).mp hp)
      ((respects_iff sem J hJ q).mp hq) hγ (fun d => by
        simp_all)
    refine ⟨r ∘ eJ, pullback_respects hJ hr, ?_, ?_⟩
    · simp_all
    · simp_all

