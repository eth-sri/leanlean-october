
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveSemantics
import VaughtConjecture.Knight.FullScopeBountiful

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveLifting
open    CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : AvoidsValue D.scope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
open CanonicalRecursiveSuccessorRows CanonicalRecursiveSuccessorSections

local notation "GradedLe₀" => GradedLe (A, n + 4)

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem inherited_lift {I J} (h : GradedLe I J)
    (hJ : ¬ GradedLe₀ J) (hb : CappedLift P.rows h) :
    CappedLift (rows sem n hA hp P) h := by
  intro p q γ hpr hqr hγ hag
  have hI : ¬ GradedLe₀ I := fun hi => hJ (hi.trans h)
  let eI := equiv sem n hA I hI
  let eJ := equiv sem n hA J hJ
  have pull (B : GradedIndex ι) (hB : ¬ GradedLe₀ B)
      (u : (carrier sem n hA).below B → ExtOrd)
      (hu : RespectsSemanticsBelow (rows sem n hA hp P) B u) :
      RespectsSemanticsBelow P.rows B (u ∘ equiv sem n hA B hB) := by
    apply (respects_iff sem n hA hp P B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hu
  have hm (d : (predecessor sem n hA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hb (p ∘ eI) (q ∘ eJ) γ
    (pull I hI p hpr) (pull J hJ q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem n hA hp P J hJ r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simp_all
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      grind
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

def lower_lift {I J} (h : GradedLe I J) (hJ : J.2 ≤ n + 3)
    (hb : CappedLift P.rows h) :=
  inherited_lift sem n hA hp P h (fun he => by have := he.2; omega) hb


