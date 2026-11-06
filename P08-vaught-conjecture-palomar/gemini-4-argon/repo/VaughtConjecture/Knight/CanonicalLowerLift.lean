/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalGradeOneLift
public import VaughtConjecture.Knight.CanonicalLowerDomain

/-! # Grade-one lifting inside the actual canonical two-grade output -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalLowerLift
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The old graded-pair clause transports exactly to the grade cut, retaining
every old occurrence and its original cap. -/
theorem cut_lift {sem : Semantics D} {I U : Finset ι × ℕ} {j : ℕ}
    (h : GradedLe I U) (hU : U.2 ≤ j) (hlift : CappedLift sem h) :
    CappedLift (GradeCutBoundary.rows D j sem) h :=
  (CappedLift.iff_of_respects_iff (GradeCutBoundary.belowEquiv D j I (h.2.trans hU))
    (GradeCutBoundary.belowEquiv D j U hU) (fun _ => rfl)
    (GradeCutBoundary.respects_iff D j sem I (h.2.trans hU))
    (GradeCutBoundary.respects_iff D j sem U hU)).mpr hlift

variable (sem : Semantics D) (hA : 1 ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (h1k : 1 < k)

def oldLow (d : Cell D) (hd : D.grade d ≤ 1) :
    (scheme sem 1 (by decide) hA k hk hkA).below (A, 1) :=
  ⟨oldCell sem 1 (by decide) hA k hk hkA (lowerOld sem 1 (by decide) hA d), by
    simpa only [oldCell, lowerOld, CanonicalGradeCutSections.old,
      SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using
      (show GradedLe (D.cell d) (A, 1) from
        ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩)⟩


