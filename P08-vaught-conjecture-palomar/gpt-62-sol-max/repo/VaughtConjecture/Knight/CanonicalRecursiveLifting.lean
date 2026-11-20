/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.FullScopeBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveLifting

open Transform Value ExtOrd CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

open CanonicalRecursiveSuccessorRows

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, n + 3) J) (hb : CappedLift S.prev.rows h) :
    CappedLift (rows S) h := by
  let L := attachment S
  let P := SeparatedSourceLayerCarrier.patch (predecessor sem n hA) (Profile sem n) (n + 3)
    L.pos L.height L.separated
  apply P.lift (inherited_row S) h _ hb
  intro z hz
  obtain ⟨d, hd⟩ := L.old_occurrence (fun he => hJ (he ▸ hz))
  exact ⟨d, hd.symm⟩

theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ n + 2)
    (hb : CappedLift S.prev.rows h) : CappedLift (rows S) h :=
  inherited_lift S h (fun he => by have := he.2; omega) hb

end

end VaughtConjecture.Knight.CanonicalRecursiveLifting
