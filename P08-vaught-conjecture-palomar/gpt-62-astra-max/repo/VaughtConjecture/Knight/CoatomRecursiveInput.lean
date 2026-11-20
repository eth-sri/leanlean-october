/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryPresentation
public import VaughtConjecture.Knight.OrdinaryRawScope

/-! # Initialized grade recursion from actual legal coatom inputs

The input schemes supply every proper-boundary hypothesis. The output is
consistent and bountiful at all nominal grades, and complete through the
coatom height. The missing highest full index and ordered stage-labelled
installation are separate obligations.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CoatomRecursiveInput
open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}

variable {m n : ℕ} (I : Input s m (n + 1) (n + 1))

def raw : OrdinaryRawScope.Ready I.rows where
  proper := I.toFaces.avoids (Finset.erase_ssubset s.ha) (Finset.erase_ssubset s.hb)
  consistent := I.consistent
  coded := I.coded
  lifts U V hu hv hV h := I.toFaces.liftWithin I.leftFace I.rightFace hu hv h
    (OrdinaryPlanScopeStep.coverage s V.1 (Plan.mem_gradedPlan.mp hv).1 hV)
  complete J hJ h := (I.occupied_iff hJ).mpr (OrdinaryPlanScopeStep.coverage s _ (Plan.mem_gradedPlan.mp hJ).1 h)

include I in
theorem card_eq : A.card = n + 2 := by
  have hh := I.toFaces.card_left
  rw [Finset.card_erase_of_mem s.ha] at hh
  omega

abbrev height_le : n + 1 ≤ A.card := (Nat.le_succ _).trans_eq (card_eq I).symm
abbrev core := OrdinaryRawScope.build I.rows (raw I) (n + 1) (Nat.succ_pos n) (card_eq I)
abbrev scheme := (core I).carrier
abbrev rows := (core I).rows

end
end VaughtConjecture.Knight.CoatomRecursiveInput
