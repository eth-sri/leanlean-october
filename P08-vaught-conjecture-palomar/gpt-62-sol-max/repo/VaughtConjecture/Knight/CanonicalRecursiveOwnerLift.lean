/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
public import VaughtConjecture.Knight.CanonicalOwnerLift

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveOwnerLift

open Transform Value ExtOrd SharpWitnessComposition CoatomBoundaryExtension

open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

theorem exists_owner_capped_lift :
    CanonicalOwnerLift.Capped (cutRows sem n) (rows S) (oldTarget sem n hA) :=
  CanonicalOwnerLift.of_layer (data S) (occurrence n) (controllerEquiv sem n hA S.proper)
    (oldTarget sem n hA) (GradeCutBoundary.grade_bound D _)
    (fun d => congrArg Prod.snd (oldTarget_cell sem n hA d))
    (source_short S) (fun a d => source_boundary S a (occurrence n d))
    (fun a {_ _} hv ht hB hag => CanonicalRecursiveCutPrefix.exists_section S a hv ht hB hag)

end

end VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
