/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DisplayFrame
public import VaughtConjecture.Knight.LowOnlyFamily

@[expose] public section
namespace VaughtConjecture.Knight.WholeDonorBoundary.Input
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m n K : ℕ} (I : Input A B C R m n n)

abbrev RootAgreement (F : LowOnly.Family I.left I.right K) :=
  ∀ i : Cell I.common.scheme, ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
    a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i

abbrev LowFrame (F : LowOnly.Family I.left I.right K) := DisplayFrame (I.RootAgreement F) A B C
end VaughtConjecture.Knight.WholeDonorBoundary.Input
