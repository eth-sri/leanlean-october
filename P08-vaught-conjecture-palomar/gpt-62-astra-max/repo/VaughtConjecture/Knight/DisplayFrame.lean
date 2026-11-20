/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary

/-! # Geometry of a two-sided display with its root attachment -/

@[expose] public section
namespace VaughtConjecture.Knight
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}

/-- Common input for a padded installation on two proper original faces. -/
structure DisplayFrame (Root : Sort*) (A B C : Finset ι) where
  attachment : Root
  height : 2 ≤ A.card
  leftProper : B ⊂ A
  rightProper : C ⊂ A

theorem DisplayFrame.positive {Root : Sort*} (fr : DisplayFrame Root A B C) : 0 < A.card :=
  lt_of_lt_of_le (by decide : 0 < 2) fr.height
theorem DisplayFrame.fullHeight {Root : Sort*} (fr : DisplayFrame Root A B C) : A.card - 2 + 2 = A.card :=
  Nat.sub_add_cancel fr.height
end VaughtConjecture.Knight
