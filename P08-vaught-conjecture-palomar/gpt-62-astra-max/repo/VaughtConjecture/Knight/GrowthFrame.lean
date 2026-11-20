/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DisplayFrame
public import VaughtConjecture.Knight.GrowthFilteredRoot

@[expose] public section
namespace VaughtConjecture.Knight.WholeDonorBoundary.Input
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m n J : ℕ} (I : Input A B C R m (n + 1) J)

abbrev GrowthData := RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows

abbrev Attachment (X : I.GrowthData) := Growth.RootAttachment I.common I.commonLeft I.visibleLeft
  I.faceLeft I.commonRight I.visibleRight I.faceRight X

abbrev GrowthFrame (X : I.GrowthData) := DisplayFrame (I.Attachment X) A B C
end VaughtConjecture.Knight.WholeDonorBoundary.Input
