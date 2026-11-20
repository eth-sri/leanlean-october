/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

/-! # Admitting higher proper owners alongside a constructed lower layer

The small carrier adds full-scope grade-j controllers to the grade-j boundary
cut. The enlarged carrier retains the entire original boundary and the very
same controller inventory. Its lower domains through j are exactly the small
carrier's, while every proper old owner's lower domain is exactly the old one.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutLayerCarrier

open Transform Value ExtOrd
open SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)

abbrev small := scheme (GradeCutBoundary.scheme D j) Q j hj hA

abbrev ownerEquiv (hp : D.AvoidsScope A) (c : Cell D) :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q j hj hA
    (SeparatedSourceLayerCarrier.separated_of_proper D j hp) c

end
end VaughtConjecture.Knight.GradeCutLayerCarrier
