
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.WholeDonorBoundary
import VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
import VaughtConjecture.Knight.OrbitSupportSubstitution

/-! # Ordinary selected sections over two literal input faces

This is the first scope step for new31, independent of LOW/HIGH catalogues.
The original schemes supply consistency and lawful input sections. The ordinary
grade recursion constructs the output rows and all selected-section receipts.
One fixed external grid and ceiling are used, and support is stated over the two
original occurrence vectors, not over unidentified intermediate coordinates.

This module does not fill missing proper mixed scopes. Inherited-target lifting
is transported, but full mixed-target lifting still needs the scope induction.
-/

namespace VaughtConjecture.Knight.WholeDonorOrdinarySections
open     SourcePrefixRows 

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

theorem covered d :
    (∃ c, I.leftFace.map c = d) ∨ ∃ c, I.rightFace.map c = d :=
  OrderedFaceBoundaryRows.covered d

theorem paste_bound {p} {q}
    {θ} (hp : BoundedBy p θ) (hq : BoundedBy q θ)
    (hroot : ∀ i, p (I.shared.f i) = q (I.shared.g i)) :
    ∀ d, I.paste p q d ≤ θ := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (I.paste_left p q c) ▸ hp c
  · exact (I.paste_right p q hroot c) ▸ hq c

theorem paste_agreement {p p'}
    {q q'} {h}
    (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
    (hr' : ∀ i, p' (I.shared.f i) = q' (I.shared.g i))
    (hp : Agree p p' h) (hq : Agree q q' h) : Agree (I.paste p q) (I.paste p' q') h := by
  intro d
  rcases covered I d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact (congrArg (fun v => min v h) (I.paste_left p q c)).trans
      ((hp c).trans (congrArg (fun v => min v h) (I.paste_left p' q' c)).symm)
  · exact (congrArg (fun v => min v h) (I.paste_right p q hr c)).trans
      ((hq c).trans (congrArg (fun v => min v h) (I.paste_right p' q' hr' c)).symm)

variable {p : CellLabels I.left.scheme} {q : CellLabels I.right.scheme}
variable (hp : RespectsSemantics I.left.rows p) (hq : RespectsSemantics I.right.rows q)
variable (hr : ∀ i, p (I.shared.f i) = q (I.shared.g i))
variable  {θ : ExtOrd}

