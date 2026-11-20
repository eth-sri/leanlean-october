/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyOrderedSources
public import VaughtConjecture.Knight.LowOnlyGradeOneSupply
public import VaughtConjecture.Knight.PaddedTowerGeometry

/-! # The retained-padded LOW row-and-rendering invariant

The base rows stay literal, including long grade-one tips and proper original
owners of arbitrary grade. Only higher full-scope rows are required short at
their own grade. This is an invariant of a constructed semantic layer, not a
lifting or bountifulness hypothesis.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedContract
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

section Catalogue
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def state {j} (a : F.Anchor j) : State P C := State.ofProfile a.val
theorem state_admissible {j} (a : F.Anchor j) : F.Admissible j (state F a) :=
  by
    obtain ⟨S, hS, he⟩ := a.property.2
    have hs : state F a = S := State.profile_injective
      ((State.profile_ofProfile a.val).trans he.symm)
    exact hs.symm ▸ hS
theorem state_profile {j} a : (state F a).profile = F.fields j a :=
  State.profile_ofProfile a.val
theorem state_proper {j} (a : F.Anchor j) d :
    (state F a).profile d ≠ ⊤ := by
  rw [state_profile]
  exact LowOnlyRecursiveCharts.anchor_proper F a d
end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)

/-- Specialize the common installer to the LowOnly catalogue. -/
def system : PaddedTower.System I.boundary (Field I.left I.right) (F.Anchor) where
  sem := I.rows
  consistent := I.consistent
  positive := frame.positive
  proper := proper I frame.leftProper frame.rightProper
  field := field I
  values := fun {j} => F.fields j
  canonical a := a.property.1
  visible := fun hj => LowOnlyRecursiveCharts.anchor_visible_one F hj
  lawful := fun {j} => LowOnlyOrderedSources.anchor_lawful I F frame.attachment j
  member j hj := (F.exists_rank_anchor hj (F.zero_admissible j)).choose
  lower hj a := LowOnlyRecursiveCoverage.normalizedAnchor F hj (Nat.le_succ _)
    (state_admissible F a) (state_proper F a)
  restricts hj a := (LowOnlyRecursiveCoverage.normalizedAnchor_fields F hj (Nat.le_succ _)
    (state_admissible F a) (state_proper F a)).trans (congrArg _ (state_profile F a))

abbrev base := (system frame).base
abbrev baseRows := (system frame).baseRows
abbrev Layer := PaddedTower.Layer (system frame)

end
end VaughtConjecture.Knight.LowOnlyPaddedContract
