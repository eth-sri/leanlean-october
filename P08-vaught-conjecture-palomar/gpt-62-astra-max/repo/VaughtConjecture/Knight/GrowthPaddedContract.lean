/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthHigherSources
public import VaughtConjecture.Knight.PaddedTowerGeometry

/-! # The retained-padded growth row-and-rendering invariant

The base rows stay literal, including long grade-one tips and proper original
owners of arbitrary grade. Only higher full-scope rows are required short at
their own grade. This is an invariant of a constructed semantic layer, not a
lifting or bountifulness hypothesis. The contract and its constructed seed
follow the checked LOW renderer, instantiated here with growth admission.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedContract
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)

/-- Specialize the common installer to the Growth catalogue. -/
def system : PaddedTower.System I.boundary (Field I.right.scheme I.left.scheme) (Catalogue X) where
  sem := I.rows
  consistent := I.consistent
  positive := frame.positive
  proper := proper I frame.leftProper frame.rightProper
  field := field I
  values := fun {j} => fields X j
  canonical a := a.property.1
  visible _ := anchor_visible_one X
  lawful := anchor_lawful_at I X frame.attachment
  member := Growth.zeroMember X
  lower hj a := normalized X hj (Nat.le_succ _) (state X a) (state_admitted X a) (state_proper X a)
  restricts hj a := (normalized_fields X hj (Nat.le_succ _) (state X a) (state_admitted X a)
    (state_proper X a)).trans (congrArg _ (state_profile X a))

abbrev base := (system frame).base
abbrev baseRows := (system frame).baseRows
abbrev Layer := PaddedTower.Layer (system frame)

end
end VaughtConjecture.Knight.GrowthPaddedContract
