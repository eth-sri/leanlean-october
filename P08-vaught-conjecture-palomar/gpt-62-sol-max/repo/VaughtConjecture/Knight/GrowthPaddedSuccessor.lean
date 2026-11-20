/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherSources
public import VaughtConjecture.Knight.PaddedInitial

public import VaughtConjecture.Knight.GrowthSupportedRepair

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedContract

open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources

open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev spec : Padded.Spec A where
  boundary := I.boundary
  boundaryRows := I.rows
  height := hA
  proper := proper I hB hC
  Field := Field I.right.scheme I.left.scheme
  State := State I.right.scheme I.left.scheme
  seed := Growth.zeroMember X
  field := field I
  context := Growth.terminalContext X
  anchorFinite j := inferInstanceAs (Fintype (Catalogue X j))
  state := state X
  state_admitted := state_admitted X
  state_profile_eq := state_profile X
  admitted_down _ hij hs := hs.down X hij
  profile_visible _ _ h := h.visible
  profile_lawful _ h := GrowthOrderedBase.boundary_lawful I X T h

abbrev base := (spec I X T hA hB hC).base

abbrev baseRows := (spec I X T hA hB hC).baseRows

abbrev Layer := Padded.Layer (spec I X T hA hB hC)

abbrev initial := Padded.Initial.layer (spec I X T hA hB hC) I.consistent

end

end VaughtConjecture.Knight.GrowthPaddedContract

namespace VaughtConjecture.Knight.GrowthPaddedSuccessor

open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources

open SourcePrefixRows PairedSlotComparison GrowthPaddedContract

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev input := Padded.Initial.input (spec I X T hA hB hC)

abbrev carrier := (input I X T hA hB hC).carrier

abbrev old := (input I X T hA hB hC).old

abbrev cell_cases := (input I X T hA hB hC).cell_cases

end

end VaughtConjecture.Knight.GrowthPaddedSuccessor
