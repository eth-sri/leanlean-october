/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyOrderedLadder
public import VaughtConjecture.Knight.LowOnlyRecursiveCoverage
public import VaughtConjecture.Knight.PaddedInitial

public import VaughtConjecture.Knight.LowOnlyTerminal

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedContract

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder

open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

section Catalogue

variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def state {j : ℕ} (a : F.Anchor j) : State P C := State.ofProfile a.val

theorem state_admissible {j : ℕ} (a : F.Anchor j) : F.Admissible j (state F a) :=
  by
    obtain ⟨S, hS, he⟩ := a.property.2
    aesop

theorem state_profile {j : ℕ} (a : F.Anchor j) : (state F a).profile = F.fields j a :=
  State.profile_ofProfile a.val

theorem state_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    (state F a).profile d ≠ ⊤ := by
  rw [state_profile]
  exact LowOnlyRecursiveCharts.anchor_proper F a d

end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : I.RootMatches F.root)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev spec : Padded.Spec A where
  boundary := I.boundary
  boundaryRows := I.rows
  height := hA
  proper := proper I hB hC
  Field := Field I.left I.right
  State := State I.left I.right
  seed j hj := LowOnlyRecursiveCoverage.normalizedAnchor F hj le_rfl (F.zero_admissible j)
    (fun d => by rcases d with d | d | d <;> exact bot_ne_top)
  field := field I
  context := F.terminalContext
  anchorFinite j := inferInstanceAs (Fintype (F.Anchor j))
  state := state F
  state_admitted := state_admissible F
  state_profile_eq := state_profile F
  admitted_down hi hij hs := LowOnlyRecursiveCoverage.admissible_down F (hi.trans hij) hij hs
  profile_visible hj _ hs := LowOnlyRecursiveCharts.profile_visible_one F hj hs
  profile_lawful := LowOnlyOrderedLadder.boundary_lawful I F hroot

abbrev base := (spec I F hroot hA hB hC).base

abbrev Layer := Padded.Layer (spec I F hroot hA hB hC)

abbrev initial := Padded.Initial.layer (spec I F hroot hA hB hC) I.consistent

end

end VaughtConjecture.Knight.LowOnlyPaddedContract
