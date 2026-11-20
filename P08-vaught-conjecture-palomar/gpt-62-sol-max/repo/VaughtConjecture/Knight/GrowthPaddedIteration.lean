/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor
public import VaughtConjecture.Knight.PaddedIteration
public import VaughtConjecture.Knight.PaddedInstallation

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedIteration

open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources

open GrowthPaddedContract

open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n J : ℕ} {I : WholeDonorBoundary.Input A B C R m (n + 1) J} {X : I.GrowthData} {attach : I.GrowthAttachment X} {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}

export Padded (successor)

variable (I X attach hA hB hC)

abbrev build := Padded.build (initial I X attach hA hB hC)

theorem build_plan (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I X attach hA hB hC t ht).carrier.plan = I.boundary.plan :=
  Padded.build_plan _ rfl t ht

end

end VaughtConjecture.Knight.GrowthPaddedIteration

namespace VaughtConjecture.Knight.GrowthPaddedIteration

/-- Fix the input, attachment and installed height for the replicated tower.
Every scope of that tower then uses the same original rows and coordinates. -/
structure BuildContext {ι : Type*} [DecidableEq ι] (A B C : Finset ι)
    (R : Finset (Finset ι)) (m n J : ℕ) where
  I : WholeDonorBoundary.Input A B C R m (n + 1) J
  X : I.GrowthData
  attach : I.GrowthAttachment X
  height : 2 ≤ A.card
  leftProper : B ⊂ A
  rightProper : C ⊂ A
  depth : ℕ
  fits : depth + 2 ≤ A.card

namespace BuildContext

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}

noncomputable abbrev tower (G : BuildContext A B C R m n J) :=
  build G.I G.X G.attach G.height G.leftProper G.rightProper G.depth G.fits

theorem pos (G : BuildContext A B C R m n J) : 0 < A.card := by
  have := G.height
  omega

/-- Keep the input and attachment and change only the installed depth. -/
def atDepth (G : BuildContext A B C R m n J) (t : ℕ) (ht : t + 2 ≤ A.card) :
    BuildContext A B C R m n J := { G with depth := t, fits := ht }

abbrev earlier (G : BuildContext A B C R m n J) {t : ℕ} (ht : t ≤ G.depth) :=
  G.atDepth t ((Nat.add_le_add_right ht 2).trans G.fits)

noncomputable def donorFace (G : BuildContext A B C R m n J) :
    ExactSemanticFace G.I.leftRows G.tower.rows := G.tower.face G.I.leftFace G.leftProper.not_ge

noncomputable def privateFace (G : BuildContext A B C R m n J) :
    ExactSemanticFace G.I.rightRows G.tower.rows := G.tower.face G.I.rightFace G.rightProper.not_ge

def full (I : WholeDonorBoundary.Input A B C R m (n + 1) J) (X : I.GrowthData)
    (T : I.GrowthAttachment X) (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A) :
    BuildContext A B C R m n J :=
  ⟨I, X, T, hA, hB, hC, A.card - 2, by omega⟩

end BuildContext

end VaughtConjecture.Knight.GrowthPaddedIteration
