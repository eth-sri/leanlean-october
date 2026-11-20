/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
public import VaughtConjecture.Knight.ExactSemanticFace

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveFace

open Transform Value ExtOrd CanonicalRecursiveContract

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B : Finset ι}

variable {D : CellScheme A} {E : CellScheme B}

variable {sem : Semantics D} {old : Semantics E}

variable (F : ExactSemanticFace old sem) (hB : ¬ A ⊆ B)

variable (hp : ∀ d : Cell D, D.scope d ≠ A) (n : ℕ) (hA : n + 3 ≤ A.card)

def face : ExactSemanticFace old (CanonicalRecursiveSemantics.rows sem hp n hA) :=
  F.through (boundary sem n hA).toEmbedding (CanonicalRecursiveInventory.boundary_cell sem (n + 3) hA)
    (fun z hz => CanonicalRecursiveInventory.proper_occurrence sem (n + 3) hA z (fun h => hB (h.trans hz)))
    (CanonicalRecursiveBoundaryTransport.row sem hp n hA)

end

end VaughtConjecture.Knight.CanonicalRecursiveFace
