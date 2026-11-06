module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: the absolute residue degree map

For a finite field `k`, arithmetic Frobenius identifies the absolute Galois
group of `k` with the profinite integers.  This file proves the missing
global statement from the compatible finite Frobenius coordinates:

* every positive integer occurs as the degree of an actual finite Galois
  intermediate field of `AlgebraicClosure k`;
* those fields detect every finite coordinate of `ℤ̂`, hence the assembled
  Frobenius map is injective;
* its compact image is all of the absolute Galois group;
* inversion gives the continuous degree map of the finite local reciprocity construction.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]

 instance finiteFieldRingCharPrime : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

 instance absoluteGaloisGroupT2 :
    T2Space (Field.absoluteGaloisGroup k) := by
  unfold Field.absoluteGaloisGroup
  exact krullTopology_t2
