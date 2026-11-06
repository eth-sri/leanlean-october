module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace RamificationTheory

/-!
# Hilbert ramification theory: valuation-subring layer

This file manages the ordinary valuation-subring decomposition/inertia exact
sequence.  For an arbitrary valuation subring the residue action need not be
onto the full residue automorphism group; the canonical theorem is the exact
sequence with target equal to the range of the residue action.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- finite Galois ramification theory:
the decomposition group of a valuation subring. -/
abbrev decompositionGroup (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group. -/
abbrev decompositionField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)

/-- The fixed-field description of decomposition source:
`L/Z_w` is Galois because `Z_w` is the fixed field of the finite
decomposition group action. -/
instance decompositionField_isGalois
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IsGalois (decompositionField K A) L :=
  IsGalois.of_fixed_field L (decompositionGroup K A)

section IntermediateFieldFunctoriality

variable {M : Type*} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- Restrict scalars on automorphisms along an intermediate field
`K ⊆ M ⊆ L`.  This is the inclusion `G(L/M) -> G(L/K)` used in
scalar-restriction compatibility of ramification subgroups. -/
def restrictAutomorphismScalars : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L) where
  toFun σ :=
    { σ with
      commutes' := by
        intro a
        simp [IsScalarTower.algebraMap_eq K M L, σ.commutes (algebraMap K M a)] }
  map_one' := by
    rfl
  map_mul' σ τ := by
    rfl
