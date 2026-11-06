module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import ValuedFieldTheory.Valuation.Topology.Models
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Coefficients for a complete DVR expansion

This file formalizes the recursive coefficient construction in the recursive coefficient proof.  Given a section of the residue map and a uniformizer `π`, every element
of the valuation ring has uniquely determined successive representative
coefficients and remainders satisfying

`u = a 0 + a 1 * π + ... + a (n - 1) * π ^ (n - 1) + π ^ n * b n`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField

/-- A normalized system of representatives for the residue field of a local
ring.  This common structure is used both for the original valuation ring and
for the valuation ring in its completion. -/
structure residueRepresentativeSystemOf
    (O : Type u) [CommRing O] [IsLocalRing O] where
  /-- The chosen representative of each residue class. -/
  repr : IsLocalRing.ResidueField O → O
  /-- Reducing a chosen representative recovers its residue class. -/
  residue_repr : ∀ a : IsLocalRing.ResidueField O,
    IsLocalRing.residue O (repr a) = a
  /-- The zero residue class is represented by zero. -/
  repr_zero : repr 0 = 0

namespace residueRepresentativeSystemOf
end residueRepresentativeSystemOf

/-- A system of representatives for the residue field of a complete DVF
valuation ring, encoded as a section of the residue map and normalized at
zero. -/
abbrev residueRepresentativeSystem
    {K : Type u} [Field K]
    (F : CompleteDVF.{u, v} K) :=
  residueRepresentativeSystemOf F.valuationSubring

namespace residueRepresentativeSystem
