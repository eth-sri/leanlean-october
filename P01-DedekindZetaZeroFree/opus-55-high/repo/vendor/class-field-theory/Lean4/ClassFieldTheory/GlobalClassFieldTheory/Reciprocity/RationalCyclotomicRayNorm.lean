module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlaceArtin
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Rational cyclotomic ray norm groups

For a positive integer `m`, the genuine idèle-class norm range of the
actual cyclotomic level `ℚ(μ_m)` is the rational ray congruence subgroup
modulo `(m)`.

The local input is the cyclotomic higher-unit calculation: at a rational prime
`q`, an
`m.factorization q`-th higher unit has trivial Artin action on every
prime-power cyclotomic part.  On the `q`-primary part this is the actual
multiplicative Lubin--Tate norm theorem; on every other primary part it is
the unramified Artin formula together with valuation zero.  The finite
cyclotomic character then detects that the full local Artin symbol is
trivial.
-/

open scoped Classical NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open LubinTate

local instance (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

attribute [local instance]
  rationalCyclotomicPrincipalPrimeLevelFiniteDimensional
  rationalCyclotomicPrincipalPrimeLevelIsAbelianGalois

section FinitePlaceLocalCalculation

attribute [local instance]
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValued
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField

section PrimePowerCalculation

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional
