module

public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldRealization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldComparison
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.AbstractClassFieldTheory.Degree.NormConjugation
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldCandidate
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
 def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup
