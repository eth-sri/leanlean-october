module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.QuotientTransport
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationValue
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.EvaluationCore
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Construction
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.Evaluation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.BigHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassField
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/














set_option autoImplicit false

/-!
# Actual realizations of the Hilbert class fields

The big and small Hilbert norm subgroups are closed and have finite
index.  The finite-index class-field construction therefore supplies
genuine finite abelian subextensions of the rational separable closure.
This file fixes those subextensions once and for all, names their actual
relative fixed fields, and identifies their determinant-norm ranges.

The resulting degrees are the orders of the corresponding reciprocity
quotients: the narrow class number for the big Hilbert class field and
the ordinary class number for the small Hilbert class field.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open NumberField
open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- The big-Hilbert congruence subgroup has finite index, registered at
the realization layer where the closed finite-index construction uses it. -/
instance bigHilbertClassFieldNormSubgroupFiniteIndex :
    (bigHilbertClassFieldNormSubgroup (K := K)).FiniteIndex := by
  unfold bigHilbertClassFieldNormSubgroup
  infer_instance

/-- The concrete finite Galois norm neighbourhood used to realize the
big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldNormAmbient (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The concrete finite Galois norm neighbourhood used to realize the
small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldNormAmbient (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible abstract base subgroup for the actual big Hilbert
class-field realization. -/
noncomputable abbrev bigHilbertClassFieldBaseSubgroup (K : Type)
    [Field K] [NumberField K] :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The finite abelian subextension selected by the big-Hilbert norm
subgroup.  This is the actual class-field witness, rather than merely an
existence proposition. -/
noncomputable abbrev bigHilbertClassFieldSubextension (K : Type)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the big-Hilbert realization. -/
noncomputable abbrev bigHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The actual big Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev bigHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] bigHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The big-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def bigHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (bigHilbertClassFieldBase K)) :=
  (bigHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (bigHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

/-- The determinant-norm range of the actual big Hilbert class field is
exactly the transported big-Hilbert norm subgroup. -/
theorem bigHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (bigHilbertClassFieldBase K)
      (bigHilbertClassField K)).range =
      bigHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [bigHilbertClassFieldTransportedNormSubgroup,
    bigHilbertClassFieldBaseEquiv, bigHilbertClassField,
    bigHilbertClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
      (bigHilbertClassFieldNormSubgroup_isClosed (K := K)))





/-- The compatible abstract base subgroup for the actual small Hilbert
class-field realization. -/
noncomputable abbrev smallHilbertClassFieldBaseSubgroup (K : Type)
    [Field K] [NumberField K] :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The finite abelian subextension selected by the small-Hilbert norm
subgroup.  This named witness is the input used by principalization. -/
noncomputable abbrev smallHilbertClassFieldSubextension (K : Type)
    [Field K] [NumberField K] :
    FiniteAbelianSubextension
      (smallHilbertClassFieldBaseSubgroup K) :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible actual copy of the original number field occurring
as the base fixed field in the small-Hilbert realization. -/
noncomputable abbrev smallHilbertClassFieldBase (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassFieldBase
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The actual small Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev smallHilbertClassField (K : Type)
    [Field K] [NumberField K] : Type :=
  closedFiniteIndexClassField
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldBaseEquiv :
    K ≃ₐ[ℚ] smallHilbertClassFieldBase K :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The small-Hilbert norm subgroup transported to the actual base fixed
field of the selected realization. -/
def smallHilbertClassFieldTransportedNormSubgroup :
    Subgroup (IdeleClassGroup (smallHilbertClassFieldBase K)) :=
  (smallHilbertClassFieldNormSubgroup (K := K)).map
    (ideleClassCongr
      (smallHilbertClassFieldBaseEquiv (K := K))).toMonoidHom

/-- The determinant-norm range of the actual small Hilbert class field
is exactly the transported small-Hilbert norm subgroup. -/
theorem smallHilbertClassField_ideleClassNorm_range :
    (_root_.ideleClassNorm
      (smallHilbertClassFieldBase K)
      (smallHilbertClassField K)).range =
      smallHilbertClassFieldTransportedNormSubgroup (K := K) := by
  simpa only [smallHilbertClassFieldTransportedNormSubgroup,
    smallHilbertClassFieldBaseEquiv, smallHilbertClassField,
    smallHilbertClassFieldBase] using
    (closedFiniteIndexClassField_ideleClassNorm_range_over_base
      (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
      (smallHilbertClassFieldNormSubgroup_isClosed (K := K)))



end GlobalClassFields
end GlobalClassFieldTheory

end
