module

public import Mathlib

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

section
variable (K : Type)
    [Field K] [NumberField K]
include K
/-- The concrete finite Galois norm neighbourhood used to realize the
big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldNormAmbient    :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The concrete finite Galois norm neighbourhood used to realize the
small Hilbert class field. -/
noncomputable abbrev smallHilbertClassFieldNormAmbient    :=
  closedFiniteIndexClassFieldNormAmbient
    (K := K)
    (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The compatible abstract base subgroup for the actual big Hilbert
class-field realization. -/
noncomputable abbrev bigHilbertClassFieldBaseSubgroup   :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))












/-- The compatible actual copy of the original number field occurring
as the base fixed field in the big-Hilbert realization. -/
noncomputable abbrev bigHilbertClassFieldBase    :=
  closedFiniteIndexClassFieldBase
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))
end










/-- The canonical equivalence from `K` to the actual base fixed field
used by the selected big Hilbert class field. -/
noncomputable abbrev bigHilbertClassFieldBaseEquiv  :=
  closedFiniteIndexClassFieldBaseEquiv
    (K := K) (bigHilbertClassFieldNormSubgroup (K := K))
    (bigHilbertClassFieldNormSubgroup_isClosed (K := K))

























































































section
variable (K : Type)
    [Field K] [NumberField K]
include K
/-- The compatible abstract base subgroup for the actual small Hilbert
class-field realization. -/
noncomputable abbrev smallHilbertClassFieldBaseSubgroup   :=
  closedFiniteIndexClassFieldBaseSubgroup
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))

/-- The finite abelian subextension selected by the small-Hilbert norm
subgroup.  This named witness is the input used by principalization. -/
noncomputable abbrev smallHilbertClassFieldSubextension    :=
  closedFiniteIndexClassFieldSubextension
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))









/-- The actual small Hilbert class field selected inside the rational
separable closure. -/
noncomputable abbrev smallHilbertClassField    :=
  closedFiniteIndexClassField
    (K := K) (smallHilbertClassFieldNormSubgroup (K := K))
    (smallHilbertClassFieldNormSubgroup_isClosed (K := K))
end

























































end GlobalClassFields
end GlobalClassFieldTheory

end
