/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.StructureIsoSetoid
public import InfinitaryLogic.Descriptive.Polish
public import Mathlib.Logic.Small.Basic
public import InfinitaryLogic.Descriptive.SatisfactionBorel
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import InfinitaryLogic.Lomega1omega.Operations
public import Mathlib.Data.Set.Countable
public import InfinitaryLogic.Lomega1omega.Semantics
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.ModelTheory.Encoding
public import InfinitaryLogic.Lomega1omega.Theory
public import Mathlib.SetTheory.Ordinal.Family
public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
public import Mathlib.Order.Zorn
public import Mathlib.Data.Fintype.Quotient
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.Order.InitialSeg
public import InfinitaryLogic.Descriptive.StructureSpace
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.ModelTheory.Substructures
public import Mathlib.GroupTheory.Perm.Basic
public import Architect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

universe u v w x y

namespace FirstOrder.Language.SmallVocabulary

open MeasureTheory Set

variable (L : Language.{u, v}) [L.IsRelational] [Countable (Σ n, L.Relations n)]

omit [Countable (Σ n, L.Relations n)] in
/-- Membership in `ModelsOf` is realization of the sentence in the decoded structure (the empty
valuation is unique).  A restatement, with `L` explicit, of the root
`FirstOrder.Language.mem_modelsOf_iff_realize` (`Descriptive/SatisfactionBorel.lean`). -/
theorem mem_modelsOf_iff_realize (c : StructureSpace L) (φ : L.Sentenceω) :
    c ∈ ModelsOf φ ↔ @Sentenceω.Realize L φ ℕ c.toStructure :=
  FirstOrder.Language.mem_modelsOf_iff_realize c φ

end FirstOrder.Language.SmallVocabulary
