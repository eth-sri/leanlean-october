module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Main
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Absolute data for finite local existence

This file isolates the common abstract Galois-theoretic realization of the absolute Galois
group, its unit representation, and the ground-field fixing subgroup.  Both
the characteristic-zero and equal-characteristic existence arguments use
these definitions.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

/-- An open finite-index subgroup of the ordinary topological group `Kˣ`.

This is a genuine public object rather than a transparent subtype alias: its
topological and finite-index contracts remain available without exposing a
particular nested-pair representation. -/
structure OpenFiniteIndexSubgroup
    (K : Type) [Field K] [TopologicalSpace K] where
  /-- The underlying subgroup of field units. -/
  subgroup : Subgroup Kˣ
  /-- The underlying subgroup is open in the unit-group topology. -/
  isOpen : IsOpen (subgroup : Set Kˣ)
  /-- The underlying subgroup has finite index. -/
  finiteIndex : subgroup.FiniteIndex

namespace OpenFiniteIndexSubgroup

variable {K : Type} [Field K] [TopologicalSpace K]

/-- Provides this instance. -/
instance : Coe (OpenFiniteIndexSubgroup K) (Subgroup Kˣ) :=
  ⟨OpenFiniteIndexSubgroup.subgroup⟩

end OpenFiniteIndexSubgroup

variable (K : Type) [Field K]

/-- The closed fixing group of the ground field is absolutely finite in the
abstract Galois-theoretic sense (indeed, it is the full absolute Galois group). -/
instance intrinsicAbstractBase_index_finite :
    Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
      extensionSubgroup (baseField (intrinsicAbsoluteGalois K))
        (intrinsicAbstractBase K) (le_baseField (intrinsicAbstractBase K))) := 
  (intrinsicFiniteAbstractBase K).finite
