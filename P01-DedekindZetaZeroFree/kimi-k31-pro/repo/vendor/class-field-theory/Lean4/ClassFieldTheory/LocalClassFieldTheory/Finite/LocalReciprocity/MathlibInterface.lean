module

public import ClassFieldTheory.Definitions.LocalClassFieldTheory.All
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.Classification
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConjugationNaturality
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization
public import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteLocalReciprocity

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# Mathlib-facing finite local class field theory

This is the implementation layer for the reader-facing local CFT module.
It collects the existing finite, absolute, naturality, normalization, and
existence results without renaming them or wrapping them in an existence
structure.
-/

noncomputable section

namespace ClassFieldTheory.LocalCFT

open ClassFormation

noncomputable local instance localNormQuotientTopologicalSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (LocalFieldTheory.NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ LocalFieldTheory.localNormSubgroup K L)
  infer_instance

noncomputable local instance fieldNormQuotientTopologicalSpace
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [TopologicalSpace K] :
    TopologicalSpace (FieldNormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ fieldNormSubgroup K L)
  infer_instance















end ClassFieldTheory.LocalCFT

end
