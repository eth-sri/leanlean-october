module

public import ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteAbelianization
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Compatibility names for the absolute abelianization

The field-generic construction is owned by
`AlgebraicNumberTheory.Galois.AbsoluteAbelianization`.  This module preserves
the established local names as definitional wrappers for downstream users.
-/

noncomputable section

namespace LocalClassFieldTheory

variable (K : Type) [Field K]















































/-- Compatibility instance for total disconnectedness. -/
instance localAbsoluteTopologicalAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (TopologicalAbelianization (intrinsicAbsoluteGalois K)) :=
  absoluteTopologicalAbelianization_totallyDisconnectedSpace K






end LocalClassFieldTheory

end
