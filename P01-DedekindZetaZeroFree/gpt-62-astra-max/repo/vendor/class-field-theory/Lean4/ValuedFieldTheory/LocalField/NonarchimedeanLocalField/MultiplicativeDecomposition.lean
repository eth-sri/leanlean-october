module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Topological decomposition of a local multiplicative group

This file packages the normalized valuation and the unit factor in the standard
decomposition of `Kˣ` as continuous homomorphisms. After fixing a
noncanonical uniformizer internally, the resulting parameter-free map lets
downstream separation arguments avoid carrying a uniformizer parameter.
-/

noncomputable section

universe u

namespace LocalFieldTheory.IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

end LocalFieldTheory.IsNonarchimedeanLocalField

end
