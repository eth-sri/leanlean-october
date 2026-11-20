module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
public import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Standard Lubin--Tate factors for finite local existence

The canonical standard Lubin--Tate level is already an intermediate field
of the fixed separable closure.  This module retains it as a named finite
abelian subextension, identifies its represented fixed field and norm
subgroup, and combines it with the canonical unramified factor.

Unlike the earlier transported Laurent-series construction, this source is
characteristic-independent.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

end LocalClassFieldTheory

end
