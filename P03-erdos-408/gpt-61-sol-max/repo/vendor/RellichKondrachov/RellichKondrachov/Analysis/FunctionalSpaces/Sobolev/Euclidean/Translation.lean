/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

module
public import Mathlib.Tactic

public import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

@[expose] public section

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory





variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩

local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F } [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq  {F}  [NormedAddCommGroup F] [NormedSpace ℝ F]  a 
     g  :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := MeasureTheory.Lp.coeFn_compMeasurePreserving g (MeasureTheory.measurePreserving_add_right μ a)

variable [IsFiniteMeasureOnCompacts μ]



end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
