module
/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the original LICENSE.
Authors: Robby Sneiderman
Narrow right-half-plane series slice from McColm repository pin
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, vendor DigammaSeries.lean.
No PNT project modules are imported. See
../../../../../third_party/twelfth/DIGAMMA_PORT_MANIFEST.json and
../../../../../third_party/twelfth/DIGAMMA-LICENSE-APACHE-2.0.txt.
-/
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Tactic
public import WeylPort.Analytic.DigammaSeries

@[expose] public section

open Filter Topology Finset Nat Complex
noncomputable section
namespace MathCollab.Density.Stronger.Fourth.Digamma

/-! ## Elementary helper lemmas -/

export Complex (cauchySeq_logGammaSeq logGammaSeq_succ_sub norm_inv_add_one_sub_inv_le exp_logGammaSeq inv_add_one_sub_inv_eq norm_natCast_add_one summable_one_div_natCast_add_one_sq logGammaSeq sum_inv_natCast_add_one)

/-! ## The series on the right half-plane -/

export Complex (hasSum_digamma_of_re_pos)

end MathCollab.Density.Stronger.Fourth.Digamma
