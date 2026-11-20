/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability of the cutoff Wick and reference densities. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem measurable_secondMoment {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [SFinite P] {f : Ω × E → ℝ} (hf : Measurable f) :
    Measurable fun x => ∫ ω, f (ω,x) ^ 2 ∂P :=
  (((hf.comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right).measurable

/-- Wick density with the deterministic equator reference density omitted. -/
noncomputable def gmcCircleWickDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P))

theorem measurable_gmcCircleWickDensity_joint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ)
    (hm : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) :
    Measurable (fun p : Ω × ℂ => gmcCircleWickDensity P Xc γ r p.1 p.2) := by
  have hv := (measurable_secondMoment P hm).comp (measurable_snd : Measurable (Prod.snd : Ω × ℂ → ℂ))
  exact ((hm.const_mul γ).sub (hv.const_mul _)).exp.ennreal_ofReal

theorem measurable_regularizedGMC_density {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ)
    (hm : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) (ω : Ω) :
    Measurable (fun x : ℂ => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) * normPlus x ^ (-4 : ℝ))) := by
  simp_rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ((measurable_gmcCircleWickDensity_joint P Xc γ r hm).comp (measurable_const.prodMk measurable_id)).mul
    ((measurable_const.max measurable_norm).pow_const _).ennreal_ofReal

end DOZZ.Proofs
