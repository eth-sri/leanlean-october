/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.OuterInverseGuard
public import DOZZ.Statements.GMC.EquatorGFFRootedGMCIdentity
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic

/-! # The zero kernel with an independent retained radius -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The literal dual mass at zero, retaining points outside a supplied radius. -/
noncomputable def dualRetainedZeroMass (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ) : ℝ≥0∞ :=
  coulombMass γ (μ.restrict {x : ℂ | r ≤ ‖x‖}) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃

/-- The retained zero mass is a measurable functional of the supplied measure. -/
theorem dual_retainedZero_measure_measurable (γ α₁ α₂ α₃ r : ℝ) :
    Measurable (dualRetainedZeroMass γ α₁ α₂ α₃ r) := by
  have hD : MeasurableSet {x : ℂ | r ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hf := (measurable_coulombWeight γ ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃).indicator hD
  convert Measure.measurable_lintegral hf using 1
  funext μ
  rw [lintegral_indicator hD]
  rfl

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)

include Ω _inst1 P X hX γ hγ hγ₂ M hM in
/-- Rooting the deleted spatial weight keeps the same literal retained mass. -/
theorem dual_retainedZero_rooted_identity 
    (α₁ α₂ α₃ r q : ℝ) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ u, f u * (dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω)) ^ (-q)
      ∂M ω ∂P) =
    ∫⁻ u, ∫⁻ ω, f u *
      (dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω))) ^ (-q)
        ∂P ∂gmcReferenceMeasure := by
  apply DOZZ.equatorGFF_rooted_GMC_identity P X hX γ hγ hγ₂ M hM
    (fun u _ μ => f u * (dualRetainedZeroMass γ α₁ α₂ α₃ r μ) ^ (-q))
  exact (hf.comp measurable_fst).mul
    (((dual_retainedZero_measure_measurable γ α₁ α₂ α₃ r).comp
      (measurable_snd.comp measurable_snd)).pow_const (-q))

/-- A fixed disk is retained at every radius at most one. -/
theorem dual_retainedZero_fixed_disk_lower (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (hr : r ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
      (4 : ℝ) ^ (-|γ * α₃|)) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      dualRetainedZeroMass γ α₁ α₂ α₃ r μ := by
  exact coulombMass_restrict_norm_fixed_disk_lower γ μ ![-2 / γ, α₁, α₂] ![0, 0, 1]
    α₃ r hr (by simp [Fin.forall_fin_succ])

include Ω _inst1 P X hX γ hγ hγ₂ M hM in
/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem dual_retainedZero_inverse_moment_uniform
    
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, r ≤ 1 →
      (∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω) ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  let w : ℝ := (2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|)
  obtain ⟨C, hC, hb⟩ := gmc_inverse_moment_uniform_of_disk_lower
    P X hX γ hγ hγ₂ M hM q w hq (by dsimp only [w]; positivity)
  refine ⟨C, hC, ?_⟩
  intro r hr
  exact hb _ fun ω => dual_retainedZero_fixed_disk_lower γ α₁ α₂ α₃ r (M ω) hr

end DOZZ.Proofs
