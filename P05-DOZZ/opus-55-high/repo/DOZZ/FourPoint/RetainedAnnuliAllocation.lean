/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliJoint
public import DOZZ.Statements.FourPoint.FreezingAnnulusMassLocal

/-! Allocation of negative moment orders to positive retained lower masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- An extended positive mass can allocate its negative order among two lower masses. -/
theorem negative_order_allocation (I A B : ℝ≥0∞) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : A ≤ I) (hB : B ≤ I) :
    I ^ (-(a + b)) ≤ A ^ (-a) * B ^ (-b) := by
  have hanti (J : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (hJ : J ≤ I) :
      I ^ (-c) ≤ J ^ (-c) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    gcongr
  have he : I ^ (-(a + b)) = I ^ (-a) * I ^ (-b) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_add_of_nonneg a b ha hb,
      ENNReal.mul_inv, ← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
    · by_cases hI : I = 0
      · simp_all
      simp_all
    · by_cases hI : I = 0
      · simp_all
      simp_all
  rw [he]
  bound

/-- Pulling deterministic lower kernel bounds through a joint inverse-moment estimate. -/
theorem retained_moment_allocation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I A B : Ω → ℝ≥0∞) (hAfinite : ∀ ω, A ω ≠ ⊤) (hBfinite : ∀ ω, B ω ≠ ⊤)
    (wA wB a b : ℝ) (hwA : 0 < wA) (hwB : 0 < wB) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ ω, ENNReal.ofReal wA * A ω ≤ I ω)
    (hB : ∀ ω, ENNReal.ofReal wB * B ω ≤ I ω) :
    (∫⁻ ω, I ω ^ (-(a + b)) ∂P) ≤ ENNReal.ofReal (wA ^ (-a) * wB ^ (-b)) *
      ∫⁻ ω, A ω ^ (-a) * B ω ^ (-b) ∂P := by
  have hpoint (ω : Ω) : I ω ^ (-(a + b)) ≤
      ENNReal.ofReal (wA ^ (-a) * wB ^ (-b)) * (A ω ^ (-a) * B ω ^ (-b)) := by
    have hh := negative_order_allocation (I ω)
      (ENNReal.ofReal wA * A ω) _ a b ha hb (hA ω) (hB ω)
    rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hAfinite ω),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hBfinite ω),
      ENNReal.ofReal_rpow_of_pos hwA, ENNReal.ofReal_rpow_of_pos hwB] at hh
    convert hh using 1
    rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hwA _).le]
    ac_rfl
  exact (lintegral_mono hpoint).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

/-- A weighted integral over an annulus dominates any retained disk on which the kernel
has a positive lower bound. No finiteness of the weighted mass is required. -/
theorem freezing_retained_lower_bound (γ α ε R w : ℝ) (M : Measure ℂ)
    (z u : ℂ) (ρ : ℝ)
    (hsub : Metric.ball u ρ ⊆ {x | ε < ‖x - z‖ ∧ ‖x - z‖ < R})
    (hw : ∀ x ∈ Metric.ball u ρ, w ≤ ‖x - z‖ ^ (-(γ * α))) :
    ENNReal.ofReal w * M (Metric.ball u ρ) ≤ freezingAnnulusMassLocal γ α M z ε R := by
  calc
    ENNReal.ofReal w * M _ =
        ∫⁻ x in Metric.ball u ρ, ENNReal.ofReal w ∂M := by simp
    _ ≤ ∫⁻ x in Metric.ball u ρ, ENNReal.ofReal _ ∂M := by
      apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
      bound
    _ ≤ freezingAnnulusMassLocal γ α M z ε R := lintegral_mono_set hsub

end DOZZ.Proofs
