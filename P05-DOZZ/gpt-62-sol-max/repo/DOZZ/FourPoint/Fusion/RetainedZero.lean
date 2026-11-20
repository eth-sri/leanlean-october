/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RetainedInverseMass
public import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
public import DOZZ.GMC.Annulus.BallCover
import DOZZ.FourPoint.Reflected.MassFiniteness
import Mathlib.Tactic

/-! The Coulomb mass at coincident zero insertions, with an independent spatial cutoff. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The coincident mass with charge `β` at the extra root, retaining the exterior of the ball. -/
noncomputable def retainedZeroMass (γ β α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ) : ℝ≥0∞ :=
  coulombMass γ (μ.restrict {x : ℂ | r ≤ ‖x‖}) ![β, α₁, α₂] ![0, 0, 1] α₃

theorem retainedZeroMass_measurable (γ β α₁ α₂ α₃ r : ℝ) :
    Measurable (retainedZeroMass γ β α₁ α₂ α₃ r) :=
  coulombMass_restrict_measurable γ ![β, α₁, α₂] ![0, 0, 1] α₃
    (isClosed_le continuous_const continuous_norm).measurableSet

private theorem retainedZeroMass_fixed_disk_lower (γ β α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (hr : r ≤ 1) :
    ENNReal.ofReal (outerGuardWeight γ β α₁ α₂ α₃) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      retainedZeroMass γ β α₁ α₂ α₃ r μ :=
  coulombMass_fixed_disk_lower_restrict γ μ _ _ _ (three_roots_in_unit_disk (by simp))
    (fixed_disk_subset_exterior hr)

/-- Uniform inverse moments, since the same disk is retained for every radius at most one. -/
theorem retainedZeroMass_inverse_moment_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (β α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, r ≤ 1 →
      (∫⁻ ω, retainedZeroMass γ β α₁ α₂ α₃ r (M ω) ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ₂ M hM _ q
    (outerGuardWeight_pos γ β α₁ α₂ α₃) hq
  exact ⟨C, hC, fun r hr => h _ fun ω => retainedZeroMass_fixed_disk_lower γ β α₁ α₂ α₃ r (M ω) hr⟩

/-- Restricting an atomless-at-the-roots mass preserves its kernel representation. -/
theorem retainedZeroMass_eq_setLIntegral (γ β α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) (K : ℂ → ℝ≥0∞)
    (hK : ∀ ν : Measure ℂ, ν {0} = 0 → ν {1} = 0 →
      coulombMass γ ν ![β, α₁, α₂] ![0, 0, 1] α₃ = ∫⁻ x, K x ∂ν) :
    retainedZeroMass γ β α₁ α₂ α₃ r μ = ∫⁻ x in {x : ℂ | r ≤ ‖x‖}, K x ∂μ := by
  let D : Set ℂ := {x | r ≤ ‖x‖}
  have hnull (x : ℂ) (hx : μ {x} = 0) : (μ.restrict D) {x} = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_le_self (s := D) {x}).trans_eq hx)
  exact hK (μ.restrict D) (hnull 0 h0) (hnull 1 h1)

/-- The complement of the retained exterior is exactly the deleted open disk. -/
theorem lintegral_exterior_add_ball (r : ℝ) (K : ℂ → ℝ≥0∞) (μ : Measure ℂ) :
    (∫⁻ x in {x : ℂ | r ≤ ‖x‖}, K x ∂μ) + (∫⁻ x in Metric.ball 0 r, K x ∂μ) =
      ∫⁻ x, K x ∂μ := by
  have hc : ({x : ℂ | r ≤ ‖x‖} : Set ℂ)ᶜ = Metric.ball 0 r := by
    ext x
    simp [Metric.mem_ball]
  rw [← hc, lintegral_add_compl _ (isClosed_le continuous_const continuous_norm).measurableSet]

/-- A positive retained mass and a finite full mass, on the Seiberg domain of the fused charge. -/
theorem retainedZeroMass_ae_positive_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (β α₁ α₂ α₃ r : ℝ) (hr : r ≤ 1)
    (hα₁ : α₁ + β < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, 0 < retainedZeroMass γ β α₁ α₂ α₃ r (M ω) ∧
      coulombMass γ (M ω) ![β, α₁, α₂] ![0, 0, 1] α₃ < ⊤ := by
  filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ₂ M hM 3 (1 / 8) (by norm_num),
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ₂ M hM 1,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ + β) α₂ α₃ hα₁ hα₂ hα₃]
      with ω hb h0 h1 hf
  refine ⟨(ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (outerGuardWeight_pos ..)).ne' hb.ne').trans_le
    (retainedZeroMass_fixed_disk_lower γ β α₁ α₂ α₃ r (M ω) hr), ?_⟩
  have he := coulombMass_at_zero_eq_rho γ (-β) α₁ α₂ α₃ (M ω) h0 h1
  simp only [neg_neg, sub_neg_eq_add] at he
  rwa [he]

end DOZZ.Proofs
