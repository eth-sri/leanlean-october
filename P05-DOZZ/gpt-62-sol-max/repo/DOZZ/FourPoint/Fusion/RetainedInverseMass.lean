/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorFixedDisk
import DOZZ.FourPoint.Reflected.MassFiniteness
import DOZZ.Brownian.Lateral.RadialProjection
import Mathlib.Tactic

/-! The moving exterior mass and its fixed-disk inverse-moment majorant, for either
of the degenerate insertions. The parameter `β` is the charge of the moving root. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

noncomputable def fusionOuterMass (γ β α₁ α₂ α₃ : ℝ) (M : Measure ℂ) (z : ℂ) (ξ : ℝ) : ℝ≥0∞ :=
  coulombMass γ (M.restrict {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}) ![β, α₁, α₂] ![z, 0, 1] α₃

theorem coulombMass_restrict_measurable {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) {D : Set ℂ} (hD : MeasurableSet D) :
    Measurable (fun μ : Measure ℂ => coulombMass γ (μ.restrict D) α z αinf) := by
  simpa only [coulombMass_eq_lintegral_coulombWeight, lintegral_indicator hD] using
    Measure.measurable_lintegral ((measurable_coulombWeight γ α z αinf).indicator hD)

theorem fusionOuterMass_measurable (γ β α₁ α₂ α₃ ξ : ℝ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => fusionOuterMass γ β α₁ α₂ α₃ μ z ξ) :=
  coulombMass_restrict_measurable γ ![β, α₁, α₂] ![z, 0, 1] α₃
    (isClosed_le continuous_const continuous_norm).measurableSet

noncomputable def outerGuardWeight (γ β α₁ α₂ α₃ : ℝ) : ℝ :=
  coulombGuardWeight γ ![β, α₁, α₂] α₃

theorem outerGuardWeight_pos (γ β α₁ α₂ α₃ : ℝ) :
    0 < outerGuardWeight γ β α₁ α₂ α₃ := coulombGuardWeight_pos ..

/-- The same positive disk weight works for every moving root and every retained radius at most one. -/
theorem fusionOuterMass_fixed_disk_lower (γ β α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hr : ‖z‖ ^ (1 - ξ) ≤ 1) :
    ENNReal.ofReal (outerGuardWeight γ β α₁ α₂ α₃) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
        fusionOuterMass γ β α₁ α₂ α₃ μ z ξ :=
  coulombMass_fixed_disk_lower_restrict γ μ _ _ _ (three_roots_in_unit_disk hz)
    (fixed_disk_subset_exterior hr)

/-- Inverse powers of the moving exterior mass are dominated by a fixed inverse ball mass. -/
theorem fusionOuterMass_inv_le (γ β α₁ α₂ α₃ ξ q : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : ℂ) (hq : 0 ≤ q) (hz : ‖z‖ ≤ 1) (hr : ‖z‖ ^ (1 - ξ) ≤ 1) :
    fusionOuterMass γ β α₁ α₂ α₃ μ z ξ ^ (-q) ≤
      ENNReal.ofReal (outerGuardWeight γ β α₁ α₂ α₃ ^ (-q)) *
        μ (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) :=
  inverse_power_le_of_guard (outerGuardWeight_pos ..) hq (measure_ne_top _ _)
    (fusionOuterMass_fixed_disk_lower γ β α₁ α₂ α₃ ξ μ z hz hr)

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hγ hγ₂ hM

/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem fusionOuterMass_inverse_moment_uniform
    (β α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      (∫⁻ ω, fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ₂ M hM _ q
    (outerGuardWeight_pos γ β α₁ α₂ α₃) hq
  exact ⟨C, hC, fun z ξ hz hr => h _ fun ω =>
    fusionOuterMass_fixed_disk_lower γ β α₁ α₂ α₃ ξ (M ω) z hz hr⟩

/-- Pointwise convergence of the moving masses implies convergence of all their
nonnegative inverse moments. -/
theorem fusionOuterMass_inverse_moment_tendsto
    (β α₁ α₂ α₃ ξ q : ℝ) (hξ : ξ ≤ 1) (hq : 0 ≤ q) (A : Ω → ℝ≥0∞)
    (hA : ∀ᵐ ω ∂P, Tendsto (fun z : ℂ => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds (A ω))) :
    Tendsto (fun z : ℂ => ∫⁻ ω, fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds (∫⁻ ω, A ω ^ (-q) ∂P)) := by
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (outerGuardWeight γ β α₁ α₂ α₃ ^ (-q)) *
    M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q)
  have hsmall : ∀ᶠ z in l, ‖z‖ < 1 := by
    have hn := (continuous_norm.tendsto (0 : ℂ)).mono_left
      (nhdsWithin_le_nhds : l ≤ nhds 0)
    exact hn.eventually (by simpa using gt_mem_nhds zero_lt_one)
  have hbound : ∀ᶠ z in l, ∀ᵐ ω ∂P,
      fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q) ≤ G ω := by
    filter_upwards [hsmall] with z hz
    apply Eventually.of_forall
    intro ω
    let _ := hM.1 ω
    exact fusionOuterMass_inv_le γ β α₁ α₂ α₃ ξ q (M ω) z hq hz.le (by
      simpa using Real.rpow_le_rpow (norm_nonneg z) hz.le (sub_nonneg.mpr hξ))
  have hfinite : (∫⁻ ω, G ω ∂P) ≠ ⊤ := by
    obtain ⟨C, _, hb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hM
      (-q) (lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)) {(3 : ℂ)} isCompact_singleton
    have hb' := (hb 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
    dsimp only [G]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb')
  have hmeas : ∀ z : ℂ, AEMeasurable
      (fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-q)) P := fun z =>
    ((fusionOuterMass_measurable γ β α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).pow_const _
  exact tendsto_lintegral_filter_of_dominated_convergence' G (Eventually.of_forall hmeas) hbound hfinite
    (hA.mono fun _ ht => (ENNReal.continuous_rpow_const.tendsto _).comp ht)

/-- The actual retained source mass is positive and finite on one full-measure event. -/
theorem fusionOuterMass_positive_finite_ae
    (β α₁ α₂ α₃ ξ : ℝ) (hβ : β < Q γ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1)
    (hr : ‖z‖^(1-ξ) ≤ 1) :
    ∀ᵐ ω ∂P, 0 < fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ∧
      fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ < ⊤ := by
  have hinj : Function.Injective (![z,0,1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ i : Fin 3, (![β,α₁,α₂] : Fin 3 → ℝ) i < Q γ := by
    intro i
    fin_cases i
    · exact hβ
    · exact hα₁
    · exact hα₂
  have hfull := coulombMass_ae_lt_top P X hX γ hγ hγ₂ M hM
    ![z,0,1] hinj ![β,α₁,α₂] α₃ hcharges hα₃
  have hmeas : AEMeasurable (fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ) P :=
    (fusionOuterMass_measurable γ β α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  obtain ⟨C, _, hb⟩ := fusionOuterMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    β α₁ α₂ α₃ 1 (by norm_num)
  have hInv : (∫⁻ ω, fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^ (-(1 : ℝ)) ∂P) < ⊤ :=
    (hb z ξ hz hr).trans_lt ENNReal.ofReal_lt_top
  filter_upwards [hfull, ae_lt_top' (hmeas.pow_const (-(1 : ℝ))) hInv.ne] with ω hf hi
  constructor
  · apply pos_iff_ne_zero.mpr
    intro he
    rw [he, ENNReal.zero_rpow_of_neg (by norm_num : -(1 : ℝ) < 0)] at hi
    exact lt_irrefl _ hi
  · have hle : fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ≤
        coulombMass γ (M ω) ![β,α₁,α₂] ![z,0,1] α₃ := by
      unfold fusionOuterMass coulombMass
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    exact hle.trans_lt hf

end

end DOZZ.Proofs
