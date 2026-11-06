/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CompleteEnvelopeBound
public import DOZZ.Correlations.Tails.CompactPinMoment
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! Uniform moments of the complete copied error envelope. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem complete_envelope_moment_uniform_compact
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    K (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    γ d s R (hd : 0 ≤ d) (hs : 0 ≤ s) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ N Nbar : Ω → ℝ,
      HasGaussianLaw N P → HasGaussianLaw Nbar P →
      (∫ ω, N ω ∂P) = 0 → (∫ ω, Nbar ω ∂P) = 0 →
      variance N P = 2*Real.log ‖z‖ → variance Nbar P = 2*Real.log ‖z‖ →
      ∀ r : ℝ, 0 < r → r ≤ R →
        (∫⁻ ω, ENNReal.ofReal (Real.exp (γ*Nbar ω-γ^2*Real.log ‖z‖) *
          ((d+s*(pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))*
            Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))) ^ r ∂P) ≤ C := by
  obtain ⟨v,a,hv,ha,hpar⟩ := compact_pin_parameters K hK hz γ
  let L := (d+5*s)*Real.exp (2*γ^2+4)
  let k := |γ|+2*a
  let C := 1+(ENNReal.ofReal L)^R*(ENNReal.ofReal (2*(Real.exp (v*(2*(R*k))^2/2)+Real.exp (v*(2*(R*k))^2/2))))
  refine ⟨C,(ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hR.le ENNReal.ofReal_ne_top) ENNReal.ofReal_lt_top⟩),?_⟩
  intro z hzk N Nb hN hNb hmN hmNb hvN hvNb r hr hrR
  let E := fun ω => ENNReal.ofReal (Real.exp (γ*Nb ω-γ^2*Real.log ‖z‖) *
    ((d+s*(pinCorrectionEnvelope z γ (N ω) (Nb ω)+4))*
      Real.exp (pinCorrectionEnvelope z γ (N ω) (Nb ω)+4)))
  have hpoint ω : E ω^R ≤ (ENNReal.ofReal L)^R*
      (ENNReal.ofReal (Real.exp ((R*k)*|Nb ω|))*ENNReal.ofReal (Real.exp ((R*k)*|N ω|))) := by
    have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (complete_envelope_gaussian_bound z γ (N ω) (Nb ω) d s a
        (hz z hzk) hd hs (hpar z hzk).2)) hR.le
    rw [ENNReal.ofReal_mul (show 0 ≤ L by dsimp [L]; positivity), ENNReal.mul_rpow_of_nonneg _ _ hR.le,
      ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul] at h
    rw [(show ((|γ|+2*a)*(|Nb ω|+|N ω|))*R = (R*k)*|Nb ω|+(R*k)*|N ω| by dsimp [k]; ring)] at h
    rw [(show ENNReal.ofReal (Real.exp ((R*k)*|Nb ω|+(R*k)*|N ω|)) = ENNReal.ofReal (Real.exp ((R*k)*|Nb ω|))*ENNReal.ofReal (Real.exp ((R*k)*|N ω|)) by rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)])] at h
    exact h
  calc
    _ ≤ ∫⁻ ω, 1+E ω^R ∂P := lintegral_mono fun ω =>
      weightedGrid_ennreal_rpow_le_one_add_rpow (E ω) hr hrR
    _ = 1+∫⁻ ω, E ω^R ∂P := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ 1+(ENNReal.ofReal L)^R*∫⁻ ω,
        ENNReal.ofReal (Real.exp ((R*k)*|Nb ω|))*ENNReal.ofReal (Real.exp ((R*k)*|N ω|)) ∂P := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∫⁻ ω, (ENNReal.ofReal L)^R*
            (ENNReal.ofReal (Real.exp ((R*k)*|Nb ω|))*ENNReal.ofReal (Real.exp ((R*k)*|N ω|))) ∂P :=
          lintegral_mono hpoint
        _ = _ := lintegral_const_mul' _ _
          (ENNReal.rpow_lt_top_of_nonneg hR.le ENNReal.ofReal_ne_top).ne
    _ ≤ C := add_le_add le_rfl (mul_le_mul' le_rfl (gaussian_product_lintegral_exp_abs_le P Nb N hNb hN hmNb hmN v v (by rw [hvNb]; exact (hpar z hzk).1) (by rw [hvN]; exact (hpar z hzk).1) (R*k)))


end DOZZ.Proofs
