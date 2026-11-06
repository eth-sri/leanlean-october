module
public import GuthMaynard.Improvement.UnequalSourceScales
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open GuthMaynard.NativeMoment

/-- Low frequency with three independent integer shells, bounded separately
by outer scale R and denominator scale K. -/
theorem mixed_source_low_frequency (n : ℕ) (f : 𝓢(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {M₁ M₂ M₃ R K : ℕ}
    (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (h₁R : M₁ ≤ R) (h₂K : M₂ ≤ K) (h₃R : M₃ ≤ R)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    2*gmAffineFirstPoissonRadius M₁ M₃ Q*
      (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q+gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q)^2 ≤
      (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by
  have henv := gmAffinePoissonEnvelopes_le_mass n f hf h₁ h₂ h₃ hQ
  pm_4473 h₃p M₃ h₃
  pm_4570
  pm_5538 hrad gmAffineFirstPoissonRadius M₁ M₃ Q
  have hsum : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j :=
    tsum_nonneg (fun j => by unfold gmIntDecayProfile; split_ifs <;> positivity)
  have henv0 : 0 ≤ gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q+gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q := by
    unfold gmAffinePoissonMainEnvelope gmAffinePoissonFarEnvelope
    positivity
  calc
    _ ≤ 2*gmAffineFirstPoissonRadius M₁ M₃ Q*
      (gmAffineRegionIConstant n*Q*(M₂:ℝ)^2*M₃*(∫ x, f x))^2 := by gcongr
    _ = (1/2:ℝ)*((gmAffineRegionIConstant n)^2*Q^3*((M₁:ℝ)*M₃)*(M₂:ℝ)^4*(∫ x, f x)^2) := by
      unfold gmAffineFirstPoissonRadius
      field_simp [h₃p.ne']
      ring
    _ ≤ (1/2:ℝ)*((gmAffineRegionIConstant n)^2*Q^3*((R:ℝ)*R)*(K:ℝ)^4*(∫ x, f x)^2) := by gcongr
    _ ≤ _ := by
      have hz : 0 ≤ (gmAffineRegionIConstant n)^2*Q^3*(R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2 := by positivity
      nlinarith only [hz]

set_option maxHeartbeats 800000 in
/-- Retained core with independent slope and translation scales; the
result uses RK, not the square of a common worst-case scale. -/
theorem mixed_source_retained_core {ε T Q Y : ℝ}
    (hT : 0 < T) (hQ : 1 ≤ Q) (hY : 0 ≤ Y) (f : 𝓢(ℝ, ℝ))
    {M₁ M₂ M₃ R K : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) (h₃ : 0 < M₃)
    (h₁R : M₁ ≤ R) (h₂K : M₂ ≤ K) (h₃R : M₃ ≤ R)
    {Cdiv : ℝ} (hCdiv : 0 ≤ Cdiv) :
    gmAffineRegionIICoreRawBound ε T Q Y hT (zero_lt_one.trans_le hQ) f M₁ M₂ M₃ Cdiv ≤
      Cdiv*gmAffineRegionIICoreConstant*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
        Q^3*((R:ℝ)*(K:ℝ))*(Real.sqrt (∫ u, f u^2)*
          Real.sqrt (gmAffineJ (gmAffineTildeSchwartz
            (gmAffineSecondPoissonCutoff T Q M₂ M₃/Q)
            (by unfold gmAffineSecondPoissonCutoff; positivity) f) M₂)) := by
  pm_5538 hrad gmAffineFirstPoissonRadius M₁ M₃ Q
  have hwindow : 0 ≤ (Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε := by positivity
  have hfactor := gmAffineFirstPoissonRadius_card_factor_mul_scale_le h₁ h₃ hQ
  pm_4570
  have hscale : (2*gmAffineFirstPoissonRadius M₁ M₃ Q+3)*(M₃:ℝ)*(M₂:ℝ) ≤ 8*Q*((R:ℝ)*(K:ℝ)) := by
    calc
      _ ≤ (4*Q*((M₁:ℝ)+M₃))*(M₂:ℝ) := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg M₂)
      _ ≤ (4*Q*((R:ℝ)+R))*(K:ℝ) := by gcongr
      _ = _ := by ring
  pm_4030
  change 2 *
      (Cdiv * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ ε *
        (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3)) *
      ((32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        (Q * (16 * (M₂ : ℝ) ^ 2 *
          ((Q / (M₂ : ℝ)) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) * H))) ≤
    Cdiv * (8192 * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 3) *
      (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ ε * Q ^ 3 * ((R : ℝ) * K) * H
  pm_4473 h₂p M₂ h₂
  calc
    _ = 1024*Cdiv*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual^3*Q^2*
      ((2*gmAffineFirstPoissonRadius M₁ M₃ Q+3)*(M₃:ℝ)*M₂)*H := by
        field_simp [h₂p.ne']
        ring
    _ ≤ 1024*Cdiv*(Y+gmAffineFirstPoissonRadius M₁ M₃ Q)^ε*
      SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual^3*Q^2*(8*Q*((R:ℝ)*K))*H := by gcongr
    _ = _ := by ring

end GuthMaynard.Improvement
