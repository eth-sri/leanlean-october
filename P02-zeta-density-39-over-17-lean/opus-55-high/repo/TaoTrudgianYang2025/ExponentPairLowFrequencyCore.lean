module
public import TaoTrudgianYang2025.ExponentPairLowFrequencySlope
public import TaoTrudgianYang2025.BetaFiniteSum
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# First-derivative cancellation at small physical height

The actual model supplies the slope gap and monotonicity. The physical
parameters and the complex conjugation are retained in the finite sum.
-/

noncomputable section

open Expdb RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_modelPhaseCore_le_firstDerivative
    {σ δ T N A : ℝ} {F : ℝ → ℝ} {L : ℕ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N)
    (hslope : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hcurv : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hstart : N < A) (hend : A+(L : ℝ)+1 < 2*N)
    (hscale : T ≤ N/4) :
    ‖∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n)‖ ≤
      (2/(2 : ℝ)^(-σ))*(N/T) := by
  let d := Real.pi*(2 : ℝ)^(-σ)*T/N
  pm_6175 hq
  have hq₁ : (2 : ℝ)^(-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hσ.le)
  pm_64 hd d
  have hTN : T/N ≤ 1/4 := (div_le_iff₀ hN).mpr (by linarith)
  have hdpi : d ≤ Real.pi := by
    have hprod := mul_le_mul_of_nonneg_right hq₁ (show 0 ≤ T/N by positivity)
    have hprod' : (2 : ℝ)^(-σ)*(T/N) ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hprod' Real.pi_pos.le
    dsimp [d]
    grind
  have hfour : 4*Real.pi*T/N ≤ Real.pi := by
    pm_1652 hh hTN Real.pi
    grind
  have hb := kusminLandau_interval (fun n => betaModelSample F T N A n) 0 L (-1) d hd
    (fun n hn => by
      have hh := betaModelSample_firstDifference_bounds hσ hT hN hslope hF
        hstart hend n hn
      pm_94 Nat.zero_add Nat.cast_add Nat.cast_one Int.cast_neg Int.cast_one
      have hlo : -(4*Real.pi*T/N) ≤
          betaModelSample F T N A (n+1)-betaModelSample F T N A n := by
        convert hh.1 using 1
        ring
      linarith)
    (fun n hn => by
      have hh := betaModelSample_firstDifference_bounds hσ hT hN hslope hF
        hstart hend n hn
      pm_94 Nat.zero_add Nat.cast_add Nat.cast_one Int.cast_neg Int.cast_one
      have hhi : betaModelSample F T N A (n+1)-betaModelSample F T N A n ≤ -d := by
        dsimp [d]
        convert hh.2 using 1
        ring
      linarith)
    (fun n hn => by
      have hh := betaModelSample_secondDifference_bounds hσ hT hN hcurv hF
        hstart hend n hn
      have hc : 0 ≤ (2*Real.pi*modelPhaseCurvatureLower σ)*T/N^2 :=
        le_of_lt (by exact div_pos (mul_pos (mul_pos (by positivity)
          (modelPhaseCurvatureLower_pos hσ)) hT) (sq_pos_of_pos hN))
      simp only [Nat.zero_add,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
      linarith [hh.1])
  simp only [Nat.zero_add] at hb
  have heq : (∑ n ∈ Finset.range (L+1), unitaryPhase (betaModelSample F T N A n)) =
      starRingEnd ℂ (∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n)) := by
    simp only [betaModelSample_phase_eq_conj,map_sum]
  rw [heq] at hb
  change ‖star (∑ n ∈ Finset.range (L+1), oscillatory F T N (A+n))‖ ≤ _ at hb
  rw [norm_star] at hb
  have hconst : 2*Real.pi/d = (2/(2 : ℝ)^(-σ))*(N/T) := by
    dsimp [d]
    field_simp
  grind

end TaoTrudgianYang2025
