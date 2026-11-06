module
import Mathlib
public import OAI.NumberTheory.DirichletL.Detector.GaussianMellin
public import OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss CubicEisenstein
open scoped EisensteinO
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

lemma gaussianCompleted_Vstar (y : ℝ) (hy : 0<y) :
    Vstar gaussianCompletedProfile y=gaussianMellinProfile y := by
  have h := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianCompletedProfile]
  field_simp

section
variable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
include S D Ψ

lemma gaussian_mellinSummand 
    (σ Z : ℝ) (hZ : 0<Z) (I J : Id) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫v : ℝ,mellinSummand S D Ψ σ Z (I,J) v)=
      correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hq : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z :=
    div_pos (mul_pos hi (pow_pos hj 3)) hZ
  have hp (v : ℝ) : mellinSummand S D Ψ σ Z (I,J) v=
      (((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z:ℝ):ℂ)^(-((σ:ℂ)+v*Complex.I))*
      Complex.exp (((σ:ℂ)+v*Complex.I)^2)*
      (completedMask S D I J*completedCorrection I J*
        (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J) := by
    unfold mellinSummand spectralSummand fullIdealWeight
    simp only [ite_eq_right hI,ite_eq_right hJ]
    rw [←gaussian_completed_norm_power _ _ Z hi hj hZ]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_mul_const,←mul_assoc,gaussianMellin_inversion _ hq σ]
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianCompleted_Vstar _ hq]
  ring

lemma gaussian_correctedSummand_summable 
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2) := by
  have hs : Summable (fun p : Id×Id=>∫v : ℝ,‖mellinSummand S D Ψ 2 Z p v‖) := by
    simp only [mellinSummand_integral_norm S D Ψ 2 Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (2:ℂ) (by norm_num)).norm.mul_right _
  have hi : Summable (fun p : Id×Id=>∫v : ℝ,mellinSummand S D Ψ 2 Z p v) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun p=>norm_integral_le_integral_norm _) hs
  have hh := hi.mul_left (((1/(2*Real.pi):ℝ):ℂ))
  simpa only [gaussian_mellinSummand S D Ψ 2 Z hZ] using hh

theorem spectralRow_eq_gaussianCompleted 
    (hΨ : ∀n,‖Ψ n‖≤1) (σ : ℝ) (hσ : 1<σ) (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral σ (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow S D Ψ t)=
      correctedCompletedT S D Ψ gaussianCompletedProfile Z := by
  rw [verticalIntegral,spectralRow_integral_eq_tsum S D Ψ hΨ σ hσ Z hZ,←tsum_mul_left]
  unfold correctedCompletedT
  apply tsum_congr
  intro p
  exact gaussian_mellinSummand S D Ψ σ Z hZ p.1 p.2
end






