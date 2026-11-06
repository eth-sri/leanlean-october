module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaBufferedLocalNonstationary
public import Mathlib.NumberTheory.Harmonic.Bounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Nonstationary bounds outside the actual cutoff-support slopes

Only the support interval [l+eta,r-eta] is used. Stationary points
elsewhere in the original model interval do not obstruct these estimates.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedNormalizedMode_eq_interval
    {l r η : ℝ} (hη : 0 < η) (F : ℝ → ℝ) (T q : ℝ) :
    modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q =
      ∫ u in (l+η)..(r-η), (modelPhaseBufferedCutoff l r η u : ℂ)*(𝐞 (T*F u-q*u) : ℂ) := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hχ : modelPhaseBufferedCutoff l r η u ≠ 0 := by
    intro hz
    simp_all
  have hh := modelPhaseBufferedCutoff_support_open hη hχ
  grind

section
variable {F : ℝ → ℝ}
include F
theorem norm_modelPhaseBufferedFourierMode_of_support_gap {σ δ T N q l r η d : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r) (hd : 0 < d)
    (hgap : q ≤ (T/N)*deriv F (r-η)-d ∨
      (T/N)*deriv F (l+η)+d ≤ q) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4/(d*Real.pi) := by
  have hab : l+η ≤ r-η := by linarith
  have ha : l+η ∈ Ioo (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hb : r-η ∈ Ioo (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  pm_5045 hm approximateModelPhase_deriv_strictAntiOn
  have hg : (∀ u ∈ Icc (l+η) (r-η), N*d ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Icc (l+η) (r-η), T*deriv F u-q*N ≤ -(N*d)) := by
    pm_640
    · left
      pm_1384
      have hs := mul_le_mul_of_nonneg_left (hm hu' hb hu.2) hT.le
      pm_1330 hp sub_mul
    · right
      pm_1384
      have hs := mul_le_mul_of_nonneg_left (hm ha hu' hu.1) hT.le
      pm_1330 hn add_mul
  have h := norm_buffered_subinterval_nonstationary (l := l) (r := r)
    hσ hδ hF hT hη hab ha.1 hb.2 (mul_pos hN hd) hg
  rw [modelPhaseFourierMode_eq_normalized _ _ _ _ hN,norm_smul,
    Real.norm_eq_abs,abs_of_pos hN,modelPhaseBufferedNormalizedMode_eq_interval hη]
  apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
  field_simp

theorem sum_norm_bufferedModes_support_right_le_harmonic {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Q : ℤ) (hQ : (T/N)*deriv F (l+η) ≤ (Q : ℝ)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)+((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_support_gap hσ hδ hF
        hT hN hη hl hr hsep (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inr (add_le_add hQ le_rfl))
      convert h using 1
      ring
    _ = _ := by
      pm_337

theorem sum_norm_bufferedModes_support_left_le_harmonic {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Q : ℤ) (hQ : (Q : ℝ) ≤ (T/N)*deriv F (r-η)) (L : ℕ) :
    (∑ n ∈ Finset.range L,
      ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((Q : ℝ)-((n+1 : ℕ) : ℝ))‖) ≤ (4/Real.pi)*(harmonic L : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range L, (4/Real.pi)*(((n+1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := norm_modelPhaseBufferedFourierMode_of_support_gap hσ hδ hF
        hT hN hη hl hr hsep (by positivity : 0 < ((n+1 : ℕ) : ℝ))
        (Or.inl (sub_le_sub_right hQ _))
      convert h using 1
      ring
    _ = _ := by
      pm_337

theorem norm_bufferedModes_support_blocks_le_log {σ δ T N l r η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hsep : l+2*η ≤ r)
    (Lminus Lplus : ℕ) :
    ‖(∑ n ∈ Finset.range Lminus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌊(T/N)*deriv F (r-η)⌋ : ℤ)-((n+1 : ℕ) : ℝ)))+
      (∑ n ∈ Finset.range Lplus,
      modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N
        ((⌈(T/N)*deriv F (l+η)⌉ : ℤ)+((n+1 : ℕ) : ℝ)))‖ ≤
      (4/Real.pi)*(2+Real.log (Lminus : ℝ)+Real.log (Lplus : ℝ)) := by
  have hm := sum_norm_bufferedModes_support_left_le_harmonic hσ hδ hF hT hN hη hl hr hsep
    ⌊(T/N)*deriv F (r-η)⌋ (Int.floor_le _) Lminus
  have hp := sum_norm_bufferedModes_support_right_le_harmonic hσ hδ hF hT hN hη hl hr hsep
    ⌈(T/N)*deriv F (l+η)⌉ (Int.le_ceil _) Lplus
  pm_130
end

end TaoTrudgianYang2025
