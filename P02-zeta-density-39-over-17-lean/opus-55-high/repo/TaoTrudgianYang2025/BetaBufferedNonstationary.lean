module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaBufferedVariation
public import TaoTrudgianYang2025.BetaWeightedPhase
public import TaoTrudgianYang2025.BetaFourierModes
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Width-independent nonstationary bounds for the original Fourier modes

The cutoff variation is proved, the monotone slope comes from the original
model, and the normalized-to-physical factor N is retained.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

section
variable {l r η : ℝ} (hη : 0 < η)
include l r η hη
theorem modelPhaseBufferedCutoff_support_open :
    Function.support (modelPhaseBufferedCutoff l r η) ⊆ Ioo (l+η) (r-η) := by
  pm_5276 le_of_not_gt

theorem modelPhaseBufferedCutoff_eq_zero_of_overlap (h : r-η ≤ l+η) :
    modelPhaseBufferedCutoff l r η = fun _ => 0 := by
  funext u
  apply Function.notMem_support.mp
  intro hu
  have hh := modelPhaseBufferedCutoff_support_open hη hu
  linarith [hh.1,hh.2]
end

theorem intervalC1Bound_modelPhaseBufferedCutoff
    {l r η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) :
    IntervalC1Bound (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)) a b 2 := by
  have he : (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)) =
      (fun u => (zetaBandCutoff (l+η) (l+2*η) (r-2*η) (r-η) u : ℂ)) := by
    funext u
    rw [modelPhaseBufferedCutoff_eq_band hη]
  rw [he]
  exact intervalC1Bound_zetaBandCutoff (by linarith) (by linarith) hab

theorem norm_modelPhaseBufferedNormalizedMode_nonstationary
    {F : ℝ → ℝ} {σ δ T q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q ≤ -lam)) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q‖ ≤
      4/(lam*Real.pi) := by
  pm_8304
  · let φ : ℝ → ℝ := fun u => T*F u-q*u
    pm_1647
    have hmono : AntitoneOn (deriv φ) (Ioo (1 : ℝ) 2) := by
      intro u hu v hv huv
      rw [hd hu,hd hv]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left
        ((approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn hu hv huv) hT.le) q
    pm_1649
    have hg : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ deriv φ u) ∨
        (∀ u ∈ Ioo (1 : ℝ) 2, deriv φ u ≤ -lam) := by
      rcases hgap with hp | hn
      pm_7630 Or.inl hp
      pm_7630 Or.inr hn
    pm_7050 IntervalC1Bound.fourierChar_of_slope_gap hsub hmono
    have hs : Function.support (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)*
        (𝐞 (φ u) : ℂ)) ⊆ Ioc (l+η) (r-η) := by
      pm_1648
    unfold modelPhaseNormalizedMode
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    convert h using 1
    norm_num
  · have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap hη (le_of_not_ge hab)
    pm_382 modelPhaseNormalizedMode hz Complex.ofReal_zero zero_mul integral_zero norm_zero
    positivity

theorem norm_modelPhaseBufferedFourierMode_nonstationary
    {F : ℝ → ℝ} {σ δ T N q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q*N ≤ -lam)) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*N/(lam*Real.pi) := by
  rw [modelPhaseFourierMode_eq_normalized _ _ _ _ hN,norm_smul,Real.norm_eq_abs,abs_of_pos hN]
  exact (mul_le_mul_of_nonneg_left
    (norm_modelPhaseBufferedNormalizedMode_nonstationary hσ hδ hF hT hη hl hr hlam hgap)
    hN.le).trans_eq (by ring)

end TaoTrudgianYang2025
