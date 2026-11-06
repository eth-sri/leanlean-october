module
public import GuthMaynard.Improvement.MixedHeightReduction
public import GuthMaynard.Improvement.UnequalHeightTheorem
public import GuthMaynard.Improvement.SparseAffineInput
public import GuthMaynard.Improvement.UniformReduction
import WeylPort.Analytic.RealLaplace

public section
open MeasureTheory
open scoped SchwartzMap
namespace GuthMaynard.Improvement
open GuthMaynard.NativeMoment

set_option maxHeartbeats 600000 in
/-- The strengthened unequal-scale estimate for the source's canonical
support/shell convention and any fixed height-mass Fourier family. All
Poisson, divisor, tail and adaptive smoothing premises are discharged. -/
theorem mixed_height_affine (D : ℝ → ℕ → ℝ) (hD : ∀ β n, 0 ≤ D β n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (f : 𝓢(ℝ, ℝ)) (R K M₁ M₂ M₃ : ℕ),
      2 ≤ T → (∀ x, 0 ≤ f x) → GMAffineSourceSupported f →
      GMAffineHeightFourierMassFamilyAtDepth T D 0 f →
      0 < K → K ≤ R → (R:ℝ) ≤ T^4 →
      0 < M₁ → 0 < M₂ → 0 < M₃ → M₁ ≤ R → M₂ ≤ K → M₃ ≤ R →
      gmAffineTransformIntegral f M₁ M₂ M₃ ≤ C*T^ε*
        ((R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)) := by
  obtain ⟨A,hA,hP⟩ := mixed_height_reduction D hD (δ := ε/2) (by positivity)
  pm_114 B hB hF adaptive_sparse_affine D hD hε
  let C := 2*A*Real.sqrt (B+1)+36992*(8:ℝ)^24
  pm_4123
  refine ⟨C,hC,?_⟩
  intro T f R K M₁ M₂ M₃ hT hf hs hp hK hKR hRT h₁ h₂ h₃ h₁R h₂K h₃R
  pm_4945 hTp T hR R hK.trans_le hKR
  pm_278 hr1 R hR
  pm_278 hk1 K hK
  pm_404 hkr K R hKR
  have hKT : (K:ℝ) ≤ T^4 := hkr.trans hRT
  pm_404 h₂k M₂ K h₂K
  have h₂T : (M₂:ℝ) ≤ T^4 := h₂k.trans hKT
  pm_4518 hmass x f integral_nonneg hf
  pm_4604
  pm_549 hpow T ε hε.le
  let W := (R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)
  pm_82 hW W
  by_cases hlarge : 8 ≤ T
  · have hq := hF T (ε/2) hlarge f M₃ M₂ hf hs hp h₂ h₂T
    have hF' : gmAffineJ (unequalAdaptive T (ε/2) M₂ M₃ f hTp) M₂ ≤
        ((B+1)*T^ε)*((K:ℝ)^6*(∫ x, f x)^2+(K:ℝ)^4*(Real.sqrt (∫ x, f x^2))^2) := by
      rw [Real.sq_sqrt hL2]
      exact hq.trans (by gcongr; linarith)
    have hP' := hP T hT f R K M₁ M₂ M₃ hf (GMAffineSupportedOn.iterationSupported hs (by norm_num) (by norm_num)) hp hK hKR hRT h₁ h₂ h₃ h₁R h₂K h₃R
    have hclosed := unequal_reduction_of_estimates
      (show 0 ≤ A*T^(ε/2) by positivity)
      (show 1 ≤ (B+1)*T^ε by nlinarith only [hB,hpow])
      (Nat.cast_nonneg K) hkr hmass (Real.sqrt_nonneg _)
      (by simpa only [mul_assoc] using hP') hF'
    have hsqrt : Real.sqrt ((B+1)*T^ε) = Real.sqrt (B+1)*T^(ε/2) := by
      rw [Real.sqrt_mul (by positivity)]
      congr 1
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hTp.le]
      congr 1
      ring
    pm_5917 hpows ε hTp
    have hfinal : gmAffineTransformIntegral f M₁ M₂ M₃ ≤ 2*A*Real.sqrt (B+1)*T^ε*W := by
      apply hclosed.trans_eq
      rw [hsqrt]
      unfold unequalScaleBound
      rw [Real.sq_sqrt hL2]
      dsimp only [W]
      calc
        _ = 2*A*Real.sqrt (B+1)*(T^(ε/2)*T^(ε/2))*
          ((R:ℝ)^2*(K:ℝ)^4*(∫ x, f x)^2+(R:ℝ)*(K:ℝ)^3*(∫ x, f x^2)) := by ring
        _ = _ := by rw [hpows]
    exact hfinal.trans (by
      pm_8921 hW
      exact le_add_of_nonneg_right (by positivity))
  · have hT8 : T ≤ 8 := le_of_lt (lt_of_not_ge hlarge)
    have hR8 : (R:ℝ)^6 ≤ (8:ℝ)^24 := by
      calc
        _ ≤ ((8:ℝ)^4)^6 := by gcongr; exact hRT.trans (by gcongr)
        _ = _ := by norm_num
    pm_4603
    have hcrude := gmAffineTransformIntegral_le_crude hf2
      (mem_gmAffineScaleTriples.mpr ⟨h₁,h₁R,h₂,h₂K.trans hKR,h₃,h₃R⟩)
    have hL2W : (∫ x, f x^2) ≤ W := by
      have hcoef : (1:ℝ) ≤ (R:ℝ)*(K:ℝ)^3 :=
        one_le_mul_of_one_le_of_one_le hr1 (one_le_pow₀ hk1)
      exact (le_mul_of_one_le_left hL2 hcoef).trans
        (le_add_of_nonneg_left (by positivity))
    calc
      _ ≤ 36992*(8:ℝ)^24*(∫ x, f x^2) := hcrude.trans (by gcongr)
      _ ≤ 36992*(8:ℝ)^24*W := mul_le_mul_of_nonneg_left hL2W (by positivity)
      _ ≤ C*T^ε*W := by
        apply mul_le_mul_of_nonneg_right _ hW
        calc
          _ ≤ C := le_add_of_nonneg_left (by positivity)
          _ ≤ C*T^ε := le_mul_of_one_le_right hC.le hpow

end GuthMaynard.Improvement
