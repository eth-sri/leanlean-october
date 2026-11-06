module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalEndpointSlab
public import GuthMaynard.NativeSource.GuthMaynard.MediumTypeIEndpoint
public import GuthMaynard.NativeSource.GuthMaynard.TypeIIFourthMomentReduction

@[expose] public section

open Asymptotics Filter Topology Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

def ClassicalEndpointPositiveSlabDensity (σ τ₀ : ℝ) : Prop :=
  EpsilonPowerBound
    (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
    (fun T => T ^ (3 * (1 - σ) / τ₀))

theorem classical_endpoint_positive_slab_of_medium_native
    (hMedium : ClassicalMediumTypeIWitnessConsumer)
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ := by
  intro ε hε
  let εs : ℝ := ε / 100
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  let d := classicalEndpointLossParameter σ τ₀ εs
  have hdSpec := classicalEndpointLossParameter_spec hσLower hσUpper hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, _hdGap, _hdUpperGap, _hdSigma,
    _hdSmall, _hdHalf, hdOne, hdSigmaStrict⟩
  have hdTwo : 0 < d ^ 2 := by dsimp only [d]; positivity
  have hdFour : 0 < d ^ 4 := by dsimp only [d]; positivity
  have hdSqOne : d ^ 2 ≤ 1 := by
    have hdLeOne : d ≤ 1 := by simpa only [d] using hdOne
    nlinarith [sq_nonneg d]
  have hOrder : d ^ 4 / 2 ≤ d ^ 2 := by
    have hdSqNonneg : 0 ≤ d ^ 2 := sq_nonneg d
    have hdFourthLe : d ^ 4 ≤ d ^ 2 := by nlinarith [sq_nonneg (d ^ 2)]
    linarith
  have hdFourSigma : d ^ 4 < σ := by
    have hdLeOne : d ≤ 1 := by simpa only [d] using hdOne
    have hdFourthLe : d ^ 4 ≤ d := by nlinarith
    exact hdFourthLe.trans_lt (by simpa only [d] using hdSigmaStrict)
  obtain ⟨Tdich, hTdich, hDich⟩ := classical_typeI_typeII_dichotomy_native
    σ d (d ^ 2) (d ^ 4) hσLower hσUpper.le hd hdTwo hdFour
      hOrder hdSqOne hdFourSigma
  obtain ⟨Cb, hCb, Tb, hTb, hBasic⟩ :=
    actual_typeI_basic_window_dichotomy_witness_consumer
      hσLower hσUpper hcert εs hεs
  obtain ⟨Cp, hCp, Tp, hTp, hPowered⟩ :=
    actual_typeI_powered_window_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  obtain ⟨Cl, hCl, Tl, hTl, hLow⟩ :=
    actual_typeI_low_window_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  obtain ⟨Cm, hCm, Tm, hTm, hMediumAt⟩ :=
    hMedium hσLower hσUpper hcert ε hε
  obtain ⟨Ci, hCi, Ti, hTi, hTypeII⟩ :=
    actual_typeII_dichotomy_witness_consumer
      hσLower hσUpper hcert εs hεs
  let C : ℝ := max Cb (max Cp (max Cl (max Cm Ci)))
  let T₀ : ℝ := max 8
    (max Tdich (max Tb (max Tp (max Tl (max Tm Ti)))))
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT8 : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hRest : max Tdich (max Tb (max Tp (max Tl (max Tm Ti)))) ≤ T :=
    (le_max_right _ _).trans hT
  have hTDich : Tdich ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tb (max Tp (max Tl (max Tm Ti))) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTB : Tb ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tp (max Tl (max Tm Ti)) ≤ T :=
    (le_max_right _ _).trans hRest₁
  have hTP : Tp ≤ T := (le_max_left _ _).trans hRest₂
  have hRest₃ : max Tl (max Tm Ti) ≤ T :=
    (le_max_right _ _).trans hRest₂
  have hTL : Tl ≤ T := (le_max_left _ _).trans hRest₃
  have hRest₄ : max Tm Ti ≤ T := (le_max_right _ _).trans hRest₃
  have hTM : Tm ≤ T := (le_max_left _ _).trans hRest₄
  have hTI : Ti ≤ T := (le_max_right _ _).trans hRest₄
  have hEpsMono : T ^ εs ≤ T ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hTOne
    dsimp only [εs]
    linarith
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
    Real.rpow_nonneg hTPos.le _
  have hCbC : Cb ≤ C := le_max_left _ _
  have hCpC : Cp ≤ C := le_max_of_le_right (le_max_left _ _)
  have hClC : Cl ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCmC : Cm ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hCiC : Ci ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _)))
  have hCnonneg : 0 ≤ C := hCb.le.trans hCbC
  have hPowerTargetNonneg :
      0 ≤ T ^ ε * T ^ (3 * (1 - σ) / τ₀) :=
    mul_nonneg (Real.rpow_nonneg hTPos.le _) hTargetNonneg
  have hLiftSmall {K : ℝ} (hK : 0 ≤ K)
      (h : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ εs * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    exact h.trans (by gcongr)
  have hLiftConstant {K : ℝ} (hKC : K ≤ C)
      (h : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          K * (T ^ ε * T ^ (3 * (1 - σ) / τ₀)) := by
            simpa only [mul_assoc] using h
      _ ≤ C * (T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :=
        mul_le_mul_of_nonneg_right hKC hPowerTargetNonneg
      _ = C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by ring
  have hDichAt := hDich T hTDich
  dsimp only [ClassicalTypeITypeIIDichotomyConclusion] at hDichAt
  rcases hDichAt with hZero | hTypeI | hTypeIIAlt
  · rw [hZero]
    simp only [Nat.cast_zero, abs_zero]
    simpa only [norm_zero] using mul_nonneg hCnonneg
      (norm_nonneg (T ^ ε * |T ^ (3 * (1 - σ) / τ₀)|))
  · rcases hTypeI with ⟨r, hr, W, hSep, hLarge, hLong, hRange, hCount⟩
    let Y := ⌊T ^ (d ^ 2)⌋₊
    let A := ⌊sharpZetaCutoff T⌋₊
    let τ := typeILogarithmicScale T (2 ^ r * Y)
    have hBound : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
      by_cases hLowScale : τ < 2 * τ₀ / 3
      · have h := hLow T hTL r (by simpa only [A] using hr) W hSep
            (by simpa only [d, Y, A] using hLarge)
            (by simpa only [d] using hRange)
            (by simpa only [d, A] using hCount)
            (by simpa only [τ, Y] using hLowScale)
        exact hLiftConstant hClC h
      · have hTauLower : 2 * τ₀ / 3 ≤ τ := le_of_not_gt hLowScale
        by_cases hBasicScale : τ ≤ τ₀
        · have h := hBasic T hTB r (by simpa only [A] using hr) W hSep
              (by simpa only [d, Y, A] using hLarge)
              (by simpa only [d] using hRange)
              (by simpa only [d, A] using hCount)
              (by simpa only [τ, Y] using hTauLower)
              (by simpa only [τ, Y] using hBasicScale)
          exact hLiftConstant hCbC (hLiftSmall hCb.le h)
        · have hTau0 : τ₀ < τ := lt_of_not_ge hBasicScale
          by_cases hRaised : 4 * τ₀ / 3 ≤ τ
          · have h := hPowered T hTP r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hRaised)
            exact hLiftConstant hCpC h
          · have hGapUpper : τ < 4 * τ₀ / 3 := lt_of_not_ge hRaised
            have hShortScale : 11 / 10 < τ := lt_of_le_of_lt hcert.tau0_ge_short hTau0
            have h := hMediumAt T hTM r (by simpa only [A] using hr) W hSep
              (by simpa only [d, Y, A] using hLarge)
              (by simpa only [d, Y, A] using hLong)
              (by simpa only [d] using hRange)
              (by simpa only [d, A] using hCount)
              (by simpa only [τ, Y] using hTau0)
              (by simpa only [τ, Y] using hShortScale)
              (by simpa only [τ, Y] using hGapUpper)
            exact hLiftConstant hCmC h
    have hCountNonneg : (0 : ℝ) ≤
        (zeroCountRect σ 1 T (2 * T) : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hCountNonneg, abs_of_nonneg hTargetNonneg,
      abs_of_nonneg hPowerTargetNonneg]
    simpa only [mul_assoc] using hBound
  · have hTypeIIAlt' :
        let X := ⌊T ^ (d ^ 4 / 2)⌋₊
        let Y := ⌊T ^ (d ^ 2)⌋₊
        (∃ r ∈ Finset.range (Nat.clog 2 Y), ∃ W : Finset ℝ,
          IsSeparated 1 W ∧
          (∀ t ∈ W, (9 / 16 : ℝ) / Nat.clog 2 Y ≤
            ‖dirichletPoly (2 ^ r * X)
              (sharpMollifiedLineCoeff Y X σ) t‖) ∧
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) ∧
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 Y *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) *
                W.card) := by
      dsimp only
      rcases hTypeIIAlt with ⟨r, hr, W, hSep, hLarge, hRange, hCount⟩
      refine ⟨r, hr, W, hSep, ?_, hRange, hCount⟩
      intro t ht
      simpa only [show (3 / 4 : ℝ) * (3 / 4) = 9 / 16 by norm_num] using
        hLarge t ht
    have h := hTypeII T hTI (by
        simpa only [d] using hTypeIIAlt')
    have h' := hLiftSmall hCi.le h
    have hCountNonneg : (0 : ℝ) ≤
        (zeroCountRect σ 1 T (2 * T) : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hCountNonneg, abs_of_nonneg hTargetNonneg,
      abs_of_nonneg hPowerTargetNonneg]
    simpa only [mul_assoc] using hLiftConstant hCiC h'

theorem classical_endpoint_positive_slab_native
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ :=
  classical_endpoint_positive_slab_of_medium_native
    classical_medium_typeI_witness_consumer_native hσLower hσUpper hcert

theorem ingham_endpoint_positive_slab_native
    {σ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ ≤ 9 / 13) :
    ClassicalEndpointPositiveSlabDensity σ (2 - σ) :=
  classical_endpoint_positive_slab_native hσLower (by linarith)
    (ingham_endpoint_scale_certificate hσLower hσUpper)

