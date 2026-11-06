module
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalEndpointSlab
public import GuthMaynard.NativeSource.GuthMaynard.MediumTypeIEndpoint
public import GuthMaynard.NativeSource.GuthMaynard.TypeIIFourthMomentReduction
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# Classical positive-slab endpoint density

This module is the source-facing consumer of the finite classical detector.
The only intermediate interface isolated below is the genuinely narrower
medium Type-I reflection case.  The final native theorem is exported only
after the imported native medium-consumer theorem discharges that interface.
-/

/-- The exact positive-slab endpoint density proposition. -/
def ClassicalEndpointPositiveSlabDensity (σ τ₀ : ℝ) : Prop :=
  EpsilonPowerBound
    (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
    (fun T => T ^ (3 * (1 - σ) / τ₀))

/-! ## Arithmetic of the medium source-deweighting route -/

/-- The small part of the nominal medium gap is still a direct MHH range.
The numerical split at `11/10` is source-independent and leaves a fixed
positive growth exponent for the genuinely reflected dual length. -/
theorem classicalMHHExponent_le_endpoint_of_short_gap
    {σ τ₀ τ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτ₀ : τ₀ < τ) (hτ : τ ≤ 11 / 10) :
    classicalMHHExponent σ τ ≤ (3 * (1 - σ) / τ₀) * τ := by
  pm_7900 hOneSigma σ
  have hτ₀Upper : τ₀ < 11 / 10 := hτ₀.trans_le hτ
  have hTarget : (5 / 2) * (1 - σ) ≤
      (3 * (1 - σ) / τ₀) * τ := by
    rw [show (3 * (1 - σ) / τ₀) * τ =
      (3 * (1 - σ) * τ) / τ₀ by ring, le_div_iff₀ hcert.tau0_pos]
    exact (calc
        (5 / 2) * (1 - σ) * τ₀ ≤ 3 * (1 - σ) * τ₀ := by
          have hnonneg : 0 ≤ (1 - σ) * τ₀ :=
            mul_nonneg hOneSigma.le hcert.tau0_pos.le
          nlinarith
        _ < 3 * (1 - σ) * τ := by simp_all).le
  have hCore : classicalMHHExponent σ τ ≤ (5 / 2) * (1 - σ) := by
    rw [classicalMHHExponent, max_le_iff]
    constructor
    · nlinarith
    grind
  grind

/-- Power form of the preceding short-gap exponent comparison at the actual
finite Type-I length. -/
theorem rpow_classicalMHHExponent_le_endpoint_of_short_gap
    {σ τ₀ T : ℝ} {Q : ℕ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q)
    (hτ₀ : τ₀ < typeILogarithmicScale T Q)
    (hτ : typeILogarithmicScale T Q ≤ 11 / 10) :
    (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      T ^ (3 * (1 - σ) / τ₀) := by
  let tau := typeILogarithmicScale T Q
  have hExp := classicalMHHExponent_le_endpoint_of_short_gap
    hσUpper hcert (by aesop)
      (by grind)
  pm_4739
  calc
    (Q : ℝ) ^ classicalMHHExponent σ tau ≤
        (Q : ℝ) ^ ((3 * (1 - σ) / τ₀) * tau) := by aesop
    _ = ((Q : ℝ) ^ tau) ^ (3 * (1 - σ) / τ₀) := by
      rw [mul_comm, Real.rpow_mul (by positivity)]
    _ = T ^ (3 * (1 - σ) / τ₀) := by
      rw [rpow_typeILogarithmicScale_eq hT hQ]

/-! ## Bounded ordinate displacement and reseparation -/

/-! ## The direct part of the apparent medium gap -/

set_option maxHeartbeats 2000000 in
/-- The actual Type-I dichotomy witness is still a direct MHH input when its
physical scale is at most `11/10`, even if it lies just above `tau0`.  This
consumer retains the original multiplicity bound and absorbs the literal
detector, harmonic, displacement and coefficient-normalization losses. -/
theorem actual_typeI_short_gap_dichotomy_witness_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          τ₀ < typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) ≤ 11 / 10 →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  pm_4766
  let εs : ℝ := ε / 100
  pm_4775
  let d := classicalEndpointLossParameter σ τ₀ εs
  pm_4777
  pm_4771 hdEps hdEpsTau _hdHalfGap hdSmall hdOne _hdSigmaStrict
  pm_4764
  pm_4760
  pm_4762
  have huLeD : u ≤ d := by
    pm_5799 hdSq
    have hdFourth : (d ^ 2) ^ 2 ≤ d ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSq)]
    calc
      d ^ 4 = (d ^ 2) ^ 2 := by ring
      _ ≤ d ^ 2 := hdFourth
      _ ≤ d := hdSq
  have hdEpsFull : d ≤ ε / 1000 := by
    dsimp only [εs] at hdEps
    linarith
  have huEpsTau : u ≤ ε * τ₀ / 1000 := by
    exact huLeD.trans (by
      dsimp only [εs] at hdEpsTau
      linarith)
  obtain ⟨K, hK, hMHH⟩ := actual_typeI_normalized_dichotomy_witness_mhh_native
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le typeIDirectPowerLossConstant K d u τ₀ ε 1
      typeIDirectPowerLossConstant_pos.le hK.le hd hu hcert.tau0_pos hε
      (by omega) hdEpsFull huEpsTau
  pm_4770
  pm_4759
  let T₀ := max Tloss (max Tscale Thalf)
  pm_4769
  intro r hr W hSep hLarge hRange hCount hTau0 hTauUpper
  pm_4763
  pm_6523
  let N := 2 ^ r * Y
  have hNOne : 1 < N := by
    have hscaleAt := hScale T r hTScale
    simpa only [Y, N] using hscaleAt.1
  pm_896
  · obtain ⟨t, ht⟩ := hW
    let L : ℝ := ((3 / 4) * (T ^ (-u) / 2)) / Nat.clog 2 A
    have hAOne : 1 < A := by
      dsimp only [A]
      pm_4735
    have hNC : N < A := by
      pm_4765
      exact typeI_start_lt_cutoff_of_positive_large_value A N σ t L hLPos
        (by simpa only [L, N, Y, A, u, s] using hLarge t ht)
    pm_4728 hBase N hNOne
    have hTauTwo : typeILogarithmicScale T N ≤ 2 :=
      hTauUpper.trans (by norm_num)
    have hTN : T ≤ (N : ℝ) ^ (2 : ℕ) := by
      pm_8595 hTPos
    pm_4761
    have hThreshold : (N : ℝ) ^ σ / P ≤ (N : ℝ) ^ σ * L := by
      calc
        (N : ℝ) ^ σ / P ≤
            (N : ℝ) ^ σ / typeIDirectThresholdLoss T A u := by
          pm_5707
        _ ≤ (N : ℝ) ^ σ * L := by
          simpa only [L, u] using hThresholdDirect
    pm_4765
    have hMHHAt := hMHH A N σ d T L W hσ.le hN (by linarith)
      hLPos hDisp hSep (by simpa only [L, N, Y, A, u, s] using hRange)
      (by simpa only [L, N, Y, A, u, s] using hLarge)
    have hEndpointPower :=
      rpow_classicalMHHExponent_le_endpoint_of_short_gap hσUpper hcert
        hTPos hNOne (by simpa only [N, Y, s] using hTau0)
          (by simpa only [N, Y, s] using hTauUpper)
    have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor
      (τ₀ := τ₀) (R := 1) hTPos hNOne
      (by omega : 0 < (1 : ℕ)) hP hThreshold (by simpa using hEndpointPower)
      (by simpa only [N, Y, A] using hCount)
      (by simp : (W.card : ℝ) ≤ (1 : ℕ) * (W.card : ℝ)) hK.le hMHHAt
    have hLossAt := hLoss T N 1 hTLoss hNOne (by omega) (by omega)
      (by
        have hLower : 2 * τ₀ / 3 < typeILogarithmicScale T N := by
          nlinarith [hcert.tau0_pos, hTau0]
        exact hLower.le)
    pm_4767
    have hEndpoint' :
        (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
      simpa only [A, d, εs, P, s, Nat.cast_one, one_mul, mul_one] using hEndpoint
    have hLossAt' :
        ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ)) ≤ Closs * T ^ ε := by
      pm_99 d u P Nat.cast_one hLossAt
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
      _ = (((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ))) * T ^ (3 * (1 - σ) / τ₀) := by ring
      _ ≤ Closs * T ^ ε * T ^ (3 * (1 - σ) / τ₀) :=
        mul_le_mul_of_nonneg_right hLossAt' hTargetNonneg
  · have hWCard : W.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hW)
    pm_4768

/-- Assembly of the real detector dichotomy once the narrower medium
reflection consumer is available.  The proof invokes the detector itself,
unpacks all three alternatives, and retains the analytic-multiplicity factor
present in each witness branch. -/
theorem classical_endpoint_positive_slab_of_medium_native
    (hMedium : ClassicalMediumTypeIWitnessConsumer)
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ := by
  intro ε hε
  let εs : ℝ := ε / 100
  pm_4775
  let d := classicalEndpointLossParameter σ τ₀ εs
  pm_4777
  pm_4771 _hdEps _hdEpsTau _hdGap _hdSmall hdOne hdSigmaStrict
  have hdTwo : 0 < d ^ 2 := by dsimp only [d]; positivity
  have hdFour : 0 < d ^ 4 := by dsimp only [d]; positivity
  have hdSqOne : d ^ 2 ≤ 1 := by
    pm_7014
    nlinarith [sq_nonneg d]
  have hOrder : d ^ 4 / 2 ≤ d ^ 2 := by
    pm_4913 hdSqNonneg d
    have hdFourthLe : d ^ 4 ≤ d ^ 2 := by nlinarith [sq_nonneg (d ^ 2)]
    linarith
  have hdFourSigma : d ^ 4 < σ := by
    pm_7014
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
  obtain ⟨Cs, hCs, Ts, hTs, hShort⟩ :=
    actual_typeI_short_gap_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  pm_5305 Cm hCm Tm hTm hMediumAt hMedium hσLower
  obtain ⟨Ci, hCi, Ti, hTi, hTypeII⟩ :=
    actual_typeII_dichotomy_witness_consumer
      hσLower hσUpper hcert εs hεs
  let C : ℝ := max Cb (max Cp (max Cl (max Cs (max Cm Ci))))
  let T₀ : ℝ := max 8
    (max Tdich (max Tb (max Tp (max Tl (max Ts (max Tm Ti))))))
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop T₀] with T hT
  pm_5456 hT8 le_max_left hT
  pm_4185
  have hRest : max Tdich (max Tb (max Tp (max Tl (max Ts (max Tm Ti))))) ≤ T :=
    (le_max_right _ _).trans hT
  pm_4630 hTDich Tdich le_max_left hRest
  have hRest₁ : max Tb (max Tp (max Tl (max Ts (max Tm Ti)))) ≤ T :=
    (le_max_right _ _).trans hRest
  pm_4630 hTB Tb le_max_left hRest₁
  pm_5711 hRest₂ Tp Tl Ts Tm Ti hRest₁
  pm_4630 hTP Tp le_max_left hRest₂
  pm_838 hRest₃ Tl Ts Tm Ti hRest₂
  pm_4630 hTL Tl le_max_left hRest₃
  pm_5098 hRest₄ Ts Tm Ti hRest₃
  pm_4630 hTS Ts le_max_left hRest₄
  pm_4639 hRest₅ Tm Ti hRest₄
  pm_4630 hTM Tm le_max_left hRest₅
  pm_4630 hTI Ti le_max_right hRest₅
  have hEpsMono : T ^ εs ≤ T ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hTOne
    dsimp only [εs]
    linarith
  pm_4767
  have hCbC : Cb ≤ C := le_max_left _ _
  have hCpC : Cp ≤ C := le_max_of_le_right (le_max_left _ _)
  have hClC : Cl ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCsC : Cs ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  pm_8185 hCmC Cm le_max_left
  pm_8185 hCiC Ci le_max_right
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
    pm_5708
    let τ := typeILogarithmicScale T (2 ^ r * Y)
    have hBound : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
      by_cases hLowScale : τ < 2 * τ₀ / 3
      pm_4722 hLow hTL hLowScale hClC
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
          pm_4722 hPowered hTP hRaised hCpC
          · have hGapUpper : τ < 4 * τ₀ / 3 := lt_of_not_ge hRaised
            by_cases hShortScale : τ ≤ 11 / 10
            · have h := hShort T hTS r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hTau0)
                (by simpa only [τ, Y] using hShortScale)
              exact hLiftConstant hCsC h
            · have h := hMediumAt T hTM r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d, Y, A] using hLong)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hTau0)
                (by simpa only [τ, Y] using lt_of_not_ge hShortScale)
                (by simpa only [τ, Y] using hGapUpper)
              exact hLiftConstant hCmC h
    pm_4721
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
      pm_7153 hTypeIIAlt
      refine ⟨r, hr, W, hSep, ?_, hRange, hCount⟩
      intro t ht
      simpa only [show (3 / 4 : ℝ) * (3 / 4) = 9 / 16 by norm_num] using
        hLarge t ht
    have h := hTypeII T hTI (by
        simpa only [d] using hTypeIIAlt')
    have h' := hLiftSmall hCi.le h
    pm_4721
    simpa only [mul_assoc] using hLiftConstant hCiC h'

/-- Native classical endpoint density on the positive slab.  The proof term
uses the actual detector dichotomy and the native medium Type-I consumer; the
other Type-I and Type-II alternatives are consumed inside
`classical_endpoint_positive_slab_of_medium_native`. -/
theorem classical_endpoint_positive_slab_native
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ :=
  classical_endpoint_positive_slab_of_medium_native
    classical_medium_typeI_witness_consumer_native hσLower hσUpper hcert

/-- Ingham endpoint specialization of the native positive-slab density
theorem. -/
theorem ingham_endpoint_positive_slab_native
    {σ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1) :
    ClassicalEndpointPositiveSlabDensity σ (2 - σ) :=
  classical_endpoint_positive_slab_native hσLower hσUpper
    (ingham_endpoint_scale_certificate hσLower hσUpper)

end GuthMaynard.NativeMoment
