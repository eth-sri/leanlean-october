module
public import GuthMaynard.NativeSource.GuthMaynard.MediumTypeIEndpoint.Part01
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap
namespace GuthMaynard.NativeMoment
set_option maxHeartbeats 1200000

/-- The power growth of a dyadic interval extracted from the actual lower
source blocks absorbs both the detector `clog` and the small `T^(d^4)`
threshold loss.  This is the quantitative bridge that allows the existing
Type-II powered-threshold envelope to be reused without changing the source
polynomial. -/
theorem eventually_lower_source_threshold_scale_growth
    (d : ℝ) (hd : 0 < d) (hdOne : d < 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Y A Q P : ℕ), T₀ ≤ T →
        Y = ⌊T ^ (d ^ 2)⌋₊ → A = ⌊sharpZetaCutoff T⌋₊ →
        Y ≤ Q → Q < 4 * P →
        6 * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) ≤
          C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
  let γ : ℝ := (d ^ 3 - d ^ 4) / 2
  have hγ : 0 < γ := by
    pm_6307
  obtain ⟨Tfloor, hTfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor (d ^ 2) (sq_pos_of_pos hd)
  have hLogEventually := eventually_log_nat_power_le_rpow 1 γ hγ
  pm_4757
  pm_8948 cLog
  let C₀ : ℝ := max 1 (6 * cLog * 4 ^ d)
  let T₀ : ℝ := max 8 (max Tfloor Tlog)
  refine ⟨C₀, le_max_left _ _, T₀, le_max_left _ _, ?_⟩
  intro T Y A Q P hT rfl rfl hYQ hQP
  pm_4629
  pm_4639 hRest Tfloor Tlog hT
  pm_4630 hTFloor Tfloor le_max_left hRest
  pm_4630 hTLog Tlog le_max_right hRest
  pm_4185
  have hLogPower : Real.log T ≤ T ^ γ := by
    have hAt := hTlog T hTLog
    simpa only [pow_one] using hAt
  pm_984 hLogSix
  pm_4168 hPowOne γ hTOne hγ.le
  pm_4778
  have hClogRaw := sharp_cutoff_clog_le_log_majorant T hTEight
  have hClog : (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) ≤
      cLog * T ^ γ := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    calc
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) + 1 ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) + 1 := by
        linarith
      _ ≤ 2 + (2 * T ^ γ) / Real.log 2 := by
        have hNumerator : Real.log 6 + Real.log T ≤ 2 * T ^ γ := by
          linarith
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * T ^ γ) / Real.log 2 :=
          div_le_div_of_nonneg_right hNumerator hLogTwo.le
        linarith
      _ = 2 + (2 / Real.log 2) * T ^ γ := by ring
      _ ≤ 2 * T ^ γ + (2 / Real.log 2) * T ^ γ := by
        linarith
      _ = (2 + 2 / Real.log 2) * T ^ γ := by ring
      _ = cLog * T ^ γ := by rfl
  have hYLower : T ^ (d ^ 2) / 2 ≤
      (⌊T ^ (d ^ 2)⌋₊ : ℝ) := (hFloor T hTFloor).1
  have hPPos : 0 < P := by omega
  have hPSource : T ^ (d ^ 2) / 8 ≤ (P : ℝ) := by
    have hYFourP : ⌊T ^ (d ^ 2)⌋₊ < 4 * P := hYQ.trans_lt hQP
    have hYFourPReal : (⌊T ^ (d ^ 2)⌋₊ : ℝ) ≤ 4 * P := by
      exact_mod_cast hYFourP.le
    nlinarith
  have hTwoP : T ^ (d ^ 2) / 4 ≤ ((2 * P : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hRaised : (T ^ (d ^ 2) / 4) ^ d ≤
      ((2 * P : ℕ) : ℝ) ^ d :=
    Real.rpow_le_rpow (by positivity) hTwoP hd.le
  have hLeftPower : (T ^ (d ^ 2) / 4) ^ d =
      (4 : ℝ) ^ (-d) * T ^ (d ^ 3) := by
    rw [Real.div_rpow (Real.rpow_nonneg hTPos.le _)
      (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_mul hTPos.le]
    ring_nf
  have hScaleLower : T ^ (d ^ 3) ≤
      4 ^ d * ((2 * P : ℕ) : ℝ) ^ d := by
    have hFourPos : 0 < (4 : ℝ) ^ d := Real.rpow_pos_of_pos (by norm_num) _
    have hFourCancel : (4 : ℝ) ^ d * (4 : ℝ) ^ (-d) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      norm_num
    rw [hLeftPower] at hRaised
    calc
      T ^ (d ^ 3) = 4 ^ d * (4 ^ (-d) * T ^ (d ^ 3)) := by
        rw [← mul_assoc, hFourCancel, one_mul]
      _ ≤ 4 ^ d * ((2 * P : ℕ) : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hRaised hFourPos.le
  have hExponent : d ^ 4 + γ ≤ d ^ 3 := by
    pm_6307
  have hTExp : T ^ (d ^ 4 + γ) ≤ T ^ (d ^ 3) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hClogTerm :
      6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
        6 * cLog * T ^ (d ^ 3) := by
    calc
      6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
          6 * (cLog * T ^ γ) * T ^ (d ^ 4) := by
        gcongr
      _ = 6 * cLog * T ^ (d ^ 4 + γ) := by
        rw [Real.rpow_add hTPos]
        ring
      _ ≤ 6 * cLog * T ^ (d ^ 3) := by gcongr
  calc
    6 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) * T ^ (d ^ 4) ≤
        6 * cLog * T ^ (d ^ 3) := hClogTerm
    _ ≤ (6 * cLog * 4 ^ d) * ((2 * P : ℕ) : ℝ) ^ d := by
      have hcLog : 0 ≤ 6 * cLog := by dsimp only [cLog]; positivity
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hScaleLower hcLog
    _ ≤ C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
      gcongr
      exact le_max_right _ _

/-- The literal threshold of a localized source block dominates the standard
powered threshold after its extra detector logarithm has been absorbed by
`eventually_lower_source_threshold_scale_growth`.  The comparison preserves
the exact dyadic relation `P < 2N`; it does not identify the extracted block
with the physical source scale. -/
theorem lower_source_threshold_ge_typeII_model
    {C₀ u η σ T : ℝ} {A N P : ℕ}
    (hC₀ : 0 < C₀) (hσ : 0 ≤ σ)
    (hT : 0 < T) (hA : 1 < A) (hP : 0 < P)
    (hPN : P < 2 * N)
    (hGrowth :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ η) :
    let V₀ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
      (Nat.clog 2 A + 1 : ℕ)
    let L := ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1)
    let L₀ := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
    let D := C₀ * ((2 * P : ℕ) : ℝ) ^ η * (P : ℝ) ^ (-σ)
    L₀ / D ≤ L := by
  dsimp only
  pm_74 hPReal P hP
  have hN : 0 < N := by omega
  pm_4863
  have hAClog : (0 : ℝ) < Nat.clog 2 (A + 1) := by
    pm_7558
  have hLossClog : (0 : ℝ) < Nat.clog 2 A + 1 := by positivity
  have hTwoP : (0 : ℝ) < ((2 * P : ℕ) : ℝ) := by positivity
  have hD : 0 < C₀ * ((2 * P : ℕ) : ℝ) ^ η * (P : ℝ) ^ (-σ) := by
    positivity
  have hPNReal : (P : ℝ) / 4 ≤ (N : ℝ) / 2 := by
    have : (P : ℝ) ≤ 2 * N := by exact_mod_cast hPN.le
    linarith
  have hPowPN : (P : ℝ) ^ σ ≤
      4 ^ σ * ((N : ℝ) / 2) ^ σ := by
    have hRaised := Real.rpow_le_rpow (by positivity) hPNReal hσ
    have hIdentity : (P : ℝ) ^ σ =
        4 ^ σ * ((P : ℝ) / 4) ^ σ := by
      pm_7445 hPReal.le
      field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) σ).ne']
    rw [hIdentity]
    exact mul_le_mul_of_nonneg_left hRaised (Real.rpow_nonneg (by norm_num) _)
  have hCore :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * (P : ℝ) ^ σ ≤
        (C₀ * ((2 * P : ℕ) : ℝ) ^ η) * ((N : ℝ) / 2) ^ σ := by
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * (P : ℝ) ^ σ ≤
          ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u) *
            (4 ^ σ * ((N : ℝ) / 2) ^ σ) := by gcongr
      _ = ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ) *
            ((N : ℝ) / 2) ^ σ := by ring
      _ ≤ (C₀ * ((2 * P : ℕ) : ℝ) ^ η) * ((N : ℝ) / 2) ^ σ := by
        gcongr
  pm_5439 hTpow T u Real.rpow_pos_of_pos hT
  pm_7060 hTPowInv u
  field_simp [hC₀.ne', hTwoP.ne', hTpow.ne', hPReal.ne', hAClog.ne',
    hLossClog.ne']
  have hPcancel : (P : ℝ) ^ σ * (P : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hPReal]
    norm_num
  have hScaled :
      3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u ≤
        2 * (C₀ * ((2 * P : ℕ) : ℝ) ^ η * ((N : ℝ) / 2) ^ σ) *
          (P : ℝ) ^ (-σ) := by
    calc
      3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u =
          2 * ((3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u *
            (P : ℝ) ^ σ) * (P : ℝ) ^ (-σ) := by
        calc
          3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u =
              3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 1 := by ring
          _ = 3 * (Nat.clog 2 A + 1 : ℕ) * T ^ u *
              ((P : ℝ) ^ σ * (P : ℝ) ^ (-σ)) := by rw [hPcancel]
          _ = _ := by ring
      _ ≤ 2 * (C₀ * ((2 * P : ℕ) : ℝ) ^ η * ((N : ℝ) / 2) ^ σ) *
          (P : ℝ) ^ (-σ) := by gcongr
  nlinarith

/-- The two literal logarithmic losses from common-source selection and
source-block localization cost an arbitrarily small power of the height.
Both `Nat.clog` arguments are the actual sharp natural cutoff. -/
theorem eventually_source_selection_log_product_le
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) ≤ C * T ^ η := by
  have hLogEventually := eventually_log_nat_power_le_rpow 2 η hη
  pm_4757
  pm_8948 c
  let C : ℝ := c ^ (2 : ℕ)
  let T₀ : ℝ := max 8 Tlog
  refine ⟨C, by dsimp only [C, c]; positivity, T₀, le_max_left _ _, ?_⟩
  intro T hT
  pm_4629
  pm_4630 hTLog Tlog le_max_right hT
  have hTPos : 0 < T := by linarith
  have hLogOne : 1 ≤ Real.log T := by
    have hExp : Real.exp 1 ≤ T := by
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
           _ ≤ 8 := by norm_num
           _ ≤ T := hTEight
    pm_6160 hExp
  pm_4778
  let A := ⌊sharpZetaCutoff T⌋₊
  pm_4715
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    apply (Nat.one_le_floor_iff _).mpr
    exact (show (1 : ℝ) ≤ 4 * T by linarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hALog : Real.log (A + 1 : ℕ) ≤ 2 * Real.log T := by
    have hASeven : ((A + 1 : ℕ) : ℝ) ≤ 7 * T := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hLogMono := Real.log_le_log (by positivity : (0 : ℝ) < (A + 1 : ℕ))
      hASeven
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) hTPos.ne'] at hLogMono
    pm_6308
    linarith
  have hClogA := sharp_cutoff_clog_le_log_majorant T hTEight
  have hFirst : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ c * Real.log T := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    pm_984 hLogSix
    calc
      (Nat.clog 2 A : ℝ) + 1 ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) + 1 := by
        linarith
      _ ≤ (2 + 2 / Real.log 2) * Real.log T := by
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * Real.log T) / Real.log 2 :=
          div_le_div_of_nonneg_right (by linarith) hLogTwo.le
        calc
          _ ≤ 2 + (2 * Real.log T) / Real.log 2 := by linarith
          _ = 2 + (2 / Real.log 2) * Real.log T := by ring
          _ ≤ 2 * Real.log T + (2 / Real.log 2) * Real.log T := by
            linarith
          _ = _ := by ring
      _ = c * Real.log T := by rfl
  have hSecond : (Nat.clog 2 (A + 1) : ℝ) ≤ c * Real.log T := by
    have hRaw := natCast_clog_two_le_one_add_log (A + 1) (by omega)
    calc
      (Nat.clog 2 (A + 1) : ℝ) ≤
          1 + Real.log (A + 1 : ℕ) / Real.log 2 := hRaw
      _ ≤ 1 + (2 * Real.log T) / Real.log 2 := by
        gcongr
      _ ≤ (2 + 2 / Real.log 2) * Real.log T := by
        calc
          _ = 1 + (2 / Real.log 2) * Real.log T := by ring
          _ ≤ 2 * Real.log T + (2 / Real.log 2) * Real.log T := by
            linarith
          _ = _ := by ring
      _ = c * Real.log T := by rfl
  pm_82 hc c
  calc
    ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) ≤
      (c * Real.log T) * (c * Real.log T) := by
        simpa only [A] using mul_le_mul hFirst hSecond (by positivity)
          (by positivity)
    _ = C * (Real.log T) ^ (2 : ℕ) := by dsimp only [C]; ring
    _ ≤ C * T ^ η := by
      gcongr
      exact hTlog T hTLog

/-- Replacing the height by `7T` in a powered normalization loss costs only
one bounded-power constant.  This is the exact comparison needed because the
literal source cover uses `A + 1`, while the sharp cutoff only gives
`A + 1 ≤ 7T`. -/
theorem classicalTypeIIPowerLoss_seven_mul_le
    {A e T : ℝ} {k Q B : ℕ}
    (hA : 0 ≤ A) (hT : 8 ≤ T) (hkB : k ≤ B) :
    classicalTypeIIPowerLoss A e (7 * T) k Q ≤
      classicalTypeIIPowerLoss ((2 : ℝ) ^ B * A) e T k Q := by
  have hTPos : 0 < T := by linarith
  pm_390 hLogT T
  pm_6308
  have hLogMul : Real.log (7 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) hTPos.ne']
    linarith
  have hFour : 4 * Real.log (7 * T) ≤ 2 * (4 * Real.log T) := by
    linarith
  have hFourNonneg : 0 ≤ 4 * Real.log (7 * T) := by
    have : 1 ≤ 7 * T := by nlinarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  have hPow : (4 * Real.log (7 * T)) ^ k ≤
      (2 : ℝ) ^ B * (4 * Real.log T) ^ k := by
    calc
      (4 * Real.log (7 * T)) ^ k ≤
          (2 * (4 * Real.log T)) ^ k :=
        pow_le_pow_left₀ hFourNonneg hFour k
      _ = (2 : ℝ) ^ k * (4 * Real.log T) ^ k := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ B * (4 * Real.log T) ^ k := by
        gcongr
        norm_num
  unfold classicalTypeIIPowerLoss
  have hScale : 0 ≤ (((2 : ℝ) ^ k) * Q) ^ (2 * e) := by positivity
  pm_96 hkNonneg k
  calc
    A * (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
          (4 * Real.log (7 * T)) ^ k ≤
        A * (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
          ((2 : ℝ) ^ B * (4 * Real.log T) ^ k) := by gcongr
    _ = ((2 : ℝ) ^ B * A) *
          (((2 : ℝ) ^ k) * Q) ^ (2 * e) * k *
            (4 * Real.log T) ^ k := by ring

/-- Sharp-cutoff specialization of the generic powered-threshold envelope.
All uses of `A + 1`, the natural floor, and the change from `T` to `7T` are
proved here, so downstream source consumers can use the ordinary physical
height in their epsilon budget. -/
theorem source_powered_threshold_loss_le_envelope
    {C₀ C e σ T : ℝ} {A N k B : ℕ}
    (hC₀ : 1 ≤ C₀) (hC : 1 ≤ C)
    (hσOne : σ ≤ 1) (hT : 8 ≤ T)
    (hA : A = ⌊sharpZetaCutoff T⌋₊)
    (hN : 0 < N) (hk : 0 < k) (hkB : k ≤ B) :
    let L := (9 / 16 : ℝ) / Nat.clog 2 (A + 1)
    let D := C₀ * (2 * N : ℝ) ^ e * (N : ℝ) ^ (-σ)
    let aLog := max 1
      (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
    let Aenv := (2 : ℝ) ^ B *
      ((2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B)
    typeIIPoweredThresholdLoss C L D e σ N k ≤
      1 + classicalTypeIIPowerLoss Aenv e T k (N ^ k) := by
  dsimp only
  pm_1380
  pm_4747
  pm_1081 A₀ C
  let Aenv : ℝ := (2 : ℝ) ^ B * A₀
  have hTPos : 0 < T := by linarith
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  pm_4715
  have hASeven : (((A + 1 : ℕ) : ℝ)) ≤ 7 * T := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hExp : Real.exp 1 ≤ 7 * T := by
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ 7 * T := by nlinarith
  have hGeneric := typeII_powered_threshold_loss_le_envelope
    (C₀ := C₀) (C := C) (e := e) (dY := 1) (σ := σ)
    (T := 7 * T) (Y := A + 1) (N := N) (k := k)
    hC₀ hC (by norm_num) hσOne hExp (by omega) (by simpa using hASeven)
    hN hk hkB
  dsimp only at hGeneric
  pm_3988 hA₀ A₀ aLog
  have hCompare := classicalTypeIIPowerLoss_seven_mul_le
    (A := A₀) (e := e) (T := T) (k := k) (Q := N ^ k) (B := B)
    hA₀ hT hkB
  simpa only [Aenv] using
    hGeneric.trans (add_le_add_right hCompare 1)

set_option maxHeartbeats 1200000

/-- Endpoint consumer for either of the two literal bottom blocks selected
from the source-smooth decomposition.  The proof chooses the natural power
from the physical scale, performs both real finite extractions, and returns
to the multiplicity-weighted zero count. -/
theorem actual_lower_source_family_endpoint_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r : ℕ, r < 2 → ∀ W : Finset ℝ,
          W.Nonempty → IsSeparated 1 W → InBaseInterval (3 * T) W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  pm_4766
  pm_5097 εs ε σ τ₀
  pm_4764
  let U : ℝ := 4 / s
  pm_5918 B U
  pm_4775
  have hdSpec := classicalEndpointLossParameter_spec
    hσLower hσUpper hcert.tau0_pos hεs
  pm_5074 hdEpsSmall hdEpsTauSmall _hdReflected _hdHalfGap _hdUpperGap hdSmall
  pm_4760
  pm_4762
  pm_3981
  pm_5878
  have hdOneStrict : d < 1 := by
    pm_6309
    have hInv : 1 / (1000 * (1 + τ₀)) < (1 : ℝ) := by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hDen
    exact hdSmall.trans_lt hInv
  pm_4776
  pm_4659
  have hC₀ : 1 ≤ C₀ := by
    have hFour : 1 ≤ (4 : ℝ) ^ σ :=
      Real.one_le_rpow (by norm_num) hσ.le
    dsimp only [C₀]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Cg * 4 ^ σ := mul_le_mul hCg hFour (by norm_num) (by linarith)
  pm_4747
  pm_4658
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le Aenv K d d τ₀ (ε / 4) B
      hAenv hK.le hd hd hcert.tau0_pos (by positivity) hB
      (by nlinarith [hdEps]) (by nlinarith [hdEpsTau])
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le (ε / 4) (by positivity)
  pm_4081 Tscale hTscale hScale eventually_lower_source_logarithmic_scale_bounds s hs
  have hPowTop := tendsto_rpow_atTop hs
  have hEventuallySixteen := (tendsto_atTop.1 hPowTop) 16
  pm_4610 eventually_atTop hEventuallySixteen Tsixteen hTsixteen
  pm_4081 Twindow hTwindow hWindow eventually_dyadic_power_scale_in_endpoint_window hcert.tau0_pos hU
  let T₀ : ℝ := max Tloss
    (max Tlog (max Tscale (max Tsixteen (max Twindow Tgrowth))))
  let C : ℝ := Closs * Clog
  pm_4662 T₀
  intro r hr W hW hSep hBase hLarge hCount
  pm_4772
  pm_5711 hRest Tlog Tscale Tsixteen Twindow Tgrowth hT
  pm_4630 hTLog Tlog le_max_left hRest
  pm_838 hRest₁ Tscale Tsixteen Twindow Tgrowth hRest
  pm_4630 hTScale Tscale le_max_left hRest₁
  pm_4640 hRest₂ Tsixteen Twindow Tgrowth hRest₁
  pm_4630 hTSixteen Tsixteen le_max_left hRest₂
  pm_4639 hRest₃ Twindow Tgrowth hRest₂
  pm_4630 hTWindow Twindow le_max_left hRest₃
  pm_4630 hTGrowth Tgrowth le_max_right hRest₃
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  pm_4185
  let Y : ℕ := ⌊T ^ s⌋₊
  pm_632 N
  have hScaleAt := hScale T r hTScale hr
  pm_5965 hScaleAt
  have hTauMargin : 8 * τ₀ ≤ typeILogarithmicScale T N := by
    have hTauSmallProduct : τ₀ * s ≤ 1 / 1000 := by
      have hdTau : τ₀ * d ≤ 1 / 1000 := by
        pb_714
      dsimp only [s]
      calc
        τ₀ * d ^ 2 = (τ₀ * d) * d := by ring
        _ ≤ (1 / 1000 : ℝ) * d :=
          mul_le_mul_of_nonneg_right hdTau hd.le
        _ ≤ 1 / 1000 := by nlinarith
    have hCore : 8 * τ₀ ≤ 1 / (2 * s) := by
      pm_585 le_div_iff₀ s
      nlinarith
    exact hCore.trans hTauLower
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  have hY : 0 < Y := by
    dsimp only [Y, s]
    apply Nat.floor_pos.mpr
    have hTOneStrict : 1 < T := by linarith only [hTEight]
    exact (Real.one_lt_rpow hTOneStrict hs).le
  let V₀ : ℝ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  pm_116 hV₀ V₀
  obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀,
      hPUpper, hPLower⟩ :=
    extract_normalized_source_dyadic_block W hY hAOne hV₀ hW hSep
      (by simpa only [V₀, u, s, Y, A] using hLarge)
  let P : ℕ := 2 ^ j
  have hN16 : 16 ≤ N := by
    have hPowSixteen : (16 : ℝ) ≤ T ^ s := hTsixteen T hTSixteen
    have hY16 : 16 ≤ Y := by
      dsimp only [Y]
      exact Nat.le_floor hPowSixteen
    pm_6903 N
  pm_4910 hUHalf U
  have hTauUpperHalf : typeILogarithmicScale T N ≤ U / 2 := by
    dsimp only [U]
    convert hTauUpper using 1
    field_simp [hs.ne']
    ring
  have hPScaleUpperData := extracted_source_logarithmic_scale_upper
    hTOne hUHalf hN16 (by simpa only [N, P] using hPLower) hTauUpperHalf
  rcases hPScaleUpperData with ⟨hPOne, hTauPUpperRaw⟩
  have hTauPUpper : typeILogarithmicScale T P ≤ U := by
    convert hTauPUpperRaw using 1
    all_goals ring
  have hPScaleLowerData := extracted_source_logarithmic_scale_lower
    hTPos (mul_nonneg (by norm_num) hcert.tau0_pos.le) (by omega : 4 ≤ N)
    (by simpa only [N, P] using hPLower)
    (by simpa only [N, P] using hPUpper) hTauMargin
  have hTauPMargin : 4 * τ₀ ≤ typeILogarithmicScale T P := by
    convert hPScaleLowerData.2 using 1
    all_goals ring
  pm_8519 hTauPMargin hTauPUpper
  let L : ℝ := ((((N : ℝ) / 2) ^ σ) * V₀) /
    Nat.clog 2 (A + 1)
  pm_116 hP P
  have hL : 0 < L := by
    dsimp only [L]
    have hCover : 0 < Nat.clog 2 (A + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  pm_4655
  obtain ⟨q, hq, W', hW'sub₀, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        have hPhase := sum_zero_real_part_eq_dirichletPoly P
          (normalizedTypeISourceDirichletCoeff Y A r σ) t
        rw [hPhase]
        simpa only [P, L, V₀, N] using hLarge₀ t ht)
  have hW'sub : W' ⊆ W := hW'sub₀.trans hW₀sub
  have hCard : (W.card : ℝ) ≤
      (Nat.clog 2 (A + 1) : ℝ) * k * (W'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤ (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) := hCard₀
      _ ≤ (Nat.clog 2 (A + 1) : ℝ) * (k * (W'.card : ℝ)) := by
        gcongr
      _ = _ := by ring
  pm_4657
  have hQWindow := hWindow T P k q hTWindow hPOne hk hkB hqk
    hTauPUpper hTauPowLower hTauPowUpper
  pm_6772
  pm_4660
  have hFourNonneg : 0 ≤ (4 : ℝ) ^ σ := Real.rpow_nonneg (by norm_num) _
  have hGrowthModel :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
    dsimp only [C₀]
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ u * 4 ^ σ ≤
          (6 * (Nat.clog 2 A + 1 : ℕ) * T ^ u) * 4 ^ σ := by
            gcongr
            norm_num
      _ ≤ (Cg * ((2 * P : ℕ) : ℝ) ^ d) * 4 ^ σ := by
            exact mul_le_mul_of_nonneg_right hGrowthAt hFourNonneg
      _ = (Cg * 4 ^ σ) * ((2 * P : ℕ) : ℝ) ^ d := by ring
  pm_4653
  have hModelBase := lower_source_threshold_ge_typeII_model
    (C₀ := C₀) (u := u) (η := d) (σ := σ) (T := T)
    (A := A) (N := N) (P := P) (by positivity) hσ.le hTPos hAOne hP
    (by simpa only [N, P] using hPUpper) hGrowthModel
  pm_4652
  pm_4654
  pm_1593
  let multiplicity : ℕ := base * cover₁
  pm_4661
  have hCount' : zeroCountRect σ 1 T (2 * T) ≤ multiplicity * W.card := by
    pm_99 base cover₁ multiplicity A hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (W'.card : ℝ) := by
    simpa only [extraction, cover₂, Nat.cast_mul, Nat.cast_ofNat,
      mul_assoc, L, Vp, P, Q, N, V₀] using hCard
  have hEndpoint := endpoint_powered_witness_count_le hσUpper hcert hTPos
    (by simpa only [Q] using hQOne) (by exact_mod_cast hExtractionPos)
    hPloss hThreshold (by simpa only [Q] using hQScaleLower)
    (by simpa only [Q] using hQScaleUpper) hCount' hExtract hK.le
    (by simpa only [Q, Vp, P, L, N, V₀, Real.rpow_zero, one_mul] using hMHH)
  have hLossAt := hLoss T Q k hTLoss (by simpa only [Q] using hQOne)
    hk hkB (by simpa only [Q] using hQScaleLower)
  have hLogsAt := hLogs T hTLog
  pm_4656
  have hEpsPow : T ^ (ε / 4) * T ^ (ε / 4) ≤ T ^ ε := by
    rw [← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have hHarmonicNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    by_cases hQZero : Q = 0
    · simp only [hQZero, harmonic_zero, Rat.cast_zero]
      norm_num
    · exact_mod_cast (harmonic_pos hQZero).le
  have hCoreNonneg : 0 ≤ ((base : ℝ) * (k : ℝ) *
      (K * (1 + (((harmonic Q : ℚ) : ℝ))))) := by
    positivity
  have hEndpoint' : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (((cover₁ : ℕ) : ℝ) * cover₂) *
        (((base : ℕ) : ℝ) * k *
          (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * Ploss ^ (6 : ℕ))) *
              T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          ((base * cover₁ : ℕ) : ℝ) * ((cover₂ * k : ℕ) : ℝ) *
            (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
              (6 * Ploss ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
            simpa only [multiplicity, extraction, Ploss] using hEndpoint
      _ = (((cover₁ : ℕ) : ℝ) * cover₂) *
          (((base : ℕ) : ℝ) * k *
            (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
              (6 * Ploss ^ (6 : ℕ))) * T ^ (3 * (1 - σ) / τ₀) := by
            norm_num only [Nat.cast_mul]
            ring
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ ≤ (((cover₁ : ℕ) : ℝ) * cover₂) *
        (((base : ℕ) : ℝ) * k *
          (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) *
              T ^ (3 * (1 - σ) / τ₀) := by
      gcongr
    _ ≤ (Clog * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
          T ^ (3 * (1 - σ) / τ₀) := by
      gcongr
    _ ≤ (Closs * Clog) * T ^ ε *
          T ^ (3 * (1 - σ) / τ₀) := by
      calc
        (Clog * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
              T ^ (3 * (1 - σ) / τ₀) =
            (Closs * Clog) * (T ^ (ε / 4) * T ^ (ε / 4)) *
              T ^ (3 * (1 - σ) / τ₀) := by ring
        _ ≤ (Closs * Clog) * T ^ ε *
              T ^ (3 * (1 - σ) / τ₀) := by gcongr
    _ = C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by rfl

/-- Powered endpoint consumer for an actual source block whose *extracted*
dyadic scale lies in the small transition strip below the endpoint window.
The natural power is selected after the literal dyadic block is known.  Thus
the scale divided by `k`, the powered coefficients and the final MHH length
all refer to the same finite object. -/
theorem actual_source_near_endpoint_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {r j : ℕ} (W W₀ : Finset ℝ),
          0 < Y → 1 < A → W.Nonempty → IsSeparated 1 W →
          InBaseInterval (3 * T) W → W₀ ⊆ W →
          IsSeparated 1 W₀ →
          (W.card : ℝ) ≤
            (Nat.clog 2 (A + 1) : ℝ) * (W₀.card : ℝ) →
          (∀ t ∈ W₀,
            let N := 2 ^ r * Y
            let V₀ := ((3 / 4 : ℝ) * (T ^ (-(d ^ 4)) / 2)) /
              (Nat.clog 2 A + 1 : ℕ)
            ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1) ≤
              ‖dirichletPoly (2 ^ j)
                (normalizedTypeISourceDirichletCoeff Y A r σ) t‖) →
          2 ^ j < 2 * (2 ^ r * Y) → 2 ^ r * Y < 4 * 2 ^ j →
          1 < 2 ^ j →
          typeILogarithmicScale T (2 ^ j) ≤ 4 / (d ^ 2) →
          4 * τ₀ / 3 - reflectedEndpointScaleSlack σ d ≤
            typeILogarithmicScale T (2 ^ j) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  pm_4766
  pm_5097 η ε σ τ₀
  let s : ℝ := reflectedEndpointScaleSlack σ d
  let Uscale : ℝ := 4 / (d ^ 2)
  pm_6416 τ₀
  pm_4756
  have hdSpec := classicalEndpointLossParameter_spec
    hσLower hσUpper hcert.tau0_pos hη
  pm_5074 hdEta hdEtaTau hdReflected hdGap hdUpper _hdSmall
  pm_4196 hs s reflectedEndpointScaleSlack_pos hσLower hd
  have hsSmall : s ≤ τ₀ / 6 := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_le_tau0_sixth hσLower hσUpper hcert
      hdGap hdUpper
  pm_116 hUscale Uscale
  have hB : 0 < B := by
    dsimp only [B]
    exact Nat.ceil_pos.mpr (div_pos
      (mul_pos (by norm_num) (add_pos hUscale hs))
      (mul_pos (by norm_num) hcert.tau0_pos))
  have hdOneStrict : d < 1 := hdOne.lt_of_ne (by
    intro h
    subst d
    linarith [hdGap, hσUpper])
  have hDisplacementBudget : 2 * s / τ₀ ≤ ε / 400 := by
    have hBudget := reflected_total_power_budget_with_gap_le hσLower hσUpper
      hcert.tau0_pos hη hd hdOne hdEta hdReflected
    dsimp only [s, η] at hBudget
    have hNonneg : 0 ≤ 24 * d *
        (⌈3 * (2 / ((σ - 1 / 2) / 2) + s) / (2 * τ₀)⌉₊ : ℝ) +
        6 * d := by positivity
    linarith
  pm_4659
  have hC₀ : 1 ≤ C₀ := by
    have hFour : 1 ≤ (4 : ℝ) ^ σ := Real.one_le_rpow (by norm_num) hσ.le
    dsimp only [C₀]
    pm_385 mul_nonneg sub_nonneg.mpr hCg hFour
  pm_4747
  pm_4658
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le Aenv K d d (9 * τ₀ / 16) (ε / 4) B
      hAenv hK.le hd hd (by nlinarith [hcert.tau0_pos]) (by positivity) hB
      (by dsimp only [η] at hdEta; nlinarith)
      (by dsimp only [η] at hdEtaTau; nlinarith)
  obtain ⟨Ccover, hCcover, Tcover, hTcover, hCover⟩ :=
    eventually_source_selection_log_product_le (ε / 4) (by positivity)
  obtain ⟨Tscale, hTscale, hScaleDyadic⟩ :=
    eventually_dyadic_power_scale_lower_half
      (τ₀ := 3 * τ₀ / 4) (U := Uscale)
      (by nlinarith [hcert.tau0_pos]) hUscale
  let C : ℝ := Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)
  pm_6533 T₀ Tloss Tcover Tscale Tgrowth
  pm_4662 T₀
  intro r j W W₀ hY hA hW hSep hBase hW₀sub hSep₀ hCard₀ hLarge₀
    hPUpper hPLower hPOne hTauPUpper hNear hCount
  pm_4772
  pm_4640 hRest Tcover Tscale Tgrowth hT
  pm_4630 hTCover Tcover le_max_left hRest
  pm_4639 hRest' Tscale Tgrowth hRest
  pm_4630 hTScale Tscale le_max_left hRest'
  pm_4630 hTGrowth Tgrowth le_max_right hRest'
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  pm_4169
  pm_7559
  pm_632 N
  let P : ℕ := 2 ^ j
  pm_605 V₀
  let L : ℝ := ((((N : ℝ) / 2) ^ σ) * V₀) / Nat.clog 2 (A + 1)
  pm_116 hP P
  have hN : 0 < N := by dsimp only [N, Y]; exact Nat.mul_pos (pow_pos (by omega) r) hY
  have hL : 0 < L := by
    dsimp only [L, V₀, N, A]
    have hCover : 0 < Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
      Nat.clog_pos Nat.one_lt_two (by omega)
    positivity
  pm_4655
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkScale, hkActualLower, hkGapLoss⟩ :=
    exists_bounded_positive_power_augmented_endpoint_with_gap hσUpper hcert
      hs.le hdUpper hsSmall
      (by simpa only [P] using hNear)
      (by simpa only [P, Uscale] using hTauPUpper)
  obtain ⟨q, hq, W', hW'sub₀, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k P (normalizedTypeISourceDirichletCoeff Y A r σ)
      0 (3 * T) L W₀ hk hkB hP (by norm_num) (by linarith) hL
      hCoeff hSep₀ hBase₀ (by
        intro t ht
        rw [sum_zero_real_part_eq_dirichletPoly]
        simpa only [P, L, V₀, N, Y, A] using hLarge₀ t ht)
  pm_4657
  pm_4653
  pm_4660
  have hGrowthModel :
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) * 4 ^ σ ≤
        C₀ * ((2 * P : ℕ) : ℝ) ^ d := by
    dsimp only [C₀]
    calc
      (3 / 2 : ℝ) * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4) * 4 ^ σ ≤
          (6 * (Nat.clog 2 A + 1 : ℕ) * T ^ (d ^ 4)) * 4 ^ σ := by
            gcongr
            norm_num
      _ ≤ (Cg * ((2 * P : ℕ) : ℝ) ^ d) * 4 ^ σ := by
            exact mul_le_mul_of_nonneg_right hGrowthAt
              (Real.rpow_nonneg (by norm_num) _)
      _ = (Cg * 4 ^ σ) * ((2 * P : ℕ) : ℝ) ^ d := by ring
  have hModelBase := lower_source_threshold_ge_typeII_model
    (C₀ := C₀) (u := d ^ 4) (η := d) (σ := σ) (T := T)
    (A := A) (N := N) (P := P) (by positivity) hσ.le hTPos hA hP
    (by simpa only [N, P] using hPUpper) hGrowthModel
  pm_4652
  have hPower := dyadic_power_mhh_le_endpoint_with_factor_of_augmented_scale
    hσLower hσUpper hcert hTOne (by simpa only [P] using hPOne)
    hk hkB hqk hkScale hkLower hkUpper hkGapLoss
  dsimp only at hPower
  have hFinalScale : 3 * τ₀ / 8 ≤ typeILogarithmicScale T Q := by
    have hScale := hScaleDyadic T P k q hTScale
      (by simpa only [P] using hPOne) hk hqk
      (by simpa only [P, Uscale] using hTauPUpper)
      (by nlinarith [hkActualLower] : 2 * (3 * τ₀ / 4) / 3 ≤
        typeILogarithmicScale T P / k)
    convert hScale using 1
    · ring
  pm_4654
  pm_1593
  pm_4661
  have hCount' : zeroCountRect σ 1 T (2 * T) ≤ (base * cover₁) * W.card := by
    simpa only [base, cover₁, A] using hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (W'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤ (cover₂ : ℝ) * (W₀.card : ℝ) := by
        simpa only [cover₂] using hCard₀
      _ ≤ (cover₂ : ℝ) * (k * (W'.card : ℝ)) := by gcongr
      _ = extraction * (W'.card : ℝ) := by
        dsimp only [extraction]
        push_cast
        ring
  have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor hTPos
    (by simpa only [Q] using
      (show 1 < 2 ^ q * P ^ k by
        exact (one_lt_pow₀ (by simpa only [P] using hPOne) hk.ne').trans_le
          (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))))
    (by exact_mod_cast hExtractionPos) hPloss hThreshold
    (R := ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀))
    (by
      calc
        (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
            ((2 : ℝ) ^ B) ^ (2 : ℕ) *
              T ^ (3 * (1 - σ) / τ₀ + 2 * s / τ₀) := by
                simpa only [Q, P] using hPower
        _ = (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀)) *
              T ^ (3 * (1 - σ) / τ₀) := by
            rw [Real.rpow_add hTPos]
            ring)
    hCount' hExtract hK.le
    (by simpa only [Q, Vp, P, L, Real.rpow_zero, one_mul] using hMHH)
  have hLossAt := hLoss T Q k hTLoss
    (by dsimp only [Q]; exact (one_lt_pow₀ (by simpa only [P] using hPOne)
      hk.ne').trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)))
    hk hkB (by nlinarith [hFinalScale])
  have hCoverAt := hCover T hTCover
  pm_4656
  have hDisp : T ^ (2 * s / τ₀) ≤ T ^ (ε / 400) :=
    Real.rpow_le_rpow_of_exponent_le hTOne hDisplacementBudget
  have hHarmonicNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    exact_mod_cast (harmonic_pos (by
      dsimp only [Q]
      positivity : Q ≠ 0)).le
  have hCoreNonneg : 0 ≤
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) := by
    positivity
  have hCoreBound :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) ≤
        Closs * T ^ (ε / 4) := by
    simpa only [base, A] using hLossAt
  have hCoverBound : (cover₁ : ℝ) * cover₂ ≤
      Ccover * T ^ (ε / 4) := by
    simpa only [cover₁, cover₂, A] using hCoverAt
  pm_1194 hCoverNonneg cover₁ cover₂
  pm_8520 hCoverTargetNonneg ε
  have hNewCoreNonneg : 0 ≤
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
        (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) := by
    positivity
  have hDyadicConstantNonneg : 0 ≤ ((2 : ℝ) ^ B) ^ (2 : ℕ) := by
    positivity
  have hSourceDispNonneg : 0 ≤ T ^ (2 * s / τ₀) := by positivity
  have hTargetDispNonneg : 0 ≤ T ^ (ε / 400) := by positivity
  have hSixPow : 6 * Ploss ^ (6 : ℕ) ≤
      6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ) :=
    mul_le_mul_of_nonneg_left hPowLoss (by norm_num)
  have hPoweredCore :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * Ploss ^ (6 : ℕ)) ≤
        (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ)) :=
    mul_le_mul_of_nonneg_left hSixPow hCoreNonneg
  have hFirstFront := mul_le_mul_of_nonneg_left hPoweredCore hCoverNonneg
  have hFirstDyadic := mul_le_mul_of_nonneg_right hFirstFront hDyadicConstantNonneg
  have hFirstDisp := mul_le_mul_of_nonneg_right hFirstDyadic hSourceDispNonneg
  have hFirstFinal := mul_le_mul_of_nonneg_right hFirstDisp hTargetNonneg
  have hCoverCore :
      ((cover₁ : ℝ) * cover₂) *
          ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) ≤
        (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) :=
    mul_le_mul hCoverBound hCoreBound hNewCoreNonneg hCoverTargetNonneg
  have hSecondDyadic := mul_le_mul_of_nonneg_right hCoverCore hDyadicConstantNonneg
  have hSecondDisp := mul_le_mul hSecondDyadic hDisp hSourceDispNonneg (by positivity)
  have hSecondFinal := mul_le_mul_of_nonneg_right hSecondDisp hTargetNonneg
  have hEpsCombine : T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 400) ≤
      T ^ ε := by
    pm_4663
  have hEndpoint' := hEndpoint
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ = ((cover₁ : ℝ) * cover₂) *
        ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * Ploss ^ (6 : ℕ))) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀) *
          T ^ (3 * (1 - σ) / τ₀) := by
      dsimp only [base, cover₁, cover₂, extraction] at hEndpoint' ⊢
      pm_8126
    _ ≤ ((cover₁ : ℝ) * cover₂) *
        ((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss Aenv d T k Q) ^ (6 : ℕ))) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / τ₀) *
          T ^ (3 * (1 - σ) / τ₀) := hFirstFinal
    _ ≤ (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
        ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (ε / 400) *
          T ^ (3 * (1 - σ) / τ₀) := hSecondFinal
    _ ≤ C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
      dsimp only [C]
      calc
        (Ccover * T ^ (ε / 4)) * (Closs * T ^ (ε / 4)) *
            ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (ε / 400) *
              T ^ (3 * (1 - σ) / τ₀) =
          (Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            (T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 400)) *
              T ^ (3 * (1 - σ) / τ₀) := by ring
        _ ≤ (Closs * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by gcongr

/-! ## Source-facing medium witness contract -/

/-- Every selected source-smooth scale is either one of the two lower-edge
blocks, one of the upper-edge blocks meeting the terminal cutoff, or is a
genuine interior block to which the normalized Poisson/B-process identity
applies.  This is the exact finite trichotomy behind the source proof; in
particular no boundary block is silently passed to the interior formula. -/
theorem typeISourceSmoothScale_lower_terminal_or_interior
    {Y A r : ℕ} (hY : 0 < Y) :
    r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
      (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
        2 * (2 ^ r * Y) ≤ A) := by
  by_cases hr : r < 2
  · exact Or.inl hr
  right
  by_cases hUpper : A < 2 * (2 ^ r * Y)
  · exact Or.inl hUpper
  right
  constructor
  · have hrTwo : 2 ≤ r := by omega
    have hpow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hrTwo
    have hYOne : 1 ≤ Y := hY
    have hNat : 2 * (Y + 1) ≤ 2 ^ r * Y := by
      calc
        2 * (Y + 1) ≤ 4 * Y := by omega
        _ ≤ 2 ^ r * Y := Nat.mul_le_mul_right Y hpow
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
      have hNatReal : (2 : ℝ) * (Y + 1) ≤ (2 ^ r * Y : ℕ) := by
        exact_mod_cast hNat
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith)
  · omega

/-- The finite dual cutoff used in the medium B-process.  The small positive
power is deliberate: it places every stationary frequency inside the finite
window while leaving an arbitrarily small power loss with which to sum the
far-frequency and Mellin tails. -/
noncomputable def mediumTypeIDualCutoff (T d : ℝ) (Q : ℕ) : ℕ :=
  ⌊T ^ (1 + d) / Q⌋₊

theorem mediumTypeIDualCutoff_cast_le
    {T d : ℝ} {Q : ℕ} (hT : 0 ≤ T) :
    (mediumTypeIDualCutoff T d Q : ℝ) ≤ T ^ (1 + d) / Q := by
  unfold mediumTypeIDualCutoff
  exact Nat.floor_le (div_nonneg (Real.rpow_nonneg hT _)
    (Nat.cast_nonneg Q))

/-- Multiplicity-safe entry from the long-tail lower bound carried by the
actual dichotomy witness.  It selects one common smooth scale on one common
subfamily and immediately records whether that scale is a lower edge, an
upper/terminal edge, or a legal interior B-process scale. -/
theorem extract_common_typeISourceSmoothBlock_classified
    {Y A k : ℕ} {σ V : ℝ} (W : Finset ℝ)
    (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (k + 1), ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ (k + 1) * W'.card ∧
      (∀ t ∈ W', V / (k + 1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖) ∧
      (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
          2 * (2 ^ r * Y) ≤ A)) := by
  obtain ⟨r, hr, W', hW', hSep', hLarge', hCard'⟩ :=
    exists_common_typeISmoothBlock_large Y A k σ V W
      hY hA hW hSeparated hLarge
  exact ⟨r, hr, W', hW', hSep', hCard', hLarge',
    typeISourceSmoothScale_lower_terminal_or_interior hY⟩

/-- The literal `Nat.clog` cover needed to instantiate the classified source
extraction at the sharp zeta cutoff.  The factor `Y` is retained explicitly,
so this also handles the smallest admissible source scale without a hidden
division or positivity assumption. -/
theorem sharp_source_cutoff_le_clog_cover
    {Y A : ℕ} (hY : 1 ≤ Y) :
    A ≤ 2 ^ (Nat.clog 2 A) * Y := by
  by_cases hA : A = 0
  · simp [hA]
  · calc
      A ≤ 2 ^ (Nat.clog 2 A) := Nat.le_pow_clog (by omega) A
      _ ≤ 2 ^ (Nat.clog 2 A) * Y :=
        Nat.le_mul_of_pos_right _ (by omega)

/-- Concrete source selection from the same long-tail lower bound exported by
the detector dichotomy.  The selected family is a subset of the original
family, and the displayed cardinality factor is the only loss; hence the
analytic-multiplicity inequality attached to that original family remains
available to the final slab consumer. -/
theorem actual_medium_long_tail_selects_classified_source
    {T d σ V : ℝ} (W : Finset ℝ)
    (hT : 1 ≤ T) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail ⌊T ^ (d ^ 2)⌋₊
        ⌊sharpZetaCutoff T⌋₊ ((σ : ℂ) + I * (t : ℂ))‖) :
    let Y := ⌊T ^ (d ^ 2)⌋₊
    let A := ⌊sharpZetaCutoff T⌋₊
    let k := Nat.clog 2 A
    ∃ r ∈ Finset.range (k + 1), ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ (k + 1) * W'.card ∧
      (∀ t ∈ W', V / (k + 1 : ℕ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖) ∧
      (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) ∧
          2 * (2 ^ r * Y) ≤ A)) := by
  dsimp only
  have hPowOne : 1 ≤ T ^ (d ^ 2) :=
    Real.one_le_rpow hT (sq_nonneg d)
  have hY : 1 ≤ ⌊T ^ (d ^ 2)⌋₊ :=
    (Nat.one_le_floor_iff _).mpr hPowOne
  exact extract_common_typeISourceSmoothBlock_classified W hY
    (sharp_source_cutoff_le_clog_cover hY) hW hSeparated hLarge

/-! ## Uniform growth on the genuinely reflected branch -/

/-- Once the terminal B-process contradiction does not apply, the physical
source scale is separated from height by a fixed positive power.  The
separation is derived from the same numerical margin used by the detector;
it is not an extra scale hypothesis. -/
theorem medium_complementary_source_scale_bounds
    {sigma d T tau : ℝ} {Q : ℕ}
    (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hT : 1 ≤ T) (hQ : 1 < Q)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMargin : -100 * d ≤ tau / 2 - sigma) :
    let a := 2 * sigma - 200 * d
    let gamma := 1 - 1 / a
    1 < a ∧ a ≤ tau ∧ 0 < gamma ∧
      (Q : ℝ) ^ a ≤ T ∧
      (Q : ℝ) ≤ T ^ (1 / a) ∧
      T ^ gamma ≤ T ^ (1 + d) / Q := by
  dsimp only
  pm_1221 sigma
  have haOne : 1 < a := by
    dsimp only [a]
    have hSigmaGap : 0 < sigma - 1 / 2 := sub_pos.mpr hsigma
    pm_4664
    linarith [hSigmaGap]
  have haPos : 0 < a := zero_lt_one.trans haOne
  have haTau : a ≤ tau := by
    dsimp only [a]
    linarith
  pm_4728 hQReal Q hQ
  have hQa : (Q : ℝ) ^ a ≤ T := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le hQReal.le haTau
  have hInvNonneg : 0 ≤ 1 / a := by positivity
  have hQRoot := Real.rpow_le_rpow
    (Real.rpow_nonneg (Nat.cast_nonneg Q) a) hQa hInvNonneg
  have hQPow : ((Q : ℝ) ^ a) ^ (1 / a) = (Q : ℝ) := by
    pm_5879
  have hQUpper : (Q : ℝ) ≤ T ^ (1 / a) := by
    simpa only [hQPow] using hQRoot
  pm_8452 gamma a
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    rw [sub_pos, div_lt_one haPos]
    exact haOne
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPowSplit : T ^ gamma * T ^ (1 / a) = T := by
    rw [← Real.rpow_add hTPos]
    dsimp only [gamma]
    calc
      T ^ (1 - 1 / a + 1 / a) = T ^ (1 : ℝ) := by
        congr 1
        field_simp [haPos.ne']
        ring
      _ = T := Real.rpow_one T
  have hRatio : T ^ gamma ≤ T / Q := by
    rw [le_div_iff₀ (by exact_mod_cast (lt_trans Nat.zero_lt_one hQ))]
    calc
      T ^ gamma * (Q : ℝ) ≤ T ^ gamma * T ^ (1 / a) := by gcongr
      _ = T := hPowSplit
  have hPowMono : T ≤ T ^ (1 + d) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (by linarith : (1 : ℝ) ≤ 1 + d)
  refine ⟨haOne, haTau, hgamma, hQa, hQUpper, ?_⟩
  exact hRatio.trans (div_le_div_of_nonneg_right hPowMono (Nat.cast_nonneg Q))

/-- A real lower bound at least two survives natural flooring with only a
factor two.  This is the exact floor bridge used for the reflected cutoff. -/
theorem half_le_natFloor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hFloor : x < (⌊x⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  nlinarith

/-- One common kernel majorant for both signs in the exact B-process on the
physical slab.  The positive sign uses the stationary estimate, while the
reversed sign uses the stronger nonstationary estimate. -/
noncomputable def mediumTypeIStationaryKernel
    (sigma T : ℝ) (Q : ℕ) : ℝ :=
  (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      (T / 4) ^ (-sigma - 1 / 2)

theorem mediumTypeIStationaryKernel_pos
    {sigma T : ℝ} {Q : ℕ} (hT : 0 < T) (hQ : 0 < Q) :
    0 < mediumTypeIStationaryKernel sigma T Q := by
  unfold mediumTypeIStationaryKernel
  positivity

theorem norm_typeIPowerReflectionIntegral_both_signs_le_mediumKernel
    {sigma T t H : ℝ} {Q M : ℕ}
    (hsigma : 0 < sigma) (hT : 0 < T)
    (htLower : T / 2 ≤ t) (_htUpper : t ≤ 3 * T)
    (hH : 0 ≤ H) (hHt : 2 * H ≤ T / 2 - 2)
    (hQ : 0 < Q) (hM : 1 ≤ M) {u : ℝ}
    (hu : u ∈ Set.Icc (-H) H) :
    ‖typeIPowerReflectionIntegral sigma (t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        mediumTypeIStationaryKernel sigma T Q ∧
      ‖typeIPowerReflectionIntegral sigma (-t + u)
        ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
        mediumTypeIStationaryKernel sigma T Q := by
  have ht : 2 ≤ t := by linarith
  have hHt' : 2 * H ≤ t - 2 := by linarith
  pm_5156 hPos norm_typeIPowerReflectionIntegral_le_on_symmetric_window ht hHt'
  have htPos : 0 < t := by linarith
  have hTwoH : 2 * H ≤ t := by linarith
  pm_5156 hNeg norm_typeIPowerReflectionIntegral_neg_le_on_symmetric_window htPos hTwoH
  have hInv : 16 / t ≤ 32 / T := by
    rw [div_le_div_iff₀ htPos hT]
    nlinarith
  have hInvNeg : 8 / t ≤ 32 / T :=
    (div_le_div_of_nonneg_right (by norm_num) htPos.le).trans hInv
  have hQuarter : T / 4 ≤ t / 2 := by linarith
  pm_7284
  have hPow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < T / 4)
    hQuarter hExp
  constructor
  · exact hPos.trans (by
      unfold mediumTypeIStationaryKernel
      gcongr)
  · calc
      ‖typeIPowerReflectionIntegral sigma (-t + u)
          ((Q : ℝ) / 2) (2 * M * Q)‖ ≤
          (8 / t) * ((Q : ℝ) / 2) ^ (-sigma) := hNeg
      _ ≤ (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) := by gcongr
      _ ≤ mediumTypeIStationaryKernel sigma T Q := by
        unfold mediumTypeIStationaryKernel
        exact le_add_of_nonneg_right (by positivity)

/-! ## Reflected endpoint exponent arithmetic -/

/- The direct exponent shortcut below is retained as design work only.  The
source-faithful assembly routes the reflected scale through the certificate's
powered/Weyl alternatives.

/-- The three real powers occurring after the medium B-process is
normalized at the reflected threshold.  This is deliberately expressed in
the original physical scale `tau = log_Q T`; doing so avoids replacing the
finite dual cutoff by an unrelated exact real power. -/
noncomputable def mediumReflectedMHHExponent (sigma tau : ℝ) : ℝ :=
  max (1 - 2 * sigma / tau)
    (min (1 + (1 - 2 * sigma) / tau)
      (2 + (2 - 6 * sigma) / tau))

/-- On the genuinely reflected branch, the loss-free B-process/MHH
exponent is bounded by the endpoint exponent.  The proof uses only the
arithmetic alternatives carried by the actual endpoint certificate. -/
theorem mediumReflectedMHHExponent_le_endpoint
    {sigma tau₀ tau : ℝ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau₀)
    (htau₀ : tau₀ < tau) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (htauUpper : tau < 4 * tau₀ / 3)
    (hNotWeyl : 6 * sigma - 3 ≤ tau) :
    mediumReflectedMHHExponent sigma tau ≤
      3 * (1 - sigma) / tau₀ := by
  have htauPos : 0 < tau := by linarith
  have htau₀Pos : 0 < tau₀ := hcert.tau0_pos
  rw [mediumReflectedMHHExponent, max_le_iff]
  constructor
  · rw [le_div_iff₀ htau₀Pos]
    field_simp [htauPos.ne']
    rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
    · by_cases hsign : 0 ≤ tau - 2 * sigma
      · have hmul := mul_le_mul_of_nonneg_left hI hsign
        nlinarith
      · nlinarith
    · by_cases hsign : 0 ≤ tau - 2 * sigma
      · have hmul := mul_le_mul_of_nonneg_left hH hsign
        nlinarith
      · nlinarith
  · rw [min_le_iff]
    by_cases hswitch : tau ≤ 4 * sigma - 1
    · right
      rw [le_div_iff₀ htau₀Pos]
      field_simp [htauPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ 2 * tau + 2 - 6 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ 2 * tau + 2 - 6 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
    · left
      have hswitch' : 4 * sigma - 1 < tau := lt_of_not_ge hswitch
      rw [le_div_iff₀ htau₀Pos]
      field_simp [htauPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hsigmaUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ tau + 1 - 2 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ tau + 1 - 2 * sigma
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
-/

/-- Uniform power bound for the common stationary kernel on a genuine
medium scale.  Both summands are put on the same `T^(-sigma-1/2)` scale;
the first uses the exact physical identity `Q^tau=T`. -/
theorem mediumTypeIStationaryKernel_le_rpow
    {sigma T tau : ℝ} {Q : ℕ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hT : 1 ≤ T) (hQ : 1 < Q) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    mediumTypeIStationaryKernel sigma T Q ≤
      (32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)) * T ^ (-sigma - 1 / 2) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4711
  have htauPos : 0 < tau := by linarith
  have hExp : -1 - sigma / tau ≤ -sigma - 1 / 2 := by
    have hprod : (sigma - 1 / 2) * (2 - tau) > 0 :=
      mul_pos (by linarith) (by linarith)
    field_simp [htauPos.ne']
    nlinarith
  have hQpow : (Q : ℝ) ^ (-sigma) = T ^ (-sigma / tau) := by
    rw [← hScale, ← Real.rpow_mul hQPos.le]
    congr 1
    field_simp [htauPos.ne']
  have hFirstPower : T ^ (-1 - sigma / tau) ≤ T ^ (-sigma - 1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hT hExp
  have hFirst : (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) ≤
      (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) := by
    rw [Real.div_rpow (by positivity : 0 ≤ (Q : ℝ)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), hQpow]
    simp only [div_eq_mul_inv, inv_inv]
    rw [← Real.rpow_neg_one]
    have hCombine : T ^ (-1 : ℝ) * T ^ (-sigma / tau) =
        T ^ (-1 - sigma / tau) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    calc
      32 * T ^ (-1 : ℝ) * (T ^ (-sigma / tau) * 2 ^ sigma) =
          (32 * 2 ^ sigma) *
            (T ^ (-1 : ℝ) * T ^ (-sigma / tau)) := by ring
      _ = (32 * 2 ^ sigma) * T ^ (-1 - sigma / tau) := by rw [hCombine]
      _ ≤ (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) := by gcongr
  have hSecondEq : (T / 4) ^ (-sigma - 1 / 2) =
      4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2) := by
    pm_7445 hTPos.le
    have hInv : ((4 : ℝ) ^ (-sigma - 1 / 2))⁻¹ =
        (4 : ℝ) ^ (sigma + 1 / 2) := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring
    rw [div_eq_mul_inv, hInv]
    ring
  unfold mediumTypeIStationaryKernel
  rw [hSecondEq]
  calc
    (32 / T) * ((Q : ℝ) / 2) ^ (-sigma) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            (4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2)) ≤
        (32 * 2 ^ sigma) * T ^ (-sigma - 1 / 2) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            (4 ^ (sigma + 1 / 2) * T ^ (-sigma - 1 / 2)) := by gcongr
    _ = (32 * 2 ^ sigma +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            4 ^ (sigma + 1 / 2)) * T ^ (-sigma - 1 / 2) := by ring

/- Elementary ratio bridge used three times in the reflected MHH bound.
It keeps the threshold constant and all real powers explicit.
theorem natPow_div_natPow_le_rpow
    {T C X L mu v : ℝ} {n : ℕ}
    (hT : 0 < T) (hC : 0 < C) (hX : 0 ≤ X) (hL : 0 < L)
    (hXUpper : X ≤ T ^ mu) (hLLower : T ^ v / C ≤ L) :
    X ^ n / L ^ n ≤ C ^ n * T ^ ((n : ℝ) * (mu - v)) := by
  have hBasePos : 0 < T ^ v / C := by positivity
  have hNum : X ^ n ≤ (T ^ mu) ^ n := pow_le_pow_left₀ hX hXUpper n
  have hDen : (T ^ v / C) ^ n ≤ L ^ n :=
    pow_le_pow_left₀ hBasePos.le hLLower n
  calc
    X ^ n / L ^ n ≤ (T ^ mu) ^ n / (T ^ v / C) ^ n := by
      exact div_le_div hNum hDen (pow_pos hBasePos n).le (pow_pos hL n)
    _ = C ^ n * T ^ ((n : ℝ) * (mu - v)) := by
      rw [div_pow, div_div, ← mul_div_assoc]
      field_simp [hC.ne']
      rw [← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le,
        ← Real.rpow_sub hT]
      congr 1
      ring

/-- Exact finite envelope for the three MHH terms after reflection.  The
input `mu` is an upper exponent for the literal floored dual length and `v`
is a lower exponent for its actual normalized threshold. -/
theorem reflected_mhh_terms_le_power_envelope
    {T C L mu v : ℝ} {P M : ℕ}
    (hT : 1 ≤ T) (hC : 1 ≤ C) (hL : 0 < L)
    (hPM : P ≤ M) (hM : (M : ℝ) ≤ T ^ mu)
    (hLLower : T ^ v / C ≤ L) :
    (P : ℝ) ^ 2 / L ^ 2 +
        (3 * T) * min ((P : ℝ) / L ^ 2)
          ((P : ℝ) ^ 4 / L ^ 6) ≤
      C ^ 6 * (T ^ (2 * (mu - v)) +
        3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v))) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hCPos : 0 < C := zero_lt_one.trans_le hC
  have hPUpper : (P : ℝ) ≤ T ^ mu := by
    exact_mod_cast hPM
    exact_mod_cast hPM
  have hPUpper' : (P : ℝ) ≤ (M : ℝ) := by exact_mod_cast hPM
  have hPToT : (P : ℝ) ≤ T ^ mu := hPUpper'.trans hM
  have hTwo := natPow_div_natPow_le_rpow hTPos hCPos
    (Nat.cast_nonneg P) hL hPToT hLLower (n := 2)
  have hOneNumerator : (P : ℝ) / L ^ 2 ≤
      C ^ 2 * T ^ (mu - 2 * v) := by
    have hDen := natPow_div_natPow_le_rpow hTPos hCPos
      (Nat.cast_nonneg P) hL hPToT hLLower (n := 1)
    have hLInv : 1 / L ≤ C * T ^ (-v) := by
      simpa only [pow_one, one_div] using hDen
    have hLInvNonneg : 0 ≤ 1 / L := by positivity
    have hPNonneg : 0 ≤ (P : ℝ) := Nat.cast_nonneg P
    calc
      (P : ℝ) / L ^ 2 = ((P : ℝ) / L) * (1 / L) := by field_simp
      _ ≤ (C * T ^ (mu - v)) * (C * T ^ (-v)) := by
        gcongr
      _ = C ^ 2 * T ^ (mu - 2 * v) := by
        rw [← Real.rpow_add hTPos]
        ring
  have hFour := natPow_div_natPow_le_rpow hTPos hCPos
    (Nat.cast_nonneg P) hL hPToT hLLower (n := 4)
  have hFourSix : (P : ℝ) ^ 4 / L ^ 6 ≤
      C ^ 6 * T ^ (4 * mu - 6 * v) := by
    have hInvTwo : 1 / L ^ 2 ≤ C ^ 2 * T ^ (-2 * v) := by
      have hZero := natPow_div_natPow_le_rpow hTPos hCPos
        (show (0 : ℝ) ≤ 1 by norm_num) hL
        (show (1 : ℝ) ≤ T ^ (0 : ℝ) by simp) hLLower (n := 2)
      simpa only [one_pow, zero_sub, Nat.cast_ofNat, zero_mul, Real.rpow_zero,
        mul_one] using hZero
    calc
      (P : ℝ) ^ 4 / L ^ 6 =
          ((P : ℝ) ^ 4 / L ^ 4) * (1 / L ^ 2) := by field_simp
      _ ≤ (C ^ 4 * T ^ (4 * (mu - v))) *
          (C ^ 2 * T ^ (-2 * v)) := by gcongr
      _ = C ^ 6 * T ^ (4 * mu - 6 * v) := by
        rw [← Real.rpow_add hTPos]
        ring
  have hCtwoSix : C ^ 2 ≤ C ^ 6 := by nlinarith [sq_nonneg (C ^ 2 - 1)]
  have hTermOne : (P : ℝ) ^ 2 / L ^ 2 ≤
      C ^ 6 * T ^ (2 * (mu - v)) := hTwo.trans (by gcongr)
  have hTermTwo : (3 * T) * min ((P : ℝ) / L ^ 2)
        ((P : ℝ) ^ 4 / L ^ 6) ≤
      C ^ 6 * (3 * min (T ^ (1 + mu - 2 * v))
        (T ^ (1 + 4 * mu - 6 * v))) := by
    have hA : T * ((P : ℝ) / L ^ 2) ≤
        C ^ 6 * T ^ (1 + mu - 2 * v) := by
      calc
        T * ((P : ℝ) / L ^ 2) ≤
            T * (C ^ 2 * T ^ (mu - 2 * v)) := by gcongr
        _ = C ^ 2 * T ^ (1 + mu - 2 * v) := by
          rw [← Real.rpow_one T, ← Real.rpow_add hTPos]
          ring
        _ ≤ C ^ 6 * T ^ (1 + mu - 2 * v) := by gcongr
    have hB : T * ((P : ℝ) ^ 4 / L ^ 6) ≤
        C ^ 6 * T ^ (1 + 4 * mu - 6 * v) := by
      calc
        T * ((P : ℝ) ^ 4 / L ^ 6) ≤
            T * (C ^ 6 * T ^ (4 * mu - 6 * v)) := by gcongr
        _ = C ^ 6 * T ^ (1 + 4 * mu - 6 * v) := by
          rw [← Real.rpow_one T, ← Real.rpow_add hTPos]
          ring
    calc
      (3 * T) * min ((P : ℝ) / L ^ 2)
          ((P : ℝ) ^ 4 / L ^ 6) =
          3 * min (T * ((P : ℝ) / L ^ 2))
            (T * ((P : ℝ) ^ 4 / L ^ 6)) := by
              rw [mul_min_of_nonneg (by positivity : 0 ≤ T)]
              ring
      _ ≤ 3 * min (C ^ 6 * T ^ (1 + mu - 2 * v))
          (C ^ 6 * T ^ (1 + 4 * mu - 6 * v)) := by gcongr
      _ = C ^ 6 * (3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v))) := by
            rw [← mul_min_of_nonneg (by positivity : 0 ≤ C ^ 6)]
            ring
  linarith

/-- The `d`, detector and logarithmic losses introduced by the literal dual
cutoff fit in one explicit exponent budget. -/
theorem reflected_power_envelope_le_endpoint
    {sigma tau₀ tau d u eta T : ℝ}
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau₀)
    (htau₀ : tau₀ < tau) (htauOne : 1 < tau) (htauTwo : tau < 2)
    (htauUpper : tau < 4 * tau₀ / 3)
    (hNotWeyl : 6 * sigma - 3 ≤ tau)
    (hd : 0 ≤ d) (hu : 0 ≤ u) (huD : u ≤ d) (heta : 0 ≤ eta)
    (hT : 1 ≤ T) :
    let mu := 1 + d - 1 / tau
    let v := 1 / 2 - u - d * sigma + (sigma - 1) / tau - eta
    T ^ (2 * (mu - v)) +
        3 * min (T ^ (1 + mu - 2 * v))
          (T ^ (1 + 4 * mu - 6 * v)) ≤
      4 * T ^ (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta) := by
  dsimp only
  let E := mediumReflectedMHHExponent sigma tau
  have hE := mediumReflectedMHHExponent_le_endpoint hsigmaLower hsigmaUpper
    hcert htau₀ htauOne htauTwo htauUpper hNotWeyl
  have hSigmaNonneg : 0 ≤ sigma := by linarith
  have hLoss₁ :
      2 * ((1 + d - 1 / tau) -
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        (1 - 2 * sigma / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hLoss₂ :
      1 + (1 + d - 1 / tau) -
          2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
        (1 + (1 - 2 * sigma) / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hLoss₃ :
      1 + 4 * (1 + d - 1 / tau) -
          6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
        (2 + (2 - 6 * sigma) / tau) + 16 * d + 6 * eta := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hsigmaUpper.le)]
  have hE₁ : 1 - 2 * sigma / tau ≤ E := by
    dsimp only [E, mediumReflectedMHHExponent]
    exact le_max_left _ _
  have hEmin : min (1 + (1 - 2 * sigma) / tau)
      (2 + (2 - 6 * sigma) / tau) ≤ E := by
    dsimp only [E, mediumReflectedMHHExponent]
    exact le_max_right _ _
  have hExp₁ :
      2 * ((1 + d - 1 / tau) -
          (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta :=
    hLoss₁.trans (add_le_add_right (hE₁.trans hE) _)
  have hMinLoss :
      min
          (1 + (1 + d - 1 / tau) -
            2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))
          (1 + 4 * (1 + d - 1 / tau) -
            6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        min (1 + (1 - 2 * sigma) / tau)
            (2 + (2 - 6 * sigma) / tau) + 16 * d + 6 * eta := by
    have hmin := min_le_min hLoss₂ hLoss₃
    simpa only [min_add_add_right] using hmin
  have hExpMin :
      min
          (1 + (1 + d - 1 / tau) -
            2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))
          (1 + 4 * (1 + d - 1 / tau) -
            6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) ≤
        3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta :=
    hMinLoss.trans (add_le_add_right (hEmin.trans hE) _)
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hPow₁ := Real.rpow_le_rpow_of_exponent_le hT hExp₁
  have hPowMin := Real.rpow_le_rpow_of_exponent_le hT hExpMin
  have hMinPow : min
      (T ^ (1 + (1 + d - 1 / tau) -
        2 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)))
      (T ^ (1 + 4 * (1 + d - 1 / tau) -
        6 * (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta))) ≤
      T ^ (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta) := by
    rw [← Real.rpow_min hTPos]
    exact hPowMin
  nlinarith [Real.rpow_nonneg hTPos.le
    (3 * (1 - sigma) / tau₀ + 16 * d + 6 * eta)]
-/

/-- Inverting the physical scale identity is legitimate for the positive
natural base and positive logarithmic scale used by the medium branch. -/
theorem natCast_eq_rpow_inv_of_rpow_eq
    {T tau : ℝ} {Q : ℕ} (hQ : 1 < Q) (htau : 0 < tau)
    (hScale : (Q : ℝ) ^ tau = T) :
    (Q : ℝ) = T ^ (1 / tau) := by
  pm_5880
  have hmul : tau * (1 / tau) = 1 := by field_simp [htau.ne']
  rw [hmul, Real.rpow_one]

section
variable {T d tau : ℝ} {Q : ℕ} (hT : 8 ≤ T)
include T d tau Q hT
/-- On a medium scale the expanded dual cutoff is still below the literal
sharp zeta cutoff.  Consequently its `Nat.clog` loss is already covered by
the source-selection logarithmic budget. -/
theorem mediumTypeIDualCutoff_le_sharpZetaCutoff (_hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hQ : 1 < Q) (_htau : 0 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    mediumTypeIDualCutoff T d Q ≤ ⌊sharpZetaCutoff T⌋₊ := by
  pm_4185
  pm_4728 hQReal Q hQ
  have hSqrt : T ^ (1 / 2 : ℝ) ≤ (Q : ℝ) := by
    pm_3991 hScale
    pm_5796 tau
  have hTd : T ^ d ≤ (Q : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hTOne hdHalf).trans hSqrt
  have hSplit : T ^ (1 + d) = T * T ^ d := by
    rw [Real.rpow_add hTPos, Real.rpow_one]
  have hRatio : T ^ (1 + d) / Q ≤ T := by
    pm_1455 hSplit div_le_iff₀ Q
    nlinarith
  have hSharp : T ≤ sharpZetaCutoff T :=
    (show T ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  unfold mediumTypeIDualCutoff
  exact Nat.floor_mono (hRatio.trans hSharp)

/-- The exact logarithmic product needed by the reflected normalized
threshold.  No new logarithmic estimate is required once the dual cutoff is
proved to lie below the sharp cutoff. -/
theorem medium_reflected_clog_product_le (hd : 0 ≤ d) (hdHalf : d ≤ 1 / 2)
    (hQ : 1 < Q) (htau : 0 < tau) (htauTwo : tau < 2)
    (hScale : (Q : ℝ) ^ tau = T) :
    ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (mediumTypeIDualCutoff T d Q) : ℝ) ≤
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
        (Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) : ℝ) := by
  have hM := mediumTypeIDualCutoff_le_sharpZetaCutoff hT hd hdHalf hQ htau
    htauTwo hScale
  have hA : ⌊sharpZetaCutoff T⌋₊ ≤ ⌊sharpZetaCutoff T⌋₊ + 1 := by omega
  have hClog : Nat.clog 2 (mediumTypeIDualCutoff T d Q) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) :=
    Nat.clog_mono_right 2 (hM.trans hA)
  gcongr
end

/-- The fixed constant in the normalized reflected-threshold lower bound. -/
noncomputable def mediumReflectedThresholdConstant (Clog CK : ℝ) : ℝ :=
  max 1 ((128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1)) /
    (3 * Real.pi))

/-- Lower bound for the literal normalized reflected threshold.  It uses
the actual detector threshold, kernel, natural dual cutoff and both `clog`
factors; the displayed exponent is exactly the one used in the reflected
MHH arithmetic above.  The constant is displayed explicitly, making its
uniformity in `T`, the source scale and the selected dyadic block literal. -/
theorem medium_reflected_threshold_explicit_lower
    {sigma T tau d u eta Clog CK : ℝ} {Q M : ℕ}
    (hsigma : 0 ≤ sigma) (hT : 1 ≤ T) (hQ : 1 < Q)
    (hM : 1 < M) (htau : 0 < tau)
    (hScale : (Q : ℝ) ^ tau = T)
    (hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau))
    (hClog : 0 < Clog)
    (hLogs :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ eta)
    (hCK : 0 < CK)
    (hKernel : mediumTypeIStationaryKernel sigma T Q ≤
      CK * T ^ (-sigma - 1 / 2)) :
    let V := ((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
    let R := (Real.pi * V) /
        (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
          (typeIDyadicCutoffMellinL1 + 1))
    let S := R / (2 * (M : ℝ) ^ sigma)
    T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) /
        mediumReflectedThresholdConstant Clog CK ≤
      S / Nat.clog 2 M := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4711
  pm_117 hMPos M
  pm_4815 hClogMNat M hM
  pm_5115 hClogM M hClogMNat
  have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    pm_4735
  have hClogA : (0 : ℝ) <
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) := by positivity
  pm_895
  have hKernelPos : 0 < mediumTypeIStationaryKernel sigma T Q :=
    mediumTypeIStationaryKernel_pos hTPos (lt_trans Nat.zero_lt_one hQ)
  pm_6537 hQEq Q tau hQ htau
  have hMPow : (M : ℝ) ^ sigma ≤
      T ^ (sigma * (1 + d - 1 / tau)) := by
    calc
      (M : ℝ) ^ sigma ≤ (T ^ (1 + d - 1 / tau)) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg M) hMUpper hsigma
      _ = T ^ (sigma * (1 + d - 1 / tau)) := by
        rw [← Real.rpow_mul hTPos.le]
        ring_nf
  pm_5797 C₀
  let C : ℝ := max 1 C₀
  pm_116 hC₀ C₀
  pm_4884 hC C
  change T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) / C ≤ _
  have hDenBound :
      (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ)) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            ((M : ℝ) ^ sigma) ≤
        (Clog * CK) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) := by
    calc
      (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ)) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            ((M : ℝ) ^ sigma) ≤
        (Clog * T ^ eta) * T ^ (1 / tau) *
          (CK * T ^ (-sigma - 1 / 2)) *
            T ^ (sigma * (1 + d - 1 / tau)) := by
              rw [hQEq]
              gcongr
      _ = (Clog * CK) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) := by
            have hPowCombine :
                T ^ eta * T ^ (1 / tau) * T ^ (-sigma - 1 / 2) *
                    T ^ (sigma * (1 + d - 1 / tau)) =
                  T ^ (eta + 1 / tau - sigma - 1 / 2 +
                    sigma * (1 + d - 1 / tau)) := by
              rw [← Real.rpow_add hTPos, ← Real.rpow_add hTPos,
                ← Real.rpow_add hTPos]
              congr 1
              ring
            rw [← hPowCombine]
            ring
  have hCore :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) / C₀ ≤
        (Real.pi * (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) /
          (2 * (M : ℝ) ^ sigma) / Nat.clog 2 M := by
    let LA : ℝ := (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
    let LM : ℝ := Nat.clog 2 M
    let K₀ : ℝ := mediumTypeIStationaryKernel sigma T Q
    let mass : ℝ := typeIDyadicCutoffMellinL1 + 1
    have hLA : 0 < LA := by simpa only [LA] using hClogA
    have hLM : 0 < LM := by simpa only [LM] using hClogM
    have hK₀ : 0 < K₀ := by simpa only [K₀] using hKernelPos
    have hmass : 0 < mass := by simpa only [mass] using hMass
    let DBig : ℝ := 128 * LA * LM * (Q : ℝ) * K₀ * mass * (M : ℝ) ^ sigma
    pm_116 hDBig DBig
    have hRhs :
        (Real.pi * (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) /
          (2 * (M : ℝ) ^ sigma) / Nat.clog 2 M =
        (3 * Real.pi * T ^ (-u)) / DBig := by
      dsimp only [DBig, LA, LM, K₀, mass]
      field_simp
      ring
    rw [hRhs, div_le_div_iff₀ hC₀ hDBig]
    have hPowEq :
        T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) *
          T ^ (eta + 1 / tau - sigma - 1 / 2 +
            sigma * (1 + d - 1 / tau)) = T ^ (-u) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    have hScaled :
        (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
            (Nat.clog 2 M : ℝ) * (Q : ℝ) *
            mediumTypeIStationaryKernel sigma T Q * ((M : ℝ) ^ sigma)) *
            T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) ≤
          (Clog * CK) * T ^ (-u) := by
      calc
        _ ≤ ((Clog * CK) *
            T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau))) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) := by
                gcongr
        _ = (Clog * CK) *
            (T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau)) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) := by
                ring
        _ = (Clog * CK) * T ^ (-u) := by
          rw [mul_comm
            (T ^ (eta + 1 / tau - sigma - 1 / 2 +
              sigma * (1 + d - 1 / tau)))
            (T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)),
            hPowEq]
    dsimp only [DBig, LA, LM, K₀, mass, C₀]
    calc
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta) *
          (128 *
            ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
            (Nat.clog 2 M : ℝ) * (Q : ℝ) *
            mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1) * (M : ℝ) ^ sigma) =
          (128 * (typeIDyadicCutoffMellinL1 + 1)) *
            ((((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
              (Nat.clog 2 M : ℝ) * (Q : ℝ) *
              mediumTypeIStationaryKernel sigma T Q * ((M : ℝ) ^ sigma)) *
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - eta)) := by ring
      _ ≤ (128 * (typeIDyadicCutoffMellinL1 + 1)) *
          ((Clog * CK) * T ^ (-u)) := by gcongr
      _ = 3 * Real.pi * T ^ (-u) *
          (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1) /
            (3 * Real.pi)) := by field_simp [Real.pi_ne_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
    hC₀ (le_max_right (1 : ℝ) C₀)).trans hCore

/-- On every genuine medium source scale, the exponent in the normalized
reflected threshold has a fixed positive margin.  The estimate uses the
literal `u = d^4` and the later choice `eta = d`; no asymptotic `o(1)` is
inserted. -/
theorem medium_reflected_threshold_exponent_lower
    {sigma tau d u : ℝ}
    (_hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (htau : 1 < tau) (hd : 0 < d)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d) :
    (sigma - 1 / 2) / 2 ≤
      1 / 2 - u - d * sigma + (sigma - 1) / tau - d := by
  have htauPos : 0 < tau := by linarith
  have hFrac : sigma - 1 ≤ (sigma - 1) / tau := by
    rw [le_div_iff₀ htauPos]
    have hneg : sigma - 1 < 0 := by linarith
    nlinarith
  have hSmall : 3 * d ≤ (sigma - 1 / 2) / 2 := by
    pm_4686 hgap sigma
    nlinarith
  pm_8786 hd.le
  linarith

/-- The normalization loss `P^sigma/L` of a retained reflected dyadic block
costs at most `T^(4d)`, up to the fixed threshold constant.  This is the
finite algebraic cancellation behind the powered reflected route. -/
theorem reflected_normalization_loss_le_four_d
    {sigma tau d u T C L : ℝ} {P M : ℕ}
    (hsigmaHalf : 1 / 2 ≤ sigma) (hsigmaUpper : sigma < 1)
    (htau : 1 < tau) (htauTwo : tau < 2)
    (hd : 0 ≤ d) (huD : u ≤ d)
    (hT : 1 ≤ T) (hC : 1 ≤ C) (hL : 0 < L)
    (hPM : P ≤ M)
    (hM : (M : ℝ) ≤ T ^ (1 + d - 1 / tau))
    (hLLower :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) / C ≤ L) :
    max 1 ((P : ℝ) ^ sigma / L) ≤ C * T ^ (4 * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have htauPos : 0 < tau := by linarith
  have hPToM : (P : ℝ) ^ sigma ≤ (M : ℝ) ^ sigma :=
    Real.rpow_le_rpow (Nat.cast_nonneg P) (by exact_mod_cast hPM) (by linarith)
  have hMPow : (M : ℝ) ^ sigma ≤
      T ^ (sigma * (1 + d - 1 / tau)) := by
    calc
      (M : ℝ) ^ sigma ≤ (T ^ (1 + d - 1 / tau)) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg M) hM (by linarith)
      _ = T ^ (sigma * (1 + d - 1 / tau)) := by
        rw [← Real.rpow_mul hTPos.le]
        ring_nf
  pm_5798 v
  have hBasePos : 0 < T ^ v / C := by dsimp only [v]; positivity
  have hRatio : (P : ℝ) ^ sigma / L ≤
      C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
    calc
      (P : ℝ) ^ sigma / L ≤
          T ^ (sigma * (1 + d - 1 / tau)) / (T ^ v / C) :=
        (div_le_div_of_nonneg_right (hPToM.trans hMPow) hL.le).trans
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hTPos.le _)
            hBasePos hLLower)
      _ = C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
        calc
          T ^ (sigma * (1 + d - 1 / tau)) / (T ^ v / C) =
              C * (T ^ (sigma * (1 + d - 1 / tau)) / T ^ v) := by
                field_simp [show C ≠ 0 by linarith,
                  (Real.rpow_pos_of_pos hTPos v).ne']
          _ = C * T ^ (sigma * (1 + d - 1 / tau) - v) := by
                rw [← Real.rpow_sub hTPos]
  have hCoreNonpos :
      sigma - 1 / 2 + (1 - 2 * sigma) / tau ≤ 0 := by
    have hProd : (2 * sigma - 1) * (tau - 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hNum : (sigma - 1 / 2) * tau + (1 - 2 * sigma) ≤ 0 := by
      nlinarith
    rw [show sigma - 1 / 2 + (1 - 2 * sigma) / tau =
      ((sigma - 1 / 2) * tau + (1 - 2 * sigma)) / tau by
        field_simp [htauPos.ne']]
    exact div_nonpos_of_nonpos_of_nonneg hNum htauPos.le
  have hExp : sigma * (1 + d - 1 / tau) - v ≤ 4 * d := by
    pm_8786 hd
    have hLoss : u + d + 2 * d * sigma ≤ 4 * d := by linarith
    dsimp only [v]
    have hIdentity :
        sigma * (1 + d - 1 / tau) -
            (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) =
          (sigma - 1 / 2 + (1 - 2 * sigma) / tau) +
            (u + d + 2 * d * sigma) := by ring
    rw [hIdentity]
    linarith
  have hRatioFinal : (P : ℝ) ^ sigma / L ≤ C * T ^ (4 * d) :=
    hRatio.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT hExp) (by linarith : 0 ≤ C))
  have hOne : 1 ≤ C * T ^ (4 * d) := by
    pm_6094
    nlinarith [mul_le_mul hC hPow (by norm_num) (by linarith : 0 ≤ C)]
  exact max_le hOne hRatioFinal

/-- Uniform powered-threshold envelope for a reflected dyadic block.  The
factor `T^(4*d*k)` is exactly the `k`-fold normalization cost established by
`reflected_normalization_loss_le_four_d`; the remaining factors are the same
finite powered MHH loss used by the source-facing consumers. -/
theorem reflected_powered_threshold_loss_le_envelope
    {C₀ C d sigma T D : ℝ} {P k B : ℕ}
    (hC₀ : 1 ≤ C₀) (hC : 1 ≤ C) (hd : 0 ≤ d)
    (hsigmaOne : sigma ≤ 1) (hT : Real.exp 1 ≤ T)
    (hD : 0 < D) (hDUpper : D ≤ C₀ * T ^ (4 * d))
    (hP : 0 < P) (hk : 0 < k) (hkB : k ≤ B) :
    let E := (2 : ℝ) ^ B * C₀ ^ B * C
    typeIIPoweredThresholdLoss C ((P : ℝ) ^ sigma) D d sigma P k ≤
      1 + T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k (P ^ k) := by
  dsimp only
  pm_8227 C₀ C
  have hTOne : 1 ≤ T := by
    pm_4748
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hLogOne : 1 ≤ Real.log T := by
    pm_6160 hT
  have hLogFactor : 1 ≤ (4 * Real.log T) ^ k := by
    exact one_le_pow₀ (by nlinarith)
  have hDPow : D ^ k ≤ C₀ ^ B * T ^ (4 * d * k) := by
    have hTPow : (T ^ (4 * d)) ^ k = T ^ (4 * d * (k : ℝ)) := by
      calc
        (T ^ (4 * d)) ^ k = (T ^ (4 * d)) ^ (k : ℝ) :=
          (Real.rpow_natCast (T ^ (4 * d)) k).symm
        _ = T ^ ((4 * d) * (k : ℝ)) :=
          (Real.rpow_mul hTPos.le (4 * d) k).symm
    calc
      D ^ k ≤ (C₀ * T ^ (4 * d)) ^ k :=
        pow_le_pow_left₀ hD.le hDUpper k
      _ = C₀ ^ k * (T ^ (4 * d)) ^ k := by rw [mul_pow]
      _ ≤ C₀ ^ B * (T ^ (4 * d)) ^ k := by
        gcongr
      _ = C₀ ^ B * T ^ (4 * d * k) := by rw [hTPow]
  pm_74 hPReal P hP
  have hCancel :
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma) /
          (((P : ℝ) ^ sigma) ^ k) = (((2 : ℝ) ^ k) ^ sigma) := by
    pm_5368 hPReal.le
    have hPPow : (((P : ℝ) ^ k) ^ sigma) = ((P : ℝ) ^ sigma) ^ k := by
      calc
        (((P : ℝ) ^ k) ^ sigma) = (((P : ℝ) ^ (k : ℝ)) ^ sigma) := by
          rw [Real.rpow_natCast]
        _ = (P : ℝ) ^ ((k : ℝ) * sigma) :=
          (Real.rpow_mul hPReal.le k sigma).symm
        _ = (P : ℝ) ^ (sigma * (k : ℝ)) := by congr 1; ring
        _ = (((P : ℝ) ^ sigma) ^ (k : ℝ)) :=
          Real.rpow_mul hPReal.le sigma k
        _ = ((P : ℝ) ^ sigma) ^ k := Real.rpow_natCast _ _
    rw [hPPow]
    field_simp [(Real.rpow_pos_of_pos hPReal sigma).ne']
  pm_4749 sigma hsigmaOne
  have hScale :
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) ≤
        ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d)) := by
    pm_4753 P
    have hBaseNat : 1 ≤ 2 ^ k * P ^ k := by
      exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ hP.ne'))
    have hBaseReal : (1 : ℝ) ≤
        ((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ) := by exact_mod_cast hBaseNat
    exact Real.rpow_le_rpow_of_exponent_le hBaseReal (by linarith)
  have hRaw :
      (((((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma) * D ^ k *
          (C * (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) * k) /
            (((P : ℝ) ^ sigma) ^ k)) ≤
        T ^ (4 * d * k) *
          classicalTypeIIPowerLoss E d T k (P ^ k) := by
    rw [div_eq_mul_inv]
    pm_4752 P sigma
    dsimp only [classicalTypeIIPowerLoss, E]
    calc
      (((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma * D ^ k *
            (C * (((2 ^ k * P ^ k : ℕ) : ℝ) ^ d)) * (k : ℝ) *
              (((P : ℝ) ^ sigma) ^ k)⁻¹) =
          ((((2 ^ k * P ^ k : ℕ) : ℝ) ^ sigma *
              (((P : ℝ) ^ sigma) ^ k)⁻¹) * D ^ k *
                (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) * (k : ℝ)) := by
            push_cast
            ring
      _ = (((2 : ℝ) ^ k) ^ sigma * D ^ k *
            (C * ((2 ^ k * P ^ k : ℕ) : ℝ) ^ d) * (k : ℝ)) := by
          rw [hIdentity]
      _ ≤ (2 : ℝ) ^ B * (C₀ ^ B * T ^ (4 * d * k)) *
            (C * ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d))) *
              (k : ℝ) := by gcongr
      _ ≤ (2 : ℝ) ^ B * (C₀ ^ B * T ^ (4 * d * k)) *
            (C * ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d))) *
              (k : ℝ) * (4 * Real.log T) ^ k := by
          exact le_mul_of_one_le_right (by positivity) hLogFactor
      _ = T ^ (4 * d * k) *
          (((2 : ℝ) ^ B * C₀ ^ B * C) *
            ((((2 : ℝ) ^ k) * ((P ^ k : ℕ) : ℝ)) ^ (2 * d)) *
              (k : ℝ) * (4 * Real.log T) ^ k) := by ring
  unfold typeIIPoweredThresholdLoss
  apply max_le
  · have hLossNonneg : 0 ≤ T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k (P ^ k) := by
      dsimp only [classicalTypeIIPowerLoss, E]
      positivity
    linarith
  · exact hRaw.trans (le_add_of_nonneg_left (by norm_num))

/-- A fixed positive-power threshold forces the dyadic block selected from
a unit-coefficient family to have uniformly bounded logarithmic height
scale.  Both the natural cast and the eventual constant absorption remain
explicit. -/
theorem eventually_threshold_forces_logarithmic_scale_upper
    {g C : ℝ} (hg : 0 < g) (hC : 1 ≤ C) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ {T L : ℝ} {P : ℕ}, T₀ ≤ T →
      0 < L → T ^ g / C ≤ L → L ≤ (P : ℝ) →
      1 < P ∧ typeILogarithmicScale T P ≤ 2 / g := by
  pm_4910 hhalf g
  have hTop := tendsto_rpow_atTop hhalf
  have hEventually := (tendsto_atTop.1 hTop) (max 2 C)
  pm_4712
  let T₀ : ℝ := max 2 Tpow
  pm_4889
  intro T L P hT hL hTL hLP
  pm_4174
  pm_4713
  have hTPos : 0 < T := by linarith
  have hRoot : max 2 C ≤ T ^ (g / 2) := hTpow T hTPow
  have hRootTwo : 2 ≤ T ^ (g / 2) := (le_max_left _ _).trans hRoot
  have hRootC : C ≤ T ^ (g / 2) := (le_max_right _ _).trans hRoot
  have hSplit : T ^ g = T ^ (g / 2) * T ^ (g / 2) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hRootToRatio : T ^ (g / 2) ≤ T ^ g / C := by
    rw [hSplit, le_div_iff₀ (by linarith : 0 < C)]
    exact mul_le_mul_of_nonneg_left hRootC (Real.rpow_nonneg hTPos.le _)
  have hRootP : T ^ (g / 2) ≤ (P : ℝ) :=
    hRootToRatio.trans (hTL.trans hLP)
  have hPtwo : 2 ≤ P := by exact_mod_cast hRootTwo.trans hRootP
  have hPOne : 1 < P := by omega
  have hRaise := Real.rpow_le_rpow
    (Real.rpow_nonneg hTPos.le _) hRootP (by positivity : 0 ≤ 2 / g)
  have hCancel : (T ^ (g / 2)) ^ (2 / g) = T := by
    rw [← Real.rpow_mul hTPos.le]
    have : g / 2 * (2 / g) = 1 := by field_simp [hg.ne']
    rw [this, Real.rpow_one]
  pm_5568 Real.logb_le_iff_le_rpow hTPos
  simpa only [hCancel] using hRaise

/-- The source-normalized reflection radius grows by a fixed positive power.
This is the quantitative content of the complementary-margin lemma after
allowing one `T^d` for the source `clog` loss. -/
theorem medium_reflection_radius_exponent_pos
    {sigma d u tau : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d)
    (hMargin : 2 * sigma - 200 * d ≤ tau) :
    0 < sigma + 1 / 2 - 1 / tau - u - d := by
  pm_1221 sigma
  have haOne : 1 < a := by
    dsimp only [a]
    pm_4664
    linarith
  have htau : 1 < tau := haOne.trans_le (by simpa only [a] using hMargin)
  have hInv : 1 / tau ≤ 1 / a := by
    exact one_div_le_one_div_of_le (by linarith) (by simpa only [a] using hMargin)
  have hProduct : 1 < (sigma + 1 / 2 - u - d) * a := by
    dsimp only [a]
    pm_4686 hSigmaGap sigma
    have hTwoD : 2 * d ≤ (sigma - 1 / 2) / 500 := by linarith
    nlinarith [mul_pos hSigmaGap hSigmaGap]
  have hCore : 1 / a < sigma + 1 / 2 - u - d := by
    rw [div_lt_iff₀ (by linarith : 0 < a)]
    simpa only [one_mul] using hProduct
  linarith

/-- Eventual finite form of the preceding radius growth.  The proof keeps
the exact source `clog`, Fourier kernel constant and Mellin mass. -/
theorem eventually_medium_reflection_radius_two
    {sigma d u : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T tau : ℝ} {Q : ℕ}, T₀ ≤ T →
      1 < Q → 1 < tau → tau < 2 →
      (Q : ℝ) ^ tau = T →
      2 * sigma - 200 * d ≤ tau →
      2 ≤ (Real.pi *
        (((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) /
        (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
          (typeIDyadicCutoffMellinL1 + 1)) := by
  have hrho : 0 < sigma + 1 / 2 -
      1 / (2 * sigma - 200 * d) - u - d :=
    medium_reflection_radius_exponent_pos hsigma hd hdGap huD le_rfl
  pm_4670
  pm_4669
  pm_116 hCK CK
  pm_5797 D
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos
      (mul_pos (mul_pos (mul_pos (by norm_num) hClog) hCK)
        (by linarith [typeIDyadicCutoffMellinL1_nonneg]))
      (mul_pos (by norm_num) Real.pi_pos)
  have hPowTop := tendsto_rpow_atTop hrho
  have hEventually := (tendsto_atTop.1 hPowTop) (2 * D)
  pm_4667
  intro T tau Q hT hQ htauOne htauTwo hScale hMargin
  pm_4666
  pm_4169
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQ htauOne htauTwo hScale
  have hLogProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      pm_4735
    pm_4668
  pm_4665
  pm_4939 hQEq Q tau hQ hScale
  have hDen :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q ≤
        (Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2) := by
    calc
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q ≤
        (Clog * T ^ d) * T ^ (1 / tau) *
          (CK * T ^ (-sigma - 1 / 2)) := by
            rw [hQEq]
            gcongr
            exact (mediumTypeIStationaryKernel_pos hTPos
              (lt_trans Nat.zero_lt_one hQ)).le
      _ = (Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2) := by
        have hPowCombine :
            T ^ d * T ^ (1 / tau) * T ^ (-sigma - 1 / 2) =
              T ^ (d + 1 / tau - sigma - 1 / 2) := by
          pm_344 hTPos
          ring
        rw [← hPowCombine]
        ring
  have hExpMono : sigma + 1 / 2 - 1 / (2 * sigma - 200 * d) - u - d ≤
      sigma + 1 / 2 - 1 / tau - u - d := by
    have haPos : 0 < 2 * sigma - 200 * d := by
      have := medium_reflection_radius_exponent_pos hsigma hd hdGap huD le_rfl
      have haOne : 1 < 2 * sigma - 200 * d := by
        pm_4664
        linarith
      exact zero_lt_one.trans haOne
    have hInv := one_div_le_one_div_of_le haPos hMargin
    linarith
  have hPowLarge : 2 * D ≤
      T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
    exact (hTpow T hTPow).trans
      (Real.rpow_le_rpow_of_exponent_le hTOne hExpMono)
  have hPowEq :
      T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
        T ^ (d + 1 / tau - sigma - 1 / 2) = T ^ (-u) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hConst : 16 * (typeIDyadicCutoffMellinL1 + 1) * Clog * CK ≤
      (3 * Real.pi / 8) *
        T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
    pm_5233 hThreePi Real.pi Real.pi_pos
    have hDiv :
        (2 * (128 * Clog * CK * (typeIDyadicCutoffMellinL1 + 1))) /
            (3 * Real.pi) ≤
          T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by
      calc
        _ = 2 * D := by dsimp only [D]; ring
        _ ≤ _ := hPowLarge
    have hCross := (div_le_iff₀ hThreePi).mp hDiv
    have hPowNonneg : 0 ≤
        T ^ (sigma + 1 / 2 - 1 / tau - u - d) := by positivity
    have hMassNonneg : 0 ≤ typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    have hXNonneg : 0 ≤
        Clog * CK * (typeIDyadicCutoffMellinL1 + 1) := by positivity
    nlinarith [hCross, mul_nonneg Real.pi_pos.le hPowNonneg]
  have hDenPos : 0 < 8 * (Q : ℝ) *
      mediumTypeIStationaryKernel sigma T Q *
        (typeIDyadicCutoffMellinL1 + 1) := by
    exact mul_pos
      (mul_pos (mul_pos (by norm_num)
          (by exact_mod_cast (lt_trans Nat.zero_lt_one hQ)))
        (mediumTypeIStationaryKernel_pos hTPos
          (lt_trans Nat.zero_lt_one hQ)))
      (by linarith [typeIDyadicCutoffMellinL1_nonneg])
  have hLAPos : 0 <
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) := by positivity
  rw [show ((3 / 4 : ℝ) * (T ^ (-u) / 2)) =
    (3 / 8) * T ^ (-u) by ring]
  rw [le_div_iff₀ hDenPos]
  rw [show Real.pi * (((3 / 8 : ℝ) * T ^ (-u)) /
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ)) =
    (Real.pi * ((3 / 8 : ℝ) * T ^ (-u))) /
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) by ring]
  rw [le_div_iff₀ hLAPos]
  calc
    (2 : ℝ) *
          (8 * Q * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1)) *
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) =
      (16 * (typeIDyadicCutoffMellinL1 + 1)) *
        (((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          Q * mediumTypeIStationaryKernel sigma T Q) := by ring
    _ ≤ (16 * (typeIDyadicCutoffMellinL1 + 1)) *
        ((Clog * CK) * T ^ (d + 1 / tau - sigma - 1 / 2)) := by
          exact mul_le_mul_of_nonneg_left hDen
            (mul_nonneg (by norm_num)
              (by linarith [typeIDyadicCutoffMellinL1_nonneg]))
    _ = (16 * (typeIDyadicCutoffMellinL1 + 1) * Clog * CK) *
        T ^ (d + 1 / tau - sigma - 1 / 2) := by ring
    _ ≤ ((3 * Real.pi / 8) *
          T ^ (sigma + 1 / 2 - 1 / tau - u - d)) *
        T ^ (d + 1 / tau - sigma - 1 / 2) := by gcongr
    _ = Real.pi * ((3 / 8 : ℝ) * T ^ (-u)) := by
      calc
        (3 * Real.pi / 8) *
              T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
            T ^ (d + 1 / tau - sigma - 1 / 2) =
          (3 * Real.pi / 8) *
            (T ^ (sigma + 1 / 2 - 1 / tau - u - d) *
              T ^ (d + 1 / tau - sigma - 1 / 2)) := by ring
        _ = (3 * Real.pi / 8) * T ^ (-u) := by rw [hPowEq]
        _ = Real.pi * ((3 / 8 : ℝ) * T ^ (-u)) := by ring

/-- Exact product bounds for the natural dual cutoff.  They are the finite
replacement for the informal notation `M asymp T^(1+d)/Q`. -/
theorem medium_dual_cutoff_product_bounds
    {T d tau : ℝ} {Q : ℕ}
    (hT : 1 ≤ T) (_hd : 0 ≤ d) (hQ : 1 < Q)
    (htau : 1 < tau) (hScale : (Q : ℝ) ^ tau = T)
    (hRatio : 2 ≤ T ^ (1 + d) / Q) :
    let M := mediumTypeIDualCutoff T d Q
    1 < M ∧ (M : ℝ) ≤ T ^ (1 + d) / Q ∧
      T ^ (1 + d) / 2 ≤ (Q : ℝ) * M ∧
      (Q : ℝ) * M ≤ T ^ (1 + d) ∧
      (Q : ℝ) ≤ T := by
  dsimp only
  let M := mediumTypeIDualCutoff T d Q
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4711
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d) / Q := by
    simpa only [M] using mediumTypeIDualCutoff_cast_le (T := T) (d := d)
      (Q := Q) (zero_le_one.trans hT)
  have hMLower : T ^ (1 + d) / Q / 2 ≤ (M : ℝ) := by
    simpa only [M, mediumTypeIDualCutoff] using half_le_natFloor_of_two_le hRatio
  have hMTwo : (2 : ℕ) ≤ M := by
    dsimp only [M, mediumTypeIDualCutoff]
    exact Nat.le_floor hRatio
  have hMNat : 1 < M := by omega
  have hProdLower : T ^ (1 + d) / 2 ≤ (Q : ℝ) * M := by
    calc
      T ^ (1 + d) / 2 = (Q : ℝ) * (T ^ (1 + d) / Q / 2) := by
        field_simp [hQPos.ne']
      _ ≤ (Q : ℝ) * M := by gcongr
  have hProdUpper : (Q : ℝ) * M ≤ T ^ (1 + d) := by
    calc
      (Q : ℝ) * M ≤ (Q : ℝ) * (T ^ (1 + d) / Q) := by gcongr
      _ = T ^ (1 + d) := by field_simp [hQPos.ne']
  have hQUpper : (Q : ℝ) ≤ T := by
    have hTauPower : (Q : ℝ) ≤ (Q : ℝ) ^ tau := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ.le)
          htau.le
    simpa only [hScale] using hTauPower
  exact ⟨hMNat, hMUpper, hProdLower, hProdUpper, hQUpper⟩

/-- A concrete tenth-order envelope for the source-normalized zero mode.
The large fixed order leaves ample room for every detector loss. -/
theorem sourceScalar_zeroMode_le_tenth_order_envelope
    {sigma T t : ℝ} {Q : ℕ}
    (hsigma : sigma ≤ 1) (hT : 1 ≤ T)
    (ht : T / 2 ≤ t) (hQ : 0 < Q) (hQT : (Q : ℝ) ≤ T)
    {C : ℝ}
    (hDecay : |t| ^ (10 : ℕ) *
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
      (Q : ℝ) ^ (1 - sigma) * C) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
      1024 * C * T ^ (1 - sigma - 10) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have htPos : 0 < t := by linarith
  pm_7905 hExp sigma
  have hQPow : (Q : ℝ) ^ (1 - sigma) ≤ T ^ (1 - sigma) :=
    Real.rpow_le_rpow (Nat.cast_nonneg Q) hQT hExp
  have hAbs : T / 2 ≤ |t| := by simpa [abs_of_pos htPos] using ht
  have hAbsPow : (T / 2) ^ (10 : ℕ) ≤ |t| ^ (10 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hAbs 10
  have hScale :
      (1024 * C * T ^ (1 - sigma - 10)) * (T / 2) ^ (10 : ℕ) =
        C * T ^ (1 - sigma) := by
    rw [div_pow, show (2 : ℝ) ^ (10 : ℕ) = 1024 by norm_num,
      ← Real.rpow_natCast]
    have hPow : T ^ (1 - sigma - 10) * T ^ (10 : ℝ) =
        T ^ (1 - sigma) := by
      rw [← Real.rpow_add hTPos]
      congr 1
      ring
    calc
      1024 * C * T ^ (1 - sigma - 10) * (T ^ (10 : ℝ) / 1024) =
          C * (T ^ (1 - sigma - 10) * T ^ (10 : ℝ)) := by ring
      _ = C * T ^ (1 - sigma) := by rw [hPow]
  have hCnonneg : 0 ≤ C := by
    have hLeft : 0 ≤ |t| ^ (10 : ℕ) *
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ := by positivity
    have hQPowPos : 0 < (Q : ℝ) ^ (1 - sigma) := by positivity
    nlinarith
  have hMajor :
      (Q : ℝ) ^ (1 - sigma) * C ≤
        (1024 * C * T ^ (1 - sigma - 10)) * |t| ^ (10 : ℕ) := by
    calc
      (Q : ℝ) ^ (1 - sigma) * C ≤ T ^ (1 - sigma) * C := by gcongr
      _ = (1024 * C * T ^ (1 - sigma - 10)) *
          (T / 2) ^ (10 : ℕ) := by rw [hScale]; ring
      _ ≤ (1024 * C * T ^ (1 - sigma - 10)) *
          |t| ^ (10 : ℕ) := by gcongr
  have hProduct := hDecay.trans hMajor
  rw [mul_comm] at hProduct
  exact le_of_mul_le_mul_right hProduct (pow_pos (abs_pos.mpr htPos.ne') 10)

/-- The actual zero Fourier mode is eventually at most one eighth of the
literal selected source threshold, uniformly over the medium slab. -/
theorem eventually_sourceScalar_zeroMode_le_detector
    {sigma d u : ℝ} (hsigmaLower : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (_hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q : ℕ}, T₀ ≤ T →
      T / 2 ≤ t → 0 < Q → (Q : ℝ) ≤ T →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t 0)‖ ≤
        ((((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
  obtain ⟨Czero, hCzero, hZeroDecay⟩ :=
    exists_sourceScalar_zeroMode_decay sigma 10
  pm_4670
  let a : ℝ := 9 + sigma - d - u
  pm_4672
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((65536 / 3 : ℝ) * Czero * Clog)
  pm_4667
  intro T t Q hT ht hQ hQT
  pm_4666
  pm_4169
  have hEnv := sourceScalar_zeroMode_le_tenth_order_envelope
    hsigmaUpper.le hTOne ht hQ hQT (hZeroDecay t Q hQ)
  have hProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      pm_4735
    pm_4668
  pm_4665
  have hLarge := hTpow T hTPow
  have hPowerEq :
      T ^ (1 - sigma - 10) * T ^ d * T ^ a = T ^ (-u) := by
    pm_4673
  have hScaled :
      1024 * Czero * T ^ (1 - sigma - 10) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        (3 / 64) * T ^ (-u) := by
    calc
      1024 * Czero * T ^ (1 - sigma - 10) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        1024 * Czero * T ^ (1 - sigma - 10) * (Clog * T ^ d) := by
          gcongr
      _ ≤ (3 / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤
            T ^ (1 - sigma - 10) * T ^ d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hLarge hNonneg]
  pm_4671
  exact (mul_le_mul_of_nonneg_right hEnv (by positivity)).trans hScaled

/-- Uniform finite envelope for the source-normalized far Poisson modes.
The exact product lower bound for `Q*M` cancels the order-`n` growth in the
ordinate, leaving the decisive factor `T^(-n*d)`. -/
theorem sourceScalar_farModes_le_power_envelope
    {sigma T t d : ℝ} {Q M n : ℕ} {K : ℝ}
    (hsigma : 0 ≤ sigma) (hT : 1 ≤ T)
    (htNonneg : 0 ≤ t) (htUpper : t ≤ 3 * T)
    (hQ : 0 < Q) (hM : 0 < M) (hK : 0 ≤ K)
    (hProd : T ^ (1 + d) / 2 ≤ (Q : ℝ) * M)
    (hRaw :
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        (Q : ℝ) ^ (-sigma) *
          (K * (1 + |t|) ^ (n + 2) /
            ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n))) :
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedFarTail sigma t Q M‖ ≤
      K * (4 : ℝ) ^ (n + 2) * 2 ^ n * T ^ (2 - (n : ℝ) * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4147
  pm_74 hMReal M hM
  pm_77 hQOne Q hQ
  have hQWeight : (Q : ℝ) ^ (-sigma) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < 1 by norm_num) hQOne (by linarith)
  have htAbs : |t| = t := abs_of_nonneg htNonneg
  have hOrd : 1 + |t| ≤ 4 * T := by rw [htAbs]; linarith
  have hOrdPow : (1 + |t|) ^ (n + 2) ≤ (4 * T) ^ (n + 2) :=
    pow_le_pow_left₀ (by positivity) hOrd (n + 2)
  have hProdPow : (T ^ (1 + d) / 2) ^ n ≤
      ((Q : ℝ) * M) ^ n := pow_le_pow_left₀ (by positivity) hProd n
  have hDenRewrite : (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n =
      (Q : ℝ) * (((Q : ℝ) * M) ^ n) := by
    rw [pow_succ']
    ring
  have hDenLower : (T ^ (1 + d) / 2) ^ n ≤
      (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n := by
    rw [hDenRewrite]
    exact hProdPow.trans (by
      pm_77 hQOne Q hQ
      nlinarith [mul_le_mul_of_nonneg_right hQOne
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg Q) (Nat.cast_nonneg M)) n)])
  have hRatio :
      K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) ≤
        K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n := by
    exact div_le_div₀ (mul_nonneg hK (pow_nonneg (by positivity) _))
      (mul_le_mul_of_nonneg_left hOrdPow hK)
      (pow_pos (by positivity) _) hDenLower
  have hAlgebra :
      K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n =
        K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
          T ^ (2 - (n : ℝ) * d) := by
    have hNum : T ^ (n + 2) = T ^ ((n + 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have hDen : (T ^ (1 + d)) ^ n =
        T ^ ((n : ℝ) * (1 + d)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
      ring_nf
    have hRatioPower : T ^ (n + 2) / (T ^ (1 + d)) ^ n =
        T ^ (2 - (n : ℝ) * d) := by
      rw [hNum, hDen, div_eq_mul_inv, ← Real.rpow_neg hTPos.le,
        ← Real.rpow_add hTPos]
      congr 1
      push_cast
      ring
    calc
      K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n =
          K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
            (T ^ (n + 2) / (T ^ (1 + d)) ^ n) := by
              rw [mul_pow, div_pow]
              field_simp [show (T ^ (1 + d)) ^ n ≠ 0 by positivity]
      _ = K * (4 : ℝ) ^ (n + 2) * 2 ^ n *
          T ^ (2 - (n : ℝ) * d) := by rw [hRatioPower]
  calc
    ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedFarTail sigma t Q M‖ ≤ _ := hRaw
    _ ≤ 1 * (K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)) := by gcongr
    _ ≤ K * (4 * T) ^ (n + 2) / (T ^ (1 + d) / 2) ^ n := by
      simpa only [one_mul] using hRatio
    _ = _ := hAlgebra

/-- The complete far-frequency sum is eventually at most one eighth of the
selected source threshold.  The decay order is chosen as a positive natural
number from the physical parameter `d`, rather than assumed. -/
theorem eventually_sourceScalar_farModes_le_detector
    {sigma d u : ℝ} (hsigma : 0 ≤ sigma)
    (hd : 0 < d) (hdOne : d ≤ 1) (hu : 0 ≤ u) (_huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q M : ℕ}, T₀ ≤ T →
      0 ≤ t → t ≤ 3 * T → 0 < Q → 0 < M →
      T ^ (1 + d) / 2 ≤ (Q : ℝ) * M →
      ‖typeISourceNormalizationScalar sigma t (Q : ℝ) *
          typeINormalizedFarTail sigma t Q M‖ ≤
        ((((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((4 + d + u) / d)
  have hnReal : (4 + d + u) / d < (n : ℝ) := by simpa using hn
  have hnTwo : 1 < n := by
    have hRatioFour : 4 < (4 + d + u) / d := by
      rw [lt_div_iff₀ hd]
      nlinarith
    have hnFour : 4 < n := by exact_mod_cast (hRatioFour.trans hnReal)
    omega
  have hnd : 4 + d + u < (n : ℝ) * d := by
    pm_276 div_lt_iff₀ hd hnReal mul_comm
  pm_98 Kfar hKfar hFarRaw exists_sourceScalar_farModes_bound sigma n
  pm_4670
  let B : ℝ := Kfar * (4 : ℝ) ^ (n + 2) * 2 ^ n
  pm_116 hB B
  let a : ℝ := (n : ℝ) * d - 2 - d - u
  pm_4672
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((64 / 3 : ℝ) * B * Clog)
  pm_4667
  intro T t Q M hT htNonneg htUpper hQ hM hProd
  pm_4666
  pm_4169
  have hEnv := sourceScalar_farModes_le_power_envelope hsigma hTOne
    htNonneg htUpper hQ hM hKfar.le hProd (hFarRaw t Q M hQ hM)
  have hProduct := hLogs T hTLog
  have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
    pm_4735
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    pm_4668
  pm_4665
  have hLarge := hTpow T hTPow
  have hPowerEq : T ^ (2 - (n : ℝ) * d) * T ^ d * T ^ a =
      T ^ (-u) := by
    pm_4673
  have hScaled :
      B * T ^ (2 - (n : ℝ) * d) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        (3 / 64) * T ^ (-u) := by
    calc
      B * T ^ (2 - (n : ℝ) * d) *
          ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
        B * T ^ (2 - (n : ℝ) * d) * (Clog * T ^ d) := by gcongr
      _ ≤ (3 / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤ T ^ (2 - (n : ℝ) * d) * T ^ d := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hLarge hNonneg]
  pm_4671
  exact (mul_le_mul_of_nonneg_right hEnv (by positivity)).trans (by
    simpa only [B] using hScaled)

/-- Coarse but uniform power envelope for either complementary Mellin tail.
The exact theorem upstream is retained in `hRaw`; this lemma only performs
the finite support and scale comparisons needed for epsilon absorption. -/
theorem reflectedMellinTail_le_power_envelope
    {sigma T d : ℝ} {Q M n : ℕ} {C E : ℝ}
    (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hT : 1 ≤ T) (_hd : 0 ≤ d)
    (hQ : 0 < Q) (hM : 1 ≤ M)
    (hQT : (Q : ℝ) ≤ T)
    (hMT : (M : ℝ) ≤ T ^ (1 + d))
    (hC : 0 ≤ C)
    (hRaw : E ≤
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
        (((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2))) *
          C * (T ^ d) ^ (1 - (n : ℝ)))) :
    E ≤ 2 ^ (sigma + 2) * C *
      T ^ (4 + 4 * d - (n : ℝ) * d) := by
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  pm_4147
  pm_77 hMReal M hM
  have hMPos : (0 : ℝ) < M := zero_lt_one.trans_le hMReal
  have hDiffNonneg : 0 ≤ 2 * (M : ℝ) * Q - (Q : ℝ) / 2 := by
    nlinarith
  have hDiff : (2 * M * Q - (Q : ℝ) / 2) ≤
      2 * (M : ℝ) * Q := by norm_num; linarith
  have hQKernel : ((Q : ℝ) / 2) ^ (-sigma) /
      ((Q : ℝ) / 2) =
      2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1) := by
    have hTwo : (2 : ℝ) ^ sigma * 2 = 2 ^ (sigma + 1) := by
      calc
        (2 : ℝ) ^ sigma * 2 = 2 ^ sigma * 2 ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = 2 ^ (sigma + 1) := by rw [← Real.rpow_add (by norm_num)]
    have hQMul : (Q : ℝ) * (Q : ℝ) ^ (-sigma - 1) =
        (Q : ℝ) ^ (-sigma) := by
      calc
        (Q : ℝ) * (Q : ℝ) ^ (-sigma - 1) =
            (Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (-sigma - 1) := by
              rw [Real.rpow_one]
        _ = (Q : ℝ) ^ ((1 : ℝ) + (-sigma - 1)) := by
          rw [← Real.rpow_add hQReal]
        _ = (Q : ℝ) ^ (-sigma) := by
          congr 1
          ring
    pm_1355 hQReal.le
    field_simp [hQReal.ne']
    calc
      (Q : ℝ) ^ (-sigma) * (2 : ℝ) ^ sigma * 2 =
          (2 : ℝ) ^ (sigma + 1) * (Q : ℝ) ^ (-sigma) := by
            calc
              (Q : ℝ) ^ (-sigma) * (2 : ℝ) ^ sigma * 2 =
                  (Q : ℝ) ^ (-sigma) *
                    ((2 : ℝ) ^ sigma * 2) := by ring
              _ = (Q : ℝ) ^ (-sigma) * 2 ^ (sigma + 1) := by rw [hTwo]
              _ = 2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma) := by ring
      _ = (Q : ℝ) * (2 : ℝ) ^ (sigma + 1) *
          (Q : ℝ) ^ (-sigma - 1) := by rw [← hQMul]; ring
  have hMWeight : (M : ℝ) ^ sigma ≤ (M : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hMReal hsigmaUpper
  have hQWeight : (Q : ℝ) ^ (1 - sigma) ≤ T := by
    calc
      (Q : ℝ) ^ (1 - sigma) ≤ (Q : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ) (by linarith)
      _ = (Q : ℝ) := Real.rpow_one _
      _ ≤ T := hQT
  have hMThree : (M : ℝ) ^ (3 : ℕ) ≤
      T ^ (3 * (1 + d)) := by
    calc
      (M : ℝ) ^ (3 : ℕ) ≤ (T ^ (1 + d)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (Nat.cast_nonneg M) hMT 3
      _ = T ^ (3 * (1 + d)) := by
        pm_336 Real.rpow_natCast Real.rpow_mul hTPos.le
  have hQCombine : (Q : ℝ) * Q * (Q : ℝ) ^ (-sigma - 1) =
      (Q : ℝ) ^ (1 - sigma) := by
    calc
      (Q : ℝ) * Q * (Q : ℝ) ^ (-sigma - 1) =
          ((Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (1 : ℝ)) *
            (Q : ℝ) ^ (-sigma - 1) := by rw [Real.rpow_one]
      _ = (Q : ℝ) ^ ((1 : ℝ) + 1) *
            (Q : ℝ) ^ (-sigma - 1) := by
              rw [← Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (((1 : ℝ) + 1) + (-sigma - 1)) := by
        rw [← Real.rpow_add hQReal]
      _ = (Q : ℝ) ^ (1 - sigma) := by
        congr 1
        ring
  have hTwoCombine : (2 : ℝ) * 2 ^ (sigma + 1) =
      2 ^ (sigma + 2) := by
    calc
      (2 : ℝ) * 2 ^ (sigma + 1) =
          2 ^ (1 : ℝ) * 2 ^ (sigma + 1) := by rw [Real.rpow_one]
      _ = 2 ^ ((1 : ℝ) + (sigma + 1)) := by
        rw [← Real.rpow_add (by norm_num)]
      _ = 2 ^ (sigma + 2) := by
        congr 1
        ring
  have hMain :
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2))) ≤
        2 ^ (sigma + 2) * T ^ (4 + 3 * d) := by
    rw [hQKernel]
    calc
      (Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1))) ≤
        (Q : ℝ) * ((M : ℝ) * M) *
          ((2 * M * Q) *
            (2 ^ (sigma + 1) * (Q : ℝ) ^ (-sigma - 1))) := by
              gcongr
      _ = 2 ^ (sigma + 2) * ((M : ℝ) ^ (3 : ℕ) *
          (Q : ℝ) ^ (1 - sigma)) := by
        rw [← hQCombine, ← hTwoCombine]
        ring
      _ ≤ 2 ^ (sigma + 2) *
          (T ^ (3 * (1 + d)) * T) := by gcongr
      _ = 2 ^ (sigma + 2) * T ^ (4 + 3 * d) := by
        have hTPow : T ^ (3 * (1 + d)) * T = T ^ (4 + 3 * d) := by
          calc
            T ^ (3 * (1 + d)) * T =
                T ^ (3 * (1 + d)) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = T ^ (3 * (1 + d) + 1) := by
              rw [← Real.rpow_add hTPos]
            _ = T ^ (4 + 3 * d) := by
              congr 1
              ring
        rw [hTPow]
  have hTailPower : (T ^ d) ^ (1 - (n : ℝ)) =
      T ^ (d * (1 - (n : ℝ))) := by
    rw [← Real.rpow_mul hTPos.le]
  have hTailNonneg : 0 ≤ (T ^ d) ^ (1 - (n : ℝ)) := by positivity
  have hPowerCombine : T ^ (4 + 3 * d) *
      T ^ (d * (1 - (n : ℝ))) =
      T ^ (4 + 4 * d - (n : ℝ) * d) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  calc
    E ≤ _ := hRaw
    _ = ((Q : ℝ) * ((M : ℝ) * (M : ℝ) ^ sigma) *
          ((2 * M * Q - (Q : ℝ) / 2) *
            (((Q : ℝ) / 2) ^ (-sigma) / ((Q : ℝ) / 2)))) *
        (C * (T ^ d) ^ (1 - (n : ℝ))) := by ring
    _ ≤ (2 ^ (sigma + 2) * T ^ (4 + 3 * d)) *
        (C * (T ^ d) ^ (1 - (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hMain (mul_nonneg hC hTailNonneg)
    _ = 2 ^ (sigma + 2) * C *
        T ^ (4 + 4 * d - (n : ℝ) * d) := by
      rw [hTailPower, ← hPowerCombine]
      ring

/-- Both exact complementary Mellin integrals are eventually smaller than
one eighth of the reflected extraction budget.  The decay order is selected
from the physical loss parameter, and the literal source `clog` factor is
absorbed rather than replaced by an asymptotic abbreviation. -/
theorem eventually_reflectedMellinTails_le_detector
    {sigma d u : ℝ} (hsigma : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hd : 0 < d) (hu : 0 ≤ u) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T t : ℝ} {Q M : ℕ}, T₀ ≤ T →
      0 < Q → 1 ≤ M → (Q : ℝ) ≤ T →
      (M : ℝ) ≤ T ^ (1 + d) →
      let V := ((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ)
      let Eneg := ‖∫ r : ℝ in (Set.Icc (-(T ^ d)) (T ^ d)).compl,
        typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖
      let Epos := ‖∫ r : ℝ in (Set.Icc (-(T ^ d)) (T ^ d)).compl,
        typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
          typeIDyadicCutoffMellin r *
            typeIPowerReflectionIntegral sigma (-t + r)
              ((Q : ℝ) / 2) (2 * M * Q)‖
      Eneg ≤ Real.pi * V / 8 ∧ Epos ≤ Real.pi * V / 8 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((5 + 5 * d + u) / d)
  have hnReal : (5 + 5 * d + u) / d < (n : ℝ) := by simpa using hn
  have hnTwo : 1 < n := by
    have hFive : 5 < (5 + 5 * d + u) / d := by
      rw [lt_div_iff₀ hd]
      nlinarith
    have : 5 < n := by exact_mod_cast (hFive.trans hnReal)
    omega
  have hnd : 5 + 5 * d + u < (n : ℝ) * d := by
    pm_276 div_lt_iff₀ hd hnReal mul_comm
  pm_4081 Ctail hCtail hTail exists_norm_typeIReflectedMellinIntegral_tail_le n hnTwo
  pm_4670
  let B : ℝ := 2 ^ (sigma + 2) * Ctail
  pm_116 hB B
  let a : ℝ := (n : ℝ) * d - 4 - 5 * d - u
  pm_4672
  have hEventually := (tendsto_atTop.1 hPowTop)
    ((64 / (3 * Real.pi) : ℝ) * B * Clog)
  pm_4667
  intro T t Q M hT hQ hM hQT hMT
  dsimp only
  pm_4666
  pm_4169
  pm_4168 hHOne d hTOne hd.le
  pm_4147
  have hRawNeg := hTail (sigma := sigma) (t := t) (Q := (Q : ℝ))
    (H := T ^ d) (M := M) hsigma hQReal hM hHOne
  have hRawPos := hTail (sigma := sigma) (t := -t) (Q := (Q : ℝ))
    (H := T ^ d) (M := M) hsigma hQReal hM hHOne
  have hEnvNeg := reflectedMellinTail_le_power_envelope hsigma hsigmaUpper
    hTOne hd.le hQ hM hQT hMT hCtail.le hRawNeg
  have hEnvPos := reflectedMellinTail_le_power_envelope hsigma hsigmaUpper
    hTOne hd.le hQ hM hQT hMT hCtail.le hRawPos
  have hProduct := hLogs T hTLog
  have hSecondClog : (1 : ℝ) ≤
      Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      pm_4735
    pm_4668
  pm_4665
  have hLarge := hTpow T hTPow
  have hPowerEq : T ^ (4 + 4 * d - (n : ℝ) * d) *
      T ^ d * T ^ a = T ^ (-u) := by
    pm_4673
  have hScaled : B * T ^ (4 + 4 * d - (n : ℝ) * d) *
        ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) ≤
      (3 * Real.pi / 64) * T ^ (-u) := by
    calc
      _ ≤ B * T ^ (4 + 4 * d - (n : ℝ) * d) *
          (Clog * T ^ d) := by gcongr
      _ ≤ (3 * Real.pi / 64) * T ^ (-u) := by
        rw [← hPowerEq]
        have hNonneg : 0 ≤
            T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d := by positivity
        have hConst : B * Clog ≤ (3 * Real.pi / 64) * T ^ a := by
          pm_5233 hPi Real.pi Real.pi_pos
          rw [div_mul_eq_mul_div] at hLarge
          field_simp [Real.pi_ne_zero] at hLarge ⊢
          nlinarith [Real.pi_pos]
        calc
          B * T ^ (4 + 4 * d - (n : ℝ) * d) * (Clog * T ^ d) =
              (B * Clog) *
                (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d) := by ring
          _ ≤ ((3 * Real.pi / 64) * T ^ a) *
              (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d) :=
                mul_le_mul_of_nonneg_right hConst hNonneg
          _ = (3 * Real.pi / 64) *
              (T ^ (4 + 4 * d - (n : ℝ) * d) * T ^ d * T ^ a) := by ring
  have hBudget : B * T ^ (4 + 4 * d - (n : ℝ) * d) ≤
      Real.pi * ((((3 / 4) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 := by
    rw [show Real.pi * ((((3 / 4 : ℝ) * (T ^ (-u) / 2)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))) / 8 =
      ((3 * Real.pi / 64) * T ^ (-u)) /
        (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) by ring]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) <
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ))]
    exact hScaled
  constructor
  · exact hEnvNeg.trans (by simpa only [B] using hBudget)
  · exact hEnvPos.trans (by simpa only [B] using hBudget)

/-- The bounded Mellin-displacement window is eventually small enough for
the uniform two-sign stationary-kernel estimate. -/
theorem eventually_two_mul_rpow_le_half_sub_two
    {d : ℝ} (hd : 0 < d) (hdOne : d < 1) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      2 * T ^ d ≤ T / 2 - 2 := by
  pm_7900 hgap d
  have hPow := tendsto_rpow_neg_atTop hgap
  have hEventually := (tendsto_order.1 hPow).2 (1 / 8 : ℝ) (by norm_num)
  pm_4712
  let T₀ : ℝ := max 8 Tpow
  pm_4637
  pm_4629
  pm_4713
  have hTPos : 0 < T := by linarith
  have hSmall := hTpow T hTPow
  have hRewrite : T ^ (-(1 - d)) = T ^ d / T := by
    rw [show -(1 - d) = d - 1 by ring, Real.rpow_sub hTPos]
    rw [Real.rpow_one]
  rw [hRewrite, div_lt_iff₀ hTPos] at hSmall
  nlinarith

/-- The complementary-margin inequality makes the literal floored dual
cutoff positive and supplies all product comparisons needed by the exact
Poisson formula.  This packages the eventual real-power comparison once,
without replacing the natural floor by an asymptotic surrogate. -/
theorem eventually_medium_dual_cutoff_product_bounds
    {sigma d : ℝ} (hsigma : 1 / 2 < sigma)
    (hd : 0 < d) (hdGap : d ≤ (sigma - 1 / 2) / 1000) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T tau : ℝ} {Q : ℕ}, T₀ ≤ T →
      1 < Q → 1 < tau → tau < 2 →
      (Q : ℝ) ^ tau = T → -100 * d ≤ tau / 2 - sigma →
      let M := mediumTypeIDualCutoff T d Q
      1 < M ∧ (M : ℝ) ≤ T ^ (1 + d) / Q ∧
        T ^ (1 + d) / 2 ≤ (Q : ℝ) * M ∧
        (Q : ℝ) * M ≤ T ^ (1 + d) ∧ (Q : ℝ) ≤ T := by
  pm_1221 sigma
  pm_8452 gamma a
  have haOne : 1 < a := by
    dsimp only [a]
    pm_4664
    linarith
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    rw [sub_pos, div_lt_one (by linarith : 0 < a)]
    exact haOne
  have hPowTop := tendsto_rpow_atTop hgamma
  have hEventually := (tendsto_atTop.1 hPowTop) 2
  pm_4712
  let T₀ : ℝ := max 8 Tpow
  pm_4889
  intro T tau Q hT hQ htauOne htauTwo hScale hMargin
  pm_4629
  pm_4713
  have hTOne : 1 ≤ T := by linarith
  have hBounds := medium_complementary_source_scale_bounds hsigma hd hdGap
    hTOne hQ hScale hMargin
  dsimp only [a, gamma] at hBounds
  have hRatio : 2 ≤ T ^ (1 + d) / Q :=
    (hTpow T hTPow).trans hBounds.2.2.2.2.2
  simpa only using medium_dual_cutoff_product_bounds hTOne hd.le hQ
    htauOne hScale hRatio

/-- Every genuinely interior source family is converted, point by point,
to one of the two exact normalized reflected wide polynomials.  The same
family, displacement window, natural dual cutoff, detector threshold and
kernel occur in the conclusion; no cardinality or multiplicity is lost at
this analytic stage. -/
theorem eventually_interior_source_family_reflects
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        (((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) →
        2 * (2 ^ r * Y) ≤ A →
        tau = typeILogarithmicScale T (2 ^ r * Y) →
        1 < tau → tau < 2 →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-u) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r sigma t‖) →
        let Q := 2 ^ r * Y
        let M := mediumTypeIDualCutoff T d Q
        let V := ((3 / 4) * (T ^ (-u) / 2)) /
          (Nat.clog 2 A + 1 : ℕ)
        let R := (Real.pi * V) /
          (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
            (typeIDyadicCutoffMellinL1 + 1))
        let S := R / (2 * (M : ℝ) ^ sigma)
        W.Nonempty → 1 < M ∧ ∀ t ∈ W,
          (∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (-(t + v))‖) ∨
          (∃ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
            S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
              (normalizedTypeIReflectedCoeff sigma M) (t - v)‖) := by
  have hdStrict : d < 1 := by
    pm_4686 hGapPos sigma
    have hSmall : d ≤ (sigma - 1 / 2) / 1000 := hdGap
    nlinarith
  obtain ⟨Tmargin, hTmargin, hMargin⟩ :=
    eventually_large_source_forces_complementary_margin
      (σ := sigma) (d := d) (u := u) hsigmaUpper hd
      hdStrict hdGap huD
  obtain ⟨Tdual, hTdual, hDual⟩ :=
    eventually_medium_dual_cutoff_product_bounds
      (sigma := sigma) (d := d) hsigma hd hdGap
  obtain ⟨Tzero, hTzero, hZero⟩ :=
    eventually_sourceScalar_zeroMode_le_detector
      (sigma := sigma) (d := d) (u := u) hsigma hsigmaUpper hd hdOne hu huD
  obtain ⟨Tfar, hTfar, hFar⟩ :=
    eventually_sourceScalar_farModes_le_detector
      (sigma := sigma) (d := d) (u := u) (by linarith) hd hdOne hu huD
  obtain ⟨Tradius, hTradius, hRadius⟩ :=
    eventually_medium_reflection_radius_two
      (sigma := sigma) (d := d) (u := u) hsigma hsigmaUpper hd hdGap huD
  obtain ⟨Ttail, hTtail, hTail⟩ :=
    eventually_reflectedMellinTails_le_detector
      (sigma := sigma) (d := d) (u := u) (by linarith) hsigmaUpper.le hd hu
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d
    hdStrict
  pm_4081 Tkernel hTkernel hKernelWindow eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  let T₀ := max Tmargin
    (max Tdual (max Tzero (max Tfar (max Tradius (max Ttail (max Thalf Tkernel))))))
  pm_4266 T₀ hTmargin.trans le_max_left
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo hRange hLarge
  dsimp only
  intro hW
  pm_4630 hTMargin Tmargin le_max_left hT
  have hRest : max Tdual
      (max Tzero (max Tfar (max Tradius (max Ttail (max Thalf Tkernel))))) ≤ T :=
    (le_max_right _ _).trans hT
  pm_4630 hTDual Tdual le_max_left hRest
  have hRest₁ : max Tzero
      (max Tfar (max Tradius (max Ttail (max Thalf Tkernel)))) ≤ T :=
    (le_max_right _ _).trans hRest
  pm_4630 hTZero Tzero le_max_left hRest₁
  pm_5711 hRest₂ Tfar Tradius Ttail Thalf Tkernel hRest₁
  pm_4630 hTFar Tfar le_max_left hRest₂
  pm_838 hRest₃ Tradius Ttail Thalf Tkernel hRest₂
  pm_4630 hTRadius Tradius le_max_left hRest₃
  pm_4640 hRest₄ Ttail Thalf Tkernel hRest₃
  pm_4630 hTTail Ttail le_max_left hRest₄
  pm_4639 hRest₅ Thalf Tkernel hRest₄
  pm_4630 hTHalf Thalf le_max_left hRest₅
  pm_4630 hTKernel Tkernel le_max_right hRest₅
  have hTEight : 8 ≤ T := hTmargin.trans hTMargin
  pm_4169
  pm_7592 hDisp hHalf hTHalf
  pm_4897 Q r Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      pm_4703
    have hProd : 4 ≤ 2 ^ r * Y := by
      calc
        4 ≤ 2 ^ r := hPow
        _ ≤ 2 ^ r * Y := Nat.le_mul_of_pos_right _ hY
    change 1 < 2 ^ r * Y
    omega
  pm_4714
  have hMarginAt : -100 * d ≤ tau / 2 - sigma := by
    obtain ⟨t, ht⟩ := hW
    exact hMargin T t tau Y A r hTMargin hA hY hr hUpper
      (hRange t ht).1 (hRange t ht).2 hDisp hTau (hLarge t ht)
  have hDualAt := hDual (T := T) (tau := tau) (Q := Q) hTDual hQOne
    htauOne htauTwo hScale hMarginAt
  dsimp only at hDualAt
  let M := mediumTypeIDualCutoff T d Q
  have hMOne : 1 < M := by simpa only [M] using hDualAt.1
  refine ⟨hMOne, ?_⟩
  intro t ht
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A + 1 : ℕ)
  let K : ℝ := mediumTypeIStationaryKernel sigma T Q
  let E : ℝ := Real.pi * V / 8
  have htRange := hRange t ht
  pm_1082 htLower htUpper
  pm_4838
  have hK : 0 < K := mediumTypeIStationaryKernel_pos hTPos (by omega)
  have hZeroAt := hZero (T := T) (t := t) (Q := Q) hTZero htLower
    (by omega) hDualAt.2.2.2.2
  have hFarAt := hFar (T := T) (t := t) (Q := Q) (M := M) hTFar
    (by linarith) htUpper (by omega) (by omega) (by simpa only [M] using hDualAt.2.2.1)
  have hKernelAt : ∀ v ∈ Set.Icc (-(T ^ d)) (T ^ d),
      ‖typeIPowerReflectionIntegral sigma (t + v) ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K ∧
      ‖typeIPowerReflectionIntegral sigma (-t + v) ((Q : ℝ) / 2) (2 * M * Q)‖ ≤ K := by
    intro v hv
    exact norm_typeIPowerReflectionIntegral_both_signs_le_mediumKernel
      (by linarith : 0 < sigma) hTPos htLower htUpper (Real.rpow_nonneg hTPos.le d)
      (hKernelWindow T hTKernel) (by omega) hMOne.le hv
  have hTailAt := hTail (T := T) (t := t) (Q := Q) (M := M) hTTail
    (by omega) hMOne.le hDualAt.2.2.2.2
    (by
      calc
        (M : ℝ) ≤ T ^ (1 + d) / Q := by simpa only [M] using hDualAt.2.1
        _ ≤ T ^ (1 + d) := by
          exact div_le_self (Real.rpow_nonneg hTPos.le _) (by exact_mod_cast hQOne.le))
  have hRadiusAt := hRadius (Q := Q) (T := T) (tau := tau) hTRadius hQOne htauOne
    htauTwo hScale (by linarith [hMarginAt])
  have hReflect := exists_signed_shift_large_normalized_reflected_wide_of_budget
    hY hLower hUpper (by linarith) hMOne hV (Real.rpow_nonneg hTPos.le d) hK
    (by simpa only [V] using hLarge t ht)
    (by simpa only [V, hA, Q] using hZeroAt)
    (by simpa only [V, hA, Q, M] using hFarAt)
    (fun v hv => (hKernelAt v hv).1)
    (fun v hv => (hKernelAt v hv).2)
    (by
      convert hTailAt.1 using 1
      all_goals rfl)
    (by
      convert hTailAt.2 using 1
      all_goals rfl)
    (by
      dsimp only [V]
      rw [hA])
    (by simpa only [V, K, hA, Q] using hRadiusAt)
  pm_383 V K E Q M hReflect

/-- Complete finite data exported by an interior source family before the
endpoint power/Weyl split.  It invokes the exact Poisson reflection, makes
the sign and bounded-displacement selections, exposes the literal dyadic
block and proves both of its physical scale bounds from its actual retained
threshold. -/
theorem eventually_interior_source_reflected_dyadic_data
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ Clog : ℝ, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 →
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-u) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ)
          let R := (Real.pi * V) /
            (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := R / (2 * (M : ℝ) ^ sigma)
          let L := S / Nat.clog 2 M
          ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
            ∃ a : ℕ → ℂ,
              IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                (Nat.clog 2 M) * U.card ∧
              (∀ n ∈ dyadicInterval (2 ^ j), ‖a n‖ ≤ 1) ∧
              (∀ v ∈ U, L ≤ ‖dirichletPoly (2 ^ j) a v‖) ∧
              (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
                ‖dirichletPoly (2 ^ j) a v‖ =
                  ‖dirichletPoly (2 ^ j)
                    (normalizedTypeIReflectedCoeff sigma M) w‖) ∧
              1 < 2 ^ j ∧ 2 ^ j < M ∧
              1 / (1 / 2 + d) ≤ typeILogarithmicScale T (2 ^ j) ∧
              typeILogarithmicScale T (2 ^ j) ≤ Uscale ∧
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
                  Cref ≤ L ∧
              T ^ g / Cref ≤ L := by
  pm_4670
  pm_4669
  pm_116 hCK CK
  pm_952
  pm_7285
  pm_4638 hg g
  let Uscale : ℝ := 2 / g
  pm_116 hUscale Uscale
  obtain ⟨Treflect, hTreflect, hReflect⟩ :=
    eventually_interior_source_family_reflects hsigma hsigmaUpper hd hdOne
      hdGap hu huD
  pm_4081 Tscale hTscale hScaleUpper eventually_threshold_forces_logarithmic_scale_upper hg hCref
  have hdStrict : d < 1 := by nlinarith [hdGap]
  pm_4081 Twindow hTwindow hWindow eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  pm_6533 T₀ Tlog Treflect Tscale Twindow
  refine ⟨Clog, hClog, hCref, hg, hUscale, T₀,
    hTlog.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hW hSep hRange hLarge
  dsimp only
  pm_4630 hTLog Tlog le_max_left hT
  pm_4640 hRest Treflect Tscale Twindow hT
  pm_4630 hTReflect Treflect le_max_left hRest
  pm_4639 hRest₁ Tscale Twindow hRest
  pm_4630 hTScale Tscale le_max_left hRest₁
  pm_4630 hTWindow Twindow le_max_right hRest₁
  have hTEight : 8 ≤ T := hTlog.trans hTLog
  pm_4169
  pm_4897 Q r Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      pm_4703
    have : 4 ≤ Q := by
      pm_1381
    omega
  pm_4714
  have hReflected := hReflect (T := T) (tau := tau) (Y := Y) (A := A)
    (r := r) W hTReflect hA hY hr hLower hUpper hTau htauOne htauTwo
      hRange hLarge hW
  let M : ℕ := mediumTypeIDualCutoff T d Q
  rcases hReflected with ⟨hMOne, hEach⟩
  have hDH : T ^ d + T ^ d ≤ T / 2 := by
    have := hWindow T hTWindow
    nlinarith
  have hExtract := extract_common_signed_reflected_block W hMOne
    (by linarith : 0 ≤ sigma) (Real.rpow_nonneg hTPos.le d) hTPos.le hDH
    hSep hRange hEach
  obtain ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU, hCoeff,
    hLargeU, hOrdinate⟩ := hExtract
  pm_4674
  pm_4676 R V Q sigma S
  have hMOne' : 1 < M := by simpa only [M, Q] using hMOne
  pm_5317 hClogM M hMOne'
  have hL : 0 < L := by
    dsimp only [L, S, R, V]
    have hKernelPos := mediumTypeIStationaryKernel_pos (sigma := sigma) hTPos
      (lt_trans Nat.zero_lt_one hQOne)
    pm_895
    positivity
  have hLogsAt := hLogs T hTLog
  have hLogProduct := medium_reflected_clog_product_le hTEight hd.le
    (by nlinarith [hdGap, hsigmaUpper] : d ≤ 1 / 2) hQOne (by linarith)
      htauTwo hScale
  have hLogsM :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ d := by
    simpa only [M] using hLogProduct.trans hLogsAt
  pm_734 hMUpperRaw mediumTypeIDualCutoff_cast_le T d Q hTPos.le
  pm_4939 hQEq Q tau hQOne hScale
  pm_4677 tau
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQOne htauOne htauTwo hScale
  have hThresholdRaw := medium_reflected_threshold_explicit_lower
    (sigma := sigma) (T := T) (tau := tau) (d := d) (u := u)
    (eta := d) (Clog := Clog) (CK := CK) (Q := Q) (M := M)
    (by linarith) hTOne hQOne hMOne (by linarith) hScale hMUpper hClog
    hLogsM hCK (by simpa only [CK] using hKernel)
  have hThresholdExact :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
          Cref ≤ L := by
    simpa only [Cref, L, S, R, V, Q, M, hA] using hThresholdRaw
  have hExponent := medium_reflected_threshold_exponent_lower hsigma
    hsigmaUpper htauOne hd hdGap huD
  have hThreshold : T ^ g / Cref ≤ L := by
    have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hExponent
    exact (div_le_div_of_nonneg_right hPow (zero_le_one.trans hCref)).trans (by
      simpa only [g, Cref, L, S, R, V, Q, M, hA] using hThresholdRaw)
  have hUNonempty : U.Nonempty := by
    pm_4675
  have hLToP : L ≤ ((2 ^ j : ℕ) : ℝ) :=
    unit_coeff_threshold_le_dyadic_length hL.le hUNonempty hCoeff hLargeU
  have hScaleData := hScaleUpper hTScale hL hThreshold hLToP
  rcases hScaleData with ⟨hPOne, hTauPUpper⟩
  have hPLtM : 2 ^ j < M := by
    exact Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hj)
  have hTauPLower := reflected_dyadic_scale_lower_of_expanded_cutoff
    (T := T) (τ := tau) (d := d) (Q := Q) (P := 2 ^ j) (M := M)
    (by linarith) hQOne hPOne htauOne htauTwo hd.le hScale hPLtM.le
      (by simpa only [M] using hMUpperRaw)
  refine ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU, hCoeff,
    ?_, hOrdinate, hPOne, hPLtM, hTauPLower, ?_, hThresholdExact, hThreshold⟩
  · simpa only [L, S, R, V, Q, M] using hLargeU
  · simpa only [Uscale] using hTauPUpper

/-- The literal quadratic and cubic side conditions needed by the reflected
Weyl A--B process hold uniformly on the far dyadic branch. -/
theorem eventually_reflected_weyl_geometry
    {sigma d s U : ℝ} (hsigmaUpper : sigma < 1) (hd : 0 < d)
    (hs : 0 < s) (hU : 0 < U) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ {T theta w : ℝ} {P : ℕ}, T₀ ≤ T →
      1 < P → 0 < theta → (P : ℝ) ^ theta = T →
      1 / (1 / 2 + d) ≤ theta → theta ≤ U →
      theta < 6 * sigma - 3 - s →
      T / 2 ≤ w → w ≤ 5 * T / 2 →
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ (2 * T ^ (4 * d)) * w ∧
        w ≤ (((P + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
  let delta : ℝ := 6 * (1 - sigma) + s
  pm_116 hdelta delta
  let rho : ℝ := delta / U
  pm_116 hrho rho
  pm_4895 hTwoD d
  have hTopD := tendsto_rpow_atTop hTwoD
  have hEventuallyFour := (tendsto_atTop.1 hTopD) 4
  pm_4610 eventually_atTop hEventuallyFour Td hTd
  have hTopRho := tendsto_rpow_atTop hrho
  have hEventuallyThree := (tendsto_atTop.1 hTopRho) 3
  pm_4610 eventually_atTop hEventuallyThree Trho hTrho
  let T₀ := max 8 (max Td Trho)
  pm_4889
  intro T theta w P hT hP htheta hScale hthetaLower hthetaUpper hthetaFar
    hwLower hwUpper
  pm_4629
  pm_4639 hTRest Td Trho hT
  pm_4630 hTD Td le_max_left hTRest
  pm_4630 hTRho Trho le_max_right hTRest
  pm_4169
  pm_5776 ha
  have hInvTheta : 1 / theta ≤ 1 / 2 + d := by
    rw [div_le_iff₀ htheta]
    have hScaled := mul_le_mul_of_nonneg_left hthetaLower ha.le
    field_simp [ha.ne'] at hScaled
    nlinarith
  pm_6537 hPEq P theta hP htheta
  have hPUpper : (P : ℝ) ≤ T ^ (1 / 2 + d) := by
    rw [hPEq]
    exact Real.rpow_le_rpow_of_exponent_le hTOne hInvTheta
  have hPSucc : ((P + 1 : ℕ) : ℝ) ≤ 2 * T ^ (1 / 2 + d) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    pm_77 hPReal P hP.le
    nlinarith [Real.rpow_nonneg hTPos.le (1 / 2 + d)]
  have hFour : 4 ≤ T ^ (2 * d) := hTd T hTD
  have hSquare : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      T ^ (1 + 4 * d) := by
    calc
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
          (2 * T ^ (1 / 2 + d)) ^ (2 : ℕ) := by gcongr
      _ = 4 * (T ^ (1 / 2 + d)) ^ (2 : ℕ) := by ring
      _ = 4 * T ^ (1 + 2 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        ring_nf
      _ ≤ T ^ (2 * d) * T ^ (1 + 2 * d) := by gcongr
      _ = T ^ (1 + 4 * d) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring
  have hQuadratic : (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤
      (2 * T ^ (4 * d)) * w := by
    calc
      (((P + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ T ^ (1 + 4 * d) := hSquare
      _ = T ^ (4 * d) * T := by
        rw [Real.rpow_add hTPos, Real.rpow_one]
        ring
      _ ≤ (2 * T ^ (4 * d)) * w := by
        have hPow : 0 ≤ T ^ (4 * d) := Real.rpow_nonneg hTPos.le _
        nlinarith
  have hRhoTheta : rho * theta ≤ delta := by
    dsimp only [rho]
    rw [div_mul_eq_mul_div]
    exact div_le_iff₀ hU |>.2 (by
      have := mul_le_mul_of_nonneg_left hthetaUpper hdelta.le
      nlinarith)
  have hThetaDelta : theta + delta < 3 := by
    dsimp only [delta]
    linarith
  have hRhoExp : 1 + rho ≤ 3 / theta := by
    rw [le_div_iff₀ htheta]
    nlinarith
  have hThree : 3 ≤ T ^ rho := hTrho T hTRho
  have hThreeT : 3 * T ≤ T ^ (1 + rho) := by
    calc
      3 * T ≤ T ^ rho * T := by gcongr
      _ = T ^ (1 + rho) := by
        rw [Real.rpow_add hTPos, Real.rpow_one]
        ring
  have hCubeP : T ^ (1 + rho) ≤ (P : ℝ) ^ (3 : ℕ) := by
    calc
      T ^ (1 + rho) ≤ T ^ (3 / theta) :=
        Real.rpow_le_rpow_of_exponent_le hTOne hRhoExp
      _ = ((P : ℝ) ^ theta) ^ (3 / theta) := by rw [hScale]
      _ = (P : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ P),
          show theta * (3 / theta) = 3 by field_simp [htheta.ne']]
        exact Real.rpow_natCast (P : ℝ) 3
  refine ⟨hQuadratic, ?_⟩
  calc
    w ≤ 3 * T := by linarith
    _ ≤ T ^ (1 + rho) := hThreeT
    _ ≤ (P : ℝ) ^ (3 : ℕ) := hCubeP
    _ ≤ ((P + 1 : ℕ) : ℝ) ^ (3 : ℕ) := by
      gcongr
      norm_num

/-- The complementary far dyadic alternative exported by the actual
reflection data is impossible.  The proof uses the retained ordinate and
coefficient identity, not merely its cardinality consequence. -/
theorem eventually_reflected_far_dyadic_data_impossible
    {sigma d u s Uscale Cref : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (huD : u ≤ d)
    (hsDef : s = reflectedEndpointScaleSlack sigma d)
    (hUscale : 0 < Uscale) (hCref : 1 ≤ Cref) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T tau theta L : ℝ} {P M : ℕ} {U : Finset ℝ} {a : ℕ → ℂ},
        T₀ ≤ T → 1 < tau → tau < 2 →
        1 < P → P < M → theta = typeILogarithmicScale T P →
        theta ≤ Uscale → 1 / (1 / 2 + d) ≤ theta →
        theta < 6 * sigma - 3 - s →
        (M : ℝ) ≤ T ^ (1 + d - 1 / tau) →
        U.Nonempty →
        (∀ v ∈ U, L ≤ ‖dirichletPoly P a v‖) →
        (∀ v ∈ U, ∃ w ∈ Set.Icc (T / 2) (5 * T / 2),
          ‖dirichletPoly P a v‖ =
            ‖dirichletPoly P
              (normalizedTypeIReflectedCoeff sigma M) w‖) →
        T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
            Cref ≤ L → False := by
  have hs : 0 < s := by
    rw [hsDef]
    exact reflectedEndpointScaleSlack_pos hsigma hd
  obtain ⟨Tgeo, hTgeo, hGeo⟩ :=
    eventually_reflected_weyl_geometry hsigmaUpper hd hs hUscale
  let Cw : ℝ := 60 * 4 ^ sigma * Real.sqrt 12
  pm_116 hCw Cw
  have hSaving : 0 < s / 24 := by positivity
  have hTop := tendsto_rpow_atTop hSaving
  have hEventually := (tendsto_atTop.1 hTop) (Cw * Cref + 1)
  pm_4610 eventually_atTop hEventually Tconst hTconst
  let T₀ := max Tgeo Tconst
  pm_4266 T₀ hTgeo.trans le_max_left
  intro T tau theta L P M U a hT htauOne htauTwo hP hPM hthetaDef
    hthetaUpper hthetaLower hthetaFar hMUpper hUNonempty hLarge hOrdinate
    hThreshold
  pm_4630 hTGeo Tgeo le_max_left hT
  pm_4630 hTConst Tconst le_max_right hT
  have hTEight : 8 ≤ T := hTgeo.trans hTGeo
  have hTOne : 1 ≤ T := by linarith
  have hTStrict : 1 < T := by linarith
  have hTPos : 0 < T := by linarith
  have htheta : 0 < theta := by
    rw [hthetaDef]
    unfold typeILogarithmicScale
    exact Real.logb_pos (by exact_mod_cast hP) hTStrict
  have hScale : (P : ℝ) ^ theta = T := by
    rw [hthetaDef]
    exact rpow_typeILogarithmicScale_eq hTPos hP
  pm_6537 hPEq P theta hP htheta
  pm_106 hPMCast P M hPM.le
  have hPowerUpper : T ^ (1 / theta) ≤ T ^ (1 + d - 1 / tau) := by
    rw [← hPEq]
    exact hPMCast.trans hMUpper
  have hDual : 1 / theta ≤ 1 + d - 1 / tau :=
    (Real.strictMono_rpow_of_base_gt_one hTStrict).le_iff_le.mp hPowerUpper
  have hMargin := reflected_weyl_exponent_margin hsigma hsigmaUpper hd huD
    hsDef htauOne htauTwo hDual hthetaLower hthetaFar
  obtain ⟨v, hv⟩ := hUNonempty
  pm_98 w hw hNormEq hOrdinate v hv
  have hwOne : 1 ≤ w := by linarith [hw.1]
  have hwThree : w ≤ 3 * T := by linarith [hw.2]
  obtain ⟨hQuadratic, hCubic⟩ := hGeo hTGeo hP htheta hScale
    hthetaLower hthetaUpper hthetaFar hw.1 hw.2
  have hWeyl := norm_normalizedTypeIReflectedCoeff_le_physical_weyl
    (sigma := sigma) (d := d) (T := T) (theta := theta) (w := w)
    (P := P) (M := M) (by linarith) hd.le hTOne hP hPM htheta hScale
      hwOne hwThree hQuadratic hCubic
  pm_5798 E
  let F : ℝ := 2 * d + 1 / (2 * theta) + 1 / 6
  have hExponent : F + s / 24 ≤ E := by
    dsimp only [F, E]
    linarith
  have hPowExponent : T ^ F * T ^ (s / 24) ≤ T ^ E := by
    rw [← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hConst : Cw * Cref < T ^ (s / 24) :=
    (show Cw * Cref < Cw * Cref + 1 by linarith).trans_le
      (hTconst T hTConst)
  have hNormUpper : Cref * ‖dirichletPoly P a v‖ < T ^ E := by
    calc
      Cref * ‖dirichletPoly P a v‖ = Cref *
          ‖dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) w‖ := by
            rw [hNormEq]
      _ ≤ Cref * (Cw * T ^ F) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Cw, F] using hWeyl) (zero_le_one.trans hCref)
      _ = (Cw * Cref) * T ^ F := by ring
      _ < T ^ (s / 24) * T ^ F := by
        exact mul_lt_mul_of_pos_right hConst (Real.rpow_pos_of_pos hTPos F)
      _ = T ^ F * T ^ (s / 24) := by ring
      _ ≤ T ^ E := hPowExponent
  have hNormThreshold : ‖dirichletPoly P a v‖ < T ^ E / Cref := by
    rw [lt_div_iff₀ (zero_lt_one.trans_le hCref)]
    simpa only [mul_comm] using hNormUpper
  have hThreshold' : T ^ E / Cref ≤ L := by simpa only [E] using hThreshold
  linarith [hLarge v hv]

set_option maxHeartbeats 4000000

/-- The powered half of the reflected medium branch, from the actual
source-smooth family all the way back to the multiplicity-weighted zero
count.  The selected dyadic block and the selected natural power both occur
inside this proof; no detached cardinality certificate is accepted. -/
theorem actual_interior_reflected_near_endpoint_consumer
    {sigma tau0 : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma < 1)
    (hcert : EndpointScaleCertificate sigma tau0)
    (Clog : ℝ) :
    ∀ eps : ℝ, 0 < eps →
      ∃ C : ℝ, 0 < C ∧ ∃ T0 : ℝ, 8 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
        let d := classicalEndpointLossParameter sigma tau0 (eps / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {tau : ℝ} {r : ℕ} (W : Finset ℝ),
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 → W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          zeroCountRect sigma 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          let g := (sigma - 1 / 2) / 2
          let Uscale := 2 / g
          ∀ {P : ℕ}, 1 < P →
            typeILogarithmicScale T P ≤ Uscale →
            4 * tau0 / 3 - reflectedEndpointScaleSlack sigma d ≤
              typeILogarithmicScale T P →
            (∃ j U a,
              P = 2 ^ j ∧ j ∈ Finset.range
                (Nat.clog 2 (mediumTypeIDualCutoff T d (2 ^ r * Y))) ∧
              IsSeparated 1 U ∧ InBaseInterval (3 * T) U ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                Nat.clog 2 (mediumTypeIDualCutoff T d (2 ^ r * Y)) * U.card ∧
              (∀ n ∈ dyadicInterval P, ‖a n‖ ≤ 1) ∧
              let Q := 2 ^ r * Y
              let M := mediumTypeIDualCutoff T d Q
              let V := ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ)
              let R := (Real.pi * V) /
                (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
                  (typeIDyadicCutoffMellinL1 + 1))
              let S := R / (2 * (M : ℝ) ^ sigma)
              let L := S / Nat.clog 2 M
              (∀ v ∈ U, L ≤ ‖dirichletPoly P a v‖) ∧
              P < M ∧
              T ^ (1 / 2 - d ^ 4 - d * sigma +
                    (sigma - 1) / tau - d) /
                  mediumReflectedThresholdConstant
                    Clog
                    (32 * 2 ^ sigma +
                      (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
                        4 ^ (sigma + 1 / 2)) ≤ L) →
            (zeroCountRect sigma 1 T (2 * T) : ℝ) ≤
              C * T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by
  intro eps heps
  pm_5097 eta eps sigma tau0
  let u : ℝ := d ^ 4
  let s : ℝ := reflectedEndpointScaleSlack sigma d
  pm_7285
  let Uscale : ℝ := 2 / g
  pm_6416 tau0
  pm_116 heta eta
  have hdSpec := classicalEndpointLossParameter_spec hsigma hsigmaUpper
    hcert.tau0_pos heta
  pm_5074 hdEta hdEtaTau hdReflected _hdGap hdUpperGap _hdSmall
  pm_4762
  pm_4196 hs s reflectedEndpointScaleSlack_pos hsigma hd
  have huD : u ≤ d := by
    pm_5799 hTwo
    have hTwoOne : d ^ 2 ≤ 1 := hTwo.trans hdOne
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hTwoOne)]
  pm_4638 hg g
  pm_116 hUscale Uscale
  have hB : 0 < B := by
    dsimp only [B]
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos (by norm_num) (add_pos hUscale (by positivity)))
      (mul_pos (by norm_num) hcert.tau0_pos)
  have hsSmall : s ≤ tau0 / 6 := by
    dsimp only [s]
    exact reflectedEndpointScaleSlack_le_tau0_sixth hsigma hsigmaUpper hcert
      _hdGap hdUpperGap
  have hdBudget := reflected_total_power_budget_with_gap_le hsigma hsigmaUpper
    hcert.tau0_pos heta hd hdOne hdEta hdReflected
  dsimp only [s, g, Uscale, B] at hdBudget
  pm_351 Cpow hCpow K hK hPowered powered_unit_block_large_values_bound_bounded_uniform B d hd
  pm_4669
  pm_952
  pm_8227 Cref Cpow
  pm_82 hE E
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le E K d d (9 * tau0 / 16) (eps / 4) B
      hE hK.le hd hd (by nlinarith [hcert.tau0_pos]) (by nlinarith [heps]) hB
      (by dsimp only [eta] at hdEta; nlinarith)
      (by dsimp only [eta] at hdEtaTau; nlinarith)
  obtain ⟨Cmult, hCmult, Tmult, hTmult, hMult⟩ :=
    eventually_dichotomy_multiplicity_factor_bound d d hd.le hd
  obtain ⟨Ccover, hCcover, Tcover, hTcover, hCover⟩ :=
    eventually_source_selection_log_product_le (eps / 4) (by positivity)
  obtain ⟨Tscale, hTscale, hScaleDyadic⟩ :=
    eventually_dyadic_power_scale_lower_half
      (τ₀ := 3 * tau0 / 4) (U := Uscale)
      (by nlinarith [hcert.tau0_pos]) hUscale
  let C : ℝ := Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)
  pm_6533 T0 Tloss Tmult Tcover Tscale
  pm_4662 T0
  intro tau r W hA hY hr hLower hUpper hTau htauOne htauTwo hW hSep
    hRange hLarge hCount P hPOne hTauPUpper hNear hData
  rcases hData with ⟨j, U, a, rfl, hj, hSepU, hBaseU, hCardU, hCoeff,
    hLargeU, hPM, hThresholdExact⟩
  pm_4772
  pm_5098 hRest Tmult Tcover Tscale hT
  pm_4630 hTMult Tmult le_max_left hRest
  pm_4639 hRest' Tcover Tscale hRest
  pm_4630 hTCover Tcover le_max_left hRest'
  pm_4630 hTScale Tscale le_max_right hRest'
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  pm_4169
  pm_7559
  pm_632 Qsrc
  let M : ℕ := mediumTypeIDualCutoff T d Qsrc
  let Vsrc : ℝ := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  pm_4676 Rsrc Vsrc Qsrc sigma Ssrc
  have hMOne : 1 < M := by
    simpa only [M, Qsrc, Y] using hPOne.trans hPM
  have hL : 0 < L := by
    have hQsrc : 0 < Qsrc := by
      dsimp only [Qsrc, Y]
      simpa only [d] using Nat.mul_pos (pow_pos (by omega) r) hY
    have hKernelPos := mediumTypeIStationaryKernel_pos (sigma := sigma)
      hTPos hQsrc
    pm_895
    pm_5317 hClogM M hMOne
    dsimp only [L, Ssrc, Rsrc, Vsrc, A]
    positivity
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Qsrc) hTPos.le
  have hQsrcOne : 1 < Qsrc := by
    dsimp only [Qsrc, Y]
    have hpow : 4 ≤ 2 ^ r := by
      pm_4703
    have : 4 ≤ 2 ^ r * ⌊T ^ d ^ 2⌋₊ :=
      hpow.trans (Nat.le_mul_of_pos_right _ (by simpa only [d] using hY))
    omega
  have hScaleSrc : (Qsrc : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Qsrc] using rpow_typeILogarithmicScale_eq hTPos hQsrcOne
  pm_4939 hQsrcEq Qsrc tau hQsrcOne hScaleSrc
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Qsrc := by
        simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQsrcEq, ← Real.rpow_sub hTPos]
  have hD := reflected_normalization_loss_le_four_d hsigma.le hsigmaUpper
    htauOne htauTwo hd.le huD hTOne hCref hL hPM.le hMUpper
    (by simpa only [Cref, L, Ssrc, Rsrc, Vsrc, Qsrc, M, u, Y, A] using
      hThresholdExact)
  let D : ℝ := max 1 (((2 ^ j : ℕ) : ℝ) ^ sigma / L)
  pm_457 hDPos D zero_lt_one
  have hDUpper : D ≤ Cref * T ^ (4 * d) := by
    simpa only [D] using hD
  obtain ⟨k, hk, hkB, hkLower, hkUpper, hkScale, hkActualLower, hkLoss⟩ :=
    exists_bounded_positive_power_augmented_endpoint_with_gap hsigmaUpper hcert
      hs.le hdUpperGap hsSmall hNear hTauPUpper
  have hP : 0 < 2 ^ j := pow_pos (by omega) j
  obtain ⟨q, hq, U', hUsub, hPowerCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k (2 ^ j) a 0 (3 * T) L U hk hkB hP (by norm_num)
      (by linarith) hL hCoeff hSepU hBaseU
      (by
        intro v hv
        rw [sum_zero_real_part_eq_dirichletPoly]
        simpa only [L, Ssrc, Rsrc, Vsrc, Qsrc, M, u, Y, A] using hLargeU v hv)
  let Q : ℕ := 2 ^ q * (2 ^ j) ^ k
  let Vp : ℝ := (L ^ k /
    (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k
  have hqk : q < k := Finset.mem_range.mp hq
  let Ploss := typeIIPoweredThresholdLoss Cpow
    (((2 ^ j : ℕ) : ℝ) ^ sigma) D d sigma (2 ^ j) k
  have hModel := typeII_powered_threshold_lower
    (C := Cpow) (L := (((2 ^ j : ℕ) : ℝ) ^ sigma)) (D := D)
    (η := d) (σ := sigma) (N := 2 ^ j) (k := k) (r := q)
    (by linarith [hCpow]) (by positivity) hDPos hP hk (by linarith) hqk
  dsimp only at hModel
  rcases hModel with ⟨hPloss, hModel⟩
  have hBaseToL : (((2 ^ j : ℕ) : ℝ) ^ sigma) / D ≤ L := by
    have hRatioLeD : (((2 ^ j : ℕ) : ℝ) ^ sigma) / L ≤ D :=
      le_max_right _ _
    have hCross : (((2 ^ j : ℕ) : ℝ) ^ sigma) ≤ D * L :=
      (div_le_iff₀ hL).mp hRatioLeD
    rw [div_le_iff₀ hDPos]
    calc
      (((2 ^ j : ℕ) : ℝ) ^ sigma) ≤ D * L := hCross
      _ = L * D := mul_comm _ _
  have hModelToActual :
      ((((((2 ^ j : ℕ) : ℝ) ^ sigma) / D) ^ k /
        (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k) ≤ Vp := by
    dsimp only [Vp]
    gcongr
  have hThreshold : (Q : ℝ) ^ sigma / Ploss ≤ Vp := by
    have hModel' : (Q : ℝ) ^ sigma / Ploss ≤
        ((((((2 ^ j : ℕ) : ℝ) ^ sigma) / D) ^ k /
          (Cpow * ((2 ^ k * (2 ^ j) ^ k : ℕ) : ℝ) ^ d)) / k) := by
      simpa only [Q, Ploss] using hModel
    exact hModel'.trans hModelToActual
  have hEnvelope := reflected_powered_threshold_loss_le_envelope
    (C₀ := Cref) (C := Cpow) (d := d) (sigma := sigma) (T := T)
    (D := D) (P := 2 ^ j) (k := k) (B := B) hCref hCpow hd.le
    hsigmaUpper.le (by
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
           _ ≤ T := by linarith) hDPos hDUpper hP hk hkB
  dsimp only at hEnvelope
  have hPlossEnvelope : Ploss ≤
      1 + T ^ (4 * d * k) *
        classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := by
    simpa only [Ploss, E] using hEnvelope
  have hFinalLength : (2 ^ j) ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) q)
  have hClassMono := classicalTypeIIPowerLoss_mono_length (k := k)
    hE hd.le hTOne hFinalLength
  have hOuter : Ploss ≤ T ^ (4 * d * k) *
      (1 + classicalTypeIIPowerLoss E d T k Q) := by
    calc
      Ploss ≤ 1 + T ^ (4 * d * k) *
          classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := hPlossEnvelope
      _ ≤ T ^ (4 * d * k) *
          (1 + classicalTypeIIPowerLoss E d T k Q) := by
        have hTonePow : 1 ≤ T ^ (4 * d * k) :=
          Real.one_le_rpow hTOne (by positivity)
        have hMonoAdd :
            1 + classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) ≤
              1 + classicalTypeIIPowerLoss E d T k Q :=
          by simpa only [add_comm] using add_le_add_left hClassMono 1
        calc
          1 + T ^ (4 * d * k) *
              classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) ≤
              T ^ (4 * d * k) + T ^ (4 * d * k) *
                classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k) := by
            gcongr
          _ = T ^ (4 * d * k) *
              (1 + classicalTypeIIPowerLoss E d T k ((2 ^ j) ^ k)) := by ring
          _ ≤ T ^ (4 * d * k) *
              (1 + classicalTypeIIPowerLoss E d T k Q) :=
            mul_le_mul_of_nonneg_left hMonoAdd
              (Real.rpow_nonneg hTPos.le (4 * d * k))
  have hPower := dyadic_power_mhh_le_endpoint_with_factor_of_augmented_scale
    hsigma hsigmaUpper hcert hTOne hPOne hk hkB hqk hkScale hkLower hkUpper
      hkLoss
  dsimp only at hPower
  have hFinalScale : 3 * tau0 / 8 ≤ typeILogarithmicScale T Q := by
    have hLowerForDyadic : 2 * (3 * tau0 / 4) / 3 ≤
        typeILogarithmicScale T (2 ^ j) / (k : ℝ) := by
      nlinarith [hkActualLower]
    have hScale := hScaleDyadic T (2 ^ j) k q hTScale hPOne hk hqk
      hTauPUpper hLowerForDyadic
    convert hScale using 1
    · ring
  pm_4654
  let cover : ℕ := Nat.clog 2 A + 1
  let extraction : ℕ :=
    (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) * k
  have hExtractionPos : 0 < extraction := by
    dsimp only [extraction]
    pm_5317 hClogMPos M hMOne
    exact Nat.mul_pos (Nat.mul_pos (by positivity) hClogMPos) hk
  have hCount' : zeroCountRect sigma 1 T (2 * T) ≤
      (base * cover) * W.card := by
    simpa only [base, cover] using hCount
  have hExtract : (W.card : ℝ) ≤ extraction * (U'.card : ℝ) := by
    calc
      (W.card : ℝ) ≤
          (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) *
            (U.card : ℝ) := by exact_mod_cast hCardU
      _ ≤ (2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M) *
          (k * (U'.card : ℝ)) := by gcongr
      _ = extraction * (U'.card : ℝ) := by
        dsimp only [extraction]
        push_cast
        ring
  have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor hTPos
    (by simpa only [Q] using
      (show 1 < 2 ^ q * (2 ^ j) ^ k by
        exact (one_lt_pow₀ hPOne hk.ne').trans_le
          (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))))
    (by exact_mod_cast hExtractionPos) hPloss hThreshold
    (R := ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))
    (by
      calc
        (Q : ℝ) ^ classicalMHHExponent sigma
            (typeILogarithmicScale T Q) ≤
          ((2 : ℝ) ^ B) ^ (2 : ℕ) *
            T ^ (3 * (1 - sigma) / tau0 + 2 * s / tau0) := by
              simpa only [Q] using hPower
        _ = (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) *
            T ^ (3 * (1 - sigma) / tau0) := by
          rw [Real.rpow_add hTPos]
          ring)
    hCount' hExtract hK.le (by
      simpa only [Q, Vp, Real.rpow_zero, one_mul] using hMHH)
  have hBaseAt := hMult T hTMult
  have hCoverAt := hCover T hTCover
  have hClogMLe : Nat.clog 2 M ≤ Nat.clog 2 A := by
    have hMSharp := mediumTypeIDualCutoff_le_sharpZetaCutoff hTEight hd.le
      (by nlinarith [hdUpperGap, hsigmaUpper] : d ≤ 1 / 2)
      hQsrcOne (by linarith) htauTwo hScaleSrc
    exact Nat.clog_mono_right 2 (by simpa only [M, Qsrc, hA] using hMSharp)
  have hExtraLeBase :
      ((2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M : ℕ) : ℝ) ≤
        (base : ℝ) := by
    have hCap : 1 ≤ classicalLocalMultiplicityCap T := by
      unfold classicalLocalMultiplicityCap
      apply Nat.ceil_pos.mpr
      have hDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
        apply Real.log_pos
        norm_num
      have hArg : 1 < (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
        have hTStrict : (1 : ℝ) < T := by linarith
        have hCube : (1 : ℝ) < T ^ (3 : ℕ) :=
          one_lt_pow₀ hTStrict (by norm_num)
        apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 0.6)).2
        norm_num [Real.rpow_natCast] at hCube ⊢
        linarith
      exact div_pos (Real.log_pos hArg) hDen
    dsimp only [base]
    exact_mod_cast (show
        2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M ≤
          4 * Nat.clog 2 A *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) by
      have hLogCap : Nat.clog 2 M ≤
          Nat.clog 2 A * classicalLocalMultiplicityCap T :=
        hClogMLe.trans (Nat.le_mul_of_pos_right _ (by omega))
      calc
        2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) * Nat.clog 2 M =
            4 * (2 * ⌈T ^ d⌉₊ + 1) * Nat.clog 2 M := by ring
        _ ≤ 4 * Nat.clog 2 A *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) := by
          have := Nat.mul_le_mul_left (4 * (2 * ⌈T ^ d⌉₊ + 1)) hLogCap
          simpa only [mul_assoc, mul_left_comm, mul_comm] using this)
  have hLossAt := hLoss T Q k hTLoss (by
      dsimp only [Q]
      exact (one_lt_pow₀ hPOne hk.ne').trans_le
        (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))) hk hkB
    (by nlinarith [hFinalScale])
  have hOuterPow : Ploss ^ (6 : ℕ) ≤
      T ^ (24 * d * B) *
        (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
    have hp := pow_le_pow_left₀ (by positivity) hOuter 6
    pm_106 hkReal k B hkB
    calc
      Ploss ^ (6 : ℕ) ≤
          (T ^ (4 * d * k) *
            (1 + classicalTypeIIPowerLoss E d T k Q)) ^ (6 : ℕ) := hp
      _ = T ^ (24 * d * k) *
          (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 2
        ring
      _ ≤ T ^ (24 * d * B) *
          (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ) := by
        gcongr
  have hExtraExponent : 3 * d + 24 * d * B + 2 * s / tau0 ≤ eps / 100 := by
    have hEtaQuarter : eta / 4 = eps / 400 := by dsimp only [eta]; ring
    rw [hEtaQuarter] at hdBudget
    have hLeft : 3 * d + 24 * d * B + 2 * s / tau0 ≤
        24 * d * B + 2 * s / tau0 + 6 * d := by linarith [hd.le]
    have hRight : eps / 400 ≤ eps / 100 := by linarith
    exact hLeft.trans (hdBudget.trans hRight)
  have hExtraRpow : T ^ (3 * d) *
      (T ^ (24 * d * B) * T ^ (2 * s / tau0)) ≤ T ^ (eps / 100) := by
    pm_4663
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - sigma) / tau0) := by positivity
  have hEndpoint' := hEndpoint
  have hEpsCombine : T ^ (eps / 4) * T ^ (eps / 4) *
      T ^ (eps / 100) ≤ T ^ eps := by
    pm_4663
  have hExtractionBound : (extraction : ℝ) ≤ (base : ℝ) * k := by
    simpa only [extraction, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right hExtraLeBase
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hQOne : 1 < Q := by
    dsimp only [Q]
    exact (one_lt_pow₀ hPOne hk.ne').trans_le
      (Nat.le_mul_of_pos_left _ (pow_pos (by omega) q))
  have hHarmNonneg : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    pm_1122
  have hGNonneg : 0 ≤ K * (1 + (((harmonic Q : ℚ) : ℝ))) :=
    mul_nonneg hK.le (by linarith)
  have hOldNonneg : 0 ≤
      6 * Ploss ^ (6 : ℕ) *
        (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by linarith [hPloss]) 6))
      (mul_nonneg (pow_nonneg (by positivity) 2)
        (Real.rpow_nonneg hTPos.le _))
  have hPowerLossBound :
      6 * Ploss ^ (6 : ℕ) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) ≤
        (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by
    calc
      6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) ≤
          6 * (T ^ (24 * d * B) *
            (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)) := by
        gcongr
      _ = (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by ring
  have hInnerBound :
      ((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          (6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) ≤
        (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by
    calc
      ((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
            (6 * Ploss ^ (6 : ℕ) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) ≤
          (((base : ℝ) * k) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
            (6 * Ploss ^ (6 : ℕ) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hExtractionBound hGNonneg)
          hOldNonneg
      _ ≤ (((base : ℝ) * k) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          ((6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by
        exact mul_le_mul_of_nonneg_left hPowerLossBound
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hGNonneg)
      _ = (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) := by ring
  have hCoverSimple : (cover : ℝ) ≤ Ccover * T ^ (eps / 4) := by
    have hAOne : 1 < ⌊sharpZetaCutoff T⌋₊ := by
      pm_6760
      exact (show (2 : ℝ) ≤ 4 * T by
        calc
          (2 : ℝ) ≤ 4 * 8 := by norm_num
          _ ≤ 4 * T := mul_le_mul_of_nonneg_left hTEight (by norm_num)).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hSecondClog : (1 : ℝ) ≤
        Nat.clog 2 (⌊sharpZetaCutoff T⌋₊ + 1) := by
      pm_4668
    have hCoverOne : (1 : ℝ) ≤ Nat.clog 2 (A + 1) := by
      simpa only [A] using hSecondClog
    pm_4802 hnonneg cover
    calc
      (cover : ℝ) = (cover : ℝ) * 1 := by ring
      _ ≤ (cover : ℝ) * Nat.clog 2 (A + 1) :=
        mul_le_mul_of_nonneg_left hCoverOne hnonneg
      _ ≤ Ccover * T ^ (eps / 4) := by
        simpa only [cover, A] using hCoverAt
  have hBaseAt' : (base : ℝ) ≤ Cmult * T ^ (3 * d) := by
    calc
      (base : ℝ) ≤ Cmult * T ^ (d + 2 * d) := by
        simpa only [base, A, hA] using hBaseAt
      _ = Cmult * T ^ (3 * d) := by
        congr 1
        ring_nf
  have hLossAt' :
      (base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ)) ≤
        Closs * T ^ (eps / 4) := by
    simpa only [base, A, hA] using hLossAt
  have hMiddleRpow :
      (Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) ≤
        (Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100)) := by
    calc
      (Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0))) =
          (Cmult * Closs * T ^ (eps / 4) * (((2 : ℝ) ^ B) ^ (2 : ℕ))) *
            (T ^ (3 * d) *
              (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by ring
      _ ≤ (Cmult * Closs * T ^ (eps / 4) * (((2 : ℝ) ^ B) ^ (2 : ℕ))) *
          T ^ (eps / 100) :=
        mul_le_mul_of_nonneg_left hExtraRpow (by positivity)
      _ = (Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100)) := by ring
  calc
    (zeroCountRect sigma 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
    _ = ((cover : ℝ) * (base : ℝ)) *
        (((extraction : ℝ) * (K * (1 + (((harmonic Q : ℚ) : ℝ))))) *
          (6 * Ploss ^ (6 : ℕ) *
            (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      dsimp only [base, cover, extraction] at hEndpoint' ⊢
      pm_8126
    _ ≤ ((cover : ℝ) * (base : ℝ)) *
        (((base : ℝ) * k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      apply mul_le_mul_of_nonneg_right _ hTargetNonneg
      exact mul_le_mul_of_nonneg_left hInnerBound (by positivity)
    _ ≤ (Ccover * T ^ (eps / 4)) *
        ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4)) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0)))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      have hFront :
          ((cover : ℝ) * (base : ℝ)) *
              ((base : ℝ) * k *
                (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) ≤
            (Ccover * T ^ (eps / 4)) *
              ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4))) := by
        calc
          ((cover : ℝ) * (base : ℝ)) *
                ((base : ℝ) * k *
                  (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                  (6 * (1 + classicalTypeIIPowerLoss E d T k Q) ^ (6 : ℕ))) ≤
              (Ccover * T ^ (eps / 4)) * (Cmult * T ^ (3 * d)) *
                (Closs * T ^ (eps / 4)) := by gcongr
          _ = (Ccover * T ^ (eps / 4)) *
              ((Cmult * T ^ (3 * d)) * (Closs * T ^ (eps / 4))) := by ring
      apply mul_le_mul_of_nonneg_right _ hTargetNonneg
      have hFactorNonneg : 0 ≤
          (((2 : ℝ) ^ B) ^ (2 : ℕ) *
            (T ^ (24 * d * B) * T ^ (2 * s / tau0))) := by positivity
      have h := mul_le_mul_of_nonneg_right hFront hFactorNonneg
      convert h using 1 <;> ring
    _ ≤ (Ccover * T ^ (eps / 4)) *
        ((Cmult * (Closs * T ^ (eps / 4))) *
          (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100))) *
          T ^ (3 * (1 - sigma) / tau0) := by
      pm_8520 hOuterNonneg eps
      have h := mul_le_mul_of_nonneg_left hMiddleRpow hOuterNonneg
      have h' := mul_le_mul_of_nonneg_right h hTargetNonneg
      exact h'
    _ ≤ C * T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by
      dsimp only [C]
      calc
        (Ccover * T ^ (eps / 4)) *
            ((Cmult * (Closs * T ^ (eps / 4))) *
              (((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (eps / 100))) *
              T ^ (3 * (1 - sigma) / tau0) =
          (Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            (T ^ (eps / 4) * T ^ (eps / 4) * T ^ (eps / 100)) *
              T ^ (3 * (1 - sigma) / tau0) := by ring
        _ ≤ (Closs * Cmult * Ccover * ((2 : ℝ) ^ B) ^ (2 : ℕ)) *
            T ^ eps * T ^ (3 * (1 - sigma) / tau0) := by gcongr

/-! ## Checked reflected endpoint assembly -/

/-
noncomputable def mediumReflectedMHHExponent (σ τ : ℝ) : ℝ :=
  max (1 - 2 * σ / τ)
    (min (1 + (1 - 2 * σ) / τ)
      (2 + (2 - 6 * σ) / τ))

theorem mediumReflectedMHHExponent_le_endpoint
    {σ τ₀ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτ₀ : τ₀ < τ) (hτPos : 0 < τ)
    (hτTwo : τ < 2) (hτUpper : τ < 4 * τ₀ / 3)
    (hNotWeyl : 6 * σ - 3 ≤ τ) :
    mediumReflectedMHHExponent σ τ ≤
      3 * (1 - σ) / τ₀ := by
  have hτ₀Pos := hcert.tau0_pos
  rw [mediumReflectedMHHExponent, max_le_iff]
  constructor
  · rw [le_div_iff₀ hτ₀Pos]
    field_simp [hτPos.ne']
    rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
    · by_cases hsign : 0 ≤ τ - 2 * σ
      · have hmul := mul_le_mul_of_nonneg_left hI hsign
        nlinarith
      · nlinarith
    · by_cases hsign : 0 ≤ τ - 2 * σ
      · have hmul := mul_le_mul_of_nonneg_left hH hsign
        nlinarith
      · nlinarith
  · rw [min_le_iff]
    by_cases hswitch : τ ≤ 4 * σ - 1
    · right
      rw [le_div_iff₀ hτ₀Pos]
      field_simp [hτPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ 2 * τ + 2 - 6 * σ
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ 2 * τ + 2 - 6 * σ
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
    · left
      have hswitch' : 4 * σ - 1 < τ := lt_of_not_ge hswitch
      rw [le_div_iff₀ hτ₀Pos]
      field_simp [hτPos.ne']
      rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
      · by_cases hsign : 0 ≤ τ + 1 - 2 * σ
        · have hmul := mul_le_mul_of_nonneg_left hI hsign
          nlinarith
        · nlinarith
      · by_cases hsign : 0 ≤ τ + 1 - 2 * σ
        · have hmul := mul_le_mul_of_nonneg_left hH hsign
          nlinarith
        · nlinarith
-/

/-- A classified interior source block in the endpoint gap cannot have
physical logarithmic scale at least two.  The endpoint certificate first
forces the Huxley alternative and hence `σ > 5/6`; the strengthened common
loss parameter then pays for the detector and source-selection losses in
the physical Weyl estimate. -/
theorem eventually_medium_source_tau_ge_two_impossible
    {σ τ₀ ε : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ {T τ : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
        2 * (2 ^ r * Y) ≤ A →
        τ = typeILogarithmicScale T (2 ^ r * Y) →
        2 ≤ τ → τ < 4 * τ₀ / 3 →
        T ^ d ≤ T / 2 → W.Nonempty →
        (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
        (∀ t ∈ W,
          ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
              (Nat.clog 2 A + 1 : ℕ) ≤
            ‖typeISourceSmoothBlock Y A r σ t‖) →
        False := by
  pm_5039
  pm_4679
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, _hdGap,
    _hdUpper, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  by_cases hσFiveSixths : 5 / 6 < σ
  · let q : ℝ := 2 * σ - 5 / 3
    pm_4638 hq q
    have hdFiveSixths : d ≤ (σ - 5 / 6) / 1000 := by
      dsimp only [d]
      exact classicalEndpointLossParameter_le_fiveSixthsGap hσFiveSixths
    let v : ℝ := q / 72
    pm_116 hv v
    have hBudget : d ^ 4 + v < q / 18 := by
      pm_4678
      have hdFourth : d ^ 4 ≤ d := by
        nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
      have hdq : d ≤ q / 2000 := by
        dsimp only [q] at hdFiveSixths ⊢
        linarith
      dsimp only [v]
      nlinarith
    pm_3983 Clog _hClog Tlog hTlog hLogs eventually_source_selection_log_product_le v hv
    obtain ⟨Tfar, hTfar, hFar⟩ := eventually_source_far_family_impossible
      hσUpper hq (by dsimp only [q]; linarith) hBudget
    let T₀ : ℝ := max Tlog Tfar
    pm_4266 T₀ hTlog.trans le_max_left
    intro T τ Y A r W hT
    dsimp only
    intro hA hY hr hInterior hτ hτTwo hτUpper hDisp hW hRange hLarge
    pm_4630 hTLog Tlog le_max_left hT
    pm_4630 hTFar Tfar le_max_right hT
    have hLogProduct := hLogs T hTLog
    have hAOne : 1 < A := by
      rw [hA]
      pm_6760
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith [hTlog]).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hSecond : (1 : ℝ) ≤ Nat.clog 2 (A + 1) := by
      pm_7558
    have hFirstNonneg : (0 : ℝ) ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) := by
      positivity
    have hLog : ((Nat.clog 2 A + 1 : ℕ) : ℝ) ≤ Clog * T ^ v := by
      calc
        ((Nat.clog 2 A + 1 : ℕ) : ℝ) =
            ((Nat.clog 2 A + 1 : ℕ) : ℝ) * 1 := by ring
        _ ≤ ((Nat.clog 2 A + 1 : ℕ) : ℝ) * Nat.clog 2 (A + 1) :=
          mul_le_mul_of_nonneg_left hSecond hFirstNonneg
        _ ≤ Clog * T ^ v := by simpa only [hA] using hLogProduct
    have hCertAlternative := endpointScaleCertificate_tau0_alternative hσUpper hcert
    have hTauFar : τ < 6 * σ - 3 - q := by
      rcases hCertAlternative with hI | hH
      pm_1438
      · have hBound : 4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
        dsimp only [q]
        nlinarith
    exact hFar W hTFar hA hY hr hInterior hτ hτTwo hTauFar hDisp hW
      hRange hLog (by simpa only [d] using hLarge)
  · refine ⟨8, le_rfl, ?_⟩
    intro T τ Y A r W hT
    dsimp only
    intro _hA _hY _hr _hInterior _hτ hτTwo hτUpper _hDisp _hW _hRange _hLarge
    have hσLe : σ ≤ 5 / 6 := le_of_not_gt hσFiveSixths
    rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
    pm_1438
    · have hBound : 4 * τ₀ / 3 ≤ 4 * (3 * σ - 1) / 3 := by gcongr
      nlinarith

section
variable {σ τ₀ : ℝ} (hσ : 1 / 2 < σ) (hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
include σ τ₀ hσ hσUpper hcert
/-- Complete consumer for the genuinely reflected source range.  It invokes
the actual pointwise Poisson reflection, selects its common signed dyadic
block, and then dispatches the exhaustive powered/Weyl scale split while
retaining the original multiplicity-weighted count. -/
theorem actual_interior_reflected_endpoint_consumer :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ {τ : ℝ} {r : ℕ} (W : Finset ℝ),
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          τ = typeILogarithmicScale T (2 ^ r * Y) →
          1 < τ → τ < 2 → W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  pm_5039
  let u : ℝ := d ^ 4
  pm_4679
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, hdGap,
    _hdUpper, _hdSigma, _hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  pm_4762
  have huD : u ≤ d := by
    dsimp only [u]
    pm_4678
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
  obtain ⟨Clog, _hClog, hCref, hg, hUscale, Tdata, hTdata, hData⟩ :=
    eventually_interior_source_reflected_dyadic_data hσ hσUpper hd hdOne
      hdGap hu.le huD
  obtain ⟨Cnear, hCnear, Tnear, hTnear, hNear⟩ :=
    actual_interior_reflected_near_endpoint_consumer hσ hσUpper hcert
      Clog ε hε
  let s : ℝ := reflectedEndpointScaleSlack σ d
  obtain ⟨Tfar, hTfar, hFar⟩ := eventually_reflected_far_dyadic_data_impossible
    hσ hσUpper hd huD rfl hUscale hCref
  let T₀ : ℝ := max Tdata (max Tnear Tfar)
  pm_7303 Cnear hCnear T₀ hTdata.trans
  intro T hT
  dsimp only
  intro τ r W hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep hRange
    hLarge hCount
  pm_4630 hTData Tdata le_max_left hT
  pm_4639 hRest Tnear Tfar hT
  pm_4630 hTNear Tnear le_max_left hRest
  pm_4630 hTFar Tfar le_max_right hRest
  have hTPos : 0 < T := by linarith [hTdata]
  pm_4680
  have hDataAt := hData (T := T) (tau := τ) (Y := Y) (A := A)
    (r := r) W hTData hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep
      hRange (by simpa only [u] using hLarge)
  dsimp only at hDataAt
  rcases hDataAt with ⟨j, hj, U, a, hSepU, hBaseU, hURange, hCardU,
    hCoeff, hLargeU, hOrdinate, hPOne, hPM, hThetaLower, hThetaUpper,
    hThresholdExact, _hThresholdGap⟩
  let P : ℕ := 2 ^ j
  pm_4897 Q r Y
  let M : ℕ := mediumTypeIDualCutoff T d Q
  pm_4674
  pm_4676 R V Q σ S
  let θ : ℝ := typeILogarithmicScale T P
  have hSplit := reflected_actual_scale_powered_gap_or_weyl_margin
    hσ hσUpper hcert hd (by simpa only [θ] using hThetaLower)
  dsimp only at hSplit
  rcases hSplit with hNearScale | hFarScale
  · apply hNear T hTNear W hA hY hr hLower hUpper hτ hτOne hτTwo hW hSep
      hRange (by simpa only [u] using hLarge) hCount
      (by simpa only [P] using hPOne) (by simpa only [P] using hThetaUpper)
      (by simpa only [P, θ] using hNearScale)
    refine ⟨j, U, a, rfl, hj, hSepU, hBaseU, hCardU, hCoeff, ?_, ?_, ?_⟩
    · simpa only [P, Q, M, V, R, S, L, u] using hLargeU
    · simpa only [P, M] using hPM
    · simpa only [Q, M, V, R, S, L, u] using hThresholdExact
  · have hUNonempty : U.Nonempty := by
      pm_4675
    have hQOne : 1 < Q := by
      dsimp only [Q]
      have hPow : 4 ≤ 2 ^ r := by
        pm_4703
      have : 4 ≤ 2 ^ r * Y := hPow.trans (Nat.le_mul_of_pos_right _ hY)
      omega
    have hScaleQ : (Q : ℝ) ^ τ = T := by
      rw [hτ]
      simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
    pm_4939 hQEq Q τ hQOne hScaleQ
    pm_734 hMUpperRaw mediumTypeIDualCutoff_cast_le T d Q hTPos.le
    pm_4677 τ
    exact (hFar hTFar hτOne hτTwo (by simpa only [P] using hPOne)
      (by simpa only [P, M] using hPM) (by rfl)
      (by simpa only [θ, P] using hThetaUpper)
      (by simpa only [θ, P] using hThetaLower)
      (by simpa only [s, θ, P] using hFarScale) hMUpper hUNonempty
      (by simpa only [P, L] using hLargeU)
      (by simpa only [P, M] using hOrdinate)
      (by simpa only [L, u] using hThresholdExact)).elim

/-- Exhaustive endpoint consumer for the literal smooth source block selected
from the detector's long tail.  Every alternative is discharged on the same
zero family and with the multiplicity factor retained: the lower family uses
direct powering, the terminal family is impossible, a near extracted dyadic
scale uses finite powering, and the remaining interior scale is either ruled
out by Weyl or consumed by the reflected B-process. -/
theorem actual_selected_source_endpoint_consumer :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r : ℕ, ∀ W : Finset ℝ,
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-(d ^ 4)) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r σ t‖) →
          zeroCountRect σ 1 T (2 * T) ≤
            (4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T)) *
                (Nat.clog 2 A + 1) * W.card →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  pm_5039
  let s := reflectedEndpointScaleSlack σ d
  pm_4679
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, hdGap,
    _hdUpper, _hdSigma, hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  have hdOneStrict : d < 1 := by
    pm_6309
    exact hdSmall.trans_lt (by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hDen)
  pm_4196 hs s reflectedEndpointScaleSlack_pos hσ hd
  have huD : d ^ 4 ≤ d := by
    pm_4678
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSqOne)]
  have huGap : d ^ 4 < σ - 1 / 2 :=
    huD.trans_lt (hdGap.trans_lt (by nlinarith [hσ]))
  pm_5305 Clower hClower Tlower hTlower hLower actual_lower_source_family_endpoint_consumer hσ
  pm_5305 Cnear hCnear Tnear hTnear hNear actual_source_near_endpoint_consumer hσ
  pm_5305 Cref hCref Tref hTref hRef actual_interior_reflected_endpoint_consumer hσ
  pm_4081 Tterminal hTterminal hTerminal eventually_no_terminal_classified_source hσ huGap
  obtain ⟨Tmargin, hTmargin, hMargin⟩ :=
    eventually_large_source_forces_complementary_margin hσUpper hd hdOneStrict
      hdGap huD
  pm_98 Tdisp hTdisp hDisp eventually_rpow_le_half_self d hdOneStrict
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_typeI_logarithmic_scale_upper (d ^ 2) (sq_pos_of_pos hd)
  obtain ⟨Tadd, hTadd, hAdd⟩ :=
    eventually_extracted_source_logarithmic_scale_lower_additive
      (δ := s) (U := 2 / (d ^ 2)) hs
      (div_pos (by norm_num) (sq_pos_of_pos hd))
  obtain ⟨Ttwo, hTtwo, hTwoImpossible⟩ :=
    eventually_medium_source_tau_ge_two_impossible hσ hσUpper hcert hε
  have hPowTop := tendsto_rpow_atTop (sq_pos_of_pos hd)
  have hEventuallyY := (tendsto_atTop.1 hPowTop) 16
  pm_4610 eventually_atTop hEventuallyY TY hTY
  let C : ℝ := max Clower (max Cnear Cref)
  let T₀ : ℝ := max Tlower
    (max Tnear (max Tref (max Tterminal
      (max Tmargin (max Tdisp (max Tscale (max Tadd (max Ttwo (max 8 TY)))))))))
  pm_8161 hC C hClower.trans_le
  have hT₀ : 8 ≤ T₀ := hTlower.trans (le_max_left _ _)
  pm_505 C hC T₀ hT₀
  intro T hT
  dsimp only
  intro r W hW hSep hRange hLarge hCount
  pm_4630 hTLower Tlower le_max_left hT
  have hRest₁ := (le_max_right Tlower _).trans hT
  pm_4630 hTNear Tnear le_max_left hRest₁
  have hRest₂ := (le_max_right Tnear _).trans hRest₁
  pm_4630 hTRef Tref le_max_left hRest₂
  have hRest₃ := (le_max_right Tref _).trans hRest₂
  pm_4630 hTTerminal Tterminal le_max_left hRest₃
  have hRest₄ := (le_max_right Tterminal _).trans hRest₃
  pm_4630 hTMargin Tmargin le_max_left hRest₄
  have hRest₅ := (le_max_right Tmargin _).trans hRest₄
  pm_4630 hTDisp Tdisp le_max_left hRest₅
  have hRest₆ := (le_max_right Tdisp _).trans hRest₅
  pm_4630 hTScale Tscale le_max_left hRest₆
  have hRest₇ := (le_max_right Tscale _).trans hRest₆
  pm_4630 hTAdd Tadd le_max_left hRest₇
  have hRest₈ := (le_max_right Tadd _).trans hRest₇
  pm_4630 hTTwo Ttwo le_max_left hRest₈
  have hRest₉ := (le_max_right Ttwo _).trans hRest₈
  pm_5456 hTEight le_max_left hRest₉
  pm_4630 hTYAt TY le_max_right hRest₉
  pm_4169
  pm_4680
  pm_4897 Q r Y
  let τ : ℝ := typeILogarithmicScale T Q
  pm_7592 hDispAt hDisp hTDisp
  have hScaleAt := hScale T r hTScale
  dsimp only at hScaleAt
  have hQOne : 1 < Q := by simpa only [Q, Y] using hScaleAt.1
  have hTauUpper : τ ≤ 2 / (d ^ 2) := by
    simpa only [τ, Q, Y] using hScaleAt.2
  have hY16 : 16 ≤ Y := by
    dsimp only [Y]
    apply Nat.le_floor
    exact hTY T hTYAt
  have hY : 0 < Y := by omega
  have hAOne : 1 < A := by
    dsimp only [A]
    pm_4735
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    have hAt := hRange t ht
    constructor <;> nlinarith
  have hPromote {C₁ : ℝ} (hC₁ : C₁ ≤ C)
      (hBound : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C₁ * T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    have hFirst : C₁ * T ^ ε ≤ C * T ^ ε :=
      mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hTPos.le ε)
    exact hBound.trans (mul_le_mul_of_nonneg_right hFirst
      (Real.rpow_nonneg hTPos.le (3 * (1 - σ) / τ₀)))
  by_cases hrLower : r < 2
  · apply hPromote (le_max_left _ _)
    exact hLower T hTLower r hrLower W hW hSep hBase
      (by simpa only [Y, A, d] using hLarge)
      (by simpa only [Y, A, d] using hCount)
  · have hrTwo : 2 ≤ r := Nat.le_of_not_gt hrLower
    rcases typeISourceSmoothScale_lower_terminal_or_interior
        (Y := Y) (A := A) (r := r) hY with hImpossible | hTerminalOrInterior
    · exact (hrLower hImpossible).elim
    · rcases hTerminalOrInterior with hTerminalScale | hInterior
      · change A < 2 * (2 ^ r * Y) at hTerminalScale
        exact (hTerminal T Y A r W hTTerminal rfl hY hrTwo
          hTerminalScale hW hSep (by simpa only [Y, A, d] using hLarge)
          (by simpa only [d] using hRange) hDispAt).elim
      · change ((((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2)) ∧
          2 * (2 ^ r * Y) ≤ A) at hInterior
        rcases hInterior with ⟨hSourceLower, hSourceUpper⟩
        let t := hW.choose
        have ht : t ∈ W := hW.choose_spec
        have hMarginAt := hMargin T t τ Y A r hTMargin rfl hY hrTwo
          hSourceUpper (hRange t ht).1 (hRange t ht).2 hDispAt rfl
          (by simpa only [Y, A, d] using hLarge t ht)
        have hTauOne : 1 < τ := by
          have hdScaled : 100 * d ≤ (σ - 1 / 2) / 10 := by
            calc
              100 * d ≤ 100 * ((σ - 1 / 2) / 1000) := by gcongr
              _ = (σ - 1 / 2) / 10 := by ring
          nlinarith
        pm_605 V
        pm_4838
        obtain ⟨j, hj, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, hPUpper,
          hPLower⟩ := extract_normalized_source_dyadic_block W hY hAOne hV hW
            hSep (by simpa only [V, Y, A, d] using hLarge)
        let P : ℕ := 2 ^ j
        have hQ16 : 16 ≤ Q := by
          pm_6903 Q
        have hExtractUpper := extracted_source_logarithmic_scale_upper hTOne
          (div_pos (by norm_num) (sq_pos_of_pos hd)) hQ16
          (by simpa only [Q, P] using hPLower) hTauUpper
        have hPOne : 1 < P := hExtractUpper.1
        have hTauPUpper : typeILogarithmicScale T P ≤ 4 / (d ^ 2) := by
          calc
            typeILogarithmicScale T P ≤ 2 * (2 / (d ^ 2)) := hExtractUpper.2
            _ = 4 / (d ^ 2) := by ring
        have hTauPos : 0 < τ := zero_lt_one.trans hTauOne
        have hAddAt := hAdd hTAdd hQOne hPOne (by simpa only [Q, P] using hPUpper)
          rfl hTauPos hTauUpper
        by_cases hNearScale : 4 * τ₀ / 3 - s ≤ typeILogarithmicScale T P
        · apply hPromote ((le_max_left Cnear Cref).trans (le_max_right Clower _))
          exact hNear T hTNear W W₀ hY hAOne hW hSep hBase hW₀sub hSep₀
            (by simpa only [A] using hCard₀)
            (by simpa only [Y, A, Q, P, V, d] using hLarge₀)
            (by simpa only [Q, P] using hPUpper)
            (by simpa only [Q, P] using hPLower) hPOne hTauPUpper
            (by simpa only [s] using hNearScale)
            (by simpa only [Y, A, d] using hCount)
        · have hTauUpperEndpoint : τ < 4 * τ₀ / 3 := by
            have hFar : typeILogarithmicScale T P < 4 * τ₀ / 3 - s :=
              lt_of_not_ge hNearScale
            linarith
          by_cases hTauTwo : 2 ≤ τ
          · exact (hTwoImpossible W hTTwo rfl hY hrTwo hSourceUpper rfl hTauTwo
              hTauUpperEndpoint hDispAt hW (by simpa only [d] using hRange)
              (by simpa only [Y, A, d] using hLarge)).elim
          · apply hPromote ((le_max_right Cnear Cref).trans (le_max_right Clower _))
            exact hRef T hTRef W rfl hY hrTwo hSourceLower hSourceUpper rfl
              hTauOne (lt_of_not_ge hTauTwo) hW hSep
              (by simpa only [d] using hRange)
              (by simpa only [Y, A, d] using hLarge)
              (by simpa only [Y, A, d] using hCount)
end

/-- The exact medium Type-I branch which remains after the direct and raised
scale consumers.  The long-tail lower bound is part of the same witness
returned by `classical_typeI_typeII_dichotomy_native`; retaining it here is
what permits a common source-smooth block to be selected without changing
the zero family or discarding analytic multiplicity. -/
def ClassicalMediumTypeIWitnessConsumer : Prop :=
  ∀ {σ τ₀ : ℝ}, 1 / 2 < σ → σ < 1 →
    EndpointScaleCertificate σ τ₀ →
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
          (∀ t ∈ W,
            (3 / 4) * (T ^ (-d ^ 4) / 2) ≤
              ‖classicalZetaLongTail Y A
                ((σ : ℂ) + I * (t : ℂ))‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          τ₀ < typeILogarithmicScale T (2 ^ r * Y) →
          11 / 10 < typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) < 4 * τ₀ / 3 →
           (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
             C * T ^ ε * T ^ (3 * (1 - σ) / τ₀)

/-- Native implementation of the remaining medium Type-I interface.  It
starts from the actual long-tail component of the detector dichotomy, selects
one common smooth source scale, transfers the original multiplicity-weighted
count through the exact `Nat.clog` cover, and invokes the exhaustive source
consumer above. -/
theorem classical_medium_typeI_witness_consumer_native :
    ClassicalMediumTypeIWitnessConsumer := by
  intro σ τ₀ hσ hσUpper hcert ε hε
  pm_5305 C hC T₀ hT₀ hSelected actual_selected_source_endpoint_consumer hσ
  pm_505 C hC T₀ hT₀
  intro T hT
  dsimp only
  intro r _hr W hSep _hLine hTail hRange hCount _hTauEndpoint _hTauLower
    _hTauUpper
  pm_5039
  pm_4680
  have hTPos : 0 < T := by linarith [hT₀]
  by_cases hW : W.Nonempty
  · have hWpos : 0 < W.card := hW.card_pos
    obtain ⟨r₀, hr₀, W₀, hW₀sub, hSep₀, hCard₀, hLarge₀, _hClass⟩ :=
      actual_medium_long_tail_selects_classified_source
        (T := T) (d := d) (σ := σ)
        (V := (3 / 4) * (T ^ (-(d ^ 4)) / 2)) W (by linarith [hT₀])
        hW hSep (by simpa only [Y, A, d] using hTail)
    have hW₀ : W₀.Nonempty := by
      by_contra hnot
      have hzero : W₀.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hnot)
      rw [hzero, mul_zero] at hCard₀
      omega
    have hRange₀ : ∀ t ∈ W₀, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d := by
      intro t ht
      exact hRange t (hW₀sub ht)
    pm_4654
    have hCount₀ : zeroCountRect σ 1 T (2 * T) ≤
        base * (Nat.clog 2 A + 1) * W₀.card := by
      calc
        zeroCountRect σ 1 T (2 * T) ≤ base * W.card := by
          simpa only [base, A, d] using hCount
        _ ≤ base * ((Nat.clog 2 A + 1) * W₀.card) :=
          Nat.mul_le_mul_left base hCard₀
        _ = base * (Nat.clog 2 A + 1) * W₀.card := by ring
    exact hSelected T hT r₀ W₀ hW₀ hSep₀
      (by simpa only [d] using hRange₀)
      (by simpa only [Y, A, d] using hLarge₀)
      (by simpa only [base, Y, A, d] using hCount₀)
  · have hWzero : W.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hZeroCount : zeroCountRect σ 1 T (2 * T) = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hWzero, mul_zero] using hCount
    rw [hZeroCount]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hTPos.le ε))
      (Real.rpow_nonneg hTPos.le (3 * (1 - σ) / τ₀))

end GuthMaynard.NativeMoment

-- Generated closures: source context is replayed in the next part.
end
