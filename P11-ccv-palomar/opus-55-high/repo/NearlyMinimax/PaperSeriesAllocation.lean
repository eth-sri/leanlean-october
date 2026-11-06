module

public import NearlyMinimax.PaperDegreeGuards
public import NearlyMinimax.PilotSeriesEnvelope
public import NearlyMinimax.ActualVarianceAllocation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The genuine factorial-pilot envelope is bounded by the scalar allocation.
Every degree and sample-denominator guard follows from the actual paper profile. -/
𝚷
𝚪
𝚨
𝚭
𝚩

𝗇 𝔇 Fintype.card (incrementVariables 𝗣) * preconditionedPilotMomentConstant C C.order
def paperPilotMomentFactor (C : ModelConstants d) (A : ℝ) : ℝ :=
  A ^ 2 * 𝔇

𝗃 𝔔 ἀ C A
theorem paperPilotMomentFactor_nonneg (C : ModelConstants d) A :
    0 ≤ 𝔔 paperPilotMomentFactor := 𝖧₁ $ 𝚍₁ (preconditionedPilotMomentConstant_pos C _).le

𝗇 𝔊 m + 𝗣 + 1
𝗇 𝔓 𝘟
𝗇 𝔍 𝔔 paperPilotMomentFactor * 𝔓 / Λ
theorem dyadicPilotSeries_eq_factorialSeries (C : ModelConstants d)
    A Λ j m :
    𝔔 dyadicPilotSeries Λ j m = factorialSeries 𝔊
      𝔍 := by
  unfold dyadicPilotSeries factorialSeries paperPilotMomentFactor
  simpa only [mul_assoc] using Fin.sum_univ_eq_sum_range (fun k =>
     (𝘆).factorial *
      (A ^ 2 * (𝔇 * 𝔓) / Λ) ^ 𝘆)
    𝔊

theorem factorialSeries_mono_argument D (hx : 0 ≤ x) (hxy : 𝗪₂) :
    factorialSeries D x ≤ factorialSeries D y := by
  unfold factorialSeries
  bound

𝗇 𝔈 12 * 𝔔 paperPilotMomentFactor ≤ C₀
/-- A genuine pilot block denominator and a fixed model constant dominate the
actual raw-feature moment argument. -/
theorem paper_pilot_series_argument_le (C : ModelConstants d) A
    (hn : 𝗧₁) (hΛ : n / 12 ≤ Λ)
    (hC : 𝔈) j :
    𝔍 ≤ C₀ * 𝔓 / n := by
  have hp := 𝔔 paperPilotMomentFactor_nonneg
  have hk := (dyadicPilotScale_pos d j).le
  apply (div_le_div_iff₀ ((div_pos hn 𝖠₄ ).trans_le hΛ) hn).mpr
  have hm := mul_le_mul_of_nonneg_right hC hk
  have hnΛ := mul_le_mul_of_nonneg_left hΛ $ mul_nonneg ((mul_nonneg  𝖠₄  hp).trans hC) hk
  nlinarith

𝗇 𝔄 𝚓₂
𝗇 𝔅 allocationWidth a offset n
𝗇 𝔉 allocationLevelPosition (paperDyadicStep C) a offset
𝗃 𝔖 ἀ C a offset 𝔄 n
𝗇 𝔎 𝔖 paperDyadicTotalDegree j
section

𝛇

𝗇 𝔏 (dyadicPilotScale_pos ..).le
𝗇 𝔐 𝔉 𝔄 n j
𝗇 𝔑 𝔖 paperDyadicApproximationDegree
𝗇 𝔒 profileVarianceWeight C₀ C_D (paperDegreeSlope C) 𝔅
/-- Exact total degree and original normalization give a levelwise domination
by the already-proved scalar variance profile. -/
theorem paper_pilot_series_weight_le_profile A a offset
    (hn : 𝗧₁) (hΛ : n / 12 ≤ Λ) (hΛn : Λ ≤ n)
    (hC : 0 < C₀) (hD : 0 < C_D) (hS : 0 < 𝔅)
    (hcoef : 𝔈) j
    (hdegree : 𝔎 =
      Nat.floor (paperDegreeSlope C * quadraticProfile 𝔅
        𝔐)) :
    𝔔 dyadicPilotSeries Λ j (𝔑 j) *
        max 1 (Λ / 𝔓) ≤
      𝔒
        𝔐 := by
  rw [actual_profileVarianceWeight_eq_cell_weight j hC hD hn hS, ← dyadicPilotScale_eq_exp C]
  rw [dyadicPilotSeries_eq_factorialSeries]
  have hΛpos := (div_pos hn 𝖠₄ ).trans_le hΛ
  have hseries := factorialSeries_mono_argument
    𝔎 (div_nonneg (mul_nonneg 𝔔 paperPilotMomentFactor_nonneg 𝔏) hΛpos.le)
    $ 𝔔 paper_pilot_series_argument_le hn hΛ hcoef j
  rw [hdegree] at hseries
  change factorialSeries 𝔎 _ * _ ≤ _
  rw [hdegree]
  exact mul_le_mul hseries (max_le_max le_rfl $ div_le_div_of_nonneg_right hΛn 𝔏 )
     𝖠₃  $ factorialSeries_nonneg _
      $ div_nonneg (mul_nonneg hC.le 𝔏) hn.le

/-- Uniform comparison of the actual maximum series on the actual three-block
pilot sample with the scalar maximum at H=C₀ C_D. -/
theorem eventually_paper_dyadic_series_envelope_le (hs : 𝘎) A a offset C₀ C_D
    (ha : 𝙆) (hC : 0 < C₀) (hD : 0 < C_D)
    (hcoef : 𝔈) :
    ∀ᶠ n : ℕ in atTop,
      𝔔 dyadicSeriesEnvelope ( threeBlockSize n / 2)
        𝔖 paperDyadicTerminalLevel
        𝔑 ≤
      actualVarianceMaximum (paperDyadicStep C) a offset C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) n := by
  have hwidth :=
    tendsto_natCast_atTop_atTop.eventually
      $ (allocationWidth_tendsto_atTop ha offset).eventually $ eventually_gt_atTop 0
  filter_upwards [ tendsto_natCast_atTop_atTop.eventually $ eventually_paper_total_degree_eq_floor C hs a offset 𝔄 ha , hwidth, eventually_ge_atTop 6] with n hd hS h6
  have hΛn : 𝚝 / 2 ≤ n := by
    have hm : threeBlockSize n ≤ n := by unfold threeBlockSize; omega
    have hmR : 𝚝 ≤ n := by exact_mod_cast hm
    linarith
  unfold dyadicSeriesEnvelope
  apply Finset.sup'_le
  intro j _
  apply (𝔔 paper_pilot_series_weight_le_profile a offset  𝖠₃  (by linarith [threeBlockSize_fraction h6]) hΛn hC hD hS hcoef j.val $ hd j.val ).trans
  exact Finset.le_sup'
     (fun i => 𝔒
      $ 𝔉 𝔄 n i ) $ Finset.mem_range.mpr j.isLt
