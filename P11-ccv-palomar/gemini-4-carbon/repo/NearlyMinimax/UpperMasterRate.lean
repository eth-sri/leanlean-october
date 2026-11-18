module

public import NearlyMinimax.CoefficientPairEstimator
public import NearlyMinimax.DyadicPilotMultilevel
public import NearlyMinimax.SaddleAsymptotics

@[expose] public section

noncomputable section
open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

-- 1. Quadratic allocation profile & level positions

def quadraticProfile (S z : ℝ) : ℝ := S / 4 + (S - z) ^ 2 / S

private theorem quadraticProfile_lower {S z : ℝ} (hS : 0 < S) :
    S / 4 ≤ quadraticProfile S z :=
  le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hS.le)

private theorem quadraticProfile_coarse_bound {S z : ℝ} (hS : 2 ≤ S) (hz : z ≤ 0) :
    Real.exp z * quadraticProfile S z ≤ 5 * S / 4 := by
  have hSp : 0 < S := by linarith
  let f : ℝ → ℝ := fun x => Real.exp x * quadraticProfile S x
  have hd (x : ℝ) : HasDerivAt f (Real.exp x * (quadraticProfile S x + 2 * (x - S) / S)) x := by
    have hq : HasDerivAt (quadraticProfile S) (2 * (x - S) / S) x := by
      convert (hasDerivAt_const x (S / 4)).add
        (((hasDerivAt_const x S).sub (hasDerivAt_id x)).pow 2 |>.div_const S) using 1
      · funext y; simp [quadraticProfile, div_eq_mul_inv]
      · simp only [Pi.sub_apply, id_eq]; ring
    convert (Real.hasDerivAt_exp x).mul hq using 1; ring
  have hm : MonotoneOn f (Iic 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iic 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [(hd x).deriv]
    have hx0 : x ≤ 0 := by simpa using interior_subset hx
    have hprod : 0 ≤ (S - x) * (S - x - 2) := mul_nonneg (by linarith) (by linarith)
    have hid : quadraticProfile S x + 2 * (x - S) / S =
        ((S - x) * (S - x - 2) + S ^ 2 / 4) / S := by dsimp [quadraticProfile]; field_simp; ring
    rw [hid]; positivity
  have h := hm hz (by simp) hz
  have hzero : f 0 = 5 * S / 4 := by dsimp [f, quadraticProfile]; rw [Real.exp_zero, one_mul]; field_simp; ring
  rwa [hzero] at h

def terminalAllocationLevel (δ a C H γ x : ℝ) : ℕ :=
  Nat.floor ((Real.log x + candidateTerminalDepth a C H γ x) / δ)

def allocationLevelPosition (δ a C H x : ℝ) (j : ℕ) : ℝ :=
  δ * (j : ℝ) - Real.log x + Real.log (H * allocationWidth a C x)

private theorem eventually_actual_allocation_level_range {δ a H γ : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ j ≤ terminalAllocationLevel δ a C H γ x,
      -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
        allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hw := allocationWidth_tendsto_atTop ha C
  filter_upwards [hw.eventually (eventually_ge_atTop (1 : ℝ)),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg ha hH C γ] with x hS hHS hLT j hj
  have hell : 0 ≤ Real.log (H * allocationWidth a C x) := Real.log_nonneg hHS
  have hlogS : 0 ≤ Real.log (allocationWidth a C x) := Real.log_nonneg hS
  have hjreal : (j : ℝ) ≤ (terminalAllocationLevel δ a C H γ x : ℝ) := by exact_mod_cast hj
  have hum : δ * (terminalAllocationLevel δ a C H γ x : ℝ) ≤
      Real.log x + candidateTerminalDepth a C H γ x := by
    have hf := mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hLT hδ.le)) hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at hf
  have hmj := mul_le_mul_of_nonneg_left hjreal hδ.le
  unfold allocationLevelPosition
  refine ⟨by linarith [mul_nonneg hδ.le (Nat.cast_nonneg j)], ?_⟩
  unfold candidateTerminalDepth at hum
  linarith [mul_nonneg hγ hlogS]

-- 2. Dyadic spatial rounding & paper upper parameters

def dyadicLevelFromLogSide (ell : ℝ) : ℕ := Nat.ceil (-ell / Real.log 2)

def dyadicRoundedLogSide (ell : ℝ) : ℝ := -Real.log 2 * (dyadicLevelFromLogSide ell : ℝ)

def dyadicRoundedSide (ell : ℝ) : ℝ := Real.exp (dyadicRoundedLogSide ell)

private theorem dyadicRoundedLogSide_bounds {ell : ℝ} (hell : ell ≤ 0) :
    ell - Real.log 2 < dyadicRoundedLogSide ell ∧ dyadicRoundedLogSide ell ≤ ell := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ -ell / Real.log 2 := div_nonneg (neg_nonneg.mpr hell) hl.le
  have hlo := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hq) hl
  have hhi := mul_le_mul_of_nonneg_right (Nat.le_ceil (-ell / Real.log 2)) hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hhi
  rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at hlo
  unfold dyadicRoundedLogSide dyadicLevelFromLogSide
  constructor <;> linarith only [hlo, hhi]

theorem dyadicRoundedSide_eq_inv_pow (ell : ℝ) :
    dyadicRoundedSide ell = ((2 : ℝ) ^ dyadicLevelFromLogSide ell)⁻¹ := by
  unfold dyadicRoundedSide dyadicRoundedLogSide
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

def paperDyadicStep {d : ℕ} (_C : ModelConstants d) : ℝ := (d : ℝ) * Real.log 2

def paperSpatialExponent {d : ℕ} (C : ModelConstants d) : ℝ := (C.smoothness - 1) / (d : ℝ)

def paperDegreeSlope {d : ℕ} (C : ModelConstants d) : ℝ := paperSpatialExponent C / paperTau C

def paperDegreeReserve {d : ℕ} (C : ModelConstants d) : ℝ :=
  ((anchoredDimension d C.order : ℝ) + 1 / 2) / paperSpatialExponent C

def paperUpperVarpi {d : ℕ} (C : ModelConstants d) : ℝ :=
  ((d : ℝ) - 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperEta {d : ℕ} (C : ModelConstants d) : ℝ :=
  2 * ((d : ℝ) + 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperSaddle {d : ℕ} (C : ModelConstants d) : ℝ :=
  upperSaddleCoefficient C.smoothness d (paperTau C)

def paperUpperShift {d : ℕ} (C : ModelConstants d) : ℝ :=
  1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C

def paperUpperRiskDepthCoefficient {d : ℕ} (C : ModelConstants d) : ℝ :=
  2 * (C.smoothness - 1) / ((d : ℝ) + 4)

def paperDyadicTerminalLevel {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) : ℕ :=
  terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n

def paperDyadicApproximationDegree {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
    (allocationLevelPosition (paperDyadicStep C) a offset H n j)) - paperPolynomialDimension C

def paperDyadicTotalDegree {d : ℕ} (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  paperDyadicApproximationDegree C a offset H n j + anchoredDimension d C.order + 1

private theorem paperDyadicStep_pos {d : ℕ} (C : ModelConstants d) : 0 < paperDyadicStep C :=
  mul_pos (Nat.cast_pos.mpr C.dimension_pos) (Real.log_pos (by norm_num))

private theorem paperSpatialExponent_pos {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperSpatialExponent C := div_pos (sub_pos.mpr hs) (Nat.cast_pos.mpr C.dimension_pos)

private theorem paperDegreeSlope_pos {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)

private theorem paperDegreeReserve_pos {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperDegreeReserve C := by
  unfold paperDegreeReserve; exact div_pos (by positivity) (paperSpatialExponent_pos C hs)

private theorem paperUpperEta_pos {d : ℕ} (C : ModelConstants d) : 0 < paperUpperEta C := by
  have : (0 : ℝ) < d := Nat.cast_pos.mpr C.dimension_pos
  have := C.smoothness_pos; unfold paperUpperEta; positivity

theorem paperUpperSaddle_pos {d : ℕ} (C : ModelConstants d) (hreg : highSmoothnessRegime C) :
    0 < paperUpperSaddle C := by
  have : (0 : ℝ) < d := Nat.cast_pos.mpr C.dimension_pos
  have : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  have := paperTau_pos C
  unfold paperUpperSaddle upperSaddleCoefficient; positivity

private theorem paperUpperRiskDepthCoefficient_pos {d : ℕ} (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperUpperRiskDepthCoefficient C := by
  have : (0 : ℝ) < d := Nat.cast_pos.mpr C.dimension_pos
  unfold paperUpperRiskDepthCoefficient
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hs)) (by positivity)

private theorem dyadicPilotScale_eq_exp {d : ℕ} (C : ModelConstants d) (j : ℕ) :
    dyadicPilotScale d j = Real.exp (paperDyadicStep C * (j : ℝ)) := by
  have hl : Real.log (dyadicPilotScale d j) = paperDyadicStep C * (j : ℝ) := by
    unfold dyadicPilotScale paperDyadicStep; rw [Real.log_pow, Real.log_pow]; ring
  rw [← hl, Real.exp_log (dyadicPilotScale_pos d j)]

private theorem quadratic_allocation_budget {β H t S : ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hS : 0 ≤ S) (hdef : S = t - (1 + 2 * H / β)) :
    β * S ^ 2 / 4 + H * S ≤ β * t ^ 2 / 4 := by
  have ht : t = S + (1 + 2 * H / β) := by linarith
  have hid : β * t ^ 2 / 4 - (β * S ^ 2 / 4 + H * S) = β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by
    rw [ht]; field_simp; ring
  have hn : 0 ≤ β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by positivity
  linarith

private theorem paper_upper_saddle_budget_identity {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 = 2 * paperUpperVarpi C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hsp : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have htau := paperTau_pos C
  have hgap : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  unfold paperDegreeSlope paperSpatialExponent paperUpperSaddle upperSaddleCoefficient paperUpperVarpi
  rw [Real.sq_sqrt (by positivity)]; field_simp; ring

private theorem paper_spatial_reserve_identity {d : ℕ} (C : ModelConstants d)
    (L T : ℝ) :
    2 * spatialBalanceLog C.smoothness d L T + 2 / (d : ℝ) * (L + T) =
      -2 * paperUpperVarpi C * L + paperUpperEta C * T := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  unfold spatialBalanceLog paperUpperVarpi paperUpperEta; field_simp; ring

-- 3. Degree sample-size guards

private theorem eventually_paper_total_degree_eq_floor {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℝ in atTop, ∀ j : ℕ,
      paperDyadicTotalDegree C a offset H n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset H n j)) := by
  have hβ := paperDegreeSlope_pos C hs
  have hpdim : paperPolynomialDimension C = anchoredDimension d C.order + 1 := by
    unfold paperPolynomialDimension anchoredDimension
    rw [anchoredIndex_card]; have := Nat.choose_pos (n := d + C.order) (k := d) (by omega); omega
  filter_upwards [eventually_width_degree_threshold ha hβ offset (paperPolynomialDimension C),
    (allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop (0 : ℝ))] with n hn hS j
  have hQ := mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := allocationLevelPosition (paperDyadicStep C) a offset H n j) hS) hβ.le
  have hq : paperPolynomialDimension C ≤ Nat.floor
      (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset H n j)) :=
    Nat.le_floor (by linarith)
  unfold paperDyadicTotalDegree paperDyadicApproximationDegree
  rw [Nat.add_assoc, ← hpdim]
  exact Nat.sub_add_cancel hq

theorem eventually_paper_degree_three_block_guards {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      paperDyadicTotalDegree C a offset H n j ≤ threeBlockSize n ∧
      0 < (threeBlockSize n : ℝ) / 2 ∧
      (threeBlockSize n : ℝ) / 2 ≤
        (threeBlockSize n : ℝ) - (paperDyadicTotalDegree C a offset H n j : ℝ) + 1 := by
  have hβ := paperDegreeSlope_pos C hs
  have hγ := (paperDegreeReserve_pos C hs).le
  let K_deg := paperDegreeSlope C * ((2 * a) / 4 + (2 * a + 1) ^ 2 / (a / 2))
  have ht := allocationWidth_div_sqrt_log_limit a offset
  have hreal : ∀ᶠ x : ℝ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H x,
      (paperDyadicTotalDegree C a offset H x j : ℝ) < (1 / 8 : ℝ) * x := by
    filter_upwards [eventually_paper_total_degree_eq_floor C hs a offset H ha,
      ht.eventually (lt_mem_nhds (by linarith : a / 2 < a)),
      ht.eventually (gt_mem_nhds (by linarith : a < 2 * a)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_actual_allocation_level_range (paperDyadicStep_pos C) ha hH hγ offset,
      eventually_log_power_lt_sample (3 / 2) K_deg (by norm_num : (0 : ℝ) < 1 / 8)]
      with x he hlo hhi hL hz hlt j hj
    rw [he]
    let L := Real.log x
    let S := allocationWidth a offset x
    let z := allocationLevelPosition (paperDyadicStep C) a offset H x j
    have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hsqrt : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
    have hSl : (a / 2) * Real.sqrt L ≤ S := ((lt_div_iff₀ hsqrt).mp hlo).le
    have hSu : S ≤ (2 * a) * Real.sqrt L := ((div_lt_iff₀ hsqrt).mp hhi).le
    have hS : 0 < S := (mul_pos (by positivity) hsqrt).trans_le hSl
    obtain ⟨hzl, hzu⟩ := hz j hj
    have hsqrtL : Real.sqrt L ≤ L := (Real.sqrt_le_left hL0.le).mpr (by nlinarith)
    have hSC : S ≤ (2 * a) * L := hSu.trans (mul_le_mul_of_nonneg_left hsqrtL (by positivity))
    have hsq : (S - z) ^ 2 ≤ ((2 * a + 1) * L) ^ 2 :=
      (sq_le_sq₀ (sub_nonneg.mpr hzu) (by positivity)).mpr (by nlinarith)
    have hdenom : 0 < (a / 2) * Real.sqrt L := mul_pos (by positivity) hsqrt
    have hterm : (S - z) ^ 2 / S ≤ ((2 * a + 1) ^ 2 / (a / 2)) * (L * Real.sqrt L) := by
      calc (S - z) ^ 2 / S ≤ (S - z) ^ 2 / ((a / 2) * Real.sqrt L) :=
            div_le_div_of_nonneg_left (sq_nonneg _) hdenom hSl
        _ ≤ ((2 * a + 1) * L) ^ 2 / ((a / 2) * Real.sqrt L) :=
            div_le_div_of_nonneg_right hsq hdenom.le
        _ = ((2 * a + 1) ^ 2 / (a / 2)) * (L ^ 2 / Real.sqrt L) := by ring
        _ = ((2 * a + 1) ^ 2 / (a / 2)) * (L * Real.sqrt L) := by
            congr 1; apply (div_eq_iff hsqrt.ne').mpr; rw [mul_assoc, Real.mul_self_sqrt hL0.le]; ring
    have hfirst : S / 4 ≤ ((2 * a) / 4) * (L * Real.sqrt L) := by
      have hm := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ (2 * a) * Real.sqrt L / 4)
      have hs' := div_le_div_of_nonneg_right hSu (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    have hpow : L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
      calc L * Real.sqrt L = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = L ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hL0 1 (1 / 2)).symm
        _ = L ^ (3 / 2 : ℝ) := by norm_num
    have hQ : quadraticProfile S z ≤ ((2 * a) / 4 + (2 * a + 1) ^ 2 / (a / 2)) * L ^ (3 / 2 : ℝ) := by
      unfold quadraticProfile; rw [← hpow]; linarith
    have hf := Nat.floor_le (mul_nonneg hβ.le ((div_nonneg hS.le (by norm_num)).trans (quadraticProfile_lower (z := z) hS)))
    exact (hf.trans (by simpa only [K_deg, mul_assoc] using mul_le_mul_of_nonneg_left hQ hβ.le)).trans_lt hlt
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, eventually_ge_atTop (6 : ℕ)] with n hn h6 j hj
  have hm := threeBlockSize_fraction h6
  have hd := hn j hj
  have hhalf : (paperDyadicTotalDegree C a offset H n j : ℝ) ≤ (threeBlockSize n : ℝ) / 2 := by linarith
  have hmpos : 0 < (threeBlockSize n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < (2 : ℕ)) (threeBlockSize_two_le h6)
  refine ⟨?_, by positivity, by linarith⟩
  exact_mod_cast hhalf.trans (by linarith : (threeBlockSize n : ℝ) / 2 ≤ threeBlockSize n)

-- 4. Gaussian lattice sum & dyadic bias budget

private theorem gaussian_sum_range_le (c : ℝ) (hc : 0 < c) (N : ℕ) :
    (∑ k ∈ Finset.range N, Real.exp (-c * (k : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / c) / 2 := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [Finset.sum_range_succ']
    have hf : AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Icc 0 (0 + (N : ℝ))) := fun x hx y hy hxy =>
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ((sq_le_sq₀ hx.1 hy.1).mpr hxy) hc.le])
    have hInt : (∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-c * x ^ 2)) ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2) := by
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
      exact setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
        (Eventually.of_forall fun _ => (Real.exp_pos _).le) (Eventually.of_forall fun _ hx => hx.1)
    have hcomp : (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2) :=
      (by simpa using hf.sum_le_integral :
        (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) ≤
          ∫ x in (0 : ℝ)..(N : ℝ), Real.exp (-c * x ^ 2)).trans hInt
    calc (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) + Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2)
      _ ≤ (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) + 1 := by simpa using add_le_add_right hcomp 1
      _ = 1 + Real.sqrt (Real.pi / c) / 2 := by rw [integral_gaussian_Ioi]; ring

private theorem normalized_gaussian_lattice_sum_le (M : ℕ) (u₀ a b S : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hS : 1 ≤ S) :
    (∑ j ∈ Finset.range M, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) / Real.sqrt S ≤
      2 + Real.sqrt (Real.pi / a) / b := by
  classical
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  let c := a / S
  have hc : 0 < c := div_pos ha hS0
  let g (k : ℕ) : ℝ := Real.exp (-(c * b ^ 2) * (k : ℝ) ^ 2)
  let P := (Finset.range M).filter fun j : ℕ => 0 ≤ u₀ + (j : ℝ) * b
  let N := (Finset.range M).filter fun j : ℕ => ¬ 0 ≤ u₀ + (j : ℝ) * b
  have hP_bd : (∑ j ∈ P, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / (c * b ^ 2)) / 2 := by
    by_cases hne : P.Nonempty
    · let j₀ := P.min' hne
      have hj₀ : 0 ≤ u₀ + (j₀ : ℝ) * b := (Finset.mem_filter.mp (P.min'_mem hne)).2
      have hterm : ∑ j ∈ P, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2) ≤ ∑ j ∈ P, g (j - j₀) := by
        refine Finset.sum_le_sum fun j hj => Real.exp_le_exp.mpr ?_
        have hle := P.min'_le j hj
        have hj_nn : 0 ≤ u₀ + (j : ℝ) * b := (Finset.mem_filter.mp hj).2
        have hdiff : ((j - j₀ : ℕ) : ℝ) * b ≤ u₀ + (j : ℝ) * b := by
          rw [Nat.cast_sub hle]; nlinarith
        have hsq := (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hb.le) hj_nn).mpr hdiff
        nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
      have hinj : Set.InjOn (fun x => x - j₀) P := fun x hx y hy h => by
        dsimp only at h; have := P.min'_le x hx; have := P.min'_le y hy; omega
      have hsub : P.image (fun x => x - j₀) ⊆ Finset.range M := fun k hk => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        exact Finset.mem_range.mpr (by omega)
      refine hterm.trans ?_
      rw [← Finset.sum_image (f := g) hinj]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans
        (gaussian_sum_range_le (c * b ^ 2) (by positivity) M)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; positivity
  have hN_bd : (∑ j ∈ N, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / (c * b ^ 2)) / 2 := by
    by_cases hne : N.Nonempty
    · let j₁ := N.max' hne
      have hj₁ : u₀ + (j₁ : ℝ) * b < 0 := not_le.mp (Finset.mem_filter.mp (N.max'_mem hne)).2
      have hterm : ∑ j ∈ N, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2) ≤ ∑ j ∈ N, g (j₁ - j) := by
        refine Finset.sum_le_sum fun j hj => Real.exp_le_exp.mpr ?_
        have hle := N.le_max' j hj
        have hj_neg : u₀ + (j : ℝ) * b < 0 := not_le.mp (Finset.mem_filter.mp hj).2
        have hdiff : ((j₁ - j : ℕ) : ℝ) * b ≤ -(u₀ + (j : ℝ) * b) := by
          rw [Nat.cast_sub hle]; nlinarith
        have hsq := (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hb.le) (by linarith)).mpr hdiff
        nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
      have hinj : Set.InjOn (fun x => j₁ - x) N := fun x hx y hy h => by
        dsimp only at h; have := N.le_max' x hx; have := N.le_max' y hy; omega
      have hsub : N.image (fun x => j₁ - x) ⊆ Finset.range (j₁ + 1) := fun k hk => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr (by omega)
      refine hterm.trans ?_
      rw [← Finset.sum_image (f := g) hinj]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans
        (gaussian_sum_range_le (c * b ^ 2) (by positivity) (j₁ + 1))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]; positivity
  have htot : (∑ j ∈ Finset.range M, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) ≤
      2 + Real.sqrt (Real.pi / a) * Real.sqrt S / b := by
    have heq : (∑ j ∈ Finset.range M, Real.exp (-a * (u₀ + (j : ℝ) * b) ^ 2 / S)) =
        (∑ j ∈ P, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2)) +
        (∑ j ∈ N, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2)) := by
      trans (∑ j ∈ Finset.range M, Real.exp (-c * (u₀ + (j : ℝ) * b) ^ 2))
      · exact Finset.sum_congr rfl fun j _ => by dsimp [c]; ring_nf
      · exact (Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun j : ℕ => 0 ≤ u₀ + (j : ℝ) * b) _).symm
    have hsp : Real.sqrt (Real.pi / (c * b ^ 2)) = Real.sqrt (Real.pi / a) * Real.sqrt S / b := by
      have halg : Real.pi / (c * b ^ 2) = (Real.pi / a * S) / b ^ 2 := by dsimp [c]; field_simp
      rw [halg, Real.sqrt_div (by positivity), Real.sqrt_mul (div_nonneg Real.pi_pos.le ha.le),
        Real.sqrt_sq hb.le]
    rw [heq]; rw [hsp] at hP_bd hN_bd; linarith
  have hp : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  rw [div_le_iff₀ hp]
  have hsqrt1 : 1 ≤ Real.sqrt S := Real.one_le_sqrt.mpr hS
  refine htot.trans ?_
  rw [show Real.sqrt (Real.pi / a) * Real.sqrt S / b = (Real.sqrt (Real.pi / a) / b) * Real.sqrt S by ring]
  nlinarith [div_nonneg (Real.sqrt_nonneg (Real.pi / a)) hb.le]

theorem eventually_paper_dyadic_bias_budget {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℝ in atTop,
      dyadicPopulationBiasBudget C (paperDyadicTerminalLevel C a offset H n)
        (paperDyadicApproximationDegree C a offset H n) ≤
      B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
  let r := anchoredDimension d C.order
  let q := paperPolynomialDimension C
  let δ := paperDyadicStep C
  let γ := paperDegreeReserve C
  let β := paperDegreeSlope C
  let θ := paperSpatialExponent C
  let τ := paperTau C
  have hδ : 0 < δ := paperDyadicStep_pos C
  have hθ : 0 < θ := paperSpatialExponent_pos C hs
  have hτ : 0 < τ := paperTau_pos C
  have hβ : 0 < β := div_pos hθ hτ
  have hτβ : τ * β = θ := mul_div_cancel₀ _ hτ.ne'
  have hθγ : θ * γ = (r : ℝ) + 1 / 2 := mul_div_cancel₀ _ hθ.ne'
  let P_gauss := (r.factorial : ℝ) / (θ / 2) ^ r * Real.exp (θ / 2)
  let C_term := (1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1)) * P_gauss
  let B₀ := C_term * (2 + Real.sqrt (Real.pi / (θ / 2)) / δ)
  have hC_term : 0 < C_term := by dsimp [C_term, P_gauss]; positivity
  have hB₀ : 0 < B₀ := mul_pos hC_term (by positivity)
  refine ⟨1 + B₀, by positivity, ?_⟩
  filter_upwards [(allocationWidth_tendsto_atTop ha offset).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg ha hH offset γ,
    eventually_width_degree_threshold ha hβ offset q] with n hS hLT hdeg
  let J := paperDyadicTerminalLevel C a offset H n
  let m := paperDyadicApproximationDegree C a offset H n
  let S := allocationWidth a offset n
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  let ell := Real.log (H * S)
  let T := δ * (J : ℝ) - Real.log n
  let u₀ := -Real.log n + ell - S / 2
  have hu : T ≤ S - ell - γ * Real.log S := (roundedTerminalDepth_bounds hδ hLT).2
  have hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T) := by
    have hm := mul_le_mul_of_nonneg_left hu hθ.le
    have he : θ * γ * Real.log S = ((r : ℝ) + 1 / 2) * Real.log S := by rw [hθγ]
    nlinarith
  have hsp_wt (j : ℕ) : (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) = Real.exp (-θ * (δ * (j : ℝ))) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_inv, Real.log_pow]
    congr 1; dsimp [θ, δ, paperSpatialExponent, paperDyadicStep]
    have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
    field_simp
  have hKstar : (dyadicPilotScale d J) ^ (-θ) = Real.exp (-θ * (δ * (J : ℝ))) := by
    rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1; dsimp [δ]; ring
  have hsum : ∑ j ∈ Finset.range (J + 1),
      (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ r * Real.exp (-(m j : ℝ) * τ) ≤
      B₀ * Real.exp (-θ * (δ * (J : ℝ))) := by
    have hterm (j : ℕ) :
        (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ r * Real.exp (-(m j : ℝ) * τ) ≤
        Real.exp (-θ * (δ * (J : ℝ))) * (C_term / Real.sqrt S * Real.exp (-(θ / 2) * (u₀ + (j : ℝ) * δ) ^ 2 / S)) := by
      let z := allocationLevelPosition δ a offset H n j
      have hz_u : z - S / 2 = u₀ + (j : ℝ) * δ := by dsimp [z, allocationLevelPosition, u₀, ell, S]; ring
      have hQ0 : 0 ≤ β * quadraticProfile S z :=
        mul_nonneg hβ.le ((div_nonneg hS0.le (by norm_num)).trans (quadraticProfile_lower hS0))
      have hq_fl : q ≤ Nat.floor (β * quadraticProfile S z) := by
        refine Nat.le_floor ?_
        have hQ := mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := z) hS0) hβ.le
        change (q : ℝ) + 2 ≤ β * S / 4 at hdeg; linarith
      have hm_eq : (m j : ℝ) = (Nat.floor (β * quadraticProfile S z) : ℝ) - (q : ℝ) :=
        Nat.cast_sub hq_fl
      have hml : β * quadraticProfile S z - (q : ℝ) - 1 ≤ (m j : ℝ) := by
        rw [hm_eq]; linarith [Nat.lt_floor_add_one (β * quadraticProfile S z)]
      have hmu : (m j : ℝ) + 1 ≤ β * quadraticProfile S z + 1 := by
        rw [hm_eq]; linarith [Nat.floor_le hQ0, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
      let t := (z - S / 2) ^ 2 / S
      have ht : 0 ≤ t := div_nonneg (sq_nonneg _) hS0.le
      -- Exponential mass bound
      have hexp_split : Real.exp (-θ * (δ * (j : ℝ))) * Real.exp (-(m j : ℝ) * τ) =
          Real.exp (-θ * (δ * (J : ℝ))) * Real.exp (-θ * (z - ell - T) - τ * (m j : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; dsimp [z, allocationLevelPosition, ell, T, S]; ring
      have hid : θ * (z + quadraticProfile S z - S) = θ * t := by
        have h1 : z + quadraticProfile S z - S = t := by
          dsimp [quadraticProfile, t]; field_simp [hS0.ne']; ring
        rw [h1]
      have hmass : Real.exp (-θ * (z - ell - T) - τ * (m j : ℝ)) ≤
          Real.exp (τ * ((q : ℝ) + 1)) * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) *
            Real.exp (-θ * t) := by
        have hml' := mul_le_mul_of_nonneg_left hml hτ.le
        have hrew : τ * (β * quadraticProfile S z - (q : ℝ) - 1) =
            θ * quadraticProfile S z - τ * ((q : ℝ) + 1) := by rw [← hτβ]; ring
        rw [hrew] at hml'
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        ring_nf at hml' hreserve hid ⊢; linarith
      -- Polynomial prefactor bound
      have hQ_up : quadraticProfile S z ≤ S + 3 / 2 * t := by
        have hdiff : S + 3 / 2 * t - quadraticProfile S z = (z + S / 2) ^ 2 / (2 * S) := by
          dsimp [quadraticProfile, t]; field_simp [hS0.ne']; ring
        have : 0 ≤ (z + S / 2) ^ 2 / (2 * S) := by positivity
        linarith
      have hpoly : ((m j + 1 : ℕ) : ℝ) ^ r ≤ (1 + 3 * β / 2) ^ r * S ^ r * (1 + t) ^ r := by
        have hup : (m j : ℝ) + 1 ≤ (1 + 3 * β / 2) * S * (1 + t) := by
          have hb := mul_le_mul_of_nonneg_left hQ_up hβ.le
          have htr := mul_nonneg hβ.le (mul_nonneg (sub_nonneg.mpr hS) ht)
          nlinarith [mul_nonneg hS0.le ht, mul_nonneg hβ.le hS0.le]
        rw [Nat.cast_add, Nat.cast_one]
        simpa only [mul_pow, mul_assoc] using pow_le_pow_left₀ (by positivity) hup r
      -- Exponential absorption of `(1 + t)^r * exp(-θ * t)`
      have habs : (1 + t) ^ r * Real.exp (-θ * t) ≤ P_gauss * Real.exp (-(θ / 2) * t) := by
        have hf : 0 < (r.factorial : ℝ) := by positivity
        have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (θ / 2 * (1 + t)) (by positivity) r)
        rw [mul_pow] at hh
        have hp : (1 + t) ^ r ≤ (r.factorial : ℝ) / (θ / 2) ^ r * Real.exp (θ / 2 * (1 + t)) := by
          calc (1 + t) ^ r ≤ (Real.exp (θ / 2 * (1 + t)) * (r.factorial : ℝ)) / (θ / 2) ^ r :=
                (le_div_iff₀ (pow_pos (by positivity) r)).mpr (by simpa [mul_comm] using hh)
            _ = (r.factorial : ℝ) / (θ / 2) ^ r * Real.exp (θ / 2 * (1 + t)) := by ring
        refine (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq ?_
        dsimp [P_gauss]
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
      -- Log cancellation `S^r * exp(-(r + 1/2) * log S) = 1 / sqrt S`
      have hlog_cancel : S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) = (Real.sqrt S)⁻¹ := by
        rw [← Real.exp_log (pow_pos hS0 r), Real.log_pow, ← Real.exp_add,
          ← Real.exp_log (Real.sqrt_pos.mpr hS0), ← Real.exp_neg, Real.log_sqrt hS0.le]
        congr 1; ring
      rw [hsp_wt]
      calc Real.exp (-θ * (δ * (j : ℝ))) * ((m j + 1 : ℕ) : ℝ) ^ r * Real.exp (-(m j : ℝ) * τ)
        _ = Real.exp (-θ * (δ * (J : ℝ))) *
              (Real.exp (-θ * (z - ell - T) - τ * (m j : ℝ)) * ((m j + 1 : ℕ) : ℝ) ^ r) := by
            rw [mul_right_comm, hexp_split, mul_assoc]
        _ ≤ Real.exp (-θ * (δ * (J : ℝ))) *
              ((Real.exp (τ * ((q : ℝ) + 1)) * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S) * Real.exp (-θ * t)) *
                ((1 + 3 * β / 2) ^ r * S ^ r * (1 + t) ^ r)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul hmass hpoly (by positivity) (by positivity)) (Real.exp_pos _).le
        _ = Real.exp (-θ * (δ * (J : ℝ))) *
              (((1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1))) *
                (S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S)) *
                ((1 + t) ^ r * Real.exp (-θ * t))) := by ring
        _ ≤ Real.exp (-θ * (δ * (J : ℝ))) *
              (((1 + 3 * β / 2) ^ r * Real.exp (τ * ((q : ℝ) + 1))) *
                (S ^ r * Real.exp (-((r : ℝ) + 1 / 2) * Real.log S)) *
                (P_gauss * Real.exp (-(θ / 2) * t))) := by
            gcongr
        _ = Real.exp (-θ * (δ * (J : ℝ))) *
              (C_term / Real.sqrt S * Real.exp (-(θ / 2) * (u₀ + (j : ℝ) * δ) ^ 2 / S)) := by
            rw [hlog_cancel]; dsimp [C_term, t]; rw [hz_u]; ring
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    have hg := normalized_gaussian_lattice_sum_le (J + 1) u₀ (θ / 2) δ S (by positivity) hδ hS
    simpa only [B₀, div_mul_eq_mul_div, mul_div_assoc] using mul_le_mul_of_nonneg_left hg hC_term.le
  unfold dyadicPopulationBiasBudget
  change (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) + _ ≤ (1 + B₀) * (dyadicPilotScale d J) ^ (-θ)
  rw [hsp_wt J, hKstar]
  exact (add_le_add le_rfl hsum).trans_eq (by ring)

-- 5. Spatial & master risk allocation

def paperAllocatedDepth {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  roundedTerminalDepth (paperDyadicStep C) (Real.log x)
    (candidateTerminalDepth (paperUpperSaddle C) (paperUpperShift C) H (paperDegreeReserve C) x)

def paperAllocatedLogSide {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x)

def paperAllocatedFinestLevel {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℕ :=
  dyadicLevelFromLogSide (paperAllocatedLogSide C H x)

def paperAllocatedSide {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  dyadicRoundedSide (paperAllocatedLogSide C H x)

def paperAllocatedRiskScale {d : ℕ} (C : ModelConstants d) (H x : ℝ) : ℝ :=
  Real.exp (-rateExponent C.smoothness d * Real.log x -
    paperUpperRiskDepthCoefficient C * paperAllocatedDepth C H x)

private theorem eventually_paper_allocated_depth_le_width {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop, paperAllocatedDepth C H x ≤
      allocationWidth (paperUpperSaddle C) (paperUpperShift C) x := by
  have hw := allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ)),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_terminal_cell_log_nonneg (paperUpperSaddle_pos C hreg) hH
      (paperUpperShift C) (paperDegreeReserve C)] with x hS hHS hLT
  have ht := (roundedTerminalDepth_bounds (paperDyadicStep_pos C) hLT).2
  have hlog : 0 ≤ Real.log (allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) :=
    Real.log_nonneg (by linarith only [hS])
  have hlogH : 0 ≤ Real.log (H * allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) :=
    Real.log_nonneg hHS
  have hm := mul_nonneg (paperDegreeReserve_pos C hreg.1).le hlog
  unfold paperAllocatedDepth candidateTerminalDepth at ht ⊢
  exact ht.trans (by linarith only [hlogH, hm])

theorem eventually_paper_allocated_grid_guard {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop,
      paperAllocatedLogSide C H x ≤ 0 ∧
      paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x ≤
        paperAllocatedFinestLevel C H x := by
  have hw := allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)
  filter_upwards [hw.eventually (eventually_ge_atTop (2 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_paper_allocated_depth_le_width C hreg hH] with x hS hL hT
  have hb := quadratic_allocation_budget (paperDegreeSlope_pos C hreg.1)
    (show 0 ≤ paperUpperEta C + 2 by linarith only [paperUpperEta_pos C])
    (by linarith only [hS])
    (show allocationWidth (paperUpperSaddle C) (paperUpperShift C) x =
      paperUpperSaddle C * Real.sqrt (Real.log x) - (1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C) from rfl)
  have hbase : paperDegreeSlope C * (paperUpperSaddle C * Real.sqrt (Real.log x)) ^ 2 / 4 =
      2 * paperUpperVarpi C * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL, ← mul_assoc, mul_div_right_comm, paper_upper_saddle_budget_identity C hreg]
  rw [hbase] at hb
  have hm := mul_le_mul_of_nonneg_left hT (paperUpperEta_pos C).le
  have hquad : 0 ≤ paperDegreeSlope C * (allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (paperDegreeSlope_pos C hreg.1).le (sq_nonneg _)) (by norm_num)
  have hn : -2 * paperUpperVarpi C * Real.log x + paperUpperEta C * paperAllocatedDepth C H x ≤ 0 := by
    nlinarith only [hb, hm, hquad, hS]
  rw [← paper_spatial_reserve_identity C] at hn
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hlevel : Real.log x + paperAllocatedDepth C H x =
      paperDyadicStep C * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) := by
    unfold paperAllocatedDepth roundedTerminalDepth paperDyadicTerminalLevel terminalAllocationLevel; ring
  rw [hlevel] at hn
  have hlog : 2 / (d : ℝ) * (paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) =
      2 * (Real.log 2 * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) := by
    unfold paperDyadicStep; field_simp
  rw [hlog] at hn
  have hg : paperAllocatedLogSide C H x + Real.log 2 *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) ≤ 0 := by
    change spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x) + _ ≤ 0; linarith only [hn]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnonneg : 0 ≤ Real.log 2 * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) :=
    mul_nonneg hl2.le (Nat.cast_nonneg _)
  refine ⟨by linarith only [hg, hnonneg], ?_⟩
  have hj : (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) ≤
      -paperAllocatedLogSide C H x / Real.log 2 := (le_div_iff₀ hl2).mpr (by linarith only [hg])
  exact_mod_cast hj.trans (Nat.le_ceil _)

def paperAllocatedMasterConstant {d : ℕ} (_C : ModelConstants d) (B : ℝ) : ℝ :=
  B ^ 2 * (d : ℝ) + 2 * (1 + Real.exp ((d : ℝ) / 2 * Real.log 2))

theorem paperAllocatedMasterConstant_pos {d : ℕ} (C : ModelConstants d) (B : ℝ) :
    0 < paperAllocatedMasterConstant C B := by unfold paperAllocatedMasterConstant; positivity

theorem eventually_paper_allocated_master_rate {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ 1 →
      (B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
        (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
          (-paperSpatialExponent C)) ^ 2 +
        pairFluctuationScale (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n) * (1 + W) ≤
      paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n := by
  let r_res := ((d : ℝ) - 4 * C.smoothness) / (4 * ((d : ℝ) + 4))
  have hr_pos : 0 < r_res := div_pos (sub_pos.mpr hreg.2)
    (mul_pos (by norm_num) (by have : (0 : ℝ) < d := Nat.cast_pos.mpr C.dimension_pos; positivity))
  have hlim := tendsto_sqrt_log_div_log.const_mul (paperUpperRiskDepthCoefficient C * paperUpperSaddle C)
  simp only [mul_zero] at hlim
  have hroot_ev : ∀ᶠ x : ℝ in atTop, Real.exp (-Real.log x / 2) ≤ paperAllocatedRiskScale C H x := by
    filter_upwards [hlim.eventually (gt_mem_nhds hr_pos),
      eventually_paper_allocated_depth_le_width C hreg hH,
      Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hT hL
    have hchi := paperUpperRiskDepthCoefficient_pos C hreg.1
    have hbeta := paperDegreeSlope_pos C hreg.1
    have hshift : 0 ≤ paperUpperShift C := add_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (by norm_num) (by linarith only [paperUpperEta_pos C])) hbeta.le)
    have hS : allocationWidth (paperUpperSaddle C) (paperUpperShift C) x ≤
        paperUpperSaddle C * Real.sqrt (Real.log x) := by unfold allocationWidth; linarith only [hshift]
    have hm := mul_le_mul_of_nonneg_left (hT.trans hS) hchi.le
    have hsmall : paperUpperRiskDepthCoefficient C * paperUpperSaddle C * Real.sqrt (Real.log x) ≤
        r_res * Real.log x := by rw [← mul_div_assoc] at hx; exact ((div_lt_iff₀ hL).mp hx).le
    have hgap : (1 / 2 - rateExponent C.smoothness d) * Real.log x = 2 * r_res * Real.log x := by
      congr 1; rw [half_minus_rateExponent hreg.1 hreg.2]; dsimp [r_res]
      have : (d : ℝ) + 4 ≠ 0 := by positivity
      field_simp; ring
    have hr0 : 0 ≤ r_res * Real.log x := mul_nonneg hr_pos.le hL.le
    unfold paperAllocatedRiskScale
    exact Real.exp_le_exp.mpr (by nlinarith only [hm, hsmall, hgap, hr0])
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard C hreg hH),
    tendsto_natCast_atTop_atTop.eventually hroot_ev, eventually_ge_atTop (1 : ℕ)] with n hgrid hroot hn W hW hW1
  have hg := hgrid.1
  -- Pair fluctuation bound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfl_eq : pairFluctuationScale (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n) =
      Real.exp (-Real.log n / 2) +
        Real.exp (-Real.log n - (d : ℝ) / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H n)) := by
    have h1 : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (-Real.log n / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR, ← Real.exp_neg]; congr 1; ring
    have h2 : Real.sqrt ((((2 : ℕ) ^ paperAllocatedFinestLevel C H n : ℕ) : ℝ) ^ d) / (n : ℝ) =
        Real.exp (-Real.log n - (d : ℝ) / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H n)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity),
        Real.log_pow, Real.log_pow, show (n : ℝ) = Real.exp (Real.log n) from (Real.exp_log hnR).symm,
        ← Real.exp_sub, Real.log_exp]
      congr 1; unfold dyadicRoundedLogSide paperAllocatedFinestLevel; ring
    exact congrArg₂ (· + ·) h1 h2
  have hpair : Real.exp (-Real.log n - (d : ℝ) / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H n)) ≤
      Real.exp ((d : ℝ) / 2 * Real.log 2) * paperAllocatedRiskScale C H n := by
    have hlo := (dyadicRoundedLogSide_bounds hg).1.le
    have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ (d : ℝ) / 2)
    have h1 : Real.exp (-Real.log n - (d : ℝ) / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H n)) ≤
        Real.exp ((d : ℝ) / 2 * Real.log 2) * Real.exp (-Real.log n - (d : ℝ) / 2 * paperAllocatedLogSide C H n) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hm])
    rwa [paperAllocatedLogSide, spatial_balance_rate hreg.1 hreg.2] at h1
  have hfl : pairFluctuationScale (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n) ≤
      (1 + Real.exp ((d : ℝ) / 2 * Real.log 2)) * paperAllocatedRiskScale C H n := by
    rw [hfl_eq]; exact (add_le_add hroot hpair).trans_eq (by ring)
  -- Bias square bound
  have hside_le : paperAllocatedSide C H n ≤ Real.exp (paperAllocatedLogSide C H n) :=
    Real.exp_le_exp.mpr (dyadicRoundedLogSide_bounds hg).2
  have hbias : (paperAllocatedSide C H n *
      (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
        (-paperSpatialExponent C)) ^ 2 ≤ paperAllocatedRiskScale C H n := by
    rw [mul_pow]
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hside_le 2) (sq_nonneg _)).trans_eq ?_
    rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    unfold paperAllocatedRiskScale
    congr 1
    have hdepth : Real.log n + paperAllocatedDepth C H n = paperDyadicStep C *
        (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n : ℝ) := by
      unfold paperAllocatedDepth roundedTerminalDepth paperDyadicTerminalLevel terminalAllocationLevel; ring
    have hbal := spatial_balance hreg.1 hreg.2 (Real.log n) (paperAllocatedDepth C H n)
    have hrate := spatial_balance_rate hreg.1 hreg.2 (Real.log n) (paperAllocatedDepth C H n)
    change _ = -rateExponent C.smoothness d * Real.log n -
      2 * (C.smoothness - 1) / ((d : ℝ) + 4) * paperAllocatedDepth C H n
    unfold paperAllocatedLogSide paperSpatialExponent
    rw [hdepth] at hbal; nlinarith only [hbal, hrate]
  have hmul := mul_le_mul_of_nonneg_left hbias (by positivity : 0 ≤ B ^ 2 * (d : ℝ))
  have hsq : (B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
      (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
        (-paperSpatialExponent C)) ^ 2 =
      (B ^ 2 * (d : ℝ)) * (paperAllocatedSide C H n *
        (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
          (-paperSpatialExponent C)) ^ 2 := by simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; ring
  rw [← hsq] at hmul
  have hfn := pairFluctuationScale_nonneg (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n)
  have hWmul := mul_le_mul_of_nonneg_left (show 1 + W ≤ 2 by linarith only [hW1]) hfn
  unfold paperAllocatedMasterConstant
  nlinarith only [hmul, hWmul, hfl]

theorem paper_allocated_risk_scale_upper {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      paperAllocatedRiskScale C H n ≤ A * paperUpperScale C n := by
  obtain ⟨_, B, _, hB, hb⟩ := rounded_upper_saddle_scale_bracket
    (paperUpperSaddle_pos C hreg) hH (paperDyadicStep_pos C)
    (paperUpperShift C) (paperDegreeReserve C) (rateExponent C.smoothness d)
    (paperUpperRiskDepthCoefficient_pos C hreg.1).le
  have hstretch : paperUpperRiskDepthCoefficient C * paperUpperSaddle C =
      stretchConstant C.smoothness d (paperTau C) :=
    upper_saddle_stretchConstant hreg.1 hreg.2 (paperTau_pos C)
  have hlogpow : paperUpperRiskDepthCoefficient C * (1 + paperDegreeReserve C) / 2 =
      lowerLogPower C.smoothness d + paperLogGap C := by
    have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
    have hdp : (d : ℝ) + 4 ≠ 0 := by positivity
    have hs0 : C.smoothness - 1 ≠ 0 := (sub_pos.mpr hreg.1).ne'
    have hq : 1 ≤ (d + C.order).choose d := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
    have hcard : (anchoredDimension d C.order : ℝ) = (paperPolynomialDimension C : ℝ) - 1 := by
      unfold anchoredDimension paperPolynomialDimension
      rw [anchoredIndex_card, Nat.cast_sub hq, Nat.cast_one]
    unfold paperUpperRiskDepthCoefficient paperDegreeReserve paperSpatialExponent lowerLogPower paperLogGap
    rw [hcard]; field_simp; ring
  have hb' : ∀ᶠ x : ℝ in atTop, paperAllocatedRiskScale C H x ≤
      B * Real.exp (-rateExponent C.smoothness d * Real.log x -
        stretchConstant C.smoothness d (paperTau C) * Real.sqrt (Real.log x) +
        (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)) := by
    simpa only [paperAllocatedRiskScale, paperAllocatedDepth, ← mul_assoc, hstretch, hlogpow] using
      hb.mono fun _ h => h.2
  refine ⟨B, hB, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hb', eventually_ge_atTop (2 : ℕ)] with n hn hn2
  rw [paperUpperScale_eq_rateScale C hn2]
  exact hn

-- 6. Factorial series & pilot variance reserve

private def factorialSeries (D : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D, ((k + 1).factorial : ℝ) * x ^ (k + 1)

private theorem factorialSeries_coarse_bound {D : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hD : (D : ℝ) * x ≤ 1 / 2) :
    factorialSeries D x ≤ 2 * x := by
  have hterm (k : ℕ) (hk : k < D) : ((k + 1).factorial : ℝ) * x ^ (k + 1) ≤ x * (1 / 2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hcast : ((k + 2 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ D)
      have hratio : ((k + 2 : ℕ) : ℝ) * x ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hcast hx).trans hD
      calc (((k + 1 + 1).factorial : ℕ) : ℝ) * x ^ (k + 1 + 1)
        _ = (((k + 2 : ℕ) : ℝ) * x) * (((k + 1).factorial : ℝ) * x ^ (k + 1)) := by
            rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]; push_cast; ring
        _ ≤ (1 / 2 : ℝ) * (x * (1 / 2 : ℝ) ^ k) :=
            mul_le_mul hratio (ih (by omega)) (by positivity) (by norm_num)
        _ = x * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have hg : (∑ k ∈ Finset.range D, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := D) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    convert h using 1 <;> norm_num
  unfold factorialSeries
  refine (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.mp hk)).trans ?_
  rw [← Finset.mul_sum]; linarith [mul_le_mul_of_nonneg_left hg hx]

private theorem factorialSeries_fine_bound {D : ℕ} {x z B A : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hDx : (D : ℝ) * x ≤ Real.exp z)
    (hDz : (D : ℝ) * z ≤ B) (hDA : (D : ℝ) ≤ A) :
    factorialSeries D x ≤ A * Real.exp B := by
  unfold factorialSeries
  refine (Finset.sum_le_sum (g := fun _ => Real.exp B) fun k hk => ?_).trans ?_
  · have hkD : k + 1 ≤ D := Finset.mem_range.mp hk
    have hfac : ((k + 1).factorial : ℝ) ≤ (D : ℝ) ^ (k + 1) := by
      exact_mod_cast (Nat.factorial_le_pow (k + 1)).trans (Nat.pow_le_pow_left hkD (k + 1))
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hkD
    calc ((k + 1).factorial : ℝ) * x ^ (k + 1)
      _ ≤ (D : ℝ) ^ (k + 1) * x ^ (k + 1) := mul_le_mul_of_nonneg_right hfac (by positivity)
      _ = ((D : ℝ) * x) ^ (k + 1) := (mul_pow _ _ _).symm
      _ ≤ (Real.exp z) ^ (k + 1) := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg D) hx) hDx (k + 1)
      _ = Real.exp (((k + 1 : ℕ) : ℝ) * z) := (Real.exp_nat_mul z (k + 1)).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hcast hz).trans hDz)
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hDA (Real.exp_pos B).le

private theorem profileVarianceWeight_uniform_bound {C₀ C_D β S z : ℝ}
    (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
    (hβ : 0 ≤ β) (hS : 2 ≤ S) (hz : z ≤ S) :
    let arg := Real.exp z / (C_D * S)
    factorialSeries (Nat.floor (β * quadraticProfile S z)) arg * max 1 (C₀ / arg) ≤
      2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  intro arg
  have hS0 : 0 < S := by linarith
  have hC0 : 0 < C₀ := by linarith
  have hD0 : 0 < C_D := by linarith
  have hCS : 0 < C_D * S := mul_pos hD0 hS0
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have hx : 0 < arg := div_pos (Real.exp_pos z) hCS
  have hQ0 : 0 ≤ quadraticProfile S z := (div_nonneg hS0.le (by norm_num)).trans (quadraticProfile_lower hS0)
  have hf := Nat.floor_le (mul_nonneg hβ hQ0)
  rcases le_or_gt z 0 with hz0 | hz0
  · have hrat : (Nat.floor (β * quadraticProfile S z) : ℝ) * arg ≤ 1 / 2 := by
      have hfe := mul_le_mul_of_nonneg_right hf (Real.exp_pos z).le
      have hc := mul_le_mul_of_nonneg_left (quadraticProfile_coarse_bound hS hz0) hβ
      have hDm := mul_le_mul_of_nonneg_right hDβ hS0.le
      dsimp [arg]; rw [← mul_div_assoc]; apply (div_le_iff₀ hCS).mpr
      nlinarith [mul_nonneg hβ hS0.le]
    have hxC : arg ≤ C₀ := ((div_le_one hCS).mpr ((Real.exp_le_one_iff.mpr hz0).trans hCS1)).trans hC
    have hm : 1 ≤ C₀ / arg := (le_div_iff₀ hx).mpr (by simpa using hxC)
    rw [max_eq_right hm]
    have hcoarse : factorialSeries (Nat.floor (β * quadraticProfile S z)) arg * (C₀ / arg) ≤ 2 * C₀ := by
      refine (mul_le_mul_of_nonneg_right (factorialSeries_coarse_bound hx.le hrat) (div_nonneg hC0.le hx.le)).trans_eq ?_
      field_simp [hx.ne']
    have hsq : 1 ≤ C_D ^ 2 * S ^ 2 := by nlinarith [sq_nonneg (C_D * S - 1)]
    have hexp : 1 ≤ Real.exp (β * S ^ 2 / 4) := Real.one_le_exp_iff.mpr (by positivity)
    have hfac : 1 ≤ C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by nlinarith
    exact hcoarse.trans (by simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ 2 * C₀))
  · have hQu : quadraticProfile S z ≤ 5 * S / 4 := by
      have hs : (S - z) ^ 2 ≤ S ^ 2 := by nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hz)]
      have hd := (div_le_div_iff_of_pos_right hS0).mpr hs
      rw [sq S, mul_div_cancel_right₀ S hS0.ne'] at hd; dsimp [quadraticProfile]; linarith
    have hQf : z * quadraticProfile S z ≤ S ^ 2 / 4 := by
      have hid : S ^ 2 / 4 - z * quadraticProfile S z = (S - z) * (2 * z - S) ^ 2 / (4 * S) := by
        dsimp [quadraticProfile]; field_simp [hS0.ne']; ring
      have : 0 ≤ (S - z) * (2 * z - S) ^ 2 / (4 * S) :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg _)) (by positivity)
      linarith
    have hdeg : (Nat.floor (β * quadraticProfile S z) : ℝ) ≤ C_D * S := by
      have hu := mul_le_mul_of_nonneg_left hQu hβ
      have hDm := mul_le_mul_of_nonneg_right hDβ hS0.le
      nlinarith [mul_nonneg hβ hS0.le]
    have hprod : (Nat.floor (β * quadraticProfile S z) : ℝ) * z ≤ β * S ^ 2 / 4 := by
      have hv := mul_le_mul_of_nonneg_left hQf hβ
      have hfm := mul_le_mul_of_nonneg_right hf hz0.le
      nlinarith
    have hDx : (Nat.floor (β * quadraticProfile S z) : ℝ) * arg ≤ Real.exp z := by
      have hd := mul_le_mul_of_nonneg_right hdeg hx.le
      rwa [show (C_D * S) * arg = Real.exp z by dsimp [arg]; rw [mul_div_cancel₀ _ hCS.ne']] at hd
    have hfs := factorialSeries_fine_bound hx.le hz0.le hDx hprod hdeg
    have hwt : max 1 (C₀ / arg) ≤ C₀ * C_D * S := by
      refine max_le (by nlinarith) ((div_le_iff₀ hx).mpr ?_)
      have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hz0.le) hC0.le
      calc C₀ ≤ C₀ * Real.exp z := by simpa using hm
        _ = (C₀ * C_D * S) * arg := by dsimp [arg]; field_simp [hCS.ne']
    have hfine : factorialSeries (Nat.floor (β * quadraticProfile S z)) arg * max 1 (C₀ / arg) ≤
        C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) :=
      (mul_le_mul hfs hwt (by positivity) (by positivity)).trans_eq (by ring)
    have : 0 ≤ C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by positivity
    linarith

def paperPilotMomentFactor {d : ℕ} (C : ModelConstants d) (A : ℝ) : ℝ :=
  A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
    preconditionedPilotMomentConstant C C.order)

def paperAllocatedPilotBudget {d : ℕ} (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicMultilevelBudget
    (dyadicSeriesEnvelope C A ((threeBlockSize n : ℝ) / 2)
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
      (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n))
    (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
    (paperAllocatedFinestLevel C (C₀ * C_D) n)

theorem paperAllocatedPilotBudget_nonneg {d : ℕ} (C : ModelConstants d)
    (A C₀ C_D : ℝ) (n : ℕ) : 0 ≤ paperAllocatedPilotBudget C A C₀ C_D n :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)

theorem eventually_paperAllocatedPilotBudget_le_one {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (A C₀ C_D : ℝ)
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, paperAllocatedPilotBudget C A C₀ C_D n ≤ 1 := by
  have hC0 : 0 < C₀ := zero_lt_one.trans_le hC
  have hD0 : 0 < C_D := zero_lt_one.trans_le hD
  let H := C₀ * C_D
  have hH : 0 < H := mul_pos hC0 hD0
  have ha := paperUpperSaddle_pos C hreg
  have hβ := paperDegreeSlope_pos C hreg.1
  have hγ := (paperDegreeReserve_pos C hreg.1).le
  have hδ := paperDyadicStep_pos C
  let hw := allocationWidth_tendsto_atTop ha (paperUpperShift C)
  have htend : Tendsto (fun n : ℕ => 2 * C₀ * C_D ^ 2 *
      (allocationWidth (paperUpperSaddle C) (paperUpperShift C) n) ^ 2 *
      Real.exp (-2 * allocationWidth (paperUpperSaddle C) (paperUpperShift C) n)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun S : ℝ => 2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S)) atTop (𝓝 0) := by
      convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 2 (by norm_num)).const_mul
        (2 * C₀ * C_D ^ 2) using 1
      · funext S; rw [Real.rpow_two]; ring
      · simp
    exact (h0.comp hw).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (paperAllocatedPilotBudget C A C₀ C_D) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall (paperAllocatedPilotBudget_nonneg C A C₀ C_D)) ?_ htend
    filter_upwards [
      tendsto_natCast_atTop_atTop.eventually (eventually_paper_total_degree_eq_floor C hreg.1 (paperUpperSaddle C) (paperUpperShift C) H ha),
      tendsto_natCast_atTop_atTop.eventually (hw.eventually (eventually_ge_atTop (2 : ℝ))),
      tendsto_natCast_atTop_atTop.eventually ((hw.const_mul_atTop hH).eventually (eventually_ge_atTop (1 : ℝ))),
      tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))),
      tendsto_natCast_atTop_atTop.eventually (eventually_terminal_cell_log_nonneg ha hH (paperUpperShift C) (paperDegreeReserve C)),
      tendsto_natCast_atTop_atTop.eventually (eventually_actual_allocation_level_range hδ ha hH hγ (paperUpperShift C)),
      tendsto_natCast_atTop_atTop.eventually ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.1),
      eventually_ge_atTop (6 : ℕ)] with n hd hS hHS hL hLT hz hside h6
    let S := allocationWidth (paperUpperSaddle C) (paperUpperShift C) n
    have hS0 : 0 < S := by linarith only [hS]
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    let Λ := (threeBlockSize n : ℝ) / 2
    have hΛ12 : (n : ℝ) / 12 ≤ Λ := by dsimp only [Λ]; linarith [threeBlockSize_fraction h6]
    have hΛpos : 0 < Λ := (div_pos hn (by norm_num)).trans_le hΛ12
    have hΛn : Λ ≤ n := by
      have hm : (threeBlockSize n : ℝ) ≤ n := by exact_mod_cast (show threeBlockSize n ≤ n by unfold threeBlockSize; omega)
      dsimp only [Λ]; linarith [Nat.cast_nonneg (α := ℝ) (threeBlockSize n)]
    let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
    let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
    -- 1. Bound `dyadicSeriesEnvelope` by `2 * C₀ * C_D^2 * S^2 * exp(β * S^2 / 4)`
    have henv : dyadicSeriesEnvelope C A Λ J m ≤
        2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (paperDegreeSlope C * S ^ 2 / 4) := by
      unfold dyadicSeriesEnvelope
      refine Finset.sup'_le _ _ fun j _ => ?_
      let z_j := allocationLevelPosition (paperDyadicStep C) (paperUpperSaddle C) (paperUpperShift C) H n j.val
      let arg_j := Real.exp z_j / (C_D * S)
      have harg_eq : arg_j = C₀ * dyadicPilotScale d j.val / n := by
        rw [dyadicPilotScale_eq_exp C]
        dsimp only [arg_j, z_j, allocationLevelPosition]
        rw [Real.exp_add, Real.exp_sub, Real.exp_log hn, Real.exp_log (mul_pos hH hS0)]
        dsimp only [H, S]; field_simp
      have hp_nn : 0 ≤ paperPilotMomentFactor C A :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
      have harg_le : paperPilotMomentFactor C A * dyadicPilotScale d j.val / Λ ≤ arg_j := by
        rw [harg_eq, div_le_div_iff₀ hΛpos hn]
        have hk := (dyadicPilotScale_pos d j.val).le
        have hm1 := mul_le_mul_of_nonneg_right hcoef hk
        have hm2 := mul_le_mul_of_nonneg_left hΛ12 (mul_nonneg hC0.le hk)
        nlinarith
      have hfs_eq : dyadicPilotSeries C A Λ j.val (m j.val) =
          factorialSeries (paperDyadicTotalDegree C (paperUpperSaddle C) (paperUpperShift C) H n j.val)
            (paperPilotMomentFactor C A * dyadicPilotScale d j.val / Λ) := by
        unfold dyadicPilotSeries factorialSeries paperPilotMomentFactor paperDyadicTotalDegree
        simpa only [mul_assoc] using Fin.sum_univ_eq_sum_range (fun k : ℕ =>
          ((k + 1).factorial : ℝ) *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
              preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j.val) / Λ) ^ (k + 1))
          (m j.val + anchoredDimension d C.order + 1)
      have hx0 : 0 ≤ paperPilotMomentFactor C A * dyadicPilotScale d j.val / Λ :=
        div_nonneg (mul_nonneg hp_nn (dyadicPilotScale_pos _ _).le) hΛpos.le
      have hmono : factorialSeries (paperDyadicTotalDegree C (paperUpperSaddle C) (paperUpperShift C) H n j.val)
          (paperPilotMomentFactor C A * dyadicPilotScale d j.val / Λ) ≤
          factorialSeries (Nat.floor (paperDegreeSlope C * quadraticProfile S z_j)) arg_j := by
        rw [hd j.val]
        exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 harg_le _) (Nat.cast_nonneg _)
      have hwt_le : max 1 (Λ / dyadicPilotScale d j.val) ≤ max 1 (C₀ / arg_j) := by
        have hc_eq : C₀ / arg_j = (n : ℝ) / dyadicPilotScale d j.val := by
          rw [harg_eq]; field_simp [hC0.ne', (dyadicPilotScale_pos d j.val).ne']
        rw [hc_eq]
        exact max_le_max le_rfl (div_le_div_of_nonneg_right hΛn (dyadicPilotScale_pos _ _).le)
      rw [hfs_eq]
      refine (mul_le_mul hmono hwt_le (by positivity)
        (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx0.trans harg_le) _))).trans ?_
      exact profileVarianceWeight_uniform_bound hC hD hDβ hβ.le hS (hz j.val (Nat.le_of_lt_succ j.isLt)).2
    -- 2. Spatial reserve factor
    have hround := Real.exp_le_exp.mpr (dyadicRoundedLogSide_bounds hside).2
    have hj_sq : ((2 : ℝ) ^ J) ^ 2 = Real.exp (2 / (d : ℝ) * (Real.log n + paperAllocatedDepth C H n)) := by
      have hd_ne : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
      have he : 2 / (d : ℝ) * (Real.log n + paperAllocatedDepth C H n) = (J : ℝ) * Real.log 2 * 2 := by
        change 2 / (d : ℝ) * (Real.log n + (paperDyadicStep C * (J : ℝ) - Real.log n)) = _
        unfold paperDyadicStep; field_simp; ring
      rw [he]
      have hJ : Real.exp ((J : ℝ) * Real.log 2) = (2 : ℝ) ^ J := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [← hJ]; simpa only [Nat.cast_ofNat, mul_comm] using (Real.exp_nat_mul ((J : ℝ) * Real.log 2) 2).symm
    have hsp_scale : (paperAllocatedSide C H n) ^ 2 * ((2 : ℝ) ^ J) ^ 2 ≤
        Real.exp (-paperDegreeSlope C * S ^ 2 / 4 - 2 * S) := by
      have h1 : (paperAllocatedSide C H n) ^ 2 * ((2 : ℝ) ^ J) ^ 2 ≤
          Real.exp (-2 * paperUpperVarpi C * Real.log n + paperUpperEta C * paperAllocatedDepth C H n) := by
        refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hround 2) (sq_nonneg _)).trans_eq ?_
        rw [hj_sq, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simpa only [paperAllocatedLogSide, Nat.cast_ofNat, mul_comm _ (2 : ℝ)] using
          paper_spatial_reserve_identity C (Real.log n) (paperAllocatedDepth C H n)
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      have hbud := quadratic_allocation_budget hβ (show 0 ≤ paperUpperEta C + 2 by linarith only [paperUpperEta_pos C])
        hS0.le (show S = paperUpperSaddle C * Real.sqrt (Real.log n) - (1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C) from rfl)
      have hbase : paperDegreeSlope C * (paperUpperSaddle C * Real.sqrt (Real.log n)) ^ 2 / 4 =
          2 * paperUpperVarpi C * Real.log n := by
        rw [mul_pow, Real.sq_sqrt hL, ← mul_assoc, mul_div_right_comm, paper_upper_saddle_budget_identity C hreg]
      rw [hbase] at hbud
      have ht_le : paperAllocatedDepth C H n ≤ S := by
        have ht := (roundedTerminalDepth_bounds hδ hLT).2
        have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by linarith only [hS])
        have hlogH : 0 ≤ Real.log (H * S) := Real.log_nonneg hHS
        unfold paperAllocatedDepth candidateTerminalDepth at ht ⊢
        linarith [mul_nonneg hγ hlogS]
      have hm := mul_le_mul_of_nonneg_left ht_le (paperUpperEta_pos C).le
      linarith
    unfold paperAllocatedPilotBudget dyadicMultilevelBudget
    rw [paperAllocatedFinestLevel, ← dyadicRoundedSide_eq_inv_pow]
    calc (paperAllocatedSide C H n) ^ 2 * ((2 : ℝ) ^ J) ^ 2 * dyadicSeriesEnvelope C A Λ J m
      _ ≤ Real.exp (-paperDegreeSlope C * S ^ 2 / 4 - 2 * S) *
            (2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (paperDegreeSlope C * S ^ 2 / 4)) :=
          mul_le_mul hsp_scale henv (dyadicSeriesEnvelope_nonneg C A _ hΛpos.le _ _) (Real.exp_pos _).le
      _ = 2 * C₀ * C_D ^ 2 * S ^ 2 *
            (Real.exp (-paperDegreeSlope C * S ^ 2 / 4 - 2 * S) * Real.exp (paperDegreeSlope C * S ^ 2 / 4)) := by ring
      _ = 2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S) := by rw [← Real.exp_add]; congr 2; ring
  exact (hzero.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le

end NearlyMinimax
