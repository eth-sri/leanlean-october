module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.BarrierSign
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

/-- Uniform damping budget on blocks no longer than `T1`. -/
def XiStar (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 * Lam * (128 * (d : ℝ) / lam) + 2 * H ^ 2 * T1 / (3 * lam)

/-- Source Gaussian level, fixed before coefficients, paths, and solutions. -/
def barrierL (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 * Real.sqrt (XiStar d lam Lam H T1)

/-- Source block radius multiplier. -/
def barrierW (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  2 + 3 / 2 * barrierL d lam Lam H T1 * Real.sqrt lam + 2 * H * Real.sqrt T1

/-- Velocity tube containment coefficient. -/
def velocityTubeConstant (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  let W := barrierW d lam Lam H T1
  W + H * W ^ 2 * Real.sqrt T1

/-- Position tube containment coefficient. -/
def positionTubeConstant (d : ℕ) (lam Lam H T1 : ℝ) : ℝ :=
  let W := barrierW d lam Lam H T1
  W ^ 3 + H * W ^ 4 * Real.sqrt T1 / 2

/-- The source minimum of time, velocity, and position step restrictions. -/
def stepSize (d : ℕ) (lam Lam H T0 T1 kx kv : ℝ) : ℝ :=
  min (T0 / (barrierW d lam Lam H T1) ^ 2)
    (min ((kv / (2 * velocityTubeConstant d lam Lam H T1)) ^ 2)
      ((kx / (2 * positionTubeConstant d lam Lam H T1)) ^ (2 / 3 : ℝ)))

/-- Source positive Gaussian gap at the block endpoint. -/
def barrierCb (L : ℝ) : ℝ := Real.exp (-3 / 4 * L ^ 2) - Real.exp (-L ^ 2)

/-- Source amplitude loss at one overlap step. -/
def barrierGamma (L : ℝ) : ℝ := barrierCb L * Real.exp (-L ^ 2 / 512)





/-- The source damping budget is positive in positive dimension. -/
theorem XiStar_pos {d : ℕ} (hd : 1 ≤ d) {lam Lam H T1 : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hT1 : 0 ≤ T1) : 0 < XiStar d lam Lam H T1 := by
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  unfold XiStar
  exact add_pos_of_pos_of_nonneg (by positivity) (by positivity)

/-- The source Gaussian level is positive. -/
theorem barrierL_pos {d : ℕ} (hd : 1 ≤ d) {lam Lam H T1 : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hT1 : 0 ≤ T1) :
    0 < barrierL d lam Lam H T1 :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr (XiStar_pos hd hlam hLam hT1))

/-- Squaring the source level gives exactly four times its damping budget. -/
theorem barrierL_sq {d : ℕ} {lam Lam H T1 : ℝ} (hXi : 0 ≤ XiStar d lam Lam H T1) :
    (barrierL d lam Lam H T1) ^ 2 = 4 * XiStar d lam Lam H T1 := by
  unfold barrierL
  rw [mul_pow, Real.sq_sqrt hXi]
  norm_num

/-- The radius multiplier is at least two. -/
theorem two_le_barrierW {d : ℕ} {lam Lam H T1 : ℝ} (hH : 0 ≤ H) :
    2 ≤ barrierW d lam Lam H T1 := by
  have hL : 0 ≤ barrierL d lam Lam H T1 := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  unfold barrierW
  have h1 : 0 ≤ 3 / 2 * barrierL d lam Lam H T1 * Real.sqrt lam := by positivity
  have h2 : 0 ≤ 2 * H * Real.sqrt T1 := by positivity
  linarith only [h1, h2]

/-- The two tube constants are positive with their literal source formulas. -/
theorem tubeConstants_pos {d : ℕ} {lam Lam H T1 : ℝ} (hH : 0 ≤ H) :
    0 < velocityTubeConstant d lam Lam H T1 ∧ 0 < positionTubeConstant d lam Lam H T1 := by
  have hW : 0 < barrierW d lam Lam H T1 := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  unfold velocityTubeConstant positionTubeConstant
  constructor <;> positivity

/-- The source minimum step is strictly positive. -/
theorem stepSize_pos {d : ℕ} {lam Lam H T0 T1 kx kv : ℝ}
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hkx : 0 < kx) (hkv : 0 < kv) :
    0 < stepSize d lam Lam H T0 T1 kx kv := by
  have hW : 0 < barrierW d lam Lam H T1 := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  obtain ⟨hc1, hc2⟩ := tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  unfold stepSize
  apply lt_min
  · positivity
  · apply lt_min <;> positivity


/-- The source loss factor is strictly between zero and one. -/
theorem barrierGamma_bounds {L : ℝ} (hL : 0 < L) :
    0 < barrierGamma L ∧ barrierGamma L < 1  := by
  have barrierCb_bounds :
      0 < barrierCb L ∧ barrierCb L < 1 := by
    have hsq : 0 < L ^ 2 := sq_pos_of_pos hL
    have he : Real.exp (-L ^ 2) < Real.exp (-3 / 4 * L ^ 2) :=
      Real.exp_lt_exp.mpr (by linarith only [hsq])
    have hu : Real.exp (-3 / 4 * L ^ 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hsq])
    unfold barrierCb
    constructor
    · exact sub_pos.mpr he
    · linarith only [hu, Real.exp_pos (-L ^ 2)]
  obtain ⟨hc0, hc1⟩ := barrierCb_bounds
  have he : Real.exp (-L ^ 2 / 512) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg L])
  constructor
  · exact mul_pos hc0 (Real.exp_pos _)
  · exact (mul_le_of_le_one_right hc0.le he).trans_lt hc1

/-- Every admissible block remains within one quarter of the initial time budget. -/
theorem propagation_step_time {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    (barrierW d lam Lam H T1) ^ 2 * h ≤ T0 ∧ 4 * h ≤ T0  := by
  have stepSize_le_time : stepSize d lam Lam H T0 T1 kx kv ≤ T0 / (barrierW d lam Lam H T1) ^ 2 :=
    min_le_left _ _
  have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  have hWpos : 0 < barrierW d lam Lam H T1 := by linarith only [hW]
  have ht := (le_div_iff₀ (sq_pos_of_pos hWpos)).mp
    (hhstar.trans (stepSize_le_time))
  constructor
  · simpa only [mul_comm] using ht
  · nlinarith only [ht, hW, hh, sq_nonneg (barrierW d lam Lam H T1 - 2)]

/-- Every admissible block satisfies the exact uniform Gaussian damping budget. -/
theorem propagation_step_damping {d : ℕ} (hd : 1 ≤ d) {lam Lam H T0 T1 kx kv h : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1)
    (hh : 0 < h) (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    Xi d lam Lam H h * h ≤ (barrierL d lam Lam H T1) ^ 2 / 4 := by
  have htime := (propagation_step_time hH hh hhstar).2
  have hhT1 : h ≤ T1 := by linarith only [htime, hT1, hh]
  have hXi := (XiStar_pos (H := H) hd hlam hLam (hT0.trans_le hT1).le).le
  rw [barrierL_sq hXi]
  have he : Xi d lam Lam H h * h =
      2 * Lam * (128 * (d : ℝ) / lam) + (2 * H ^ 2 / (3 * lam)) * h := by
    unfold Xi
    field_simp
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hhT1
    (show 0 ≤ 2 * H ^ 2 / (3 * lam) by positivity)
  calc
    _ ≤ 2 * Lam * (128 * (d : ℝ) / lam) + (2 * H ^ 2 / (3 * lam)) * T1 :=
      add_le_add le_rfl hm
    _ = _ := by unfold XiStar; ring


/-- The source velocity step restriction gives the half-radius containment bound. -/
theorem propagation_step_velocity {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkv : 0 < kv) (_hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    velocityTubeConstant d lam Lam H T1 * Real.sqrt h ≤ kv / 2  := by
  have stepSize_le_velocity : stepSize d lam Lam H T0 T1 kx kv ≤
      (kv / (2 * velocityTubeConstant d lam Lam H T1)) ^ 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).1
  have hratio : 0 < kv / (2 * velocityTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.sqrt_le_sqrt
    (hhstar.trans (stepSize_le_velocity))
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hratio] at hb
  calc
    _ ≤ velocityTubeConstant d lam Lam H T1 *
        (kv / (2 * velocityTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

/-- The source position step restriction gives the half-radius containment bound. -/
theorem propagation_step_position {d : ℕ} {lam Lam H T0 T1 kx kv h : ℝ}
    (hH : 0 ≤ H) (hkx : 0 < kx) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv) :
    positionTubeConstant d lam Lam H T1 * h ^ (3 / 2 : ℝ) ≤ kx / 2  := by
  have stepSize_le_position : stepSize d lam Lam H T0 T1 kx kv ≤
      (kx / (2 * positionTubeConstant d lam Lam H T1)) ^ (2 / 3 : ℝ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hc := (tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH).2
  have hratio : 0 < kx / (2 * positionTubeConstant d lam Lam H T1) := by positivity
  have hb := Real.rpow_le_rpow hh.le
    (hhstar.trans (stepSize_le_position))
    (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  rw [← Real.rpow_mul hratio.le] at hb
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hb
  calc
    _ ≤ positionTubeConstant d lam Lam H T1 *
        (kx / (2 * positionTubeConstant d lam Lam H T1)) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = _ := by field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Holder

