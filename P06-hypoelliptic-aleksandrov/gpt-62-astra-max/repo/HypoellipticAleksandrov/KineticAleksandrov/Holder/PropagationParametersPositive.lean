module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParameters
import Mathlib.Tactic

/-! # Positivity and damping budget of the jointly fixed propagation parameters -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

section
variable {d : ℕ} {L : ℝ} (hd : 1 ≤ d) (hL : 0 < L) {lam Lam H T1 : ℝ} (hlam : 0 < lam)
    (hH : 0 ≤ H) (hLam : lam ≤ Lam) (hT1 : 0 ≤ T1)

include hd hlam hLam hT1 in
/-- The source damping budget is positive in positive dimension. -/
theorem XiStar_pos : 0 < XiStar d lam Lam H T1 := by
  have hd0 : 0 < d := Nat.cast_pos.mpr (by omega)
  have hLam0 := hlam.trans_le hLam
  unfold XiStar
  exact add_pos_of_pos_of_nonneg (by positivity) (by positivity)

include hd hlam hLam hT1 in
/-- The source Gaussian level is positive. -/
theorem barrierL_pos :
    0 < barrierL d lam Lam H T1 :=
  mul_pos (by norm_num) (Real.sqrt_pos.mpr (XiStar_pos hd hlam hLam hT1))

/-- Squaring the source level gives exactly four times its damping budget. -/
theorem barrierL_sq (hXi : 0 ≤ XiStar d lam Lam H T1) :
    (barrierL d lam Lam H T1) ^ 2 = 4 * XiStar d lam Lam H T1 := by
  unfold barrierL
  rw [mul_pow, Real.sq_sqrt hXi]
  norm_num

include hH in
/-- The radius multiplier is at least two. -/
theorem two_le_barrierW :
    2 ≤ barrierW d lam Lam H T1 := by
  have hL : 0 ≤ barrierL d lam Lam H T1 := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  unfold barrierW
  have h1 : 0 ≤ 3 / 2 * barrierL d lam Lam H T1 * Real.sqrt lam := by positivity
  have h2 : 0 ≤ 2 * H * Real.sqrt T1 := by positivity
  linarith only [h1, h2]

include hH in
/-- The two tube constants are positive with their literal source formulas. -/
theorem tubeConstants_pos :
    0 < velocityTubeConstant d lam Lam H T1 ∧ 0 < positionTubeConstant d lam Lam H T1 := by
  have hW : 0 < barrierW d lam Lam H T1 := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  unfold velocityTubeConstant positionTubeConstant
  constructor <;> positivity

/-- The source minimum step is strictly positive. -/
theorem stepSize_pos {lam Lam H T0 T1 kx kv : ℝ}
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hkx : 0 < kx) (hkv : 0 < kv) :
    0 < stepSize d lam Lam H T0 T1 kx kv := by
  have hW : 0 < barrierW d lam Lam H T1 := lt_of_lt_of_le (by norm_num) (two_le_barrierW hH)
  obtain ⟨hc1, hc2⟩ := tubeConstants_pos (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  unfold stepSize
  apply lt_min
  · positivity
  positivity

include hL in
/-- The Gaussian gap is positive and below one. -/
theorem barrierCb_bounds : 0 < barrierCb L ∧ barrierCb L < 1 := by
  have hsq := sq_pos_of_pos hL
  have hu : Real.exp (-3 / 4 * L ^ 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hsq])
  unfold barrierCb
  constructor
  · exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith only [hsq]))
  · linarith only [hu, Real.exp_pos (-L ^ 2)]

include hL in
/-- The source loss factor is strictly between zero and one. -/
theorem barrierGamma_bounds :
    0 < barrierGamma L ∧ barrierGamma L < 1 := by
  obtain ⟨hc0, hc1⟩ := barrierCb_bounds hL
  constructor
  · exact mul_pos hc0 (Real.exp_pos _)
  · exact (mul_le_of_le_one_right hc0.le (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg L]))).trans_lt hc1

end

variable {d : ℕ} (hd : 1 ≤ d) {lam Lam H T0 T1 kx kv h : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hH : 0 ≤ H) (hT0 : 0 < T0) (hT1 : T0 ≤ T1) (hh : 0 < h)
    (hhstar : h ≤ stepSize d lam Lam H T0 T1 kx kv)
include hH hh hhstar

/-- Every admissible block remains within one quarter of the initial time budget. -/
theorem propagation_step_time :
    (barrierW d lam Lam H T1) ^ 2 * h ≤ T0 ∧ 4 * h ≤ T0 := by
  have hW := two_le_barrierW (d := d) (lam := lam) (Lam := Lam) (T1 := T1) hH
  have hWpos : 0 < barrierW d lam Lam H T1 := by linarith only [hW]
  have ht := (le_div_iff₀ (sq_pos_of_pos hWpos)).mp
    (hhstar.trans (stepSize_le_time d lam Lam H T0 T1 kx kv))
  constructor
  · simpa [mul_comm] using ht
  · nlinarith only [ht, hW, hh, sq_nonneg (barrierW d lam Lam H T1 - 2)]

include hd hlam hLam hT0 hT1 in
/-- Every admissible block satisfies the exact uniform Gaussian damping budget. -/
theorem propagation_step_damping :
    Xi d lam Lam H h * h ≤ (barrierL d lam Lam H T1) ^ 2 / 4 := by
  have hhT1 : h ≤ T1 := by linarith only [((propagation_step_time hH hh hhstar).2), hT1, hh]
  rw [barrierL_sq ((XiStar_pos (H := H) hd hlam hLam (hT0.trans_le hT1).le).le)]
  have he : Xi d lam Lam H h * h =
      2 * Lam * (128 * d / lam) + (2 * H ^ 2 / (3 * lam)) * h := by
    unfold Xi
    field_simp
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hhT1
    (show 0 ≤ 2 * H ^ 2 / (3 * lam) by positivity)
  calc
    _ ≤ 2 * Lam * (128 * d / lam) + (2 * H ^ 2 / (3 * lam)) * T1 :=
      add_le_add le_rfl hm
    _ = _ := by unfold XiStar; ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
