module

public import RoughRegime.HolderGeometry


@[expose] public section

/-! A uniform spatial modulus derived from the model's actual Hölder norm. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

section
variable {d : ℕ} {f : Covariate d → ℝ} {t H : ℝ} (hH : 0 ≤ H) (hf : f ∈ holderBall t H)
include hf

theorem holderBall_regular : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) := by
  change _ ≤ ENNReal.ofReal H at hf
  unfold holderNorm at hf
  aesop

include hH in
theorem holderBall_coordinate_bound {q : ℕ} (hq : q ≤ holderOrder t)
    (σ : Fin q → Fin d) {x : Covariate d} (hx : x ∈ cube d) :
    |coordinateDerivative f σ x| ≤ H := by
  have hreg := holderBall_regular hf
  change _ ≤ ENNReal.ofReal H at hf
  have hp : ENNReal.ofReal |coordinateDerivative f σ x| ≤ derivativeSup f (holderOrder t) :=
    le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ
      (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
  exact (ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans (by
    unfold holderNorm at hf
    rw [ite_eq_left hreg] at hf
    exact le_trans le_self_add hf))

include hH in
theorem holderBall_coordinate_modulus (σ : Fin (holderOrder t) → Fin d)
    {x y : Covariate d} (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |coordinateDerivative f σ x - coordinateDerivative f σ y| ≤
      H * ‖x - y‖ ^ holderExponent t := by
  by_cases he : x = y
  · subst y
    simpa using mul_nonneg hH (by positivity)
  · change _ ≤ ENNReal.ofReal H at hf
    have hsem : holderSeminorm f t ≤ ENNReal.ofReal H := by
      unfold holderNorm at hf
      rw [ite_eq_left (holderBall_regular hf)] at hf
      exact le_trans le_add_self hf
    have hp : ENNReal.ofReal (|coordinateDerivative f σ x -
        coordinateDerivative f σ y| / ‖x - y‖ ^ holderExponent t) ≤
        holderSeminorm f t := le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx
      (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le he le_rfl)))))
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr he)) _)).mp ((ENNReal.ofReal_le_ofReal_iff hH).mp (hp.trans hsem))

end

lemma linear_norm_le_coordinate_bound {d : ℕ} (L : Covariate d →L[ℝ] ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hb : ∀ i, |L (EuclideanSpace.single i 1)| ≤ H) :
    ‖L‖ ≤ (d : ℝ) * H := by
  classical
  apply L.opNorm_le_bound (by positivity)
  intro x
  have hx : x = ∑ i : Fin d, x i • EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  calc
    _ ≤ ∑ i : Fin d, ‖L (x i • EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le x i)
        (by bound) (abs_nonneg _) (norm_nonneg _)
    _ = d * H * ‖x‖ := by simp; ring

lemma coordinateDerivative_of_order_zero {d : ℕ} (f : Covariate d → ℝ)
    (q : ℕ) (hq : q = 0) (σ : Fin q → Fin d) (x : Covariate d) :
    coordinateDerivative f σ x = f x := by
  subst q
  rfl

theorem holderBall_spatial_modulus {d : ℕ} {f : Covariate d → ℝ} {t H : ℝ}
    (hH : 0 ≤ H) (hf : f ∈ holderBall t H) {x y : Covariate d}
    (hx : x ∈ cube d) (hy : y ∈ cube d) :
    |f x - f y| ≤ (d + 1) * H * ‖x - y‖ ^ min t 1 := by
  have hreg := holderBall_regular hf
  by_cases ht : t ≤ 1
  · have hk : holderOrder t = 0 := by
      have hh : Nat.ceil t ≤ 1 := Nat.ceil_le.mpr (by simpa using ht)
      unfold holderOrder
      omega
    have hb := holderBall_coordinate_modulus hH hf
      (fun i => Fin.elim0 (show Fin 0 from hk ▸ i)) hx hy
    have hzero : ∀ (σ : Fin (holderOrder t) → Fin d) z,
        coordinateDerivative f σ z = f z := by
      solve_by_elim [coordinateDerivative_of_order_zero]
    rw [hzero, hzero] at hb
    simp only [holderExponent, hk, min_eq_left ht, sub_zero, Nat.cast_zero] at hb ⊢
    exact hb.trans (mul_le_mul_of_nonneg_right
      (show H ≤ (d + 1) * H by nlinarith)
      (by positivity))
  · have hk : 1 ≤ holderOrder t := by
      have hh : 1 < Nat.ceil t := Nat.lt_ceil.mpr (by simpa using lt_of_not_ge ht)
      unfold holderOrder
      omega
    have hbound : ∀ z ∈ cube d, ‖fderivWithin ℝ f (cube d) z‖ ≤ d * H := by
      intro z hz
      apply linear_norm_le_coordinate_bound _ H hH
      intro i
      simpa only [coordinateDerivative, iteratedFDerivWithin_one_apply ((uniqueDiffOn_cube d) z hz)] using holderBall_coordinate_bound hH hf hk (fun _ => i) hz
    have hlip := (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le (hreg.2.differentiableOn (by positivity)) hbound hy hx
    rw [min_eq_right (le_of_not_ge ht), Real.rpow_one]
    exact hlip.trans (by bound)

end RoughRegime.Model
