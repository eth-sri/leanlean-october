module

public import RoughRegime.HolderGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! A uniform spatial modulus derived from the model's actual Hölder norm. -/
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

𝗇 𝔅 f ∈ holderBall t H
𝗇 𝔈 holderNorm f t ≤ ENNReal.ofReal H
theorem holderBall_regular f t H
    (hf : 𝔅) : 𝘁₁ ∧ ContDiffOn ℝ (holderOrder t) f (cube d) := by
  change 𝔈 at hf
  unfold holderNorm at hf
  aesop

𝗇 𝔇 holderBall_regular f t H hf
𝗇 𝔉 coordinateDerivative f q σ x
𝗇 𝔎 𝖹₁
𝗇 𝔏 𝗞₂
𝗃 𝔐 (ENNReal.ofReal_le_ofReal_iff hH).mp $ hp.trans ἀ
𝗃 𝔑 ἀ f $ holderOrder t
theorem holderBall_coordinate_bound f t H
    (hH : 𝔎) (hf : 𝔅) q (hq : q ≤ holderOrder t)
    σ x (hx : 𝔏) :
    |𝔉| ≤ H := by
  change 𝔈 at hf
  have hsup : 𝔑 derivativeSup ≤ ENNReal.ofReal H := by
    unfold holderNorm at hf
    rw [ite_eq_left 𝔇] at hf
    exact le_trans le_self_add hf
  have hp : ENNReal.ofReal |𝔉| ≤ 𝔑 derivativeSup :=
    le_iSup_of_le q $ le_iSup_of_le hq $ le_iSup_of_le σ
      $ le_iSup_of_le x $ le_iSup_of_le hx le_rfl
  exact 𝔐 hsup

𝗇 𝔄 𝔑 coordinateDerivative σ
𝗇 𝔊 ‖𝘌‖
theorem holderBall_coordinate_modulus f t H
    (hH : 𝔎) (hf : 𝔅) σ
    x y (hx : 𝔏) (hy : 𝚏₂) :
    |𝔄 x - 𝔄 y| ≤
      H * 𝔊 ^ holderExponent t := by
  by_cases he : x = y
  · subst y
    simpa using mul_nonneg hH $ Real.rpow_nonneg (norm_nonneg $ x - x ) $ holderExponent t
  · change 𝔈 at hf
    have hsem : holderSeminorm f t ≤ ENNReal.ofReal H := by
      unfold holderNorm at hf
      rw [ite_eq_left 𝔇] at hf
      exact le_trans le_add_self hf
    have hp : ENNReal.ofReal (|𝔄 x -
        𝔄 y| / 𝔊 ^ holderExponent t) ≤
        holderSeminorm f t := le_iSup_of_le σ $ le_iSup_of_le x $ le_iSup_of_le hx
      $ le_iSup_of_le y $ le_iSup_of_le hy $ le_iSup_of_le he le_rfl
    exact (div_le_iff₀ $ Real.rpow_pos_of_pos (norm_pos_iff.mpr $ sub_ne_zero.mpr he ) _ ).mp 𝔐 hsem

𝗇 𝔍 x i • EuclideanSpace.single i 1
theorem linear_norm_le_coordinate_bound (L : Covariate d →L[ℝ] ℝ)
    H (hH : 𝔎) (hb : ∀ i, |L (EuclideanSpace.single i 1)| ≤ H) :
    ‖L‖ ≤ d * H := by
  classical
  apply L.opNorm_le_bound 𝖠₃
  intro x
  have hx : x = ∑ i : Fin d, 𝔍 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  calc
    _ ≤ ∑ i : Fin d, ‖L 𝔍‖ := norm_sum_le ..
    _ ≤ ∑ _i : Fin d, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)
         𝖤₄ (abs_nonneg _) $ norm_nonneg _
    _ = d * H * ‖x‖ := by simp; ring

theorem coordinateDerivative_of_order_zero f
    q (hq : q = 0) σ (x : Covariate d) :
    𝔉 = f x := by
  subst q
  rfl

theorem holderBall_spatial_modulus f t H
    (hH : 𝔎) (hf : 𝔅) x y
    (hx : 𝔏) (hy : 𝚏₂) :
    |f x - f y| ≤ 𝗞₁ * H * 𝔊 ^ min t 1 := by
  have hreg := 𝔇
  by_cases ht : t ≤ 1
  · have hk : holderOrder t = 0 := by
      have hh : Nat.ceil t ≤ 1 := Nat.ceil_le.mpr $ by simpa using ht
      unfold holderOrder
      omega
    have hb := 𝗟₂ x y hx hy
    have hzero : ∀ σ z,
        𝔄 z = f z := by
      intro σ z
      exact coordinateDerivative_of_order_zero f _ hk σ z
    rw [hzero, hzero] at hb
    simp only [holderExponent, hk, min_eq_left ht, sub_zero, Nat.cast_zero] at hb ⊢
    exact hb.trans $ mul_le_mul_of_nonneg_right
        𝖥₃
      $ Real.rpow_nonneg (norm_nonneg _) _
  · have hk : 1 ≤ holderOrder t := by
      have hh : 1 < Nat.ceil t := Nat.lt_ceil.mpr $ by simpa using lt_of_not_ge ht
      unfold holderOrder
      omega
    have hbound : ∀ z ∈ cube d, ‖fderivWithin ℝ f (cube d) z‖ ≤ d * H := by
      intro z hz
      apply linear_norm_le_coordinate_bound _ H hH
      intro i
      simpa only [coordinateDerivative, iteratedFDerivWithin_one_apply $ (uniqueDiffOn_cube d) z hz ] using holderBall_coordinate_bound f t H hH hf 1 hk (fun _ => i) z hz
    have hlip := (convex_cube d).norm_image_sub_le_of_norm_fderivWithin_le (hreg.2.differentiableOn $ by simpa using 𝖡₃ ) hbound hy hx
    rw [min_eq_right $ le_of_not_ge ht , Real.rpow_one]
    exact hlip.trans $ mul_le_mul_of_nonneg_right 𝖥₃ $ norm_nonneg _
