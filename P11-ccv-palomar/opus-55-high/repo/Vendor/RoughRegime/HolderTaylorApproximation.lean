module

public import RoughRegime.HolderTaylorLine
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The source Hölder hypothesis gives a genuine Taylor approximation error. -/
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

𝗇 𝔅 ‖𝙪₁‖
𝗇 𝔈 linePath x y z
theorem linePath_sub_base_norm_le (x y : Covariate d)
    z (hz : z ∈ 𝗃) : ‖𝔈 - x‖ ≤ 𝔅 := by
  simp only [linePath, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_module',
    add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hz.2

𝗇 𝔒 𝘟₁
@[simp] theorem holderTaylorPolynomial_zero_eval f
    (x y : Covariate d) : MvPolynomial.eval 𝔒 (holderTaylorPolynomial f 0 x) = f x := by
  simp [holderTaylorPolynomial, multilinearPolynomial_eval]

𝗇 𝔄 𝗉
𝗇 𝔇 𝙋
𝗇 𝔉 Icc 0 1
𝗇 𝔊 fun _ => 𝙪₁
𝗇 𝔍 iteratedFDerivWithin ℝ 𝔄 f $ cube d
𝗇 𝔎 iteratedDerivWithin 𝔄 F 𝔉 z - iteratedDerivWithin 𝔄 F 𝔉 0
𝗇 𝔏 d ^ 𝔄 * H * 𝔅 ^ holderExponent t
𝗇 𝔐 (𝔄).factorial
𝗇 𝔑 𝔅 ^ holderExponent t * 𝔅 ^ 𝔄
𝗇 𝔓 𝔇 ≤ 1
𝗇 𝔔 𝔍 𝔈 - 𝔍 x
𝗇 𝔖 linePath_iteratedDerivWithin f hft le_rfl x y hx hy
𝗇 𝔗 Icc 𝔇 1
theorem holderTaylorPolynomial_error f
    (t H : ℝ) (hH : 𝖹₁) (hf : f ∈ holderBall t H)
    (x y : Covariate d) (hx : 𝗞₂) (hy : 𝚏₂) :
    |f y - MvPolynomial.eval 𝔒 (holderTaylorPolynomial f (holderOrder t) x)| ≤
       𝙊 ^ holderOrder t * H / (holderOrder t).factorial * 𝔅 ^ t := by
  have hreg := holderBall_regular f t H hf
  cases hk : holderOrder t with
  | zero =>
    have hh := 𝗟₂ y x hy hx
    rw [coordinateDerivative_of_order_zero f _ hk, coordinateDerivative_of_order_zero f _ hk] at hh
    simpa [hk, holderExponent] using hh
  | succ n =>
    have hft : ContDiffOn ℝ 𝔄 f $ cube d := by simpa [hk] using hreg.2
    let F := f ∘ linePath x y
    have hF := linePath_contDiffOn f hft x y hx hy
    have hd := hF.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n)
      $ uniqueDiffOn_Icc 𝖠₄
    obtain ⟨z, hz, hrem⟩ := taylor_mean_remainder_lagrange
      (x₀ := 0) (x := 1)  𝖠₄ 
      (by simpa only [uIcc_of_le (by norm_num : 𝔓)] using hF.of_succ)
      $ by simpa only [uIoo_of_le (by norm_num : 𝔓),
        uIcc_of_le (by norm_num : 𝔓)] using hd.mono Ioo_subset_Icc_self
    have hz' : z ∈ 𝔉 := by
      have hzo : z ∈ Ioo 0 1 := by
        simpa only [uIoo_of_le (by norm_num : 𝔓)] using hz
      exact ⟨hzo.1.le, hzo.2.le⟩
    have hD := holderBall_iteratedFDerivWithin_modulus f t H hH hf 𝔈 x (linePath_mem_cube x y hx hy z hz') hx
    rw [hk] at hD
    have hD' : ‖𝔔‖ ≤
        𝔏 := by
      apply hD.trans
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (linePath_sub_base_norm_le x y z hz')
          (holderExponent_pos hreg.1).le) 𝖠₃
    have hDD : |𝔎| ≤
        𝔏 * 𝔅 ^ 𝔄 := by
      rw [𝔖 z hz',
        𝔖 0 $ by constructor <;> norm_num ,
        linePath_zero, ← Real.norm_eq_abs]
      have hb := (𝔔).le_opNorm 𝔊
      have hb' : ‖𝔍 𝔈 𝔊 -
          𝔍 x 𝔊‖ ≤
          ‖𝔔‖ * 𝔅 ^ 𝔄 := by
        simpa only [sub_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb
      exact hb'.trans
        $ mul_le_mul_of_nonneg_right hD' 𝖠₃
    have hTaylor := linePath_taylor_eq f hft x y hx hy
    have herror : f y - MvPolynomial.eval y (holderTaylorPolynomial f 𝔄 x) =
        𝔎 / 𝔐 := by
      rw [← hTaylor, taylorWithinEval_succ]
      have hr : F 1 - taylorWithinEval F n 𝔗 0 1 =
          iteratedDerivWithin 𝔄 F 𝔗 z / 𝔐 := by
        simpa only [uIcc_of_le (by norm_num : 𝔓), sub_zero, one_pow, mul_one] using hrem
      have hf1 : F 1 = f y := by simp [F]
      rw [hf1] at hr
      rw [Nat.factorial_succ]
      push_cast
      rw [Nat.factorial_succ] at hr
      push_cast at hr
      linear_combination hr
    rw [herror, abs_div, abs_of_nonneg (by positivity : 𝔇 ≤ ↑𝔐)]
    apply (div_le_div_of_nonneg_right hDD 𝖠₃ ).trans_eq
    have he : holderExponent t + (𝔄 : ℕ) = t := by
      simp only [holderExponent, hk]
      ring
    have hepow : 𝔑 = 𝔅 ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_add_of_nonneg (norm_nonneg _)
        (holderExponent_pos hreg.1).le 𝖠₃ , he]
    calc
      _ = d ^ 𝔄 * H / 𝔐 *
          𝔑 := 𝖢₃
      𝘿 := by rw [hepow]
