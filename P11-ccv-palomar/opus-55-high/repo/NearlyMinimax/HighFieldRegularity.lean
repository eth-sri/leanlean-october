module

public import NearlyMinimax.HighSmoothnessWindows
public import NearlyMinimax.CoordinatePartialBridge
public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.AnchoredGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Resolution-independent derivative and Hölder estimates for actual
periodic window fields. -/
𝚸
open scoped BigOperators ContDiff ENNReal
𝚨
𝚩
𝚭
𝚬

𝗇 𝔎 fun j => g j ≠ 0
𝗇 𝔑 ‖g j‖
theorem finite_sum_norm_le_active_count [Fintype J]
    [NormedAddCommGroup E] (g : J → E) N B (hB : 𝙐)
    (hbound : ∀ j, 𝔑 ≤ B)
    (hcount : (Finset.univ.filter 𝔎).card ≤ N) :
    ‖∑ j, g j‖ ≤ N * B := by
  let A := Finset.univ.filter 𝔎
  have hsum : ∑ j, 𝔑 = ∑ j ∈ A, 𝔑 := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    simp_all
  calc
    _ ≤ ∑ j, 𝔑 := norm_sum_le ..
    𝘿 := hsum
    _ ≤ ∑ _j ∈ A, B := Finset.sum_le_sum fun j _ => hbound j
    _ = A.card * B := 𝖢₄
    𝖦 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB

𝗇 𝔈 1 - α
𝗇 𝔊 r ^ α
𝗇 𝔏 2 * A
𝗇 𝔔 (k * r) ^ 𝔈 * 𝔊
𝗇 𝔚 A * k ^ 𝔈 * r
𝗃 𝔟 k ^ (-ἀ)
/-- Combining the uniform derivative bound and the next-derivative
Lipschitz bound preserves the fractional exponent, uniformly in resolution. -/
theorem holder_of_scaled_sup_and_lipschitz (k r A α q : ℝ)
    (hk : 𝖰) (hr : 𝘵₁) (hA : 𝖲₁) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hsup : q ≤ 𝔏 * 𝔟 α)
    (hlip : q ≤ 𝔚) :
    q ≤ 𝔏 * 𝔊 := by
  by_cases hr0 : r = 0
  · subst r
    simpa only [mul_zero, Real.zero_rpow hα0.ne'] using hlip
  by_cases hkr : k * r ≤ 1
  · have hp :=
      Real.rpow_le_one (mul_nonneg hk.le hr) hkr $ sub_nonneg.mpr hα1
    have hid : k ^ 𝔈 * r = 𝔔 := by
      rw [Real.mul_rpow hk.le hr]
      rw [mul_assoc, ← Real.rpow_add $ lt_of_le_of_ne hr $ Ne.symm hr0 ]
      simp
    have hsmall : 𝔚 ≤ A * 𝔊 := by
      calc
        _ = A * 𝔔 := 𝖤₃
        _ ≤ A * (1 * 𝔊) := 𝖩₃
        𝘿 := 𝖢₃
    have hpositive : 0 ≤ A * 𝔊 := mul_nonneg hA $ Real.rpow_nonneg hr _
    linarith
  · have hkinv : 𝔟 α ≤ 𝔊 := by
      rw [Real.rpow_neg hk.le, ← one_div]
      apply (div_le_iff₀ $ Real.rpow_pos_of_pos hk α ).mpr
      simpa only [Real.mul_rpow hk.le hr, one_mul, mul_comm] using Real.one_le_rpow (le_of_not_ge hkr) hα0.le
    nlinarith

theorem multiIndexBasis_norm (γ : Fin d → ℕ) j :
    ‖multiIndexBasis γ j‖ = 1 := by
  simp [multiIndexBasis, wordBasis, Pi.norm_single]

𝗇 𝔄 ∑ r, γ r
𝗇 𝔒 ContDiff ℝ ∞ F
𝗇 𝔓 iteratedFDeriv ℝ 𝔄 F x
𝗇 𝔗 multiPartial_eq_iteratedFDeriv univ isOpen_univ F 𝔄
𝗃 𝔠 (ἀ).le_opNorm $ multiIndexBasis γ
theorem multiPartial_norm_le_iterated F
    (hF : 𝔒) γ (x : Covariate d) :
    |multiPartial F γ x| ≤ ‖𝔓‖ := by
  rw [𝔗
    (hF.of_le 𝖢₄ ).contDiffOn γ le_rfl x $ mem_univ x ]
  simpa only [Real.norm_eq_abs, multiIndexBasis_norm, Finset.prod_const_one, mul_one] using 𝔠 𝔓

𝗇 𝔛 𝔓 - iteratedFDeriv ℝ 𝔄 F y
theorem multiPartial_diff_norm_le_iterated F
    (hF : 𝔒) γ (x y : Covariate d) :
    |multiPartial F γ x - multiPartial F γ y| ≤
      ‖𝔛‖ := by
  rw [𝔗
    (hF.of_le 𝖢₄ ).contDiffOn γ le_rfl x $ mem_univ x ,
    𝔗
    (hF.of_le 𝖢₄ ).contDiffOn γ le_rfl y $ mem_univ y ]
  have hh := 𝔠 𝔛
  simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs, multiIndexBasis_norm,
    Finset.prod_const_one, mul_one] using hh

theorem covariate_norm_le_euclidean (x : Covariate d) : ‖x‖ ≤ euclideanNorm x := by
  apply (pi_norm_le_iff_of_nonneg $ Real.sqrt_nonneg _ ).mpr
  intro r
  simpa only [Real.norm_eq_abs, euclideanNorm] using abs_coordinate_le_euclideanNorm x r

𝗇 𝔅 fun r => 𝗅₁
𝗇 𝔇 ∑ r, 𝗅₁
𝗇 𝔉 𝗈₂
𝗇 𝔖 iteratedFDeriv ℝ C.order F
𝗇 𝔍 ‖𝔖 x - 𝔖 y‖
𝗇 𝔐 𝘌
𝗇 𝔘 A * k ^ (1 - C.alpha)
𝗇 𝔙 (𝔉 : ℕ)
𝗇 𝔜 ‖iteratedFDeriv ℝ q F x‖
𝗇 𝔞 (𝔇 : ℕ)
𝗃 𝔡 ἀ - C.smoothness
/-- The actual scaled Fréchet bounds imply the manuscript's sorted mixed
partial bounds and top-order Euclidean Hölder modulus. -/
theorem mixed_bounds_of_scaled_derivatives (C : ModelConstants d)
    F (hF : 𝔒) (k A : ℝ)
    (hk : 𝗽₁) (hA : 𝖲₁)
    (hbound : ∀ q ≤ 𝔉, ∀ x,
      𝔜 ≤ A * k ^ ((q : ℝ) - C.smoothness)) :
    (∀ γ : Fin d → Fin 𝔉, 𝔇 ≤ C.order → ∀ x,
      |multiPartial F 𝔅 x| ≤ A) ∧
     ∀ γ : Fin d → Fin 𝔉, 𝔇 = C.order → ∀ x y,
      |multiPartial F 𝔅 x - multiPartial F 𝔅 y| ≤
        𝔏 * euclideanNorm 𝔐 ^ C.alpha := by
  have hkpos : 𝖰 := lt_of_lt_of_le 𝖠₄ hk
  constructor
  · intro γ hγ x
    apply (multiPartial_norm_le_iterated F hF _ x).trans
    apply (hbound _ 𝖡₃ x).trans
    have hcast : (𝔞 : ℝ) ≤ C.order := by exact_mod_cast hγ
    have hp : k ^ 𝔡 𝔞 ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk $ by linarith [C.order_lt]
    bound
  · intro γ hγ x y
    have hsup z : ‖𝔖 z‖ ≤ A * 𝔟 C.alpha := by
      have he : 𝔡 C.order = -C.alpha := by unfold ModelConstants.alpha; ring
      grind
    have hnext (z : Covariate d) : ‖fderiv ℝ 𝔖 z‖ ≤
        𝔘 := by
      rw [norm_fderiv_iteratedFDeriv]
      have he : 𝔡 𝔙 = 1 - C.alpha := by
        unfold ModelConstants.alpha
        push_cast
        ring
      grind
    have hsmall : 𝔍 ≤
        𝔘 * ‖𝔐‖ := by
      have hfFinite : ContDiff ℝ 𝔉 F := hF.of_le 𝖢₄
      exact Convex.norm_image_sub_le_of_norm_fderiv_le
         fun z _hz =>
          hfFinite.contDiffAt.differentiableAt_iteratedFDeriv
            $ by exact_mod_cast Nat.lt_succ_self C.order
        (fun z _ => hnext z) convex_univ (mem_univ y) $ mem_univ x
    have hh := holder_of_scaled_sup_and_lipschitz k ‖𝔐‖ A C.alpha
      𝔍
      hkpos (norm_nonneg _) hA C.alpha_pos C.alpha_le_one ((norm_sub_le _ _).trans 𝖤₃ ) hsmall
    have heval := multiPartial_diff_norm_le_iterated F hF 𝔅 x y
    rw [hγ] at heval
    exact (heval.trans hh).trans $ mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (covariate_norm_le_euclidean 𝔐) C.alpha_pos.le)
      𝖠₃

theorem holderNorm_of_scaled_derivatives (C : ModelConstants d)
    U (F : 𝙀) (hF : 𝔒)
    k A (hk : 𝗽₁) (hA : 𝖲₁)
    (hbound : ∀ q ≤ 𝔉, ∀ x,
      𝔜 ≤ A * k ^ 𝔡 q) :
    𝘍₂ C.order C.alpha ≤
      ENNReal.ofReal ((𝔙 ^ d + 2) * A) := by
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F hF k A hk hA hbound
  have hh := holderNorm_of_global_mixed_bounds U F C.order C.alpha A 𝔏
    hA 𝖠₃ hs hm
  convert hh using 1
  ring
