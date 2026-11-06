module

public import NearlyMinimax.ExponentialSpatialKernels
public import NearlyMinimax.GammaTailBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine scalar pair Laplace kernels and fine-tail spatial integrability. -/
𝚫
𝚨
𝚩
𝚰

𝗃 𝔜 Real.exp $ -(ἀ*r)
𝗇 𝔄 𝔜 T
𝗇 𝔧 T * 𝔄
/-- The true scalar pair kernel from the source integral. -/
def pairLaplaceKernel (N r : ℝ) : ℝ := ∫ T in (𝙋)..N, 𝔧

/-- The true fine alias Laplace kernel. -/
def fineAliasLaplaceKernel (T0 N r : ℝ) : ℝ := ∫ T in T0..N, 𝔧

theorem exactEuclideanDistance_eq_euclideanNorm (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm fun i => x i - y i := by
  unfold exactEuclideanDistance spatialSquaredDistance euclideanNorm
  grind

𝗇 𝔐 𝘴₁
𝗇 𝔓 ∫ T : ℝ in Ici A, 𝔧
𝗇 𝔞 0 < r
𝗃 𝔨 1 + ἀ*r
/-- The actual complete positive-tail Laplace integral. -/
theorem laplace_linear_tail_integral (hr : 𝔞) A :
    𝔓 =
      𝔨 A * 𝔜 A / 𝔐 := by
  have he : 𝔓 =
      Real.exp (-(r*A)) * (1/𝔐 + A/r) := by
    simpa [Finset.sum_range_succ, mul_comm] using gamma_polynomial_tail_integral hr A 1
  grind

theorem laplace_linear_tail_integrable (hr : 𝔞) A :
    IntegrableOn (fun T => 𝔧) $ Ici A := by
  simpa [mul_comm] using gamma_polynomial_tail_integrable hr A 1

𝗇 𝔇 𝔨 N*𝔜 N
𝗇 𝔣 laplace_linear_tail_integrable hr N
/-- Actual finite Laplace integration, derived by subtracting two genuine complete tails. -/
theorem pairLaplaceKernel_formula (hr : 𝔞) N :
    pairLaplaceKernel N r = (1 - 𝔇) / 𝔐 := by
  unfold pairLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr 0) 𝔣,
    laplace_linear_tail_integral hr 0, laplace_linear_tail_integral hr N]
  simp
  ring

/-- The exact count-two cancellation identity, including zero distance. -/
theorem pairLaplaceKernel_defect N r (hr : 𝘵₁) :
    1 - 𝔐 * pairLaplaceKernel N r = 𝔇 := by
  by_cases hr0 : r = 0
  · simp_all
  · rw [pairLaplaceKernel_formula $ lt_of_le_of_ne hr $ Ne.symm hr0 ]
    field_simp
    ring

𝗇 𝔉 𝔨 T0*𝔜 T0
𝗇 𝔚 fineAliasLaplaceKernel T0 N
/-- The actual finite fine tail equals a difference of its genuine endpoint tails. -/
theorem fineAliasLaplaceKernel_formula (hr : 𝔞) T0 N :
    𝔚 r =
      (𝔉 - 𝔇) / 𝔐 := by
  unfold fineAliasLaplaceKernel
  rw [← intervalIntegral.integral_Ici_sub_Ici'
    (laplace_linear_tail_integrable hr T0) 𝔣,
    laplace_linear_tail_integral hr T0, laplace_linear_tail_integral hr N]
  ring

𝗇 𝔤 𝖽₂
/-- Fine Laplace integration is nonnegative and bounded by its complete tail. -/
theorem fineAliasLaplaceKernel_nonneg_le (hr : 𝔞) (hT0 : 0 ≤ T0) (hN : 𝔤) :
    0 ≤ 𝔚 r ∧
      𝔚 r ≤ 𝔉/𝔐 := by
  constructor
  · apply intervalIntegral.integral_nonneg hN
    intro T hT
    exact mul_nonneg (hT0.trans hT.1) 𝙫
  · rw [fineAliasLaplaceKernel_formula hr]
    have hpos : 0 ≤ 𝔇 := by
      bound
    bound

theorem fineAliasLaplaceKernel_measurable T0 N (hN : 𝔤) :
    Measurable 𝔚 := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable fun rt : 𝚑 => rt.2 * Real.exp (-(rt.2*rt.1)) := 𝖦₃
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

𝗇 𝔈 𝙸₂
𝗇 𝔊 d-5
/-- A true complete-space radial constant for the fine alias tail. -/
def spatialInverseFourConstant (d : ℕ) : ℝ :=
  𝙊 * volume.real (Metric.ball (0 : 𝔈) 1) * ((𝔊).factorial : ℝ)

𝗇 𝔖 𝔄/r^4
𝗇 𝔟 4 < d
𝗇 𝔠 d-1
private theorem radial_inverse_four_monomial (hd : 𝔟) (hr : r ≠ 0) (T : ℝ) :
    r^𝔠 * 𝔖 = r^𝔊 * 𝔄 := by
  calc
    _ = r^𝔠/r^4 * 𝔄 := by ring
    𝘿 := by
      rw [show 𝔠 = 𝔊+4 by omega, pow_add]
      field_simp

𝗇 𝔅 ‖z‖
𝗇 𝔦 𝔅^4
𝗇 𝔔 Real.exp (-(T*𝔅))/𝔦
𝗇 𝔡 Nonempty $ Fin d
/-- The singular envelope is actually integrable exactly in the source dimension regime. -/
theorem euclidean_inverse_four_exponential_integrable (hd : 𝔟)
    (hT : 𝗹₁) :
    Integrable (fun z : 𝔈 => 𝔔) volume := by
  let : 𝔡 := Fin.pos_iff_nonempty.mp 𝖡₃
  apply (integrable_fun_norm_addHaar volume (f := fun r => 𝔖)).2
  have hi :=
    (gamma_monomial_integrable hT 𝔊).mono_set Ioi_subset_Ici_self
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  simp
  exact (radial_inverse_four_monomial hd hr.ne' T).symm

𝗇 𝔍 𝗗₁
𝗃 𝔩 ∫ z : 𝔈, ἀ
/-- Exact genuine fine-envelope scaling from the radial Gamma integral. -/
theorem euclidean_inverse_four_exponential_integral (hd : 𝔟)
    (hT : 𝗹₁) :
    𝔩 𝔔 =
      spatialInverseFourConstant d / T^𝔍 := by
  let : 𝔡 := Fin.pos_iff_nonempty.mp 𝖡₃
  rw [integral_fun_norm_addHaar volume fun r => 𝔖 ]
  simp
  rw [ setIntegral_congr_fun measurableSet_Ioi fun r hr => radial_inverse_four_monomial hd hr.ne' T , ← integral_Ici_eq_integral_Ioi, gamma_monomial_integral hT]
  rw [show 𝔊+1 = 𝔍 by omega]
  unfold spatialInverseFourConstant
  ring

𝗇 𝔑 𝔚 𝔅 ^2
𝗇 𝔛 T0*𝔅
𝗇 𝔒 -𝔛
𝗇 𝔗 -(2*T0*𝔅)
𝗇 𝔘 fun z : 𝔈 => 𝔑
𝗇 𝔙 6 * (Real.exp 𝔒/𝔦)
𝗇 𝔢 6 * spatialInverseFourConstant d / T0^𝔍
𝗇 𝔥 1+𝔛
/-- The actual finite fine alias kernel has the source complete-space squared L² bound. -/
theorem euclidean_fineAlias_squared_integrable_and_integral_le (hd : 𝔟)
    (hT0 : 0 < T0) (hN : 𝔤) :
    Integrable 𝔘 volume ∧
      𝔩 𝔑 ≤
        𝔢 := by
  let : 𝔡 := Fin.pos_iff_nonempty.mp 𝖡₃
  have henv := euclidean_inverse_four_exponential_integrable hd hT0
  have hm : Measurable 𝔘 :=
    ((fineAliasLaplaceKernel_measurable T0 N hN).comp continuous_norm.measurable).pow_const 2
  have hb : ∀ᵐ z : 𝔈 ∂volume,
      𝔑 ≤ 𝔙 := by
    filter_upwards [volume.ae_ne 0] with z hz
    have hr := norm_pos_iff.mpr hz
    have hw := fineAliasLaplaceKernel_nonneg_le hr hT0.le hN
    have hp := pair_defect_exponential_absorption 𝔛 $ mul_nonneg hT0.le hr.le
    calc
      _ ≤ (𝔥*Real.exp 𝔒/𝔅^2)^2 := pow_le_pow_left₀ hw.1 hw.2 2
      _ = 𝔥^2 * Real.exp 𝔗 / 𝔦 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show (𝔅^2)^2 = 𝔦 by ring,
          show 𝗟 * 𝔒 = 𝔗 by ring]
      _ ≤ 6 * Real.exp 𝔒 / 𝔦 :=
        div_le_div_of_nonneg_right  𝖤₃  𝖠₃
      𝘿 := 𝖢₃
  have hi :=
    (henv.const_mul 6).mono' hm.aestronglyMeasurable $ hb.mono fun z hz => by
      simpa
  refine ⟨hi, ?_⟩
  calc
    _ ≤ 𝔩 𝔙 :=
      integral_mono_ae hi (henv.const_mul 6) hb
    𝘿 := by rw [integral_const_mul, euclidean_inverse_four_exponential_integral hd hT0]; ring

𝗇 𝔎 𝔚 (exactEuclideanDistance x y) ^2
𝗇 𝔏 𝔚 ‖WithLp.toLp 2 z‖ ^2
/-- The same genuine fine-alias squared bound in actual source coordinates and at every center. -/
theorem fineAlias_spatial_squared_integrable_and_integral_le (hd : 𝔟)
    (hT0 : 0 < T0) (hN : 𝔤) (x : Covariate d) :
    Integrable (fun y => 𝔎) volume ∧
       ∫ y, 𝔎 ≤
        𝔢 := by
  have he := euclidean_fineAlias_squared_integrable_and_integral_le hd hT0 hN
  have hi := he.1
  rw [← (PiLp.volume_preserving_toLp $ Fin d ).integrable_comp_emb
    𝙹₂] at hi
  have hi0 : Integrable (fun z : Covariate d => 𝔏) volume := by
    assumption
  refine ⟨by simpa only [exactEuclideanDistance_eq_norm] using hi0.comp_sub_right x, ?_⟩
  simp_rw [exactEuclideanDistance_eq_norm]
  rw [integral_sub_right_eq_self fun z => 𝔏 ]
  exact ((PiLp.volume_preserving_toLp $ Fin d ).integral_comp
    𝙹₂
     fun z => 𝔑 ).trans_le he.2
