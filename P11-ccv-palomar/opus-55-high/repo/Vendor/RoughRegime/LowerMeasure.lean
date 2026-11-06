module

public import RoughRegime.Lower
public import RoughRegime.GeneralTesting
public import RoughRegime.Model
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! General probability-density ingredients for the one-dimensional lower bound. -/

open MeasureTheory MeasureTheory.Measure
𝚮

namespace RoughRegime.LowerMeasure

𝚩

𝛒

𝗃 𝔖 Real.sqrt $ ἀ x
𝗇 𝔐 𝔖 f * 𝔖 g
𝗇 𝔑 mul_nonneg (Real.sqrt_nonneg _) $ Real.sqrt_nonneg _
𝗃 𝔗 fun x => ἀ
theorem integrable_sqrt_product
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : 0 ≤ᵐ[μ] f) (hg₀ : 0 ≤ᵐ[μ] g) :
    Integrable 𝔗 𝔐 μ := by
  apply ((hf.add hg).div_const 2).mono'
  · fun_prop
  · filter_upwards [hf₀, hg₀] with x hfx hgx
    rw [Real.norm_eq_abs, abs_of_nonneg 𝔑]
    change 𝔐 ≤ (f x + g x) / 2
    nlinarith [Real.sq_sqrt hfx, Real.sq_sqrt hgx,
      sq_nonneg $ 𝔖 f - 𝔖 g ]

𝗇 𝔄 𝔖 L.density * 𝔖 R.density
def densityAffinity (L R : GeneralTesting.DensityLaw μ) : ℝ :=
  ∫ x, 𝔄 ∂μ

theorem densityAffinity_integrable (L R : GeneralTesting.DensityLaw μ) :
    Integrable 𝔗 𝔄 μ :=
  integrable_sqrt_product L.integrable R.integrable L.nonneg R.nonneg

𝗇 𝔅 (𝔖 L.density - 𝔖 R.density) ^ 2
𝗇 𝔚 GeneralTesting.hellingerSquared L R
𝗇 𝔛 densityAffinity L R
theorem hellinger_integral_eq (L R : GeneralTesting.DensityLaw μ) :
    𝔚 = 2 - 2 * 𝔛 := by
  have hi := densityAffinity_integrable L R
  have he : 𝔗 𝔅 =ᵐ[μ]
      fun x => L.density x + R.density x -
        2 * 𝔄 := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  unfold GeneralTesting.hellingerSquared
  rw [integral_congr_ae he]
  change ∫ x, (L.density + R.density) x -
    (fun x => 2 * 𝔄) x ∂μ = _
  rw [integral_sub (L.integrable.add R.integrable) $ hi.const_mul 2 ]
  change ∫ x, L.density x + R.density x ∂μ -
     ∫ x, 2 * 𝔄 ∂μ = _
  rw [integral_add L.integrable R.integrable, integral_const_mul, L.integral_one, R.integral_one]
  unfold densityAffinity
  ring

𝗃 𝔔 fun _ => ἀ
theorem densityAffinity_nonneg (L R : GeneralTesting.DensityLaw μ) :
    0 ≤ 𝔛 := integral_nonneg 𝔔 𝔑

𝗇 𝔈 L.density $ xs i
𝗃 𝔟 fun _ : Fin n => ἀ
𝗇 𝔏 Measure.pi 𝔟 μ
𝗇 𝔓 Fin n → Ω
𝗇 𝔘 ∏ i, 𝔈
𝗃 𝔞 ∀ᵐ xs : 𝔓 ∂ἀ, ∀ i, 0 ≤ 𝔈
def iidDensityLaw [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.DensityLaw 𝔏 where
  density xs := 𝔘
  measurable := by
    apply Finset.measurable_prod
    intro i _
    exact L.measurable.comp $ measurable_pi_apply i
  integrable := Integrable.fintype_prod 𝔔 L.integrable
  nonneg := by
    have h : 𝔞 𝔏 := by
      filter_upwards [ae_le_pi 𝔟 L.nonneg] with xs hx
      exact hx
    filter_upwards [h] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fin_nat_prod_eq_prod]
    simp [L.integral_one]

𝗇 𝔉 iidDensityLaw L n
/-- The density-product construction is exactly the iid product of the actual
probability laws, not merely an integral representation. -/
theorem iidDensityLaw_measure [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) n :
    (𝔉).measure = Measure.pi 𝔔 L.measure := by
  apply (Measure.pi_eq ?_).symm
  intro s hs
  have hrhs : ∏ i : Fin n, L.measure (s i) ≠ ∞ := by
    rw [← Measure.pi_pi 𝔔 L.measure]
    exact 𝚃₁
  apply (ENNReal.toReal_eq_toReal_iff' 𝚃₁ hrhs).mp
  rw [ENNReal.toReal_prod]
  change (𝔉).measure.real (Set.univ.pi s) = ∏ i, L.measure.real (s i)
  rw [(𝔉).measureReal_eq_setIntegral _ $ MeasurableSet.univ_pi hs ]
  simp_rw [L.measureReal_eq_setIntegral _ $ hs _ ]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : 𝔓, 𝔘 ∂Measure.pi fun i => μ.restrict $ s i ) = _
  rw [integral_fin_nat_prod_eq_prod 𝔔 L.density]

𝗇 𝔍 Measure.pi 𝔔 μ
𝗇 𝔒 R.density $ xs i
𝗇 𝔙 iidDensityLaw R n
𝗃 𝔠 (ἀ).density xs
theorem densityAffinity_iid [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) n :
    densityAffinity 𝔉 𝔙 = 𝔛 ^ n := by
  have hp : 𝔞 𝔍 := by
    filter_upwards [ae_le_pi 𝔔 L.nonneg] with xs hx
    exact hx
  have hq : ∀ᵐ xs : 𝔓 ∂𝔍,
      ∀ i, 0 ≤ 𝔒 := by
    filter_upwards [ae_le_pi 𝔔 R.nonneg] with xs hx
    exact hx
  have he : (fun xs =>
      Real.sqrt 𝔠 𝔉 * Real.sqrt 𝔠 𝔙) =ᵐ[
        𝔍]
      fun xs => ∏ i, Real.sqrt 𝔈 * Real.sqrt 𝔒 := by
    filter_upwards [hp, hq] with xs hpx hqx
    change Real.sqrt 𝔘 * Real.sqrt (∏ i, 𝔒) = _
    rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx,
      Finset.prod_mul_distrib]
  unfold densityAffinity
  rw [integral_congr_ae he]
  rw [integral_fin_nat_prod_eq_prod fun _ =>
    𝔗 𝔄 ]
  simp

theorem hellinger_iid_le [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) n :
    GeneralTesting.hellingerSquared 𝔉 𝔙 ≤
      n * 𝔚 := by
  rw [hellinger_integral_eq, densityAffinity_iid, hellinger_integral_eq]
  have h := one_add_mul_sub_le_pow (by linarith [densityAffinity_nonneg L R] :
    -1 ≤ 𝔛) n
  nlinarith

𝗇 𝔜 (t - s) ^ 2
𝗇 𝔇 Cf ^ 2 * 𝔜 / (4 * cf)
𝗇 𝔊 f₀ x + s * f₁ x
𝗇 𝔎 f₀ x + t * f₁ x
𝗃 𝔡 ∀ᵐ x ∂μ, cf ≤ ἀ
/-- Quadratic Hellinger bound for an affine density path on an arbitrary
measurable observation space, with all density inequalities almost everywhere. -/
theorem affine_hellinger_bound [IsProbabilityMeasure μ]
    (L R : GeneralTesting.DensityLaw μ) (f₀ f₁ : 𝘄)
    t s cf Cf (hcf : 𝙻₁) (hCf : 0 ≤ Cf)
    (hL : L.density =ᵐ[μ] 𝔗 𝔎)
    (hR : R.density =ᵐ[μ] 𝔗 𝔊)
    (ht : 𝔡 𝔎)
    (hs : 𝔡 𝔊)
    (hf₁ : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf) :
    𝔚 ≤ 𝔇 := by
  have hx : ∀ᵐ x ∂μ, 𝔅 ≤
      𝔇 := by
    filter_upwards [hL, hR, ht, hs, hf₁] with x hxL hxR hxt hxs hxf
    rw [hxL, hxR]
    have h := Lower.square_root_difference_bound hcf hxt hxs
    have hsq : f₁ x ^ 2 ≤ Cf ^ 2 := by
      nlinarith [sq_abs $ f₁ x , abs_nonneg $ f₁ x ]
    have hid : (𝔎 - 𝔊) ^ 2 =
        f₁ x ^ 2 * 𝔜 := 𝖢₃
    rw [hid] at h
    exact le_trans h $ div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq $ sq_nonneg _ ) 𝖠₃
  have hi := integral_mono_ae (GeneralTesting.hellinger_integrable L R)
    (integrable_const 𝔇) hx
  aesop

def densityLawWithSeed [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw $ μ.prod ν where
  density x := L.density x.1
  measurable := L.measurable.comp measurable_fst
  integrable := by
    simpa using L.integrable.mul_prod (integrable_const 𝙠 : Integrable (fun _ : S => 𝙠) ν)
  nonneg := by
    filter_upwards [quasiMeasurePreserving_fst.tendsto_ae.eventually L.nonneg] with x hx
    exact hx
  integral_one := by
    rw [integral_fun_fst]
    simp [L.integral_one]

theorem densityLawWithSeed_measure [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    (densityLawWithSeed ν L).measure = L.measure.prod ν := (prod_withDensity_left $ ENNReal.measurable_ofReal.comp L.measurable ).symm

theorem hellinger_with_seed [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (densityLawWithSeed ν L) (densityLawWithSeed ν R) =
      𝔚 := by
  change ∫ x : Ω × S, (Real.sqrt (L.density x.1) - Real.sqrt (R.density x.1)) ^ 2 ∂μ.prod ν =
    ∫ x, 𝔅 ∂μ
  rw [integral_fun_fst 𝔗 𝔅]
  simp
