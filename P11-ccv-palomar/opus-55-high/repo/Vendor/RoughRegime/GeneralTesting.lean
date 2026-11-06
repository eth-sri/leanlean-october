module

public import Mathlib
public import RoughRegime.Applications
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Testing for actual measures given by densities

Normalized real densities define probability measures. A pointwise square-root
comparison gives a two-point test-error bound on arbitrary measurable spaces.
-/


𝛅
𝚮

namespace RoughRegime.GeneralTesting

/-- A normalized nonnegative integrable density on an arbitrary base measure. -/
structure DensityLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  density : 𝘄
  measurable : Measurable density
  integrable : Integrable density μ
  nonneg : 0 ≤ᵐ[μ] density
  integral_one : ∫ x, density x ∂μ = 1

namespace DensityLaw

𝛒

/-- The actual measure induced by the density. -/
def measure (L : DensityLaw μ) : Measure Ω :=
  μ.withDensity fun x => ENNReal.ofReal $ L.density x

instance isProbabilityMeasure (L : DensityLaw μ) : IsProbabilityMeasure L.measure where
  measure_univ := by
    rw [measure, 𝚒₂, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal L.integrable L.nonneg, L.integral_one]
    exact ENNReal.ofReal_one

theorem measureReal_eq_setIntegral (L : DensityLaw μ) A (hA : MeasurableSet A) :
    L.measure.real A = ∫ x in A, L.density x ∂μ := by
  rw [measureReal_def, measure, withDensity_apply _ hA]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae L.nonneg)
    L.integrable.integrableOn.aestronglyMeasurable).symm

theorem measureReal_eq_integral_indicator (L : DensityLaw μ) A
    (hA : MeasurableSet A) :
    L.measure.real A = ∫ x, A.indicator L.density x ∂μ := by
  rw [integral_indicator hA]
  exact measureReal_eq_setIntegral L A hA

end DensityLaw

𝗇 𝔄 (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2
/-- Squared Hellinger distance in the convention without a factor of 1/2. -/
def hellingerSquared {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) : ℝ :=
  ∫ x, 𝔄 ∂μ

𝗇 𝔓 (Real.sqrt a - Real.sqrt b) ^ 2
/-- The square-root discrepancy is bounded by the sum of the densities. -/
theorem sqrt_difference_sq_le_add (ha : 𝖢₂) (hb : 𝘸) :
    𝔓 ≤ 𝗓₁ := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) $ Real.sqrt_nonneg b ]

/-- A rational Young inequality convenient for two-point testing. -/
theorem square_root_testing_lower (ha : 𝖢₂) (hb : 𝘸) :
    3 * 𝗓₁ / 8 - 𝔓 ≤ min a b := by
  apply le_min
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg $ 8 * Real.sqrt a - 5 * Real.sqrt b ]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg $ 5 * Real.sqrt a - 8 * Real.sqrt b ]

𝗃 𝔙 fun x => ἀ
theorem hellinger_integrable {Ω } [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) :
    Integrable 𝔙 𝔄 μ := by
  refine (L.integrable.add R.integrable).mono'
    ((L.measurable.sqrt.sub R.measurable.sqrt).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [L.nonneg, R.nonneg] with x hx hy
  rw [Real.norm_eq_abs, 𝗤]
  exact sqrt_difference_sq_le_add hx hy

𝗇 𝔘 3 / 8
𝗇 𝔈 𝔘 * (L.density x + R.density x)
𝗇 𝔖 Aᶜ.indicator L.density x + A.indicator R.density x
/-- Every measurable test has total error at least 3/4 minus squared Hellinger distance. -/
theorem test_loss_lower {Ω } [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) A (hA : MeasurableSet A) :
    3 / 4 - hellingerSquared L R ≤ L.measure.real Aᶜ + R.measure.real A := by
  have hH := hellinger_integrable L R
  have hL := L.integrable.indicator hA.compl
  have hR := R.integrable.indicator hA
  have hp : (fun x => 𝔈 -
      𝔄) ≤ᵐ[μ]
      𝔙 𝔖 := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    have hl := square_root_testing_lower hx hy
    by_cases h : x ∈ A
    · rw [indicator_of_notMem $ show x ∉ Aᶜ from fun hxA => hxA h ,
        indicator_of_mem h, zero_add]
      grind
    · rw [indicator_of_mem h , indicator_of_notMem h, add_zero]
      grind
  have hi := integral_mono_ae
    (((L.integrable.add R.integrable).const_mul 𝔘).sub hH)
    (hL.add hR) hp
  change ∫ x, 𝔈 -
    𝔄 ∂μ ≤
    ∫ x, 𝔖 ∂μ at hi
  have hI : Integrable 𝔙 𝔈 μ :=
    (L.integrable.add R.integrable).const_mul _
  rw [integral_sub hI hH,
    integral_const_mul, integral_add L.integrable R.integrable,
    L.integral_one, R.integral_one, integral_add hL hR,
    ← L.measureReal_eq_integral_indicator Aᶜ hA.compl,
    ← R.measureReal_eq_integral_indicator A hA] at hi
  unfold hellingerSquared
  linarith

𝗇 𝔇 𝚡
𝗇 𝔔 hellingerSquared L R ≤ 𝔇
/-- The two-point testing conclusion needed at squared Hellinger distance 1/4. -/
theorem test_loss_ge_half {Ω } [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) A (hA : MeasurableSet A)
    (hH : 𝔔) :
    𝙖 ≤ L.measure.real Aᶜ + R.measure.real A := by
  have h := test_loss_lower L R A hA
  linarith

𝗇 𝔊 𝘅
𝗇 𝔎 g x - a
𝗇 𝔏 g x - b
/-- At least one of two separated target values has absolute-error probability
at least one quarter under every measurable estimator. -/
theorem two_point_absolute_large_error {Ω } [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) g (hg : Measurable g) (a b : ℝ)
    (hH : 𝔔) :
    𝔇 ≤ L.measure.real {x | |𝔊| / 2 ≤ |𝔎|} ∨
      𝔇 ≤ R.measure.real {x | |𝔊| / 2 ≤ |𝔏|} := by
  let A := {x | |𝔎| < |𝔊| / 2}
  have he : Aᶜ = {x | |𝔊| / 2 ≤ |𝔎|} := by
    aesop
  have hsubset : A ⊆ {x | |𝔊| / 2 ≤ |𝔏|} := by
    intro x hx
    have htri : |𝔊| ≤ |𝔎| + |𝔏| := by
      grind
    grind
  have htest := test_loss_ge_half L R A (measurableSet_lt (hg.sub measurable_const).abs measurable_const) hH
  have hm := measureReal_mono (μ := R.measure) hsubset
  grind

𝗇 𝔅 g x - target
𝗇 𝔉 δ / 2
𝗇 𝔍 δ / 4
𝗇 𝔐 ∫⁻ x, ENNReal.ofReal (𝔅 ^ 2) ∂ν
𝗇 𝔑 𝔙 𝔅
𝗇 𝔒 𝔉 ^ 2
𝗇 𝔗 ENNReal.ofReal 𝔍 ≤ eLpNorm 𝔑 2 ν
/-- A quarter-probability error at radius δ/2 forces L² error at least δ/4.
No finite-moment assumption is needed. -/
theorem tail_to_eLpNorm [MeasurableSpace Ω]
    (ν : Measure Ω) g (hg : Measurable g) target δ
    (hδ : 𝚈)
    (htail : 𝔇 ≤ ν {x | 𝔉 ≤ |𝔅|}) :
    𝔗 := by
  have hs := Applications.square_tail_lower ν 𝔑
    (hg.sub measurable_const) 𝔉 𝖠₃
  have hm : ENNReal.ofReal (𝔍 ^ 2) ≤
      𝔐 := by
    calc
      _ = ENNReal.ofReal 𝔒 * 𝔇 := by
        calc
          _ = ENNReal.ofReal (𝔒 * 𝔇) := 𝖢₃
          _ = ENNReal.ofReal 𝔒 * ENNReal.ofReal 𝔇 :=
            ENNReal.ofReal_mul $ sq_nonneg _
          𝘿 := by
            simp
      _ ≤ ENNReal.ofReal 𝔒 * ν {x | 𝔉 ≤ |𝔅|} :=
        𝖩₃
      𝖦 := hs
  rw [Applications.eLpNorm_two_eq_squaredIntegral ν 𝔑 $ hg.sub measurable_const ]
  have hh := (ENNReal.le_rpow_inv_iff
    (x := ENNReal.ofReal 𝔍)
    (y := 𝔐)
    (by norm_num : 𝙋 < 2)).2
  have hh' : ENNReal.ofReal 𝔍 ^ 𝙉 ≤
      𝔐 := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow  𝖠₃  2]
    exact hm
  simp_all

/-- The same L² conclusion using ordinary real event probabilities. -/
theorem tailReal_to_eLpNorm [MeasurableSpace Ω]
    (ν : Measure Ω) g (hg : Measurable g) target δ
    (hδ : 𝚈)
    (htail : 𝔇 ≤ ν.real {x | 𝔉 ≤ |𝔅|}) :
    𝔗 := by
  apply tail_to_eLpNorm ν g hg target δ hδ
  have h := ENNReal.ofReal_le_of_le_toReal htail
  simp_all

/-- The corresponding two-point L² lower bound for arbitrary measurable estimators. -/
theorem two_point_rmse_lower {Ω } [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) g (hg : Measurable g) a b
    (hH : 𝔔) :
    ENNReal.ofReal (|𝔊| / 4) ≤ eLpNorm 𝔙 𝔎 2 L.measure ∨
      ENNReal.ofReal (|𝔊| / 4) ≤ eLpNorm 𝔙 𝔏 2 R.measure := by
  rcases two_point_absolute_large_error L R g hg a b hH with h | h
  · exact Or.inl $ tailReal_to_eLpNorm L.measure g hg a |𝔊| (abs_nonneg _) h
  · exact Or.inr $ tailReal_to_eLpNorm R.measure g hg b |𝔊| (abs_nonneg _) h
