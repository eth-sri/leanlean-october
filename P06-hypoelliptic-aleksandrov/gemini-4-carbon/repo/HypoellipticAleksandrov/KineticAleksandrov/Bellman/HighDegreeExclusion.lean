module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTail
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Group.Integral
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Add
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
import Mathlib.Analysis.Calculus.FDeriv.Mul
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- The second angular moment is nonnegative on positive oriented intervals. -/
theorem bellmanAngularSecondMoment_nonneg {f : ℝ → ℝ}
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ bellmanAngularSecondMoment f y := by
  apply intervalIntegral.integral_nonneg_of_ae hy
  filter_upwards [hf] with z hz
  exact mul_nonneg (sq_nonneg z) hz

/-- On the positive half-line the second moment is bounded by y times the first moment. -/
theorem bellmanAngularSecondMoment_le {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : 0 ≤ y) :
    bellmanAngularSecondMoment f y ≤ y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    ← intervalIntegral.integral_const_mul]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume 0 y := by
    simpa using bellmanAngularMoment_intervalIntegrable hi 0 y 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi 0 y 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.2) (mul_nonneg hzy.1 hz)]

/-- The integrated angular identity bounds the positive first moment using nonnegative h. -/
theorem bellmanAngularFirstMoment_bound (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hi : LocallyIntegrable f volume)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    {y : ℝ} (hy : 0 < y) :
    bellmanAngularFirstMoment f y ≤ 3 * (h 0 / y + J 0) := by
  have hp : 0 ≤ (β - 3) / 3 := by linarith
  have hb := mul_le_mul_of_nonneg_left (bellmanAngularSecondMoment_le hi hf hy.le) hp
  have hn := hh y
  rw [he y] at hn
  apply le_of_mul_le_mul_right _ hy
  have heq : (3 * (h 0 / y + J 0)) * y = 3 * (h 0 + J 0 * y) := by
    field_simp [hy.ne']
  rw [heq]
  nlinarith




/-- On the negative side minus the second moment is bounded by minus y times the first moment. -/
theorem bellmanAngularSecondMoment_negative_bound {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : y ≤ 0) :
    -bellmanAngularSecondMoment f y ≤ -y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    intervalIntegral.integral_symm (b := 0),
    intervalIntegral.integral_symm (a := y) (b := 0), neg_neg]
  have he : -y * (-(∫ z in y..0, z * f z)) = ∫ z in y..0, y * (z * f z) := by
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [he]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume y 0 := by
    simpa using bellmanAngularMoment_intervalIntegrable hi y 0 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi y 0 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.1) (mul_nonneg (neg_nonneg.mpr hzy.2) hz)]

/-- The second moment divided by its endpoint is bounded in norm by the first moment. -/
theorem bellmanAngularSecondMoment_div_norm_le {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (y : ℝ) :
    ‖bellmanAngularSecondMoment f y / y‖ ≤ bellmanAngularFirstMoment f y  := by
  have bellmanAngularSecondMoment_nonpos_negative {y : ℝ} (hy : y ≤ 0) :
      bellmanAngularSecondMoment f y ≤ 0 := by
    rw [bellmanAngularSecondMoment, intervalIntegral.integral_symm]
    apply neg_nonpos.mpr
    apply intervalIntegral.integral_nonneg_of_ae hy
    filter_upwards [hf] with z hz
    exact mul_nonneg (sq_nonneg z) hz
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have hm := bellmanAngularSecondMoment_nonpos_negative hy.le
    have hb := bellmanAngularSecondMoment_negative_bound hi hf hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg_of_nonpos hm hy.le)]
    apply (div_le_iff_of_neg hy).mpr
    linarith
  · subst y
    simp only [div_zero, norm_zero, bellmanAngularFirstMoment, intervalIntegral.integral_same]
    exact le_rfl
  · have hm := bellmanAngularSecondMoment_nonneg hf hy.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hm hy.le)]
    exact (div_le_iff₀ hy).mpr (by simpa only [mul_comm] using (bellmanAngularSecondMoment_le hi hf hy.le))


/-- A finite angular tail cannot dominate a positive nonintegrable power on a positive half-
line. -/
theorem bellmanAngularTail_not_power_lower_bound (f : ℝ → ℝ) (β a c p : ℝ)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume)
    (ha : 2 ≤ a) (hc : 0 < c) (hp : -1 ≤ p)
    (hlower : ∀ᵐ y ∂volume.restrict (Ioi a), c * y ^ p ≤ f y * y ^ (β - 4)) : False := by
  have hap : 0 < a := by linarith
  have hi : IntegrableOn (fun y => f y * y ^ (β - 4)) (Ioi a) volume := by
    apply (htail.mono_set (show Ioi a ⊆ {y : ℝ | 2 < |y|} by
      intro y hy; change a < y at hy
      change 2 < |y|
      rw [abs_of_pos (by linarith : 0 < y)]
      linarith)).congr_fun _ measurableSet_Ioi
    intro y hy
    change f y * |y| ^ (β - 4) = f y * y ^ (β - 4)
    rw [abs_of_pos (hap.trans hy)]
  have hpow : IntegrableOn (fun y => c * y ^ p) (Ioi a) volume := by
    apply hi.mono' (by fun_prop)
    filter_upwards [hlower, ae_restrict_mem measurableSet_Ioi] with y hy hya
    have hn : 0 ≤ c * y ^ p := mul_nonneg hc.le (Real.rpow_nonneg (hap.trans hya).le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hy
  have hrpow : IntegrableOn (fun y => y ^ p) (Ioi a) volume := by
    change Integrable (fun y => y ^ p) (volume.restrict (Ioi a))
    convert! (Integrable.const_mul hpow c⁻¹) using 1
    funext y
    field_simp [hc.ne']
  have he := (integrableOn_Ioi_rpow_iff hap).mp hrpow
  linarith


/-- Ellipticity and the finite tail exclude a positive limit of h(y)/y. -/
theorem bellmanAngularTail_no_positive_linear_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h : ℝ → ℝ)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume)
    (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun y => h y / y) atTop (𝓝 L)) : False := by
  have hRp : 0 < R := by linarith
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_nhds (by linarith : L / 2 < L)))
  let b := max 2 a
  have hb : 2 ≤ b := le_max_left _ _
  have hc : 0 < L / (2 * R) := div_pos hL (by positivity)
  apply bellmanAngularTail_not_power_lower_bound f β b (L / (2 * R)) (β - 3)
    htail hb hc (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hcy
  have hyp : 0 < y := by have := (le_max_left 2 a).trans hy.le; linarith
  have hly := (lt_div_iff₀ hyp).mp (ha y ((le_max_right 2 a).trans hy.le))
  have hfy : (L / (2 * R)) * y ≤ f y := by
    have heq : R * ((L / (2 * R)) * y) = L / 2 * y := by field_simp
    rw [← heq] at hly
    exact le_of_mul_le_mul_left (hly.le.trans hcy) hRp
  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ 1 * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (L / (2 * R)) * y ^ (β - 3) =
        ((L / (2 * R)) * y) * y ^ (β - 4) := by rw [mul_assoc, hp]
    _ ≤ _ := (mul_le_mul_of_nonneg_right hfy (Real.rpow_nonneg hyp.le (β - 4)))


/-- A nonnegative angular density bounded below by its value at zero must vanish there. -/
theorem bellmanAngularDensity_zero_at_origin (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h : ℝ → ℝ) (hh : 0 ≤ h 0)
    (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y)
    (hlower : ∀ y : ℝ, 0 < y → h 0 ≤ h y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    h 0 = 0 := by
  by_contra hn
  have hRp : 0 < R := by linarith
  apply bellmanAngularTail_not_power_lower_bound f β 2 (h 0 / R) (β - 4)
    htail le_rfl (div_pos (lt_of_le_of_ne hh (Ne.symm hn)) hRp) (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hc
  have hf := (div_le_iff₀ hRp).mpr (by simpa only [mul_comm] using (hlower y (by have : 2 < y := hy; linarith)).trans hc)
  exact mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg (by have : 2 < y := hy; linarith) _)



/-- Nonnegativity on both sides and the integrated identity force the flux at zero to vanish. -/
theorem bellmanAngularFlux_zero_at_origin (β : ℝ) (f h J : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (hh : ∀ y : ℝ, 0 ≤ h y) (h0 : h 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y) :
    J 0 = 0   := by
  have bellmanAngularFirstMoment_tendsto_zero :
      Tendsto (bellmanAngularFirstMoment f) (𝓝 0) (𝓝 0) := by
    have hi : LocallyIntegrable (fun z => z * f z) volume := by
      simpa using bellman_polynomial_locallyIntegrable f hf 1
    change Tendsto (fun y => ∫ z in 0..y, z * f z) (𝓝 0) (𝓝 0)
    simpa using (bellman_lebesguePrimitive_continuous _ hi).tendsto 0
  have bellmanAngularSecondMoment_div_tendsto_zero :
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm
      (fun y => bellmanAngularSecondMoment_div_norm_le hf hn y)
      (bellmanAngularFirstMoment_tendsto_zero)
  have ht : Tendsto (fun y => J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
      ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y)) (𝓝 0) (𝓝 (J 0)) := by
    simpa using
      (tendsto_const_nhds.sub (bellmanAngularFirstMoment_tendsto_zero.const_mul ((β - 2) / 3))).add
        (bellmanAngularSecondMoment_div_tendsto_zero.const_mul ((β - 3) / 3))
  have heq (y : ℝ) (hy : y ≠ 0) : h y / y =
      J 0 - ((β - 2) / 3) * bellmanAngularFirstMoment f y +
        ((β - 3) / 3) * (bellmanAngularSecondMoment f y / y) := by
    rw [he y, h0]
    field_simp
    ring
  have hp : 0 ≤ J 0 := by
    apply ge_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← heq y hy.ne']
    exact div_nonneg (hh y) hy.le
  have hm : J 0 ≤ 0 := by
    apply le_of_tendsto (ht.mono_left (nhdsWithin_le_nhds (s := Iio 0)))
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [← heq y hy.ne]
    exact div_nonpos_of_nonneg_of_nonpos (hh y) hy.le
  exact le_antisymm hm hp


/-- Two integrations of the actual density and flux give the source angular identity. -/
theorem angular_integrated (R β : ℝ) (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y)) :
    ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y * bellmanAngularFirstMoment f y +
      ((β - 3) / 3) * bellmanAngularSecondMoment f y := by
  exact bellmanAngularDensity_integrated β f h J hd.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2


/-- A nonnegative angular solution of degree at least three has finite positive first moment. -/
theorem bellmanAngularFirstMoment_integrable (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hi : LocallyIntegrable f volume)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y) :
    IntegrableOn (fun z => z * f z) (Ioi 0) volume := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (3 * (h 0 + J 0)) 0
    (b := fun y => y) (l := atTop)
  · intro y
    simpa using (bellmanAngularMoment_intervalIntegrable hi 0 y 1).1
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop 1] with y hy
    have hyp : 0 < y := by linarith
    have hb := bellmanAngularFirstMoment_bound β f h J hβ hi hf hh he hyp
    have hh0 := hh 0
    have hdiv : h 0 / y ≤ h 0 := by
      apply (div_le_iff₀ hyp).mpr
      nlinarith
    have hn : (∫ z in 0..y, ‖z * f z‖) = bellmanAngularFirstMoment f y := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hyp.le]
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hf] with z hz hfz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz.1.le hfz)]
    rw [hn]
    linarith

/-- The first angular moment converges to the full positive first-moment integral. -/
theorem bellmanAngularFirstMoment_tendsto (f : ℝ → ℝ)
    (hi : IntegrableOn (fun z => z * f z) (Ioi 0) volume) :
    Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 (∫ z in Ioi 0, z * f z)) :=
  intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id



/-- A nonnegative integrated angular solution has zero linear growth at positive infinity. -/
theorem bellmanAngularPositiveTail_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h J : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 L) ∧
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) ∧
      J 0 = ((β - 2) / 3) * L ∧ ∀ y : ℝ, 0 < y → h 0 ≤ h y   := by
  have bellmanAngularSecondMoment_div_tendsto (_hf : LocallyIntegrable f volume) (hi : IntegrableOn (fun z => z * f z) (Ioi 0) volume) :
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) := by
    let G := fun y => (Iic y).indicator (fun z => (z / y) * (z * f z))
    have hmeas : ∀ᶠ y : ℝ in atTop,
        AEStronglyMeasurable (G y) (volume.restrict (Ioi 0)) := by
      apply Eventually.of_forall
      intro y
      exact ((measurable_id.div_const y).aestronglyMeasurable.mul
        hi.aestronglyMeasurable).indicator measurableSet_Iic
    have hbound : ∀ᶠ y : ℝ in atTop, ∀ᵐ z ∂volume.restrict (Ioi 0),
        ‖G y z‖ ≤ ‖z * f z‖ := by
      filter_upwards [eventually_ge_atTop 1] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      by_cases hzy : z ≤ y
      · rw [show G y z = (z / y) * (z * f z) from indicator_of_mem (show z ∈ Iic y from hzy) _]
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hz.le (by linarith))]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (div_le_one (by linarith : 0 < y)).mpr hzy
      · rw [show G y z = 0 from indicator_of_notMem (show z ∉ Iic y from hzy) _]
        simpa using norm_nonneg (z * f z)
    have hlim : ∀ᵐ z ∂volume.restrict (Ioi 0),
        Tendsto (fun y => G y z) atTop (𝓝 0) := by
      apply ae_of_all
      intro z
      have he : (fun y => G y z) =ᶠ[atTop] (fun y => (z / y) * (z * f z)) := by
        filter_upwards [eventually_ge_atTop z] with y hy
        exact indicator_of_mem (show z ∈ Iic y from hy) _
      have hr : Tendsto (fun y => z / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ht := hr.mul_const (z * f z)
      simpa using ht.congr' he.symm
    have ht := tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖z * f z‖) hmeas hbound hi.norm hlim
    simp at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with y hy
    dsimp [G]
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      show Iic y ∩ Ioi 0 = Ioc 0 y from
        Set.ext (fun z => by simp; tauto),
      bellmanAngularSecondMoment, intervalIntegral.integral_of_le (by linarith : 0 ≤ y)]
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z _
    ring
  have bellmanAngularFirstMoment_total_nonneg (hf : ∀ᵐ z ∂volume, 0 ≤ f z) :
      0 ≤ ∫ z in Ioi 0, z * f z := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hf] with z hz hfz
    exact mul_nonneg hz.le hfz
  have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
  let L := ∫ z in Ioi 0, z * f z
  have hI := bellmanAngularFirstMoment_tendsto f hi
  have hM := bellmanAngularSecondMoment_div_tendsto hf hi
  have h0 : Tendsto (fun y => h 0 / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hdiv : Tendsto (fun y => h y / y) atTop (𝓝 (J 0 - ((β - 2) / 3) * L)) := by
    have ht := ((h0.add (tendsto_const_nhds (x := J 0))).sub
      (hI.const_mul ((β - 2) / 3))).add (hM.const_mul ((β - 3) / 3))
    simp at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with y hy
    rw [he y]
    field_simp
  have hlower : 0 ≤ J 0 - ((β - 2) / 3) * L := by
    apply ge_of_tendsto hdiv
    filter_upwards [eventually_ge_atTop 0] with y hy
    exact div_nonneg (hh y) hy
  have hz : J 0 - ((β - 2) / 3) * L = 0 := by
    by_contra hne
    have hp := lt_of_le_of_ne hlower (Ne.symm hne)
    exact bellmanAngularTail_no_positive_linear_limit R β hR hβ f h htail hcomp _ hp hdiv
  have hj : J 0 = ((β - 2) / 3) * L := by linarith
  refine ⟨L, (bellmanAngularFirstMoment_total_nonneg hn), hI, hM, hj, ?_⟩
  intro y hy
  have hIy : bellmanAngularFirstMoment f y ≤ L := by
    rw [bellmanAngularFirstMoment, intervalIntegral.integral_of_le hy.le]
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
      exact mul_nonneg hz.le hnz
    · exact Eventually.of_forall (fun z hz => hz.1)
  rw [he y, hj]
  have hc : 0 ≤ (β - 2) / 3 := by linarith
  have hd : 0 ≤ (β - 3) / 3 := by linarith
  have hp := mul_nonneg (mul_nonneg hc hy.le) (sub_nonneg.mpr hIy)
  have hq := mul_nonneg hd (bellmanAngularSecondMoment_nonneg hn hy.le)
  nlinarith


/-- Actual angular densities of degree at least three satisfy the source positive-tail limit. -/
theorem angular_positive_tail_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 L) ∧
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) ∧
      J 0 = ((β - 2) / 3) * L ∧ ∀ y : ℝ, 0 < y → h 0 ≤ h y := by
  exact bellmanAngularPositiveTail_limit R β hR hβ f h J hd.2.2.1 hd.2.2.2.1 (bellmanAngularDensity_nonneg hd.2.2.2.2.1 hd.2.2.2.1 (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1)))
    (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)) he htail


/-- At degree at least three, finite tails force the positive angular density and origin flux
to vanish. -/
theorem angular_positive_vanishes (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    h 0 = 0 ∧ J 0 = 0 ∧ (∀ᵐ y ∂volume.restrict (Ioi 0), f y = 0) ∧
      (∀ y : ℝ, 0 < y → h y = 0) := by
  have hf := hd.2.2.1
  have hn := hd.2.2.2.1
  have hac := hd.2.2.2.2.1
  have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
  have hh := bellmanAngularDensity_nonneg hac hn (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))
  obtain ⟨L, _, hI, _, hj, hlower⟩ :=
    angular_positive_tail_limit R β hR hβ F H f h J hd he htail
  have h0 := bellmanAngularDensity_zero_at_origin R β hR hβ f h (hh 0) hcomp hlower htail
  have hj0 := bellmanAngularFlux_zero_at_origin β f h J hf hn hh h0 he
  have hL0 : L = 0 := by
    have hc : 0 < (β - 2) / 3 := by linarith
    rw [hj0] at hj
    nlinarith
  have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
  have htotal : (∫ z in Ioi 0, z * f z) = 0 := by
    have heq := tendsto_nhds_unique hI (bellmanAngularFirstMoment_tendsto f hi)
    linarith
  have hzn : ∀ᵐ z ∂volume.restrict (Ioi 0), 0 ≤ z * f z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
    exact mul_nonneg hz.le hnz
  have hz := (integral_eq_zero_iff_of_nonneg_ae hzn hi).mp htotal
  have hfzero : ∀ᵐ z ∂volume.restrict (Ioi 0), f z = 0 := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with z hz hpos
    exact (mul_eq_zero.mp hz).resolve_left hpos.ne'
  have hhzero : h =ᵐ[volume.restrict (Ioi 0)] (fun _ => 0) := by
    filter_upwards [hfzero, ae_restrict_of_ae hcomp] with z hz hc
    rw [hz, mul_zero] at hc
    exact le_antisymm hc (hh z)
  exact ⟨h0, hj0, hfzero, fun y hy => (Measure.eqOn_open_of_ae_eq hhzero isOpen_Ioi (bellman_locallyAC_continuous hac).continuousOn continuous_const.continuousOn) hy⟩



/-- The integrated angular identity gives the source negative linear lower bound. -/
theorem bellmanAngularDensity_negative_lower (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hf : LocallyIntegrable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (y : ℝ) (hy : y ≤ 0) :
    (-y / 3) * bellmanAngularFirstMoment f y ≤ h y := by
  have hd : 0 ≤ (β - 3) / 3 := by linarith
  have hm := mul_le_mul_of_nonneg_left (bellmanAngularSecondMoment_negative_bound hf hn hy) hd
  rw [he y, h0, hj0]
  nlinarith


/-- Reflection preserves the two-sided density-tail integrability condition. -/
theorem bellmanAngularTail_reflect (β : ℝ) (f : ℝ → ℝ)
    (ht : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    IntegrableOn (fun y => f (-y) * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume := by
  have hi := ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).mpr ht
  have he : (fun y => -y) ⁻¹' {y : ℝ | 2 < |y|} = {y : ℝ | 2 < |y|} := by
    ext y
    simp
  rw [he] at hi
  apply hi.congr_fun _ (by measurability)
  intro y _
  change f (-y) * |-y| ^ (β - 4) = f (-y) * |y| ^ (β - 4)
  rw [abs_neg]



/-- Finite tails force every negative first moment to vanish once the value and flux at zero
vanish. -/
theorem bellmanAngularFirstMoment_negative_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h J : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∀ a : ℝ, a < 0 → bellmanAngularFirstMoment f a = 0    := by
  intro a ha
  have bellmanAngularFirstMoment_nonneg_negative {y : ℝ} (hy : y ≤ 0) :
      0 ≤ bellmanAngularFirstMoment f y := by
    rw [bellmanAngularFirstMoment, intervalIntegral.integral_of_ge hy]
    apply neg_nonneg.mpr
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with z hz hfz
    exact mul_nonpos_of_nonpos_of_nonneg hz.2 hfz
  have bellmanAngularComparison_reflect (R : ℝ) (hc : ∀ᵐ y ∂volume, h y ≤ R * f y) : ∀ᵐ y ∂volume, h (-y) ≤ R * f (-y) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hc
  have bellmanAngularFirstMoment_negative_mono (y : ℝ) (hya : y ≤ a) (ha : a ≤ 0) :
      bellmanAngularFirstMoment f a ≤ bellmanAngularFirstMoment f y := by
    have hi (u v : ℝ) : IntervalIntegrable (fun z => z * f z) volume u v := by
      simpa using bellmanAngularMoment_intervalIntegrable hf u v 1
    have he := intervalIntegral.integral_add_adjacent_intervals (hi y a) (hi a 0)
    have hnon : (∫ z in y..a, z * f z) ≤ 0 := by
      rw [intervalIntegral.integral_of_le hya]
      apply integral_nonpos_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with z hz hfz
      exact mul_nonpos_of_nonpos_of_nonneg (hz.2.trans ha) hfz
    rw [bellmanAngularFirstMoment, bellmanAngularFirstMoment,
      intervalIntegral.integral_symm (a := a) (b := 0),
      intervalIntegral.integral_symm (a := y) (b := 0)]
    linarith
  have hnI := bellmanAngularFirstMoment_nonneg_negative ha.le
  by_contra hne
  have hIp := lt_of_le_of_ne hnI (Ne.symm hne)
  have hRp : 0 < R := by linarith
  let b := max 2 (-a)
  have hb : 2 ≤ b := le_max_left _ _
  have hc : 0 < bellmanAngularFirstMoment f a / (3 * R) := div_pos hIp (by positivity)
  apply bellmanAngularTail_not_power_lower_bound (fun y => f (-y)) β b
    (bellmanAngularFirstMoment f a / (3 * R)) (β - 3)
    (bellmanAngularTail_reflect β f htail) hb hc (by linarith)
  have href := bellmanAngularComparison_reflect R hcomp
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae href] with y hy hcy
  have hyp : 0 < y := by have : 2 < y := hb.trans_lt hy; linarith
  have hya : -y ≤ a := by have := (le_max_right 2 (-a)).trans hy.le; linarith
  have hm := bellmanAngularFirstMoment_negative_mono (-y) hya ha.le
  have hl := bellmanAngularDensity_negative_lower β f h J hβ hf hn h0 hj0 he (-y)
    (by linarith)
  have hfy : (bellmanAngularFirstMoment f a / (3 * R)) * y ≤ f (-y) := by
    have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ y / 3)
    simp at hl
    have hl' : (y / 3) * bellmanAngularFirstMoment f a ≤ h (-y) := by
      simpa using hm'.trans hl
    apply le_of_mul_le_mul_left (a := R) _ hRp
    have heq : R * ((bellmanAngularFirstMoment f a / (3 * R)) * y) =
        (y / 3) * bellmanAngularFirstMoment f a := by field_simp
    rw [heq]
    exact hl'.trans hcy
  have hm := mul_le_mul_of_nonneg_right hfy (Real.rpow_nonneg hyp.le (β - 4))
  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ 1 * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (bellmanAngularFirstMoment f a / (3 * R)) * y ^ (β - 3) =
        ((bellmanAngularFirstMoment f a / (3 * R)) * y) * y ^ (β - 4) := by
      rw [mul_assoc, hp]
    _ ≤ _ := hm



/-- At degree at least three every angular pair with actual densities and finite tails
vanishes. -/
theorem bellmanAngularMeasures_eq_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y))
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    F = 0 ∧ H = 0  := by
  have bellmanAngularDensity_negative_zero (hf : LocallyIntegrable f volume) (hz : ∀ y : ℝ, y < 0 → bellmanAngularFirstMoment f y = 0) :
      ∀ᵐ y ∂volume.restrict (Iio 0), f y = 0 := by
    have hi : LocallyIntegrable (fun z => z * f z) volume := by
      simpa using bellman_polynomial_locallyIntegrable f hf 1
    have hd := _root_.LocallyIntegrable.ae_hasDerivAt_integral hi
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Iio] with y hdy hy
    have he : bellmanAngularFirstMoment f =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hy] with z hz'
      exact hz z hz'
    have heder := he.deriv_eq
    rw [deriv_const] at heder
    have hder : deriv (bellmanAngularFirstMoment f) y = y * f y := (hdy 0).deriv
    rw [hder] at heder
    exact (mul_eq_zero.mp heder).resolve_left hy.ne
  obtain ⟨h0, hj0, hpos, _⟩ := angular_positive_vanishes R β hR hβ F H f h J hd he htail
  have hf := hd.2.2.1
  have hn := hd.2.2.2.1
  have hcomp := hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.2)
  have hIneg := bellmanAngularFirstMoment_negative_zero R β hR hβ f h J hf hn
    hcomp h0 hj0 he htail
  have hneg := bellmanAngularDensity_negative_zero hf hIneg
  have hfn : ∀ᵐ y ∂volume, f y = 0 := by
    have hp := (ae_restrict_iff' measurableSet_Ioi).mp hpos
    have hm := (ae_restrict_iff' measurableSet_Iio).mp hneg
    have hne : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := Measure.ae_ne volume 0
    filter_upwards [hp, hm, hne] with y hypos hyneg hyne
    rcases lt_or_gt_of_ne hyne with hy | hy
    · exact hyneg hy
    · exact hypos hy
  have hh := bellmanAngularDensity_nonneg hd.2.2.2.2.1 hn
    (hd.2.2.2.2.2.2.1.mono (fun _ hx => hx.1))
  have hhn : ∀ᵐ y ∂volume, h y = 0 := by
    filter_upwards [hfn, hcomp] with y hy hc
    rw [hy, mul_zero] at hc
    exact le_antisymm hc (hh y)
  constructor
  · rw [hd.1]
    calc
      _ = volume.withDensity (fun _ => 0) := by
        apply withDensity_congr_ae
        filter_upwards [hfn] with y hy
        rw [hy, ENNReal.ofReal_zero]
      _ = 0 := withDensity_zero
  · rw [hd.2.1]
    calc
      _ = volume.withDensity (fun _ => 0) := by
        apply withDensity_congr_ae
        filter_upwards [hhn] with y hy
        rw [hy, ENNReal.ofReal_zero]
      _ = 0 := withDensity_zero

/-- A homogeneous stationary pair of degree at least three has no mass on positive position. -/
theorem bellmanAdjointPair_positive_position_zero (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    μ {q | 0 < q.val.1} = 0 ∧ η {q | 0 < q.val.1} = 0 := by
  obtain ⟨F, H, f, h, J, hrep, hd, ht⟩ := exists_angular_densities_tail R β hR hβ μ η hp
  have he := angular_integrated R β F H f h J hd
  obtain ⟨hF, hH⟩ := bellmanAngularMeasures_eq_zero R β hR hβ F H f h J hd he ht
  have hμ : μ.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.1, hF, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  have hη : η.restrict {q | 0 < q.val.1} = 0 := by
    rw [hrep.2, hH, bellmanAngularRep, Measure.prod_zero, Measure.map_zero]
  constructor
  · simpa using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hμ
  · simpa using
      congrArg (fun ν : Measure BellmanPuncturedPlane => ν univ) hη


/-- Simultaneous reflection of position and velocity on the punctured plane. -/
def bellmanReflection : BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane where
  toFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  invFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  left_inv q := by apply Subtype.ext; exact neg_neg _
  right_inv q := by apply Subtype.ext; exact neg_neg _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Reflection commutes with every positive kinetic dilation. -/
theorem bellmanReflection_dilation (r : ℝ) (hr : 0 < r) (q : BellmanPuncturedPlane) :
    bellmanReflection (bellmanDilation r hr q) =
      bellmanDilation r hr (bellmanReflection q) := by
  apply Subtype.ext
  apply Prod.ext
  · change -(r ^ 3 * q.val.1) = r ^ 3 * (-q.val.1)
    ring
  · change -(r * q.val.2) = r * (-q.val.2)
    ring

/-- The first reflected test jet changes sign. -/
theorem bellman_reflected_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (q e : ℝ × ℝ) :
    fderiv ℝ (fun z => φ (-z)) q e = -fderiv ℝ φ (-q) e := by
  have hd := (hφ.differentiable (by simp) (-q)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).neg)
  change fderiv ℝ (φ ∘ Neg.neg) q e = _
  rw [hd.fderiv]
  change fderiv ℝ φ (-q) (-e) = -fderiv ℝ φ (-q) e
  exact map_neg _ _

/-- The second velocity jet of a reflected test retains its sign. -/
theorem bellman_reflected_second_velocity (φ : ℝ × ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) q (0, 1) =
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (-q) (0, 1) := by
  have hjet := bellman_contDiff_direction hφ (0, 1)
  have he : (fun z => fderiv ℝ (fun w => φ (-w)) z (0, 1)) =
      (fun z => -(fderiv ℝ φ (-z) (0, 1))) := by
    funext z
    exact bellman_reflected_fderiv φ hφ z (0, 1)
  let g := fun z => fderiv ℝ φ z (0, 1)
  have hd := ((hjet.differentiable (by simp) (-q)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).neg)).neg
  rw [he]
  change fderiv ℝ (-(g ∘ Neg.neg)) q (0, 1) = _
  rw [hd.fderiv]
  change -(fderiv ℝ g (-q) (-(0, 1))) = fderiv ℝ g (-q) (0, 1)
  rw [map_neg, neg_neg]


/-- The pushforward homogeneity formula implies the source measurable-set density degree. -/
theorem bellman_densityDegree_of_map_dilation (β : ℝ) (μ : Measure BellmanPuncturedPlane)
    (hm : ∀ r : ℝ, ∀ hr : 0 < r, Measure.map (bellmanDilation r hr) μ =
      ENNReal.ofReal (r ^ (β - 4)) • μ) : HasBellmanDensityDegree β μ := by
  intro r hr E hE
  let D := bellmanDilationHomeomorph r hr
  have hi : MeasurableSet (D '' E) := D.measurableEmbedding.measurableSet_image.mpr hE
  have he := congrArg (fun ν : Measure BellmanPuncturedPlane => ν (D '' E)) (hm r hr)
  change (Measure.map D μ) (D '' E) = _ at he
  rw [Measure.map_apply D.measurable hi, D.injective.preimage_image,
    Measure.smul_apply, smul_eq_mul] at he
  have hc := bellmanRadial_degreeFactors_cancel β r hr
  calc
    μ (bellmanDilation r hr '' E) =
        (ENNReal.ofReal (r ^ (4 - β)) * ENNReal.ofReal (r ^ (β - 4))) * μ (D '' E) := by
      rw [mul_comm (ENNReal.ofReal (r ^ (4 - β))), hc, one_mul]
      rfl
    _ = ENNReal.ofReal (r ^ (4 - β)) * μ E := by rw [mul_assoc, ← he]

/-- Simultaneous reflection preserves every source density degree. -/
theorem HasBellmanDensityDegree.reflect {β : ℝ} {μ : Measure BellmanPuncturedPlane}
    (hμ : HasBellmanDensityDegree β μ) :
    HasBellmanDensityDegree β (Measure.map bellmanReflection μ) := by
  apply bellman_densityDegree_of_map_dilation
  intro r hr
  have he : bellmanDilation r hr ∘ bellmanReflection =
      bellmanReflection ∘ bellmanDilation r hr := by
    funext q
    exact (bellmanReflection_dilation r hr q).symm
  rw [Measure.map_map (measurable_bellmanDilation r hr) bellmanReflection.measurable,
    he, ← Measure.map_map bellmanReflection.measurable (measurable_bellmanDilation r hr),
    hμ.map_dilation r hr, Measure.map_smul _ bellmanReflection.measurable.aemeasurable]

/-- Simultaneous reflection preserves the positive Radon property on the punctured plane. -/
theorem IsBellmanRadon.reflect {μ : Measure BellmanPuncturedPlane} (hμ : IsBellmanRadon μ) :
    IsBellmanRadon (Measure.map bellmanReflection μ) := by
  let : IsFiniteMeasureOnCompacts μ := hμ.1
  let : Measure.InnerRegular μ := hμ.2
  exact ⟨bellman_map_homeomorph_finiteOnCompacts bellmanReflection μ,
    Measure.InnerRegular.map bellmanReflection⟩


/-- Simultaneous position–velocity reflection preserves the stationary adjoint equation. -/
theorem IsBellmanStationaryAdjointPair.reflect {μ η : Measure BellmanPuncturedPlane}
    (hpair : IsBellmanStationaryAdjointPair μ η) :
    IsBellmanStationaryAdjointPair (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  intro φ hφ hc hs
  let ψ := fun q => φ (-q)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp contDiff_neg
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.neg (ℝ × ℝ))
  have hsψ : tsupport ψ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
    intro q hq hzero
    have hn := hs ((tsupport_comp_subset_preimage φ continuous_neg) hq)
    apply hn
    rw [hzero]
    simp
  have he := hpair ψ hψ hcψ hsψ
  rw [bellmanReflection.measurableEmbedding.integral_map,
    bellmanReflection.measurableEmbedding.integral_map]
  have htransport : (fun q =>
      (bellmanReflection q).val.2 * fderiv ℝ φ (bellmanReflection q).val (1, 0)) =
      (fun q => q.val.2 * fderiv ℝ ψ q.val (1, 0)) := by
    funext q
    change (-q.val.2) * fderiv ℝ φ (-q.val) (1, 0) =
      q.val.2 * fderiv ℝ (fun z => φ (-z)) q.val (1, 0)
    rw [bellman_reflected_fderiv φ hφ]
    ring
  have hvv : (fun q =>
      fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) (bellmanReflection q).val (0, 1)) =
      (fun q => fderiv ℝ (fun z => fderiv ℝ ψ z (0, 1)) q.val (0, 1)) := by
    funext q
    exact (bellman_reflected_second_velocity φ hφ q.val).symm
  rw [htransport, hvv]
  exact he

/-- Reflection preserves the complete genuine homogeneous adjoint-pair condition. -/
theorem IsBellmanAdjointPair.reflect {R β : ℝ} {μ η : Measure BellmanPuncturedPlane}
    (hp : IsBellmanAdjointPair 1 R β μ η) :
    IsBellmanAdjointPair 1 R β (Measure.map bellmanReflection μ)
      (Measure.map bellmanReflection η) := by
  refine ⟨hp.1.reflect, hp.2.1.reflect, Or.inl ?_, ?_, ?_, hp.2.2.2.2.2.1.reflect,
    hp.2.2.2.2.2.2.1.reflect, hp.2.2.2.2.2.2.2.reflect⟩
  · intro he
    apply hp.left_ne_zero
    apply bellmanReflection.measurableEmbedding.map_injective
    simpa using he
  · have he := Measure.map_mono hp.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he
  · have he := Measure.map_mono hp.2.2.2.2.1 bellmanReflection.measurable
    rwa [Measure.map_smul _ bellmanReflection.measurable.aemeasurable] at he


/-- Multiplication by position has the literal product-rule jet. -/
theorem bellman_position_mul_fderiv (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q e : ℝ × ℝ) :
    fderiv ℝ (fun z => z.1 * g z) q e = q.1 * fderiv ℝ g q e + e.1 * g q := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul
    (hg.differentiable (by simp) q).hasFDerivAt
  change HasFDerivAt (fun z => z.1 * g z) _ q at hd
  rw [hd.fderiv]
  change q.1 * fderiv ℝ g q e + e.1 * g q = _
  rfl

/-- The second velocity jet retains the normal position factor. -/
theorem bellman_position_mul_second_velocity (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1)) q (0, 1) =
      q.1 * fderiv ℝ (fun z => fderiv ℝ g z (0, 1)) q (0, 1) := by
  have he : (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1)) =
      (fun z => z.1 * fderiv ℝ g z (0, 1)) := by
    funext z
    rw [bellman_position_mul_fderiv g hg z (0, 1)]
    simp
  rw [he, bellman_position_mul_fderiv _ (bellman_contDiff_direction hg (0, 1))]
  simp


/-- Every degree of a genuine normalized stationary homogeneous Radon pair is below three. -/
theorem admissible_degree_lt_three (R : ℝ) (hR : 1 ≤ R) (β : ℝ)
    (hβ : β ∈ bellmanAdmissibleDegrees R) : β < 3   := by
  have stationary_axis_pair_eq_zero (_hR : 1 ≤ R) (μ η : Measure BellmanPuncturedPlane) (hμ : IsBellmanRadon μ) (_hη : IsBellmanRadon η) (_hlo : μ ≤ η) (hhi : η ≤ ENNReal.ofReal R • μ) (heq : IsBellmanStationaryAdjointPair μ η) (haxis : μ {q | q.val.1 ≠ 0} = 0) :
      μ = 0 ∧ η = 0 := by
    have bellman_axis_velocity_test_zero (μ η : Measure BellmanPuncturedPlane) (hstationary : IsBellmanStationaryAdjointPair μ η) (haxisμ : μ {q | q.val.1 ≠ 0} = 0) (haxisη : η {q | q.val.1 ≠ 0} = 0) (χ : ℝ × ℝ → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)}) :
        (∫ q : BellmanPuncturedPlane, q.val.2 ^ 2 * χ q.val ∂μ) = 0 := by
      let g := fun q => q.2 * χ q
      let φ := fun q => q.1 * g q
      have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_snd.mul hχ
      have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_fst.mul hg
      have hcφ : HasCompactSupport φ := (hc.mul_left).mul_left
      have hsφ : tsupport φ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} :=
        tsupport_mul_subset_right.trans (tsupport_mul_subset_right.trans hs)
      have he := hstationary φ hφ hcφ hsφ
      have haμ : ∀ᵐ q ∂μ, q.val.1 = 0 := by simpa only [ae_iff] using haxisμ
      have haη : ∀ᵐ q ∂η, q.val.1 = 0 := by simpa only [ae_iff] using haxisη
      have h1 : (∫ q : BellmanPuncturedPlane,
          q.val.2 * fderiv ℝ φ q.val (1, 0) ∂μ) =
          ∫ q : BellmanPuncturedPlane, q.val.2 ^ 2 * χ q.val ∂μ := by
        apply integral_congr_ae
        filter_upwards [haμ] with q hq
        change q.val.2 * fderiv ℝ (fun z => z.1 * g z) q.val (1, 0) = _
        rw [bellman_position_mul_fderiv g hg, hq]
        dsimp [g]
        ring
      have h2 : (∫ q : BellmanPuncturedPlane,
          fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q.val (0, 1) ∂η) = 0 := by
        calc
          _ = ∫ _q : BellmanPuncturedPlane, 0 ∂η := by
            apply integral_congr_ae
            filter_upwards [haη] with q hq
            change fderiv ℝ (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1))
              q.val (0, 1) = 0
            rw [bellman_position_mul_second_velocity g hg, hq, zero_mul]
          _ = 0 := integral_zero _ _
      rw [h1, h2, add_zero] at he
      exact he
    have bellman_axis_support_comparison (μ η : Measure BellmanPuncturedPlane) (hhi : η ≤ ENNReal.ofReal R • μ) (haxis : μ {q | q.val.1 ≠ 0} = 0) :
        η {q | q.val.1 ≠ 0} = 0 := by
      have he := hhi {q | q.val.1 ≠ 0}
      rw [Measure.smul_apply, smul_eq_mul, haxis, mul_zero] at he
      exact le_antisymm he bot_le
    let : IsFiniteMeasureOnCompacts μ := hμ.1
    let : Measure.InnerRegular μ := hμ.2
    have hηaxis := bellman_axis_support_comparison μ η hhi haxis
    have hzero : μ = 0 := by
      apply Measure.support_eq_empty_iff.mp
      rw [eq_empty_iff_forall_notMem]
      intro q
      by_cases hqx : q.val.1 = 0
      · have hqv : q.val.2 ≠ 0 := by
          intro hv
          apply q.property
          exact Prod.ext hqx hv
        have ho : IsOpen {p : ℝ × ℝ | p ≠ (0, 0)} := isClosed_singleton.isOpen_compl
        obtain ⟨χ, hsχ, hcχ, hχ, hrχ, hχq⟩ :=
          exists_contDiff_tsupport_subset (n := ⊤) (ho.mem_nhds q.property)
        let w := fun p => p.2 ^ 2 * χ p
        have hw : Continuous w := (continuous_snd.pow 2).mul hχ.continuous
        have hcw : HasCompactSupport w := hcχ.mul_left
        have hsw : tsupport w ⊆ {p : ℝ × ℝ | p ≠ (0, 0)} :=
          tsupport_mul_subset_right.trans hsχ
        have hcwP : HasCompactSupport (fun p : BellmanPuncturedPlane => w p.val) :=
          bellman_test_compact_subtype hcw hsw
        have hi : Integrable (fun p => w p.val) μ :=
          (hw.comp continuous_subtype_val).integrable_of_hasCompactSupport hcwP
        have hn : ∀ᵐ p : BellmanPuncturedPlane ∂μ, 0 ≤ w p.val := by
          apply ae_of_all
          intro p
          exact mul_nonneg (sq_nonneg p.val.2) (hrχ ⟨p.val, rfl⟩).1
        have hz : (∫ p : BellmanPuncturedPlane, w p.val ∂μ) = 0 :=
          bellman_axis_velocity_test_zero μ η heq haxis hηaxis χ hχ hcχ hsχ
        have ha := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
        let U : Set BellmanPuncturedPlane := {p | w p.val ≠ 0}
        have hU : IsOpen U := isOpen_ne_fun (hw.comp continuous_subtype_val) continuous_const
        have hqU : q ∈ U := by
          change q.val.2 ^ 2 * χ q.val ≠ 0
          rw [hχq, mul_one]
          exact pow_ne_zero 2 hqv
        have hμU : μ U = 0 := by
          have ha' : ∀ᵐ p ∂μ, w p.val = 0 := ha
          exact ae_iff.mp ha'
        exact Measure.notMem_support_iff_exists.mpr ⟨U, hU.mem_nhds hqU, hμU⟩
      · have ho : IsOpen {p : BellmanPuncturedPlane | p.val.1 ≠ 0} :=
          isOpen_ne_fun (continuous_fst.comp continuous_subtype_val) continuous_const
        exact Measure.notMem_support_iff_exists.mpr
          ⟨{p | p.val.1 ≠ 0}, ho.mem_nhds hqx, haxis⟩
    refine ⟨hzero, le_antisymm ?_ bot_le⟩
    simpa [hzero] using hhi
  have adjoint_vanishes_off_position_axis (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β) (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
      μ {q | q.val.1 ≠ 0} = 0 ∧ η {q | q.val.1 ≠ 0} = 0 := by
    have hpos := bellmanAdjointPair_positive_position_zero R β hR hβ μ η hp
    have hneg := bellmanAdjointPair_positive_position_zero R β hR hβ
      (Measure.map bellmanReflection μ) (Measure.map bellmanReflection η) hp.reflect
    have hm : MeasurableSet {q : BellmanPuncturedPlane | 0 < q.val.1} := by measurability
    rw [Measure.map_apply bellmanReflection.measurable hm,
      Measure.map_apply bellmanReflection.measurable hm] at hneg
    have he : bellmanReflection ⁻¹' {q : BellmanPuncturedPlane | 0 < q.val.1} =
        {q : BellmanPuncturedPlane | q.val.1 < 0} := by
      ext q
      change (0 < -q.val.1) ↔ q.val.1 < 0
      exact neg_pos
    rw [he] at hneg
    have hunion : {q : BellmanPuncturedPlane | q.val.1 ≠ 0} =
        {q | 0 < q.val.1} ∪ {q | q.val.1 < 0} := by
      ext q
      simp only [mem_ofPred_eq, mem_union]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim LT.lt.ne' LT.lt.ne⟩
    rw [hunion]
    exact ⟨measure_union_null hpos.1 hneg.1, measure_union_null hpos.2 hneg.2⟩
  by_contra hn
  have hge : 3 ≤ β := le_of_not_gt hn
  obtain ⟨μ, η, hp⟩ := (mem_bellmanAdmissibleDegrees_iff R β).mp hβ
  have haxis := adjoint_vanishes_off_position_axis R β hR hge μ η hp
  have hlo : μ ≤ η := by
    simpa using hp.2.2.2.1
  obtain ⟨hμ, _⟩ := stationary_axis_pair_eq_zero hR μ η hp.1 hp.2.1 hlo
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 haxis.1
  exact hp.left_ne_zero hμ

end HypoellipticAleksandrov.KineticAleksandrov

