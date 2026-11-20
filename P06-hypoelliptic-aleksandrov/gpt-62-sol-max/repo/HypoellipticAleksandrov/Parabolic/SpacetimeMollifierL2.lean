module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Analysis.L2Convergence
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Translation input for spacetime mollification in `L²`

This module begins the `L²` approximation theory for the fixed spacetime
mollifier by connecting raw translations to the continuous translation action
on `Lp`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Convolution ENNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2

open Analysis

private lemma weighted_cauchy_schwarz {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {k u : X → ℝ} (hk : Integrable k μ) (hu : AEStronglyMeasurable u μ)
    (hsq : Integrable (fun x => |k x| * u x ^ 2) μ) :
    Integrable (fun x => k x * u x) μ ∧
      (∫ x, k x * u x ∂μ) ^ 2 ≤ (∫ x, |k x| ∂μ) * ∫ x, |k x| * u x ^ 2 ∂μ := by
  let a x := √|k x|
  let b x := a x * |u x|
  have haM : AEStronglyMeasurable a μ := Real.continuous_sqrt.comp_aestronglyMeasurable hk.1.norm
  have haSq (x : X) : a x ^ 2 = |k x| := Real.sq_sqrt (abs_nonneg _)
  have hbSq (x : X) : b x ^ 2 = |k x| * u x ^ 2 := by simp only [b, mul_pow, haSq, sq_abs]
  have hprod (x : X) : a x * b x = ‖k x * u x‖ := by
    simp only [b, ← mul_assoc, ← pow_two, haSq, Real.norm_eq_abs, abs_mul]
  have ha : MemLp a 2 μ := (memLp_two_iff_integrable_sq haM).2 (hk.abs.congr (.of_forall fun x => (haSq x).symm))
  have hb : MemLp b 2 μ := (memLp_two_iff_integrable_sq (haM.mul hu.norm)).2
    (hsq.congr (.of_forall fun x => (hbSq x).symm))
  refine ⟨(ha.integrable_mul hb).mono' (hk.1.mul hu) (.of_forall fun x => (hprod x).ge), ?_⟩
  have h := (norm_integral_le_integral_norm (fun x => k x * u x)).trans
    ((integral_congr_ae (.of_forall hprod)).symm.le.trans
      ((Real.le_norm_self _).trans (norm_integral_mul_le_eLpNorm_two ha hb)))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).2 h
  rw [mul_pow, ← Lp.norm_toLp a ha, ← Lp.norm_toLp b hb,
    ← integral_sq_eq_norm_toLp_sq ha, ← integral_sq_eq_norm_toLp_sq hb] at hs
  simpa only [Real.norm_eq_abs, sq_abs, haSq, hbSq] using hs

local notation "vol" => (volume : Measure (TimeVelocity _))

section
variable {d : ℕ}

private lemma weighted_average_sq {k : TimeVelocity d → ℝ}
    {G : TimeVelocity d × TimeVelocity d → ℝ} (hk : Integrable k vol)
    (hG : AEStronglyMeasurable G (Measure.prod vol vol))
    (hsq : Integrable (fun p => |k p.2| * G p ^ 2) (Measure.prod vol vol)) :
    let F z := ∫ x, k x * G (z,x) ∂vol
    MemLp F 2 vol ∧ (∫ z, F z ^ 2 ∂vol) ≤
      (∫ x, |k x| ∂vol) * ∫ x, |k x| * (∫ z, G (z,x) ^ 2 ∂vol) ∂vol := by
  dsimp only
  have hm := (hk.1.comp_snd.mul hG).integral_prod_right'
  have hb := hsq.integral_prod_left.const_mul (∫ x, |k x| ∂vol)
  have h := hsq.prod_right_ae.and hG.prodMk_left
  have hbound := h.mono fun z hz => (weighted_cauchy_schwarz hk hz.2 hz.1).2
  have hF := (memLp_two_iff_integrable_sq hm).2
    (hb.mono' (hm.pow 2) (by simpa only [Pi.pow_apply, Pi.mul_apply, Real.norm_eq_abs, abs_sq] using hbound))
  refine ⟨hF, ?_⟩
  have hi := integral_mono_ae hF.integrable_sq hb (by
    filter_upwards [hbound] with z hz
    simpa only [Pi.mul_apply] using hz)
  rw [integral_const_mul, integral_integral_swap hsq] at hi
  simpa only [Pi.mul_apply, integral_const_mul] using hi

private lemma aestronglyMeasurable_sub_prod {f : TimeVelocity d → ℝ}
    (hf : AEStronglyMeasurable f vol) :
    AEStronglyMeasurable (fun p : TimeVelocity d × TimeVelocity d => f (p.1 - p.2)) (Measure.prod vol vol) :=
  hf.comp_fst.comp_measurePreserving (measurePreserving_sub_prod vol vol)

section
variable {k f : TimeVelocity d → ℝ} (hk : Integrable k vol) (hf : MemLp f 2 vol)
include k f hk hf

private lemma integrable_weighted_sq_translate :
    Integrable (fun p : TimeVelocity d × TimeVelocity d => |k p.2| * f (p.1 - p.2) ^ 2) (Measure.prod vol vol) :=
  (measurePreserving_sub_prod vol vol).integrable_comp_of_integrable (hf.integrable_sq.mul_prod hk.abs)
    |>.congr (.of_forall fun p => mul_comm _ _)

/-- Young's `L¹ * L²` inequality in squared form, for real-valued kernels. -/
theorem integral_kernel_mul_translate_L2 :
    let F z := ∫ x, k x * f (z - x) ∂vol
    MemLp F 2 vol ∧ (∫ z, F z ^ 2 ∂vol) ≤ (∫ x, |k x| ∂vol) ^ 2 * ∫ z, f z ^ 2 ∂vol := by
  have h := weighted_average_sq hk (aestronglyMeasurable_sub_prod hf.aestronglyMeasurable)
    (integrable_weighted_sq_translate hk hf)
  have ht (x : TimeVelocity d) : (∫ z, f (z - x) ^ 2 ∂vol) = ∫ z, f z ^ 2 ∂vol := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (μ := (volume : Measure (TimeVelocity d)))
      (fun z => f z ^ 2) (-x)
  dsimp only at h
  simp only [ht, integral_mul_const] at h
  simpa only [pow_two, mul_assoc] using h

end

private lemma spacetimeMollification_apply (ε : ℝ) (f : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    spacetimeMollification ε f z = ∫ x, spacetimeMollifier ε x * f (z - x) ∂vol := rfl

private lemma integral_sq_spacetimeMollification_le {ε : ℝ} (hε : 0 < ε)
    {f : TimeVelocity d → ℝ} (hf : MemLp f 2 vol) :
    MemLp (spacetimeMollification ε f) 2 vol ∧
      (∫ z, spacetimeMollification ε f z ^ 2 ∂vol) ≤ ∫ z, f z ^ 2 ∂vol := by
  let F z := ∫ x, spacetimeMollifier ε x * f (z - x) ∂vol
  change MemLp F 2 vol ∧ _
  simp_rw [spacetimeMollification_apply]
  simpa only [abs_of_nonneg (spacetimeMollifier_nonneg ε _), spacetimeMollifier_integral hε, one_pow, one_mul]
    using integral_kernel_mul_translate_L2 (integrable_of_integral_eq_one (spacetimeMollifier_integral (d := d) hε)) hf

end

section
variable {d : ℕ} {ε : ℝ} (hε : 0 < ε) (f : TimeVelocity d → ℝ) (hf : MemLp f 2 vol)
include hε hf

/-- Positive-radius spacetime mollification maps `L²` to `L²`. -/
theorem spacetimeMollification_memLp : MemLp (spacetimeMollification ε f) 2 vol :=
  (integral_sq_spacetimeMollification_le hε hf).1

/-- Positive-radius spacetime mollification is an exact `L²` contraction. -/
theorem eLpNorm_spacetimeMollification_le : eLpNorm (spacetimeMollification ε f) 2 vol ≤ eLpNorm f 2 vol := by
  obtain ⟨hg, h⟩ := integral_sq_spacetimeMollification_le hε hf
  rw [← Lp.enorm_toLp hg, ← Lp.enorm_toLp hf, ← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_)
  simpa only [← integral_sq_eq_norm_toLp_sq hg, ← integral_sq_eq_norm_toLp_sq hf, Real.norm_eq_abs, sq_abs] using h

end

section
variable {d : ℕ}

private lemma tendsto_sq_translate {f : TimeVelocity d → ℝ} (hf : MemLp f 2 vol) :
    Tendsto (fun x => ∫ z, (f (z - x) - f z) ^ 2 ∂vol) (𝓝 0) (𝓝 0) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  letI : ContinuousVAdd (TimeVelocity d)ᵈᵃᵃ (Lp ℝ 2 (volume : Measure (TimeVelocity d))) := Lp.instContinuousVAddDomAddAct
  let F := hf.toLp f
  let G (x : TimeVelocity d) := DomAddAct.mk (-x) +ᵥ F
  have hG : Continuous G := continuous_vadd.comp ((DomAddAct.continuous_mk.comp continuous_neg).prodMk continuous_const)
  have h : Tendsto (fun x => ‖G x - F‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun x => ‖G x - F‖ ^ 2) := (hG.sub continuous_const).norm.pow 2
    have hh := hcont.continuousAt (x := 0)
    change Tendsto _ _ (𝓝 (‖G 0 - F‖ ^ 2)) at hh
    simpa [G] using hh
  refine h.congr' (.of_forall fun x => ?_)
  have he := integral_sq_eq_norm_toLp_sq (Lp.memLp (G x - F))
  rw [Lp.toLp_coeFn] at he
  rw [← he]
  have hcomp := (quasiMeasurePreserving_add_left vol (-x)).ae_eq_comp hf.coeFn_toLp
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (G x) F, DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-x)) F,
    hcomp, hf.coeFn_toLp] with z hz hgz htz hFz
  simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs, sub_eq_neg_add, G, Function.comp_apply] using
    congrArg (fun t : ℝ => t ^ 2) (hz.trans (congrArg₂ (· - ·) (hgz.trans htz) hFz))

private lemma integrable_weighted_sq_difference {k f : TimeVelocity d → ℝ}
    (hk : Integrable k vol) (hf : MemLp f 2 vol) :
    Integrable (fun p : TimeVelocity d × TimeVelocity d => |k p.2| * (f (p.1 - p.2) - f p.1) ^ 2)
      (Measure.prod vol vol) := by
  refine (((integrable_weighted_sq_translate hk hf).add (hf.integrable_sq.mul_prod hk.abs)).const_mul 2).mono'
    (hk.1.norm.comp_snd.mul (((aestronglyMeasurable_sub_prod hf.aestronglyMeasurable).sub hf.aestronglyMeasurable.comp_fst).pow 2)) ?_
  exact .of_forall fun p => by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_sq, Pi.add_apply]
    calc
      _ ≤ |k p.2| * (2 * (f (p.1 - p.2) ^ 2 + f p.1 ^ 2)) := by
        gcongr
        nlinarith [sq_nonneg (f (p.1 - p.2) + f p.1)]
      _ = _ := by ring

private lemma sq_spacetimeMollification_sub_le {ε : ℝ} (hε : 0 < ε)
    {f : TimeVelocity d → ℝ} (hf : MemLp f 2 vol) :
    (∫ z, (spacetimeMollification ε f z - f z) ^ 2 ∂vol) ≤
      ∫ x, spacetimeMollifier ε x * (∫ z, (f (z - x) - f z) ^ 2 ∂vol) ∂vol := by
  let k : TimeVelocity d → ℝ := spacetimeMollifier ε
  have h1 : (∫ x, k x ∂vol) = 1 := spacetimeMollifier_integral hε
  have hk := integrable_of_integral_eq_one h1
  have hn x : |k x| = k x := abs_of_nonneg (spacetimeMollifier_nonneg ε x)
  have h := weighted_average_sq hk ((aestronglyMeasurable_sub_prod hf.aestronglyMeasurable).sub hf.aestronglyMeasurable.comp_fst)
    (integrable_weighted_sq_difference hk hf)
  dsimp only at h
  have hint := (integrable_weighted_sq_translate hk hf).prod_right_ae
  have hae : ∀ᵐ z ∂vol, (∫ x, k x * (f (z - x) - f z) ∂vol) = spacetimeMollification ε f z - f z := by
    filter_upwards [hint, (aestronglyMeasurable_sub_prod hf.aestronglyMeasurable).prodMk_left] with z hz hm
    have hi := (weighted_cauchy_schwarz hk hm hz).1
    simp_rw [mul_sub]
    rw [integral_sub hi (hk.mul_const _), integral_mul_const, h1, one_mul, spacetimeMollification_apply]
  rw [← integral_congr_ae (hae.mono fun z hz => congrArg (fun t : ℝ => t ^ 2) hz)]
  simpa only [hn, h1, one_mul, Pi.sub_apply, k] using h.2

/-- Spacetime mollification approximates a fixed global `L²` datum. -/
theorem tendsto_eLpNorm_spacetimeMollification_sub (f : TimeVelocity d → ℝ)
    (hf : MemLp f 2 vol) :
    Tendsto (fun ε => eLpNorm (spacetimeMollification ε f - f) 2 vol) (𝓝[>] 0) (𝓝 0) := by
  let q (x : TimeVelocity d) := ∫ z, (f (z - x) - f z) ^ 2 ∂vol
  have hq : Tendsto q (𝓝 0) (𝓝 0) := tendsto_sq_translate hf
  have hb : Tendsto (fun ε => ∫ x, spacetimeMollifier ε x * q x ∂vol) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => .of_forall fun ε => ha.trans_le (integral_nonneg fun x =>
      mul_nonneg (spacetimeMollifier_nonneg ε x) (integral_nonneg fun _ => sq_nonneg _)), ?_⟩
    intro a ha
    obtain ⟨r, hr, hbr⟩ := Metric.mem_nhds_iff.1 (hq (Iio_mem_nhds (half_pos ha)))
    filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr)] with ε hε hεr
    have h1 := spacetimeMollifier_integral (d := d) hε
    have hk := integrable_of_integral_eq_one h1
    have hqint := (integrable_weighted_sq_difference hk hf).swap.integral_prod_left
    simp only [Function.comp_apply, Prod.swap, abs_of_nonneg (spacetimeMollifier_nonneg ε _), integral_const_mul] at hqint
    calc
      _ ≤ ∫ x, spacetimeMollifier ε x * (a / 2) ∂vol := by
        refine integral_mono hqint (hk.mul_const _) (fun x => ?_)
        by_cases hx : x ∈ Function.support (spacetimeMollifier (d := d) ε)
        · rw [spacetimeMollifier_support hε] at hx
          exact mul_le_mul_of_nonneg_left (hbr (Metric.ball_subset_ball hεr.le hx)).le
            (spacetimeMollifier_nonneg ε x)
        · simp [Function.notMem_support.mp hx]
      _ < a := by rw [integral_mul_const, h1, one_mul]; exact half_lt_self ha
  have hsq : Tendsto (fun ε => ∫ z, (spacetimeMollification ε f z - f z) ^ 2 ∂vol) (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _)
      (Filter.Eventually.mono self_mem_nhdsWithin fun _ hε => sq_spacetimeMollification_sub_le hε hf) hb
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsq.sqrt
  rw [Real.sqrt_zero, ENNReal.ofReal_zero] at h
  refine h.congr' (Filter.Eventually.mono self_mem_nhdsWithin fun ε hε => ?_)
  have hg := (spacetimeMollification_memLp hε f hf).sub hf
  have he := integral_sq_eq_norm_toLp_sq hg
  simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] at he
  dsimp only [Function.comp_apply]
  rw [he, Real.sqrt_sq (norm_nonneg _), ofReal_norm, Lp.enorm_toLp]

/-- Positive-radius mollifications strongly approximate a fixed global `L²` datum. -/
theorem spacetimeMollification_strongL2 {f : TimeVelocity d → ℝ}
    (hf : MemLp f 2 volume) :
    Analysis.StrongL2Limit (𝓝[>] (0 : ℝ)) volume (fun ε => spacetimeMollification ε f) f :=
  ⟨Filter.Eventually.mono self_mem_nhdsWithin fun _ hε => spacetimeMollification_memLp hε f hf,
    hf, tendsto_eLpNorm_spacetimeMollification_sub f hf⟩

end

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
