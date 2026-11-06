module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L2Space
import Aesop
public import HypoellipticAleksandrov.Measure.TimeVelocity




/-!
# Translation input for spacetime mollification in `L²`

This module begins the `L²` approximation theory for the fixed spacetime
mollifier by connecting raw translations to the continuous translation action
on `Lp`.
-/

 public section



open Filter MeasureTheory
open scoped ENNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2

variable {d : ℕ}

private theorem tendsto_eLpNorm_add_translate_sub

    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    Tendsto
      (fun x  =>
        eLpNorm (fun z => f (x + z) - f z) (2 )
          )
      (nhds 0) (nhds 0) := by
  let sharedTerm_29c0ecd356 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : ContinuousVAdd (TimeVelocity d)ᵈᵃᵃ
      (Lp ℝ (2 ) sharedTerm_29c0ecd356) :=
    MeasureTheory.Lp.instContinuousVAddDomAddAct
  let F : Lp ℝ (2 ) sharedTerm_29c0ecd356 := hf.toLp f
  have hcont : Continuous (fun x : TimeVelocity d => DomAddAct.mk x +ᵥ F) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have hzero : DomAddAct.mk (0 : TimeVelocity d) +ᵥ F = F := by simp

  have hsub : Tendsto
      (fun x : TimeVelocity d => (DomAddAct.mk x +ᵥ F) - F)
      (nhds 0) (nhds 0) := by

    simpa only [hzero, sub_self] using (show Tendsto
        (fun x : TimeVelocity d => (DomAddAct.mk x +ᵥ F) - F)
        (nhds 0)
        (nhds ((DomAddAct.mk (0 : TimeVelocity d) +ᵥ F) - F)) from (hcont.sub (continuous_const )).continuousAt)
  have henorm : Tendsto
      (fun x : TimeVelocity d => ‖(DomAddAct.mk x +ᵥ F) - F‖ₑ)
      (nhds 0) (nhds 0) := by
    simpa only [enorm_zero] using hsub.enorm
  apply henorm.congr'
  filter_upwards with x
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae

  filter_upwards [Lp.coeFn_sub (DomAddAct.mk x +ᵥ F) F,
    DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk x) F,
    hf.coeFn_toLp, (show (fun z  => F (x + z)) =ᵐ[volume]
      (fun z => f (x + z)) by
        simpa only [Function.comp_def] using
          (quasiMeasurePreserving_add_left sharedTerm_29c0ecd356 x).ae_eq_comp
            hf.coeFn_toLp)] with z hsubz hz hzf hzf_add_z
  rw [hsubz]
  change (DomAddAct.mk x +ᵥ F : HypoellipticAleksandrov.Parabolic.ScalarField d) z - F z =
    f (x + z) - f z
  rw [hz, hzf]
  change F (x + z) - f z = f (x + z) - f z
  rw [hzf_add_z]

variable {ε : ℝ} (hε : 0 < ε)

include hε in
private theorem spacetimeMollifier_integrable
      :
    Integrable (spacetimeMollifier (d := d) ε)
       := (spacetimeMollifier_contDiff (d := d) ε).continuous
    |>.integrable_of_hasCompactSupport (spacetimeMollifier_hasCompactSupport hε)

section
variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

include hε hf
private theorem integrable_spacetimeMollifier_mul_sq_sub

     :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        spacetimeMollifier ε p.1 * f (p.2 - p.1) ^ 2)
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := (MeasurePreserving.integrable_comp_of_integrable
  (measurePreserving_prod_sub (timeVelocityVolume d) (timeVelocityVolume d))
  (Integrable.mul_prod (spacetimeMollifier_integrable hε) (MemLp.integrable_sq hf)))

private theorem integral_integral_spacetimeMollifier_mul_sq_sub_swap

     :
    (∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2) =
      ∫ x : TimeVelocity d, ∫ z : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2 := (integral_integral_swap (id (Integrable.swap (integrable_spacetimeMollifier_mul_sq_sub hε f hf))))

private theorem ae_sq_integral_spacetimeMollifier_mul_le

     :
    ∀ᵐ z : TimeVelocity d,
      |∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x)| ^ 2 ≤
        ∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2 := by
  let sharedTerm_30643657ca := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  filter_upwards [((integrable_spacetimeMollifier_mul_sq_sub hε f hf).prod_left_ae)] with z hz
  let a : HypoellipticAleksandrov.Parabolic.ScalarField d := fun x => Real.sqrt (spacetimeMollifier ε x)
  let b  := fun x =>
    Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|
  have ha_cont : Continuous a :=
    (spacetimeMollifier_contDiff (d := d) ε).continuous.sqrt

  have ha : MemLp a (2 )
      sharedTerm_30643657ca :=
    (memLp_two_iff_integrable_sq ha_cont.aestronglyMeasurable).2 (by
        apply (spacetimeMollifier_integrable hε).congr
        exact ae_of_all _ fun x => by
          simp only [a, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)])

  have hb_meas : AEStronglyMeasurable b
      sharedTerm_30643657ca :=
    ha_cont.aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.comp_measurePreserving (show MeasurePreserving (fun x  => z - x)
      sharedTerm_30643657ca by
          simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
            (measurePreserving_add_left sharedTerm_30643657ca z).comp
              (Measure.measurePreserving_neg sharedTerm_30643657ca))).norm)

  have hb : MemLp b (2 )
      sharedTerm_30643657ca :=
    (memLp_two_iff_integrable_sq hb_meas).2 (by
        convert hz using 1
        · funext x
          simp only [b, mul_pow, sq_abs, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)])
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := sharedTerm_30643657ca) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun x => Real.sqrt_nonneg _)
    (ae_of_all _ fun x => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa only [ENNReal.ofReal_ofNat] using
      ha) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hholder' :
      (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * |f (z - x)|) ≤
        Real.sqrt (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2) := by
    calc
      _ = ∫ x : TimeVelocity d,
          Real.sqrt (spacetimeMollifier ε x) *
            (Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change spacetimeMollifier ε x * |f (z - x)| =
            Real.sqrt (spacetimeMollifier ε x) *
              (Real.sqrt (spacetimeMollifier ε x) * |f (z - x)|)
          rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]
      _ ≤ _ := hholder
      _ = _ := by
        have hone : (∫ x : TimeVelocity d,
            Real.sqrt (spacetimeMollifier ε x) ^ 2) = 1 := by
          calc
            _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x := by
              apply integral_congr_ae
              exact ae_of_all _ fun x => Real.sq_sqrt (spacetimeMollifier_nonneg ε x)
            _ = 1 := spacetimeMollifier_integral hε
        have htwo : (∫ x : TimeVelocity d,
            Real.sqrt (spacetimeMollifier ε x) ^ 2 * f (z - x) ^ 2) =
            ∫ x : TimeVelocity d,
              spacetimeMollifier ε x * f (z - x) ^ 2 := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change Real.sqrt (spacetimeMollifier ε x) ^ 2 * f (z - x) ^ 2 =
              spacetimeMollifier ε x * f (z - x) ^ 2
            rw [Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]
        rw [hone, htwo, Real.one_rpow, one_mul, Real.sqrt_eq_rpow]
        congr 2
        norm_num
  have habs :
      |∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x)| ≤
        (∫ x : TimeVelocity d,
          spacetimeMollifier ε x * f (z - x) ^ 2) ^ (2 : ℝ)⁻¹ := by
    calc
      |∫ x : TimeVelocity d, spacetimeMollifier ε x * f (z - x)| =
          ‖∫ x : TimeVelocity d, spacetimeMollifier ε x * f (z - x)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : TimeVelocity d,
          ‖spacetimeMollifier ε x * f (z - x)‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ x : TimeVelocity d,
          spacetimeMollifier ε x * |f (z - x)| := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          change |spacetimeMollifier ε x * f (z - x)| =
            spacetimeMollifier ε x * |f (z - x)|
          rw [abs_mul,
            abs_of_nonneg (spacetimeMollifier_nonneg ε x)]
      _ ≤ _ := by simpa only [Real.sqrt_eq_rpow, one_div] using hholder'



  have hsquare := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 (by
      simpa only [Real.sqrt_eq_rpow, one_div] using habs)
  simpa only [Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x) (sq_nonneg _))] using hsquare

private theorem integral_integral_spacetimeMollifier_mul_sq_sub

     :
    (∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2) =
      ∫ z : TimeVelocity d, f z ^ 2 := by
  rw [integral_integral_spacetimeMollifier_mul_sq_sub_swap hε f hf]
  have htranslate (x : TimeVelocity d) :
      (∫ z : TimeVelocity d, f (z - x) ^ 2) =
        ∫ z : TimeVelocity d, f z ^ 2 := by
    have hsub : MeasurePreserving (MeasurableEquiv.addLeft (-x ))
        (volume )  := measurePreserving_add_left _ (-x)
    simpa [sub_eq_add_neg, add_comm] using
      hsub.integral_comp' (fun z => f z ^ 2)
  simp_rw [integral_const_mul, htranslate]
  rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]

/-- Positive-radius spacetime mollification is an exact `L²` contraction. -/
theorem eLpNorm_spacetimeMollification_le

     :
    eLpNorm (spacetimeMollification ε f) (2 )
         ≤
      eLpNorm f (2 )
         := by
  let sharedTerm_8cc8f38c81 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hcont : Continuous (spacetimeMollification ε f) :=
    (contDiff_spacetimeMollification hε f (hf.locallyIntegrable (by norm_num))).continuous
  have hweighted : Integrable (fun z : TimeVelocity d =>
      ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * f (z - x) ^ 2)
      sharedTerm_8cc8f38c81 := by
    simpa only [Function.comp_def, Prod.swap] using
      (integrable_spacetimeMollifier_mul_sq_sub hε f hf).swap.integral_prod_left
  have hsquare : Integrable (fun z : TimeVelocity d =>
      spacetimeMollification ε f z ^ 2)
      sharedTerm_8cc8f38c81 := by
    apply hweighted.mono' (hcont.aestronglyMeasurable.pow 2)
    filter_upwards [ae_sq_integral_spacetimeMollifier_mul_le hε f hf] with z hz
    rw [Pi.pow_apply, Real.norm_eq_abs, abs_sq]
    simpa only [spacetimeMollification, convolution_def, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul, sq_abs] using hz


  rw [((memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hsquare).eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  apply ENNReal.ofReal_le_ofReal
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) (by
      calc
        _ ≤ ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
            spacetimeMollifier ε x * f (z - x) ^ 2 := by
          apply integral_mono_ae hsquare hweighted
          filter_upwards [ae_sq_integral_spacetimeMollifier_mul_le hε f hf] with z hz
          simpa only [spacetimeMollification, convolution_def, ContinuousLinearMap.lsmul_apply,
            smul_eq_mul, sq_abs] using hz
        _ = _ := integral_integral_spacetimeMollifier_mul_sq_sub hε f hf) (by norm_num)

/-- Positive-radius spacetime mollification preserves global `L²`
membership. -/
theorem spacetimeMollification_memLp

     :
    MemLp (spacetimeMollification ε f) (2 )
       := (eLpNorm_spacetimeMollification_le hε f hf).trans_lt hf.eLpNorm_lt_top

private theorem integrable_spacetimeMollifier_mul_sq_sub_self

     :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        spacetimeMollifier ε p.1 * (f (p.2 - p.1) - f p.2) ^ 2)
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := by
  let sharedTerm_893dc382f0 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))


  apply (((integrable_spacetimeMollifier_mul_sq_sub hε f hf).const_mul 2).add (by
      simpa only [mul_assoc] using
        ((spacetimeMollifier_integrable hε).const_mul 2).mul_prod hf.integrable_sq)).mono'
  · have hz : AEStronglyMeasurable
        (fun p : TimeVelocity d × TimeVelocity d => f p.2)
        (sharedTerm_893dc382f0.prod volume) :=
      hf.aestronglyMeasurable.comp_snd
    have hsub : AEStronglyMeasurable
        (fun p : TimeVelocity d × TimeVelocity d => f (p.2 - p.1))
        (sharedTerm_893dc382f0.prod volume) := by
      simpa only [Function.comp_def] using hz.comp_measurePreserving
        (measurePreserving_prod_sub
          sharedTerm_893dc382f0
          sharedTerm_893dc382f0)
    exact ((spacetimeMollifier_contDiff (d := d) ε).continuous.comp continuous_fst
      |>.aestronglyMeasurable).mul ((hsub.sub hz).pow 2)
  · exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (spacetimeMollifier_nonneg ε p.1), abs_sq, Pi.add_apply]
      have hρ := spacetimeMollifier_nonneg ε p.1
      nlinarith [sq_nonneg (f (p.2 - p.1) + f p.2),
        sq_nonneg (f (p.2 - p.1) - f p.2)]
end


private theorem tendsto_eLpNorm_sub_translate_sub

    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    Tendsto
      (fun x  =>
        eLpNorm (fun z => f (z - x) - f z) (2 )
          )
      (nhds 0) (nhds 0) := by

  have h := (tendsto_eLpNorm_add_translate_sub f hf).comp (by
      have hn := continuousAt_neg (G := TimeVelocity d) (x := (0 ))
      change Tendsto (fun x : TimeVelocity d => -x) (nhds 0) (nhds (-0)) at hn
      simpa only [neg_zero] using hn)
  simpa [Function.comp_def, sub_eq_add_neg, add_comm] using h

private theorem integral_sq_sub_translate_eq_toReal_eLpNorm_sq
     (x : TimeVelocity d)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2) =
      (eLpNorm (fun z => f (z - x) - f z) (2 )
        ).toReal ^ 2 := by
  let sharedTerm_8d6ae70512 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  have hd : MemLp (fun z => f (z - x) - f z) (2 )
      sharedTerm_8d6ae70512 :=
    (hf.comp_measurePreserving (by
        simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
          (measurePreserving_add_left sharedTerm_8d6ae70512 (-x)))).sub hf
  rw [hd.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _),
    ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm

private theorem tendsto_integral_sq_sub_translate

    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    Tendsto (fun x : TimeVelocity d =>
      ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2)
      (nhds 0) (nhds 0) := by
  let sharedTerm_a5c5331320 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hfinite (x : TimeVelocity d) :
      eLpNorm (fun z => f (z - x) - f z) (2 )
        sharedTerm_a5c5331320 ≠ ∞ := by

    exact ((hf.comp_measurePreserving (by
        simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
          measurePreserving_add_left sharedTerm_a5c5331320 (-x))).sub hf).eLpNorm_ne_top

  simpa only [integral_sq_sub_translate_eq_toReal_eLpNorm_sq (f := f) (hf := hf),
    zero_pow (by norm_num : (2 ) ≠ 0)] using ((ENNReal.tendsto_toReal_zero_iff hfinite).2 (tendsto_eLpNorm_sub_translate_sub f hf)).pow 2

private theorem ae_sq_integral_spacetimeMollifier_mul_sub_self_le
     {ε : ℝ} (hε : 0 < ε)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    ∀ᵐ z : TimeVelocity d,
      Integrable (fun x  => spacetimeMollifier ε x *
          (f (z - x) - f z))  ∧
        |∫ x : TimeVelocity d, spacetimeMollifier ε x *
            (f (z - x) - f z)| ^ 2 ≤
          ∫ x : TimeVelocity d, spacetimeMollifier ε x *
            (f (z - x) - f z) ^ 2 := by
  let sharedTerm_c5e956ca18 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  filter_upwards [((integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).prod_left_ae)] with z hz
  let a : HypoellipticAleksandrov.Parabolic.ScalarField d := fun x => Real.sqrt (spacetimeMollifier ε x)
  let b  := fun x =>
    Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|
  have ha_cont : Continuous a :=
    (spacetimeMollifier_contDiff (d := d) ε).continuous.sqrt

  have ha : MemLp a (2 )
      sharedTerm_c5e956ca18 :=
    (memLp_two_iff_integrable_sq ha_cont.aestronglyMeasurable).2 (by
        apply (spacetimeMollifier_integrable hε).congr
        exact ae_of_all _ fun x => by
          simp only [a, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)])
  have hsub : MeasurePreserving (fun x  => z - x)
      sharedTerm_c5e956ca18  := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left sharedTerm_c5e956ca18 z).comp
        (Measure.measurePreserving_neg sharedTerm_c5e956ca18)
  have hb_meas : AEStronglyMeasurable b
      sharedTerm_c5e956ca18 :=
    ha_cont.aestronglyMeasurable.mul
      (((hf.aestronglyMeasurable.comp_measurePreserving hsub).sub
        (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _ : TimeVelocity d => f z) )).norm)

  have hb : MemLp b (2 )
      sharedTerm_c5e956ca18 :=
    (memLp_two_iff_integrable_sq hb_meas).2 (by
        convert hz using 1
        · funext x
          simp only [b, mul_pow, sq_abs, Real.sq_sqrt (spacetimeMollifier_nonneg ε x)])
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := sharedTerm_c5e956ca18) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => Real.sqrt_nonneg _)
    (ae_of_all _ fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa only [ENNReal.ofReal_ofNat] using
      ha) (by simpa only [ENNReal.ofReal_ofNat] using hb)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hone : (∫ x : TimeVelocity d,
      Real.sqrt (spacetimeMollifier ε x) ^ 2) = 1 := by
    calc
      _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => Real.sq_sqrt (spacetimeMollifier_nonneg ε x)
      _ = 1 := spacetimeMollifier_integral hε
  have htwo : (∫ x : TimeVelocity d,
      Real.sqrt (spacetimeMollifier ε x) ^ 2 * (f (z - x) - f z) ^ 2) =
      ∫ x : TimeVelocity d,
        spacetimeMollifier ε x * (f (z - x) - f z) ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      let sharedTerm_eb7955a7f8 := ((f (z - x) - f z) ^ 2)
      change Real.sqrt (spacetimeMollifier ε x) ^ 2 * sharedTerm_eb7955a7f8 =
        spacetimeMollifier ε x * sharedTerm_eb7955a7f8
      rw [Real.sq_sqrt (spacetimeMollifier_nonneg ε x)]


  have hsquare := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).2 (by
      calc
        _ = ‖∫ x : TimeVelocity d, spacetimeMollifier ε x *
            (f (z - x) - f z)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x : TimeVelocity d, ‖spacetimeMollifier ε x *
            (f (z - x) - f z)‖ := norm_integral_le_integral_norm _
        _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
            |f (z - x) - f z| := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change |spacetimeMollifier ε x * (f (z - x) - f z)| =
              spacetimeMollifier ε x * |f (z - x) - f z|
            rw [abs_mul,
              abs_of_nonneg (spacetimeMollifier_nonneg ε x)]
        _ = ∫ x : TimeVelocity d, Real.sqrt (spacetimeMollifier ε x) *
            (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|) := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            change spacetimeMollifier ε x * |f (z - x) - f z| =
              Real.sqrt (spacetimeMollifier ε x) *
                (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|)
            rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]
        _ ≤ _ := hholder
        _ = _ := by
          rw [hone, htwo, Real.one_rpow, one_mul, Real.sqrt_eq_rpow]
          congr 2
          norm_num)
  have habint : Integrable (fun x  =>
      spacetimeMollifier ε x * |f (z - x) - f z|)  := by
    convert ha.integrable_mul hb using 1
    funext x
    simp only [a, b]
    change spacetimeMollifier ε x * |f (z - x) - f z| =
      Real.sqrt (spacetimeMollifier ε x) *
        (Real.sqrt (spacetimeMollifier ε x) * |f (z - x) - f z|)
    rw [← mul_assoc, Real.mul_self_sqrt (spacetimeMollifier_nonneg ε x)]

  exact ⟨(by
      apply habint.mono' ((spacetimeMollifier_contDiff (d := d) ε).continuous
        |>.aestronglyMeasurable.mul
          (((hf.aestronglyMeasurable.comp_measurePreserving hsub).sub
            (aestronglyMeasurable_const : AEStronglyMeasurable
              (fun _ : TimeVelocity d => f z) ))))
      exact ae_of_all _ fun x => by
        change |spacetimeMollifier ε x * (f (z - x) - f z)| ≤
          spacetimeMollifier ε x * |f (z - x) - f z|
        rw [abs_mul,
          abs_of_nonneg (spacetimeMollifier_nonneg ε x)]), by simpa only [Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x) (sq_nonneg _))] using hsquare⟩

variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : MemLp f (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

include hf
private theorem tendsto_weighted_integral_sq_sub_translate

     :
    Tendsto (fun ε : ℝ => ∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2))
      (𝓝[>] 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hsmall := (tendsto_integral_sq_sub_translate f hf).eventually
    (Metric.ball_mem_nhds 0 (half_pos hδ))
  rcases Metric.mem_nhds_iff.1 hsmall with ⟨r, hr, hrball⟩

  filter_upwards [self_mem_nhdsWithin, (Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr))] with ε hεpos hεr
  have hε : 0 < ε := hεpos

  have hnonneg : 0 ≤ ∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2) :=
    integral_nonneg fun x => mul_nonneg (spacetimeMollifier_nonneg ε x)
      (integral_nonneg fun _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (show (∫ x : TimeVelocity d,
      spacetimeMollifier ε x *
        (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2)) ≤ δ / 2 by


      calc
        _ ≤ ∫ x : TimeVelocity d, spacetimeMollifier ε x * (δ / 2) := by
          apply integral_mono (by
              apply (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).integral_prod_left.congr
              exact ae_of_all _ fun x => by
                change (∫ y : TimeVelocity d, spacetimeMollifier ε x *
                  (f (y - x) - f y) ^ 2) =
                    spacetimeMollifier ε x *
                      ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2
                rw [integral_const_mul]) ((spacetimeMollifier_integrable hε).mul_const (δ / 2))
          intro x
          by_cases hx : x ∈ Metric.ball (0 : TimeVelocity d) ε
          ·
            have hs := hrball ((Metric.ball_subset_ball hεr.le) hx)
            change dist (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2) 0 <
              δ / 2 at hs
            rw [Real.dist_eq, sub_zero] at hs

            exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hs.le)
              (spacetimeMollifier_nonneg ε x)
          · have hzero  :=
              Function.notMem_support.mp (by
                rw [spacetimeMollifier_support hε]
                exact hx)
            simpa only [hzero, zero_mul] using (le_refl (0 : ℝ))
        _ = δ / 2 := by
          rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]).trans_lt (half_lt_self hδ)

/-- Spacetime mollification converges strongly in global `L²` as the positive
radius tends to zero. -/
theorem tendsto_eLpNorm_spacetimeMollification_sub

     :
    Filter.Tendsto
      (fun ε  =>
        eLpNorm
          (spacetimeMollification ε f - f)
          (2 )
          )
      (𝓝[>] 0) (𝓝 0) := by
  let q  := fun ε => ∫ z : TimeVelocity d,
    (spacetimeMollification ε f z - f z) ^ 2
  have hq : Tendsto q (𝓝[>] 0) (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun ε => integral_nonneg fun _ => sq_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hg := (spacetimeMollification_memLp hε f hf).sub hf
      have hright : Integrable (fun z : TimeVelocity d =>
            ∫ x : TimeVelocity d, spacetimeMollifier ε x *
              (f (z - x) - f z) ^ 2) volume :=
          (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).integral_prod_right
      calc
        q ε ≤ ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
              spacetimeMollifier ε x * (f (z - x) - f z) ^ 2 := by
            apply integral_mono_ae hg.integrable_sq hright
            filter_upwards [ae_sq_integral_spacetimeMollifier_mul_sub_self_le hε f hf]
              with z hz
            have hconst : Integrable (fun x : TimeVelocity d =>
                spacetimeMollifier ε x * f z)  :=
              (spacetimeMollifier_integrable hε).mul_const (f z)
            have htrans : Integrable (fun x  =>
                spacetimeMollifier ε x * f (z - x))  := by
              apply (hz.1.add hconst).congr
              exact ae_of_all _ fun x => by
                change spacetimeMollifier ε x * (f (z - x) - f z) +
                    spacetimeMollifier ε x * f z = spacetimeMollifier ε x * f (z - x)
                ring
            have hid : spacetimeMollification ε f z - f z =
                ∫ x : TimeVelocity d, spacetimeMollifier ε x *
                  (f (z - x) - f z) := by
              calc
                _ = (∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    f (z - x)) - f z := by
                  rfl
                _ = (∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    f (z - x)) -
                    ∫ x : TimeVelocity d, spacetimeMollifier ε x * f z := by
                  rw [integral_mul_const, spacetimeMollifier_integral hε, one_mul]
                _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
                    (f (z - x) - f z) := by
                  rw [← integral_sub htrans hconst]
                  apply integral_congr_ae
                  exact ae_of_all _ fun x => by ring
            simpa only [q, Pi.sub_apply, hid, sq_abs] using hz.2
        _ = ∫ x : TimeVelocity d, spacetimeMollifier ε x *
              (∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2) := by
            rw [integral_integral_swap (by
              simpa only [Function.comp_def, Function.uncurry_def, Prod.swap] using
                (integrable_spacetimeMollifier_mul_sq_sub_self hε f hf).swap)]
            apply integral_congr_ae
            exact ae_of_all _ fun x => by
              change (∫ z : TimeVelocity d, spacetimeMollifier ε x *
                (f (z - x) - f z) ^ 2) =
                  spacetimeMollifier ε x *
                    ∫ z : TimeVelocity d, (f (z - x) - f z) ^ 2
              rw [integral_const_mul]
    · exact tendsto_weighted_integral_sq_sub_translate f hf
  have hrpow : Tendsto (fun ε => (q ε) ^ (1 / (2 : ℝ))) (𝓝[>] 0) (nhds 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using
      hq.rpow_const (Or.inr (by norm_num : 0 ≤ (1 / (2 : ℝ))))
  have hofReal : Tendsto (fun ε => ENNReal.ofReal ((q ε) ^ (1 / (2 : ℝ))))
      (𝓝[>] 0) (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrpow
  apply hofReal.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hg := (spacetimeMollification_memLp hε f hf).sub hf
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  aesop

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
