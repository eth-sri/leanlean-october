module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.SpacetimeMollifier
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.bump_volume_integral_pos from HypoellipticAleksandrov.Parabolic.SpacetimeMollifier


/-!
# Weighted time energy for spacetime mollification

This module develops the kernel-derivative facts used to prove the weighted
time-energy limit for the fixed spacetime mollifier.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution ENNReal NNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy

variable {d : ℕ}

private theorem timeDerivative_spacetimeMollifier
     {ε : ℝ} (hε : 0 < ε) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) z =
      (((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) *
          ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹) * ε⁻¹ *
        fderiv ℝ (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d)
          (ε⁻¹ • z) (1, 0) := by

  let s : TimeVelocity d → TimeVelocity d := fun y => ε⁻¹ • y
  have hu : DifferentiableAt ℝ
      (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d) (s z) :=
    (ExistsContDiffBumpBase.u_smooth (TimeVelocity d)).differentiable
      (by simp) (s z)
  have hs : HasFDerivAt s (ε⁻¹ • ContinuousLinearMap.id ℝ (TimeVelocity d)) z := by
    simpa [s, Pi.smul_def, id_eq] using (hasFDerivAt_id (𝕜 := ℝ) z).const_smul ε⁻¹

  have hinner :
      fderiv ℝ (fun y : TimeVelocity d => ExistsContDiffBumpBase.u (ε⁻¹ • y)) z =
        (fderiv ℝ (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d)
          (ε⁻¹ • z)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ (TimeVelocity d)) := by
    change fderiv ℝ (ExistsContDiffBumpBase.u ∘ s) z = _
    rw [(fderiv_comp z hu hs.differentiableAt), hs.fderiv]
  unfold timeDerivative spacetimeMollifier
  rw [abs_of_nonneg hε.le, fderiv_const_mul]
  · rw [hinner]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring_nf
  · exact hu.comp z hs.differentiableAt

private theorem timeDerivative_spacetimeMollifier_neg
     (ε : ℝ) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) (-z) =
      -timeDerivative (spacetimeMollifier ε) z := by
  let ρ : HypoellipticAleksandrov.Parabolic.ScalarField d := spacetimeMollifier ε
  let n : TimeVelocity d → TimeVelocity d := fun y => -y

  have hn (y : TimeVelocity d) :
      HasFDerivAt n (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) y := by
    simpa [n, Pi.neg_def, id_eq] using (hasFDerivAt_id (𝕜 := ℝ) y).neg
  have heq : ρ ∘ n = ρ := by
    funext y
    exact spacetimeMollifier_neg ε y
  have hcomp := fderiv_comp z (((spacetimeMollifier_contDiff ε).differentiable (by simp)) (-z)) (hn z).differentiableAt

  unfold timeDerivative
  change fderiv ℝ ρ (-z) (1, 0) = -fderiv ℝ ρ z (1, 0)
  have happ := congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => L (1, 0)) (show fderiv ℝ ρ (-z) ∘L (-(ContinuousLinearMap.id ℝ (TimeVelocity d))) =
        fderiv ℝ ρ z by
      rw [← (hn z).fderiv, ← hcomp, heq])
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at happ
  linarith

private theorem integrable_timeDerivative_spacetimeMollifier
     {ε : ℝ} (hε : 0 < ε) :
    Integrable (timeDerivative (spacetimeMollifier (d := d) ε))
       := by
  have hsmooth : ContDiff ℝ PDE.smoothOrder
      (timeDerivative (spacetimeMollifier (d := d) ε)) := by
    unfold timeDerivative
    exact ((spacetimeMollifier_contDiff (d := d) ε).fderiv_right
      (by simp)).clm_apply contDiff_const

  exact hsmooth.continuous.integrable_of_hasCompactSupport ((id (HasCompactSupport.fderiv_apply ℝ (spacetimeMollifier_hasCompactSupport hε) (1, 0))))




private theorem integral_norm_mul_abs_timeDerivative_spacetimeMollifier
    {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (∫ z : TimeVelocity d,
        ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))⁻¹ *
        ∫ y : TimeVelocity d, ‖y‖ *
          |fderiv ℝ (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d)
            y (1, 0)| ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let A : ℝ := ∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
    ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
  let g  := fun y =>
    ‖y‖ * |fderiv ℝ (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d) y (1, 0)|
  have hA : A ≠ 0 := (_root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.bump_volume_integral_pos d).ne'
  have hεne  := hε.ne'
  have hpoint (z : TimeVelocity d) :
      ‖z‖ * |timeDerivative (spacetimeMollifier ε) z| =
        ((A * ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹ * ε⁻¹ * ε) *
          g (ε⁻¹ • z) := by
    rw [timeDerivative_spacetimeMollifier hε]
    simp only [A, g, abs_mul, abs_inv, abs_pow, abs_of_pos hε,
      abs_of_pos (_root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.bump_volume_integral_pos d),
      norm_smul, Real.norm_eq_abs]
    field_simp
  simp_rw [hpoint, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg
    (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) g hε.le]
  change ((A * ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹ * ε⁻¹ * ε) *
      (ε ^ Module.finrank ℝ (TimeVelocity d) * ∫ y, g y) =
    A⁻¹ * ∫ y, g y
  field_simp

private theorem exists_uniform_firstMoment_timeDerivative_spacetimeMollifier
    (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      (∫ z : TimeVelocity d,
          ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) ≤ C := by
  let C : ℝ :=
    (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))⁻¹ *
      ∫ y : TimeVelocity d, ‖y‖ *
        |fderiv ℝ (ExistsContDiffBumpBase.u : HypoellipticAleksandrov.Parabolic.ScalarField d)
          y (1, 0)| ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
  refine ⟨C, mul_nonneg (inv_nonneg.mpr (_root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.bump_volume_integral_pos d).le)
    (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)), ?_⟩
  intro ε hε
  exact (integral_norm_mul_abs_timeDerivative_spacetimeMollifier hε).le

variable {d : ℕ}

private theorem mul_memLp_two_of_contDiff_hasCompactSupport
     (q w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : MemLp q (2 )
      )
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    MemLp (fun z => w z * q z) (2 )
       := by
  have hw : MemLp w ∞  :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  simpa only [mul_comm] using hq.fun_mul hw

private theorem timeDerivative_spacetimeMollification_mul
     {ε : ℝ} (hε : 0 < ε)
    (q w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : MemLp q (2 )
      )
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w)
    (z : TimeVelocity d) :
    timeDerivative
        (spacetimeMollification ε (fun y => w y * q y)) z =
      ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x *
          (w (z - x) * q (z - x))
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_35fb792ccf := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let sharedTerm_f23ee2e29f := ((fderiv ℝ (spacetimeMollifier (d := d) ε)))
  let f  := fun y => w y * q y
  have hf : MemLp f (2 )
      sharedTerm_35fb792ccf :=
    mul_memLp_two_of_contDiff_hasCompactSupport q w hq hwSmooth hwCompact
  have hfLoc : LocallyIntegrable f
      sharedTerm_35fb792ccf := hf.locallyIntegrable (by norm_num)
  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((spacetimeMollifier_contDiff ε).of_le (by simp)) hfLoc z
  have hkernel : HasCompactSupport
      sharedTerm_f23ee2e29f :=
    (spacetimeMollifier_hasCompactSupport hε).fderiv ℝ
  have hkernelCont : Continuous
      sharedTerm_f23ee2e29f :=
    (spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)


  unfold timeDerivative spacetimeMollification
  rw [hderiv.fderiv]
  calc
    ((fderiv ℝ (spacetimeMollifier ε) ⋆[ContinuousLinearMap.precompL
        (TimeVelocity d) (ContinuousLinearMap.lsmul ℝ ℝ), volume] f) z) (1, 0) =
        ∫ x : TimeVelocity d,
          (((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x))) (1, 0) := (id (Eq.symm (ContinuousLinearMap.integral_comp_comm ((ContinuousLinearMap.apply ℝ ℝ) (1, 0)) (show Integrable
      (fun x  =>
        ((ContinuousLinearMap.precompL (TimeVelocity d)
          (ContinuousLinearMap.lsmul ℝ ℝ))
            (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x)))
      sharedTerm_35fb792ccf by
                  exact (show MeasureTheory.ConvolutionExistsAt
                    sharedTerm_f23ee2e29f f z
                    (ContinuousLinearMap.precompL (TimeVelocity d)
                      (ContinuousLinearMap.lsmul ℝ ℝ))
                    sharedTerm_35fb792ccf from hkernel.convolutionExists_left _ hkernelCont hfLoc z)))))
    _ = _ := by
      rfl

private theorem integrable_kernel_mul_memLp_two_mul_translate
     (k f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hk : Integrable k )
    (hf : MemLp f (2 ) )
    (hg : MemLp g (2 ) ) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        k p.1 * f p.2 * g (p.2 - p.1))
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := by
  let sharedTerm_3aca2530c6 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hfirst : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        |k p.1| * f p.2 ^ 2)
      (sharedTerm_3aca2530c6.prod volume) :=
    hk.abs.mul_prod hf.integrable_sq


  apply (hfirst.add (by
      simpa only [Function.comp_def] using
        (measurePreserving_prod_sub
          sharedTerm_3aca2530c6
          sharedTerm_3aca2530c6).integrable_comp_of_integrable (show Integrable
        (fun p : TimeVelocity d × TimeVelocity d =>
          |k p.1| * g p.2 ^ 2)
        (sharedTerm_3aca2530c6.prod volume) from hk.abs.mul_prod hg.integrable_sq))).mono'
  · exact hk.1.comp_fst |>.mul hf.aestronglyMeasurable.comp_snd |>.mul <| by
      simpa only [Function.comp_def] using hg.aestronglyMeasurable.comp_snd.comp_measurePreserving
        (measurePreserving_prod_sub
          sharedTerm_3aca2530c6
          sharedTerm_3aca2530c6)
  · exact ae_of_all _ fun p => by
      let sharedTerm_3e0f5f2bf0 := ((g (p.2 - p.1)))
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hk0 := abs_nonneg (k p.1)
      have hs := sq_nonneg (|f p.2| - |sharedTerm_3e0f5f2bf0|)
      have hfabs : |f p.2| ^ 2 = f p.2 ^ 2 := sq_abs (f p.2)
      have hgabs : |sharedTerm_3e0f5f2bf0| ^ 2 = sharedTerm_3e0f5f2bf0 ^ 2 :=
        sq_abs sharedTerm_3e0f5f2bf0
      simp only [Pi.add_apply]
      nlinarith

section
variable {ε : ℝ} (hε : 0 < ε) (q w : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : MemLp q (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) (hwSmooth : ContDiff ℝ PDE.smoothOrder w) (hwCompact : HasCompactSupport w)

include hε hq hwSmooth hwCompact
private theorem integrable_pairing_doubleIntegrand
      :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        q p.2 * timeDerivative (spacetimeMollifier ε) p.1 *
          (w (p.2 - p.1) * q (p.2 - p.1)))
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := by

  have h := integrable_kernel_mul_memLp_two_mul_translate
    _ q _
    (integrable_timeDerivative_spacetimeMollifier hε) hq (mul_memLp_two_of_contDiff_hasCompactSupport q w hq hwSmooth hwCompact)
  apply h.congr
  exact ae_of_all _ fun p => by ring_nf

private theorem pairing_eq_integral_integral
      :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        q y * timeDerivative (spacetimeMollifier ε) x *
          (w (y - x) * q (y - x))
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by

  calc
    _ = ∫ z : TimeVelocity d, ∫ x : TimeVelocity d,
        q z * timeDerivative (spacetimeMollifier ε) x *
          (w (z - x) * q (z - x)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only
        rw [timeDerivative_spacetimeMollification_mul hε q w hq hwSmooth hwCompact]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring_nf
    _ = _ := by
      apply integral_integral_swap
      convert (integrable_pairing_doubleIntegrand hε q w hq hwSmooth hwCompact).swap using 1
      funext p
      rcases p with ⟨x, y⟩
      rfl

private theorem pairing_eq_translated_integral_integral
      :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w y * q y * q (y + x)
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  rw [pairing_eq_integral_integral hε q w hq hwSmooth hwCompact]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hmp : MeasurePreserving (MeasurableEquiv.addLeft x)
        (volume )  :=
      measurePreserving_add_left _ x
    have htranslate := hmp.integral_comp'
      (fun y : TimeVelocity d =>
        q y * timeDerivative (spacetimeMollifier ε) x *
          (w (y - x) * q (y - x)))
    dsimp only
    rw [← htranslate]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      simp only [MeasurableEquiv.coe_addLeft, add_sub_cancel_left]
      ring_nf

private theorem pairing_eq_neg_reflected_integral_integral
      :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      -(∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * w (y + x) * q y * q (y + x)
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) := by
  rw [pairing_eq_integral_integral hε q w hq hwSmooth hwCompact]
  have hmp : MeasurePreserving (MeasurableEquiv.neg (TimeVelocity d))
      (volume )  :=
    Measure.measurePreserving_neg (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
  have hreflect := hmp.integral_comp'
    (fun x  => ∫ y : TimeVelocity d,
      q y * timeDerivative (spacetimeMollifier ε) x *
        (w (y - x) * q (y - x)))
  rw [← hreflect, ← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ y : TimeVelocity d,
      q y * timeDerivative (spacetimeMollifier ε) (-x) *
        (w (y - (-x)) * q (y - (-x)))) = _
    dsimp only
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      simp_all [timeDerivative_spacetimeMollifier_neg] <;> ring

private theorem pairing_eq_half_symmetrized
      :
    (∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (1 / 2 : ℝ) * ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          q y * q (y + x)
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_10a27d6cbf := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let P : ℝ := ∫ z : TimeVelocity d,
    q z * timeDerivative
      (spacetimeMollification ε (fun y => w y * q y)) z
  let A : ℝ := ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * w y * q y * q (y + x)
  let B : ℝ := ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * w (y + x) * q y * q (y + x)
  have hPA : P = A :=
    pairing_eq_translated_integral_integral hε q w hq hwSmooth hwCompact
  have hPB : P = -B :=
    pairing_eq_neg_reflected_integral_integral hε q w hq hwSmooth hwCompact
  have hdouble := integrable_pairing_doubleIntegrand hε q w hq hwSmooth hwCompact
  have hAprod : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        timeDerivative (spacetimeMollifier ε) p.1 * w p.2 * q p.2 * q (p.2 + p.1))
      (sharedTerm_10a27d6cbf.prod volume) := by
    have hc := (measurePreserving_prod_add
      sharedTerm_10a27d6cbf
      sharedTerm_10a27d6cbf).integrable_comp_of_integrable hdouble
    apply hc.congr
    exact ae_of_all _ fun p => by
      simp only [Function.comp_apply, add_sub_cancel_left, add_comm]
      ring_nf
  have hnegProd : MeasurePreserving
      (fun p : TimeVelocity d × TimeVelocity d => (-p.1, p.2))
      (sharedTerm_10a27d6cbf.prod volume)
      (sharedTerm_10a27d6cbf.prod volume) :=
    (Measure.measurePreserving_neg sharedTerm_10a27d6cbf).prod
      (MeasurePreserving.id sharedTerm_10a27d6cbf)
  have hBprod : Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        timeDerivative (spacetimeMollifier ε) p.1 * w (p.2 + p.1) *
          q p.2 * q (p.2 + p.1))
      (sharedTerm_10a27d6cbf.prod volume) := by

    apply (hnegProd.integrable_comp_of_integrable hdouble).neg.congr
    exact ae_of_all _ fun p => by
      change -(q p.2 * timeDerivative (spacetimeMollifier ε) (-p.1) *
        (w (p.2 - (-p.1)) * q (p.2 - (-p.1)))) = _
      rw [timeDerivative_spacetimeMollifier_neg]
      simp only [sub_neg_eq_add]
      ring_nf
  have hAB : (∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
      timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
        q y * q (y + x)) = A - B := by


    simp only [A, B]
    rw [← integral_sub ((Integrable.integral_prod_left hAprod)) ((Integrable.integral_prod_left hBprod))]
    apply integral_congr_ae
    filter_upwards [hAprod.prod_right_ae, hBprod.prod_right_ae] with x hAi hBi
    rw [← integral_sub hAi hBi]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by ring_nf
  change P = _
  rw [hAB]
  linarith
end


variable (x : TimeVelocity d)

private theorem memLp_add_translate
      (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      ) :
    MemLp (fun y => f (y + x)) (2 )
       := by
  simpa only [Function.comp_def, add_comm] using
    hf.comp_measurePreserving
      (measurePreserving_add_left _ x)

private theorem integral_abs_mul_add_translate_le
      (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      )
    (hg : MemLp g (2 )
      ) :
    (∫ y : TimeVelocity d, |f y| * |g (y + x)|
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) ≤
      Real.sqrt (∫ y : TimeVelocity d, f y ^ 2) *
        Real.sqrt (∫ y : TimeVelocity d, g y ^ 2) := by
  have hgt := memLp_add_translate x g hg
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
    (f := fun y => |f y|) (g := fun y => |g (y + x)|)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ fun _ => abs_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hgt.norm)
  have htranslate : (∫ y : TimeVelocity d, g (y + x) ^ 2) =
      ∫ y : TimeVelocity d, g y ^ 2 := by
    have hmp : MeasurePreserving (MeasurableEquiv.addLeft x)
        (volume )  :=
      measurePreserving_add_left _ x
    simpa only [MeasurableEquiv.coe_addLeft, add_comm] using
      hmp.integral_comp' (fun y : TimeVelocity d => g y ^ 2)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two, sq_abs, htranslate] using hholder

private theorem exists_lipschitzWith_weight
     (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    ∃ K : ℝ≥0, LipschitzWith K w := ContDiff.lipschitzWith_of_hasCompactSupport hwCompact hwSmooth (by simp)

private theorem abs_integral_symmetrized_inner_le
     (K : ℝ≥0) (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwLip : LipschitzWith K w)
    (x : TimeVelocity d) (k : ℝ)
    (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      )
    (hg : MemLp g (2 )
      ) :
    |∫ y : TimeVelocity d,
        k * (w y - w (y + x)) * f y * g (y + x)
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)| ≤
      |k| * (K : ℝ) * ‖x‖ *
        (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2)) := by
  let sharedTerm_57fc423c03 := ((|k| * (K : ℝ) * ‖x‖))
  have hfg : Integrable (fun y  => |f y| * |g (y + x)|)
       := by
    have hgt := memLp_add_translate x g hg
    simpa only [Real.norm_eq_abs, Pi.mul_def] using hf.norm.integrable_mul hgt.norm
  calc
    _ = ‖∫ y : TimeVelocity d,
        k * (w y - w (y + x)) * f y * g (y + x)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ y : TimeVelocity d,
        ‖k * (w y - w (y + x)) * f y * g (y + x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : TimeVelocity d,
        (sharedTerm_57fc423c03) * (|f y| * |g (y + x)|) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun _ => norm_nonneg _
      · exact hfg.const_mul sharedTerm_57fc423c03
      · exact ae_of_all _ fun y => by
          let sharedTerm_a26d035b87 := (|f y| * |g (y + x)|)
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]

          calc
            _ = (|k| * |w y - w (y + x)|) *
                (sharedTerm_a26d035b87) := by ring
            _ ≤ (|k| * ((K : ℝ) * ‖x‖)) *
                (sharedTerm_a26d035b87) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by
                    simpa [Real.norm_eq_abs] using hwLip.norm_sub_le y (y + x)) (abs_nonneg k))
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            _ = _ := by ring
    _ = (sharedTerm_57fc423c03) *
        ∫ y : TimeVelocity d, |f y| * |g (y + x)| := by
      rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_abs_mul_add_translate_le x f g hf hg)
      (mul_nonneg (mul_nonneg (abs_nonneg _) K.coe_nonneg) (norm_nonneg _))

private theorem integrable_norm_mul_abs_timeDerivative_spacetimeMollifier
     {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : TimeVelocity d =>
      ‖x‖ * |timeDerivative (spacetimeMollifier ε) x|)
       := (Continuous.integrable_of_hasCompactSupport
  (Continuous.mul continuous_norm
    (Continuous.abs
      (id
        (Continuous.clm_apply
          (ContDiff.continuous_fderiv (spacetimeMollifier_contDiff ε)
            (of_eq_true
              (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1))
                not_false_eq_true)))
          continuous_const))))
  (HasCompactSupport.mul_left
    (HasCompactSupport.abs (id (HasCompactSupport.fderiv_apply ℝ (spacetimeMollifier_hasCompactSupport hε) (1, 0))))))

private theorem abs_symmetrized_bilinear_le
     {ε M : ℝ} (hε : 0 < ε)
    (hmoment : (∫ x : TimeVelocity d,
      ‖x‖ * |timeDerivative (spacetimeMollifier ε) x|) ≤ M)
    (K : ℝ≥0) (w : HypoellipticAleksandrov.Parabolic.ScalarField d) (hwLip : LipschitzWith K w)
    (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 ) )
    (hg : MemLp g (2 ) ) :
    |∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x)| ≤
      (K : ℝ) * M *
        (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2)) := by
  let S : ℝ := Real.sqrt (∫ y : TimeVelocity d, f y ^ 2) *
    Real.sqrt (∫ y : TimeVelocity d, g y ^ 2)


  change _ ≤ (K : ℝ) * M * S
  calc
    _ = ‖∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : TimeVelocity d, |∫ y : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
          f y * g (y + x)| := (id
  (norm_integral_le_integral_norm fun x =>
    ∫ (y : TimeVelocity d), timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) * f y * g (y + x)))
    _ ≤ ∫ x : TimeVelocity d,
        ((K : ℝ) * S) *
          (‖x‖ * |timeDerivative (spacetimeMollifier ε) x|) := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun _ => abs_nonneg _
      · exact (integrable_norm_mul_abs_timeDerivative_spacetimeMollifier (d := d) hε).const_mul ((K : ℝ) * S)
      · exact ae_of_all _ fun x => by
          have hx := abs_integral_symmetrized_inner_le K w hwLip x
            (timeDerivative (spacetimeMollifier ε) x) f g hf hg
          linarith
    _ = ((K : ℝ) * S) * ∫ x : TimeVelocity d,
        ‖x‖ * |timeDerivative (spacetimeMollifier ε) x| := by
      rw [integral_const_mul]
    _ ≤ ((K : ℝ) * S) * M :=
      mul_le_mul_of_nonneg_left hmoment (mul_nonneg K.coe_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    _ = _ := by ring

private theorem exists_uniform_symmetrized_bilinear_bound
     (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ (f g : HypoellipticAleksandrov.Parabolic.ScalarField d),
      MemLp f (2 )  →
      MemLp g (2 )  →
      |∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
          timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
            f y * g (y + x)| ≤
        C * (Real.sqrt (∫ y : TimeVelocity d, f y ^ 2) *
          Real.sqrt (∫ y : TimeVelocity d, g y ^ 2)) := by
  obtain ⟨K, hwLip⟩ := exists_lipschitzWith_weight w hwSmooth hwCompact
  obtain ⟨M, hM, hmoment⟩ :=
    exists_uniform_firstMoment_timeDerivative_spacetimeMollifier d
  refine ⟨(K : ℝ) * M, mul_nonneg K.coe_nonneg hM, ?_⟩
  intro ε hε f g hf hg
  exact abs_symmetrized_bilinear_le hε (hmoment hε) K w hwLip f g hf hg

private def symmetrizedBilinear
     (ε : ℝ) (w f g : HypoellipticAleksandrov.Parabolic.ScalarField d) : ℝ :=
  ∫ x : TimeVelocity d, ∫ y : TimeVelocity d,
    timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
      f y * g (y + x)

variable {ε : ℝ} (hε : 0 < ε)

section
variable (w f g : HypoellipticAleksandrov.Parabolic.ScalarField d) (hwSmooth : ContDiff ℝ PDE.smoothOrder w) (hwCompact : HasCompactSupport w) (hf : MemLp f (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) (hg : MemLp g (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

include hε hwSmooth hwCompact hf hg
private theorem integrable_symmetrizedBilinear_double

     :
    Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * (w p.2 - w (p.2 + p.1)) *
        f p.2 * g (p.2 + p.1))
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := by
  let sharedTerm_2e65013ebe := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hwf := mul_memLp_two_of_contDiff_hasCompactSupport f w hf hwSmooth hwCompact
  have hwg := mul_memLp_two_of_contDiff_hasCompactSupport g w hg hwSmooth hwCompact
  have hk := integrable_timeDerivative_spacetimeMollifier (d := d) hε
  have hbaseA := integrable_kernel_mul_memLp_two_mul_translate
    _ g _ hk hg hwf
  have hAcomp := (measurePreserving_prod_add
    sharedTerm_2e65013ebe
    sharedTerm_2e65013ebe).integrable_comp_of_integrable hbaseA
  have hA : Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * w p.2 * f p.2 * g (p.2 + p.1))
      (sharedTerm_2e65013ebe.prod volume) := by
    apply hAcomp.congr
    exact ae_of_all _ fun p => by
      simp only [Function.comp_apply, add_sub_cancel_left, add_comm]
      ring
  have hbaseB := integrable_kernel_mul_memLp_two_mul_translate
    _ f
      _
      ((integrable_timeDerivative_spacetimeMollifier hε).comp_neg) hf hwg
  have hnegProd : MeasurePreserving
      (fun p : TimeVelocity d × TimeVelocity d => (-p.1, p.2))
      (sharedTerm_2e65013ebe.prod volume)
      (sharedTerm_2e65013ebe.prod volume) :=
    (Measure.measurePreserving_neg sharedTerm_2e65013ebe).prod
      (MeasurePreserving.id sharedTerm_2e65013ebe)
  have hBcomp := hnegProd.integrable_comp_of_integrable hbaseB

  apply (hA.sub (show Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      timeDerivative (spacetimeMollifier ε) p.1 * w (p.2 + p.1) *
        f p.2 * g (p.2 + p.1))
      (sharedTerm_2e65013ebe.prod volume) by
      apply hBcomp.congr
      exact ae_of_all _ fun p => by
        simp_all [timeDerivative, spacetimeMollifier] <;> ring)).congr
  exact ae_of_all _ fun p => by
    simp only [Pi.sub_apply]
    ring

private theorem integrable_symmetrizedBilinear_outer

     :
    Integrable (fun x  => ∫ y : TimeVelocity d,
      timeDerivative (spacetimeMollifier ε) x * (w y - w (y + x)) *
        f y * g (y + x))
       := (Integrable.integral_prod_left (integrable_symmetrizedBilinear_double hε w f g hwSmooth hwCompact hf hg))
end


include hε in
private theorem symmetrizedBilinear_quadratic_sub

    (w q p : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 ) )
    (hp : MemLp p (2 ) ) :
    symmetrizedBilinear ε w q q - symmetrizedBilinear ε w p p =
      symmetrizedBilinear ε w (q - p) q +
        symmetrizedBilinear ε w p (q - p) := by
  have hqp := hq.sub hp


  have hdq := integrable_symmetrizedBilinear_outer hε w (q - p) q
    hwSmooth hwCompact hqp hq
  have hpd := integrable_symmetrizedBilinear_outer hε w p (q - p)
    hwSmooth hwCompact hp hqp
  unfold symmetrizedBilinear
  rw [← integral_sub (integrable_symmetrizedBilinear_outer hε w q q hwSmooth hwCompact hq hq) (integrable_symmetrizedBilinear_outer hε w p p hwSmooth hwCompact hp hp), ← integral_add hdq hpd]
  apply integral_congr_ae
  filter_upwards [
    (integrable_symmetrizedBilinear_double hε w q q hwSmooth hwCompact hq hq).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w p p hwSmooth hwCompact hp hp).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w (q - p) q hwSmooth hwCompact hqp hq).prod_right_ae,
    (integrable_symmetrizedBilinear_double hε w p (q - p) hwSmooth hwCompact hp hqp).prod_right_ae]
      with x hqqx hppx hdqx hpdx
  rw [← integral_sub hqqx hppx, ← integral_add hdqx hpdx]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [Pi.sub_apply]
    ring

private theorem exists_uniform_pairing_quadratic_continuity
     (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ (q p : HypoellipticAleksandrov.Parabolic.ScalarField d),
      MemLp q (2 )  →
      MemLp p (2 )  →
      |(∫ z : TimeVelocity d, q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z) -
        ∫ z : TimeVelocity d, p z * timeDerivative
          (spacetimeMollification ε (fun y => w y * p y)) z| ≤
        (1 / 2 : ℝ) * C *
          (Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2) *
              Real.sqrt (∫ y : TimeVelocity d, q y ^ 2) +
            Real.sqrt (∫ y : TimeVelocity d, p y ^ 2) *
              Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_symmetrized_bilinear_bound w hwSmooth hwCompact
  refine ⟨C, hC, ?_⟩
  intro ε hε q p hq hp
  have hqp := hq.sub hp


  have hquad := symmetrizedBilinear_quadratic_sub hε w q p
    hwSmooth hwCompact hq hp
  have hfirst := hbound hε (q - p) q hqp hq
  have hsecond := hbound hε p (q - p) hp hqp
  change |_ - _| ≤ _
  rw [(pairing_eq_half_symmetrized hε q w hq hwSmooth hwCompact), (pairing_eq_half_symmetrized hε p w hp hwSmooth hwCompact)]
  change |(1 / 2 : ℝ) * symmetrizedBilinear ε w q q -
      (1 / 2 : ℝ) * symmetrizedBilinear ε w p p| ≤ _
  rw [← mul_sub, hquad, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2 : ℝ) * |symmetrizedBilinear ε w (q - p) q +
        symmetrizedBilinear ε w p (q - p)| ≤
        (1 / 2 : ℝ) * (|symmetrizedBilinear ε w (q - p) q| +
          |symmetrizedBilinear ε w p (q - p)|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ _ := by
      let sharedTerm_4a9500ea90 := (Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2 ∂volume))
      simp only [Pi.sub_apply] at hfirst hsecond

      calc
        _ ≤ (1 / 2 : ℝ) *
            (C * (sharedTerm_4a9500ea90 *
                Real.sqrt (∫ y : TimeVelocity d, q y ^ 2)) +
              C * (Real.sqrt (∫ y : TimeVelocity d, p y ^ 2) *
                sharedTerm_4a9500ea90)) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)
        _ = _ := by ring

private theorem timeDerivative_mul
     (f g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : TimeVelocity d) :
    timeDerivative (fun y => f y * g y) z =
      timeDerivative f z * g z + f z * timeDerivative g z := by
  unfold timeDerivative
  change (fderiv ℝ (f * g) z) (1, 0) = _
  rw [fderiv_mul (hf z) (hg z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem smooth_weighted_time_energy_identity
     (p w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hpSmooth : ContDiff ℝ PDE.smoothOrder p)
    (hp : MemLp p (2 ) )
    (hpt : MemLp (timeDerivative p) (2 )
      )
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    (∫ z : TimeVelocity d,
      p z * timeDerivative (fun y => w y * p y) z) =
      (1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * p z ^ 2 := by
  let sharedTerm_90eba5a907 := ((fun y => w y * p y))
  let sharedTerm_d30352a4f4 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let sharedTerm_96e2eb44e6 := (∫ z : TimeVelocity d, (w z * p z) * timeDerivative p z ∂volume)
  have hpDiff : Differentiable ℝ p := hpSmooth.differentiable (by simp)
  have hwDiff : Differentiable ℝ w := hwSmooth.differentiable (by simp)

  have hwTop : MemLp w ∞ sharedTerm_d30352a4f4 :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  have hwtSmooth : ContDiff ℝ PDE.smoothOrder (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const


  have hpp : Integrable (fun z  => p z * p z)  := by
    simpa only [Pi.mul_def] using hp.integrable_mul hp
  have hwtpp : Integrable (fun z : TimeVelocity d =>
      timeDerivative w z * p z ^ 2) volume := by
    have := hpp.mul_of_top_left (hwtSmooth.continuous.memLp_of_hasCompactSupport (show _ by
        unfold timeDerivative
        exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hwCompact (1, 0)))
    apply this.congr
    exact ae_of_all _ fun z => by simp only [Pi.mul_apply, pow_two]; ring
  have hppt : Integrable (fun z  => p z * timeDerivative p z)  := by
    simpa only [Pi.mul_def] using hp.integrable_mul hpt
  have hwppt : Integrable (fun z  =>
      (w z * p z) * timeDerivative p z)  := by
    have := hppt.mul_of_top_left hwTop
    apply this.congr
    exact ae_of_all _ fun z => by simp only [Pi.mul_apply]; ring
  have hdtwp_p : Integrable (fun z  =>
      timeDerivative sharedTerm_90eba5a907 z * p z)  := by
    apply (hwtpp.add hwppt).congr
    exact ae_of_all _ fun z => by
      simp only [Pi.add_apply]
      rw [timeDerivative_mul w p hwDiff hpDiff]
      ring


  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable

    hdtwp_p hwppt (by
        have := hpp.mul_of_top_left hwTop
        apply this.congr
        exact ae_of_all _ fun z => by simp only [Pi.mul_apply]; ring) (fun z _ => (hwDiff.mul hpDiff) z) (fun z _ => hpDiff z)
  change (sharedTerm_96e2eb44e6) =
      -(∫ z, timeDerivative sharedTerm_90eba5a907 z * p z) at hibp
  have hsplit : (∫ z : TimeVelocity d,
      p z * timeDerivative sharedTerm_90eba5a907 z) =
      (∫ z : TimeVelocity d, timeDerivative w z * p z ^ 2) +
        sharedTerm_96e2eb44e6 := by
    rw [← integral_add hwtpp hwppt]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      rw [timeDerivative_mul w p hwDiff hpDiff]
      ring
  rw [hsplit]
  have hcomm : (∫ z : TimeVelocity d,
      timeDerivative sharedTerm_90eba5a907 z * p z) =
      ∫ z : TimeVelocity d,
        p z * timeDerivative sharedTerm_90eba5a907 z := by
    apply integral_congr_ae
    exact ae_of_all _ fun z => by ring
  rw [hcomm] at hibp
  linarith

private theorem timeDerivative_spacetimeMollification
     {ε : ℝ} (hε : 0 < ε)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 )
      )
    (z : TimeVelocity d) :
    timeDerivative (spacetimeMollification ε f) z =
      ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * f (z - x)
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by


  have hfLoc  := hf.locallyIntegrable (by norm_num)
  have hderiv := (spacetimeMollifier_hasCompactSupport hε).hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((spacetimeMollifier_contDiff ε).of_le (by simp)) hfLoc z


  have hconv : MeasureTheory.ConvolutionExistsAt
      (((fderiv ℝ (spacetimeMollifier (d := d) ε)))) f z
      (ContinuousLinearMap.precompL (TimeVelocity d)
        (ContinuousLinearMap.lsmul ℝ ℝ))
      (((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) :=
    ((spacetimeMollifier_hasCompactSupport hε).fderiv ℝ).convolutionExists_left _ ((spacetimeMollifier_contDiff ε).continuous_fderiv (by simp)) hfLoc z

  unfold timeDerivative spacetimeMollification
  rw [hderiv.fderiv]
  calc
    ((fderiv ℝ (spacetimeMollifier ε) ⋆[ContinuousLinearMap.precompL
        (TimeVelocity d) (ContinuousLinearMap.lsmul ℝ ℝ), volume] f) z) (1, 0) =
        ∫ x : TimeVelocity d,
          (((ContinuousLinearMap.precompL (TimeVelocity d)
            (ContinuousLinearMap.lsmul ℝ ℝ))
              (fderiv ℝ (spacetimeMollifier ε) x)) (f (z - x))) (1, 0) := (id (Eq.symm (ContinuousLinearMap.integral_comp_comm ((ContinuousLinearMap.apply ℝ ℝ) (1, 0)) hconv)))
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by rfl

private theorem spacetimeMollification_smooth_memLp
     {δ : ℝ} (hδ : 0 < δ)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : MemLp q (2 )
      ) :
    ContDiff ℝ PDE.smoothOrder (spacetimeMollification δ q) ∧
      MemLp (spacetimeMollification δ q) (2 )
         := ⟨contDiff_spacetimeMollification hδ q
      (hq.locallyIntegrable (by norm_num)),
    SpacetimeMollifierL2.spacetimeMollification_memLp hδ q hq⟩

section
variable (p w : HypoellipticAleksandrov.Parabolic.ScalarField d) (hpSmooth : ContDiff ℝ PDE.smoothOrder p) (hp : MemLp p (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) (hpt : MemLp (timeDerivative p) (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) (hwSmooth : ContDiff ℝ PDE.smoothOrder w) (hwCompact : HasCompactSupport w)

include hpSmooth hp hpt hwSmooth hwCompact
private theorem timeDerivative_mul_memLp_two
      :
    MemLp (timeDerivative (fun y => w y * p y)) (2 )
       := by


  have hwTop : MemLp w ∞  :=
    hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact
  have hwtSmooth : ContDiff ℝ PDE.smoothOrder (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const


  have hfirst : MemLp (fun z => timeDerivative w z * p z) (2 )  :=
    by simpa only [mul_comm] using hp.fun_mul (show MemLp (timeDerivative w) ∞ from hwtSmooth.continuous.memLp_of_hasCompactSupport ((id (HasCompactSupport.fderiv_apply ℝ hwCompact (1, 0)))))

  have heq : timeDerivative (fun y => w y * p y) = fun z =>
      timeDerivative w z * p z + w z * timeDerivative p z := by
    funext z
    rw [timeDerivative_mul w p (hwSmooth.differentiable (by simp)) (hpSmooth.differentiable (by simp))]
  rw [heq]
  simpa only [Pi.add_def] using hfirst.add (by simpa only [mul_comm] using hpt.fun_mul hwTop)

private theorem tendsto_smooth_pairing
      :
    Tendsto (fun ε  => ∫ z : TimeVelocity d,
      p z * timeDerivative
        (spacetimeMollification ε (fun y => w y * p y)) z)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d,
        p z * timeDerivative (fun y => w y * p y) z)) := by
  let f  := fun y => w y * p y
  let df  := timeDerivative f


  have hdf : MemLp df (2 )  :=
    timeDerivative_mul_memLp_two p w hpSmooth hp hpt hwSmooth hwCompact
  have hweak : HasWeakTimeDerivOn Set.univ f df :=
    HypoellipticAleksandrov.Parabolic.contDiffOn_one_hasWeakTimeDerivOn
      Set.univ isOpen_univ f (((hwSmooth.mul hpSmooth).of_le (by norm_num)).contDiffOn)
  have hcomm : ∀ {ε : ℝ}, 0 < ε →
      timeDerivative (spacetimeMollification ε f) = spacetimeMollification ε df := by
    intro ε hε
    exact SpacetimeMollifier.timeDerivative_spacetimeMollification hε f df
      ((mul_memLp_two_of_contDiff_hasCompactSupport p w hp hwSmooth hwCompact).locallyIntegrable (by norm_num)) (hdf.locallyIntegrable (by norm_num)) hweak
  have ht := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    (fun ε  => p) (fun ε => spacetimeMollification ε df) p df
    (μ := (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
    (l := 𝓝[>] (0 ))
    (Eventually.of_forall fun _ => hp)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε
        exact SpacetimeMollifierL2.spacetimeMollification_memLp hε df hdf)
    hp hdf
    (by
      simp_all)
    (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub df hdf)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hcomm hε]

private theorem tendsto_smooth_pairing_to_half
      :
    Tendsto (fun ε  => ∫ z : TimeVelocity d,
      p z * timeDerivative
        (spacetimeMollification ε (fun y => w y * p y)) z)
      (𝓝[>] 0) (𝓝 ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * p z ^ 2)) := by
  rw [← smooth_weighted_time_energy_identity p w hpSmooth hp hpt hwSmooth hwCompact]
  exact tendsto_smooth_pairing p w hpSmooth hp hpt hwSmooth hwCompact
end


section
variable (k f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hk : Integrable k (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) (hf : MemLp f (2 ) (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

include hk hf
private theorem integrable_abs_kernel_mul_sq_translate
      :
    Integrable (fun p : TimeVelocity d × TimeVelocity d =>
      |k p.2| * f (p.1 - p.2) ^ 2)
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).prod volume) := by
  let sharedTerm_72c375ad14 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  have h := (measurePreserving_sub_prod
    sharedTerm_72c375ad14
    sharedTerm_72c375ad14).integrable_comp_of_integrable (hf.integrable_sq.mul_prod hk.abs)
  apply h.congr
  exact ae_of_all _ fun p => by
    simp only [Function.comp_apply]
    ring

private theorem ae_sq_integral_kernel_mul_translate_le
      :
    ∀ᵐ z : TimeVelocity d,
      |∫ x : TimeVelocity d, k x * f (z - x)| ^ 2 ≤
        (∫ x : TimeVelocity d, |k x|) *
          ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 := by
  let sharedTerm_c345d1916f := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  let sharedTerm_c49501b54e := ((∫ x : TimeVelocity d, |k x| ∂volume))
  have hsections := (integrable_abs_kernel_mul_sq_translate k f hk hf).prod_right_ae
  filter_upwards [hsections] with z hz
  let a  := fun x => Real.sqrt |k x|
  let b  := fun x => Real.sqrt |k x| * |f (z - x)|
  have haSq : Integrable (fun x => a x ^ 2) volume := by
    apply hk.abs.congr
    exact ae_of_all _ fun x => by simp only [a, Real.sq_sqrt (abs_nonneg _)]
  have ha : MemLp a (2 )  :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hk.1.norm)).2 haSq
  have hbSq : Integrable (fun x => b x ^ 2) volume := by
    apply hz.congr
    exact ae_of_all _ fun x => by
      simp only [b, mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]


  have hb : MemLp b (2 )  :=
    (memLp_two_iff_integrable_sq (show AEStronglyMeasurable b from (Real.continuous_sqrt.comp_aestronglyMeasurable hk.1.norm).mul (show AEStronglyMeasurable (fun x  => f (z - x)) by
        have hmp : MeasurePreserving (fun x  => z - x) volume  := by
          simpa only [Function.comp_def, sub_eq_add_neg] using
            (measurePreserving_add_left sharedTerm_c345d1916f z).comp
              (Measure.measurePreserving_neg sharedTerm_c345d1916f)
        exact hf.aestronglyMeasurable.comp_measurePreserving hmp).norm)).2 hbSq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := sharedTerm_c345d1916f) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => Real.sqrt_nonneg _)
    (ae_of_all _ fun _ => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (by simpa using ha) (by simpa)
  simp only [a, b, Real.rpow_two, one_div, mul_pow, sq_abs] at hholder
  have hrewrite : (∫ x : TimeVelocity d,
      Real.sqrt |k x| * (Real.sqrt |k x| * |f (z - x)|)) =
      ∫ x : TimeVelocity d, |k x| * |f (z - x)| := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
  rw [hrewrite] at hholder
  have haInt : (∫ x : TimeVelocity d, Real.sqrt |k x| ^ 2) =
      sharedTerm_c49501b54e := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => Real.sq_sqrt (abs_nonneg _)
  have hbInt : (∫ x : TimeVelocity d,
      Real.sqrt |k x| ^ 2 * f (z - x) ^ 2) =
      ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2 := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [Real.sq_sqrt (abs_nonneg _)]
  rw [haInt, hbInt] at hholder
  have habs : |∫ x : TimeVelocity d, k x * f (z - x)| ≤
      Real.sqrt sharedTerm_c49501b54e *
        Real.sqrt (∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2) := by
    calc
      _ ≤ ∫ x : TimeVelocity d, |k x| * |f (z - x)| := by
        calc
          _ = ‖∫ x : TimeVelocity d, k x * f (z - x)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ ∫ x : TimeVelocity d, ‖k x * f (z - x)‖ :=
            norm_integral_le_integral_norm _
          _ = _ := by
            norm_num
      _ ≤ _ := by
        simpa only [Real.sqrt_eq_rpow, one_div] using hholder
  have hleft := sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    |>.2 habs
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => abs_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))] at hleft
  exact hleft

private theorem memLp_integral_kernel_mul_translate
      :
    MemLp (fun z => ∫ x : TimeVelocity d, k x * f (z - x))
      (2 )  := by
  let sharedTerm_92699644ff := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))

  have houtMeas := (show AEStronglyMeasurable
      (fun p : TimeVelocity d × TimeVelocity d => k p.2 * f (p.1 - p.2))
      (sharedTerm_92699644ff.prod volume) by

      exact hk.1.comp_snd.mul (show AEStronglyMeasurable
          (fun p : TimeVelocity d × TimeVelocity d => f (p.1 - p.2))
          (sharedTerm_92699644ff.prod volume) by
          simpa only [Function.comp_def] using hf.aestronglyMeasurable.comp_fst.comp_measurePreserving
            (measurePreserving_sub_prod
              sharedTerm_92699644ff
              sharedTerm_92699644ff))).integral_prod_right'
  have hright : Integrable (fun z : TimeVelocity d =>
      (∫ x : TimeVelocity d, |k x|) *
        ∫ x : TimeVelocity d, |k x| * f (z - x) ^ 2) volume := by
    exact (integrable_abs_kernel_mul_sq_translate k f hk hf).integral_prod_left.const_mul _
  apply (memLp_two_iff_integrable_sq houtMeas).2
  apply hright.mono' (houtMeas.pow 2)
  filter_upwards [ae_sq_integral_kernel_mul_translate_le k f hk hf] with z hz
  rw [Real.norm_eq_abs, Pi.pow_apply, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using hz
end


private theorem timeDerivative_spacetimeMollification_memLp
     {δ : ℝ} (hδ : 0 < δ)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : MemLp q (2 ) ) :
    MemLp (timeDerivative (spacetimeMollification δ q)) (2 )
       := (Eq.mpr (id (congrArg (fun _a => MemLp _a 2 volume) (funext fun z => timeDerivative_spacetimeMollification hδ q hq z)))
  (memLp_integral_kernel_mul_translate (timeDerivative (spacetimeMollifier δ)) q
    (integrable_timeDerivative_spacetimeMollifier hδ) hq))

private theorem sqrt_integral_sq_eq_eLpNorm_toReal
     (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : MemLp f (2 ) ) :
    Real.sqrt (∫ z : TimeVelocity d, f z ^ 2) =
      (eLpNorm f (2 ) ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _),
    ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow,
    one_div]

private theorem tendsto_weighted_sq_integral
     (w q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 ) (volume )) :
    Tendsto (fun δ : ℝ => ∫ z : TimeVelocity d,
      timeDerivative w z * spacetimeMollification δ q z ^ 2)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, timeDerivative w z * q z ^ 2)) := by
  let a  := fun δ => spacetimeMollification δ q
  let b  := fun δ z =>
    timeDerivative w z * spacetimeMollification δ q z
  let b0  := fun z => timeDerivative w z * q z
  have hwtSmooth : ContDiff ℝ PDE.smoothOrder (timeDerivative w) := by
    unfold timeDerivative
    exact (hwSmooth.fderiv_right (by simp)).clm_apply contDiff_const

  have hwtTop : MemLp (timeDerivative w) ∞ volume :=
    hwtSmooth.continuous.memLp_of_hasCompactSupport ((id (HasCompactSupport.fderiv_apply ℝ hwCompact (1, 0))))

  have haMem : ∀ᶠ δ : ℝ in 𝓝[>] 0, MemLp (a δ) (2 ) volume := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hδ q hq

  have haT := SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub q hq

  have ht := HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    a b q b0 haMem (by
        filter_upwards [haMem] with δ hδ
        simpa only [b, mul_comm] using hδ.fun_mul hwtTop) hq (by
        simpa only [b0, mul_comm] using hq.fun_mul hwtTop) haT (show _ by

            apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
              (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0))
              (by
                  simpa only [mul_zero] using ENNReal.Tendsto.mul
                    (tendsto_const_nhds : Tendsto (fun _ : ℝ => eLpNorm (timeDerivative w) ∞ volume)
                      (𝓝[>] 0) (𝓝 (eLpNorm (timeDerivative w) ∞ volume)))
                    (Or.inr ENNReal.zero_ne_top) haT
                    (Or.inr hwtTop.eLpNorm_ne_top))
            · exact Eventually.of_forall fun _ => bot_le
            · filter_upwards [haMem] with δ hδ
              have hle := eLpNorm_smul_le_mul_eLpNorm
                (p := ∞) (q := (2 )) (r := (2 ))
                hwtTop.aestronglyMeasurable (hδ.sub hq).aestronglyMeasurable
              simpa only [a, b, b0, Pi.smul_def', smul_eq_mul, Pi.sub_def,
                Pi.mul_def, mul_sub] using hle)
  simpa only [a, b, b0, pow_two, mul_assoc, mul_comm, mul_left_comm] using ht

/-- Weighted time-energy limit for raw global `L²` data. -/
theorem tendsto_integral_mul_timeDerivative_spacetimeMollification_mul
     (q w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : MemLp q (2 )
      )
    (hwSmooth : ContDiff ℝ PDE.smoothOrder w)
    (hwCompact : HasCompactSupport w) :
    Tendsto
      (fun ε  => ∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
      (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * q z ^ 2
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) := by
  let P : (HypoellipticAleksandrov.Parabolic.ScalarField d) → ℝ → ℝ := fun f ε => ∫ z : TimeVelocity d,
    f z * timeDerivative (spacetimeMollification ε (fun y => w y * f y)) z
  let R : (HypoellipticAleksandrov.Parabolic.ScalarField d) → ℝ := fun f =>
    (1 / 2 : ℝ) * ∫ z : TimeVelocity d, timeDerivative w z * f z ^ 2
  obtain ⟨C, hC, hcont⟩ := exists_uniform_pairing_quadratic_continuity w hwSmooth hwCompact
  have hD : Tendsto (fun δ  =>
      (eLpNorm (spacetimeMollification δ q - q) (2 ) ).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
        (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub q hq)


  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  have heventErr := (show Tendsto (fun δ  => C *
      (eLpNorm (spacetimeMollification δ q - q) (2 ) ).toReal *
      (eLpNorm q (2 ) ).toReal) (𝓝[>] 0) (𝓝 0) by
      simpa using (tendsto_const_nhds.mul hD).mul tendsto_const_nhds).eventually (Metric.ball_mem_nhds 0 hη3)
  have heventR := (show Tendsto (fun δ  => R (spacetimeMollification δ q))
      (𝓝[>] 0) (𝓝 (R q)) by
      exact (tendsto_const_nhds.mul
        (tendsto_weighted_sq_integral w q hwSmooth hwCompact hq))).eventually (Metric.ball_mem_nhds (R q) hη3)
  have hall : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      δ ∈ Ioi 0 ∧
      C * (eLpNorm (spacetimeMollification δ q - q) (2 ) ).toReal *
        (eLpNorm q (2 ) ).toReal ∈ Metric.ball 0 (η / 3) ∧
      R (spacetimeMollification δ q) ∈ Metric.ball (R q) (η / 3) := by
    filter_upwards [self_mem_nhdsWithin, heventErr, heventR] with δ hδ hδErr hδR
    exact ⟨hδ, hδErr, hδR⟩
  rcases hall.exists with ⟨δ, hδ, hδErr, hδR⟩
  let p  := spacetimeMollification δ q

  have hp : MemLp p (2 )  :=
    (spacetimeMollification_smooth_memLp hδ q hq).2

  have hpLimit := tendsto_smooth_pairing_to_half p w ((spacetimeMollification_smooth_memLp hδ q hq).1) hp (timeDerivative_spacetimeMollification_memLp hδ q hq) hwSmooth hwCompact

  filter_upwards [(hpLimit.eventually (Metric.ball_mem_nhds (R p) hη3)), self_mem_nhdsWithin] with ε hεp hε
  have hqp := hcont hε q p hq hp
  have hpNorm := SpacetimeMollifierL2.eLpNorm_spacetimeMollification_le hδ q hq
  change eLpNorm p (2 )  ≤ eLpNorm q (2 )  at hpNorm
  have hqpReal : Real.sqrt (∫ y : TimeVelocity d, (q y - p y) ^ 2) =
      (eLpNorm (p - q) (2 ) ).toReal := by
    rw [show (∫ y : TimeVelocity d, (q y - p y) ^ 2) =
        ∫ y : TimeVelocity d, (p - q) y ^ 2 by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by simp only [Pi.sub_apply]; ring]
    exact sqrt_integral_sq_eq_eLpNorm_toReal (p - q) (hp.sub hq)


  change dist (P q ε) (R q) < η
  rw [Real.dist_eq]
  calc
    |P q ε - R q| ≤ |P q ε - P p ε| + |P p ε - R p| + |R p - R q| := by
      let sharedTerm_764734c106 := (((P p ε - R p) + (R p - R q)))
      rw [show P q ε - R q = (P q ε - P p ε) +
          (sharedTerm_764734c106) by ring]
      have h₁ := abs_add_le (P q ε - P p ε) sharedTerm_764734c106
      have h₂ := abs_add_le (P p ε - R p) (R p - R q)
      linarith
    _ < η / 3 + η / 3 + η / 3 := by
      gcongr
      · exact (show |P q ε - P p ε| ≤ C *
      (eLpNorm (p - q) (2 ) ).toReal *
      (eLpNorm q (2 ) ).toReal by
          calc
            _ ≤ 1 / 2 * C *
                (Real.sqrt (∫ y, (q y - p y) ^ 2) *
                    Real.sqrt (∫ y, q y ^ 2) +
                  Real.sqrt (∫ y, p y ^ 2) *
                    Real.sqrt (∫ y, (q y - p y) ^ 2)) := hqp
            _ ≤ _ := by
              rw [hqpReal, sqrt_integral_sq_eq_eLpNorm_toReal q hq,
                sqrt_integral_sq_eq_eLpNorm_toReal p hp]
              have hpReal := ENNReal.toReal_mono hq.eLpNorm_ne_top hpNorm
              have hpReal' := mul_le_mul_of_nonneg_right hpReal
                (show 0 ≤ (eLpNorm (p - q) (2 ) ).toReal from ENNReal.toReal_nonneg)
              have hpReal'' := mul_le_mul_of_nonneg_left hpReal' hC
              nlinarith).trans_lt (by
          rw [Metric.mem_ball, Real.dist_eq] at hδErr
          simpa only [p, sub_zero, abs_of_nonneg
            (mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)] using hδErr)
      · exact hεp
      · exact hδR
    _ = η := by ring

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
