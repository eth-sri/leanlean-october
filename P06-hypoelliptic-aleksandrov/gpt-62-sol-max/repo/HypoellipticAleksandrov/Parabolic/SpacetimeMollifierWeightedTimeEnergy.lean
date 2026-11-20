module

public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Weighted time energy for spacetime mollification

This module develops the kernel-derivative facts used to prove the weighted
time-energy limit for the fixed spacetime mollifier.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped Convolution ENNReal NNReal Topology
open HypoellipticAleksandrov.Parabolic.SpacetimeMollifier

namespace HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy

section
variable {d : ℕ}

private def norm₂ (f : TimeVelocity d → ℝ) : ℝ :=
  (eLpNorm f 2 volume).toReal

private theorem timeDerivative_spacetimeMollifier {ε : ℝ} (hε : 0 < ε) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) z =
      (((∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(volume : Measure (TimeVelocity d))) *
          ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹) * ε⁻¹ *
        fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
          (ε⁻¹ • z) (1, 0) := by
  unfold timeDerivative spacetimeMollifier
  rw [abs_of_nonneg hε.le, fderiv_const_mul, fderiv_comp_smul]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc]
  · exact ((ExistsContDiffBumpBase.u_smooth (TimeVelocity d)).differentiable
      (by simp)).comp (differentiable_id.const_smul (ε⁻¹ : ℝ)) z

private theorem timeDerivative_spacetimeMollifier_neg (ε : ℝ) (z : TimeVelocity d) :
    timeDerivative (spacetimeMollifier ε) (-z) =
      -timeDerivative (spacetimeMollifier ε) z := by
  have heq : (fun y : TimeVelocity d => spacetimeMollifier ε ((-1 : ℝ) • y)) =
      spacetimeMollifier ε := funext fun y => by simpa using spacetimeMollifier_neg ε y
  have h := fderiv_comp_smul (f := (spacetimeMollifier ε : TimeVelocity d → ℝ)) (x := z) (-1 : ℝ)
  rw [heq, neg_one_smul, neg_one_smul] at h
  unfold timeDerivative
  simpa only [ContinuousLinearMap.neg_apply, neg_neg] using
    (congrArg (fun L : TimeVelocity d →L[ℝ] ℝ => -L (1, 0)) h).symm

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε

private theorem integrable_timeDerivative_spacetimeMollifier :
    Integrable (timeDerivative (spacetimeMollifier (d := d) ε))
      (volume : Measure (TimeVelocity d)) := 
  (timeDerivative_continuous (spacetimeMollifier_contDiff ε)).integrable_of_hasCompactSupport
    (timeDerivative_compact (spacetimeMollifier_hasCompactSupport hε))

private theorem integral_norm_mul_abs_timeDerivative_spacetimeMollifier :
    (∫ z : TimeVelocity d,
        ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
        ∂(volume : Measure (TimeVelocity d))) =
      (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
          ∂(volume : Measure (TimeVelocity d)))⁻¹ *
        ∫ y : TimeVelocity d, ‖y‖ *
          |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
            y (1, 0)| ∂(volume : Measure (TimeVelocity d)) := by
  let A : ℝ := ∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
    ∂(volume : Measure (TimeVelocity d))
  let g : TimeVelocity d → ℝ := fun y =>
    ‖y‖ * |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ) y (1, 0)|
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
    (volume : Measure (TimeVelocity d)) g hε.le]
  change ((A * ε ^ Module.finrank ℝ (TimeVelocity d))⁻¹ * ε⁻¹ * ε) *
      (ε ^ Module.finrank ℝ (TimeVelocity d) * ∫ y, g y ∂volume) =
    A⁻¹ * ∫ y, g y ∂volume
  field_simp

end

end

private theorem exists_uniform_firstMoment_timeDerivative_spacetimeMollifier
    (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      (∫ z : TimeVelocity d,
          ‖z‖ * |timeDerivative (spacetimeMollifier ε) z|
          ∂(volume : Measure (TimeVelocity d))) ≤ C := by
  let C :=
    (∫ x : TimeVelocity d, ExistsContDiffBumpBase.u x
        ∂(volume : Measure (TimeVelocity d)))⁻¹ *
      ∫ y : TimeVelocity d, ‖y‖ *
        |fderiv ℝ (ExistsContDiffBumpBase.u : TimeVelocity d → ℝ)
          y (1, 0)| ∂(volume : Measure (TimeVelocity d))
  refine ⟨C, mul_nonneg (inv_nonneg.mpr (_root_.HypoellipticAleksandrov.Parabolic.SpacetimeMollifier.bump_volume_integral_pos d).le)
    (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)), ?_⟩
  intro ε hε
  exact (integral_norm_mul_abs_timeDerivative_spacetimeMollifier hε).le

section
variable {d : ℕ}

private theorem timeDerivative_spacetimeMollification {ε : ℝ} (hε : 0 < ε)
    (f : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (z : TimeVelocity d) :
    timeDerivative (spacetimeMollification ε f) z =
      ∫ x : TimeVelocity d,
        timeDerivative (spacetimeMollifier ε) x * f (z - x)
        ∂(volume : Measure (TimeVelocity d)) := by
  have hk := spacetimeMollifier_hasCompactSupport (d := d) hε
  have hs := spacetimeMollifier_contDiff (d := d) ε
  have hf := hf.locallyIntegrable (by norm_num)
  have hderiv := hk.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hs.of_le (by simp)) hf z
  unfold timeDerivative spacetimeMollification
  rw [hderiv.fderiv]
  have hconv := (hk.fderiv ℝ).convolutionExists_left
    (ContinuousLinearMap.precompL (TimeVelocity d) (ContinuousLinearMap.lsmul ℝ ℝ))
    (hs.continuous_fderiv (by simp)) hf z
  exact ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : TimeVelocity d)).integral_comp_comm hconv).symm

private theorem integrable_kernel_mul_memLp_two_mul_translate (k f g : TimeVelocity d → ℝ)
    (hk : Integrable k (volume : Measure (TimeVelocity d)))
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Integrable
      (fun p : TimeVelocity d × TimeVelocity d =>
        k p.1 * f p.2 * g (p.2 - p.1))
      ((volume : Measure (TimeVelocity d)).prod volume) := by
  let μ : Measure (TimeVelocity d) := volume
  have hsub := measurePreserving_prod_sub μ μ
  refine ((hk.abs.mul_prod hf.integrable_sq).add
    (hsub.integrable_comp_of_integrable (hk.abs.mul_prod hg.integrable_sq))).mono' ?_ ?_
  · exact (hk.1.comp_fst.mul hf.aestronglyMeasurable.comp_snd).mul
      (hg.aestronglyMeasurable.comp_snd.comp_measurePreserving hsub)
  · refine ae_of_all _ fun p => ?_
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul, Pi.add_apply]
    have h : |f p.2| * |g (p.2 - p.1)| ≤ f p.2 ^ 2 + g (p.2 - p.1) ^ 2 := by
      nlinarith only [sq_nonneg (|f p.2| - |g (p.2 - p.1)|),
        sq_abs (f p.2), sq_abs (g (p.2 - p.1)), sq_nonneg (f p.2), sq_nonneg (g (p.2 - p.1))]
    simpa only [mul_add, mul_assoc] using mul_le_mul_of_nonneg_left h (abs_nonneg (k p.1))

private theorem integrable_kernel_mul_memLp_two_mul_add {k f g : TimeVelocity d → ℝ} (hk : Integrable k)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun p : TimeVelocity d × TimeVelocity d => k p.1 * f p.2 * g (p.2 + p.1))
      (volume.prod volume) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure (TimeVelocity d))).prod
    (MeasurePreserving.id (volume : Measure (TimeVelocity d)))).integrable_comp_of_integrable
      (integrable_kernel_mul_memLp_two_mul_translate _ f g hk.comp_neg hf hg)
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, neg_neg, sub_neg_eq_add] using h

section
variable (ε : ℝ) (w f g : TimeVelocity d → ℝ)
include ε w f g

private def symmetrizedIntegrand (p : TimeVelocity d × TimeVelocity d) : ℝ :=
  timeDerivative (spacetimeMollifier ε) p.1 * (w p.2 - w (p.2 + p.1)) * f p.2 * g (p.2 + p.1)

private def symmetrizedBilinear : ℝ :=
  ∫ p, symmetrizedIntegrand ε w f g p ∂(volume.prod volume)

end

section
variable {ε : ℝ} (hε : 0 < ε)
include hε

private theorem integrable_symmetrizedIntegrand {w f g : TimeVelocity d → ℝ}
    (hw : MemLp w ∞ volume) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (symmetrizedIntegrand ε w f g) (volume.prod volume) := by
  have hk := integrable_timeDerivative_spacetimeMollifier (d := d) hε
  refine ((integrable_kernel_mul_memLp_two_mul_add hk (hw.mul' hf) hg).sub
    (integrable_kernel_mul_memLp_two_mul_add hk hf (hw.mul' hg))).congr (ae_of_all _ fun p => ?_)
  unfold symmetrizedIntegrand
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

private theorem pairing_eq_half_symmetrized (q w : TimeVelocity d → ℝ)
    (hq : MemLp q 2 volume) (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    (∫ z, q z * timeDerivative (spacetimeMollification ε (w * q)) z ∂volume) =
      (1 / 2 : ℝ) * symmetrizedBilinear ε w q q := by
  let k : TimeVelocity d → ℝ := timeDerivative (spacetimeMollifier ε)
  let F : TimeVelocity d × TimeVelocity d → ℝ := fun p => k p.1 * q p.2 * (w * q) (p.2 - p.1)
  let μ : Measure (TimeVelocity d) := volume
  have hwq : MemLp (w * q) 2 volume := (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact (p := ∞)).mul' hq
  have hF : Integrable F (μ.prod μ) := integrable_kernel_mul_memLp_two_mul_translate k q (w * q)
    (integrable_timeDerivative_spacetimeMollifier hε) hq hwq
  have hp : (∫ z, q z * timeDerivative (spacetimeMollification ε (w * q)) z ∂volume) =
      ∫ p, F p ∂(μ.prod μ) := by
    rw [integral_prod_symm _ hF]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    change q z * timeDerivative (spacetimeMollification ε (w * q)) z = _
    rw [timeDerivative_spacetimeMollification hε _ hwq, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [F, k, Pi.mul_apply]; ring)
  let T := MeasurableEquiv.shearAddRight (TimeVelocity d)
  let N := (MeasurableEquiv.neg (TimeVelocity d)).prodCongr (MeasurableEquiv.refl (TimeVelocity d))
  have hT : MeasurePreserving T (μ.prod μ) (μ.prod μ) := measurePreserving_prod_add μ μ
  have hN : MeasurePreserving N (μ.prod μ) (μ.prod μ) :=
    (Measure.measurePreserving_neg μ).prod (MeasurePreserving.id μ)
  have hsym : symmetrizedIntegrand ε w q q = (F ∘ T) + (F ∘ N) := by
    funext p
    have hTapp : T p = (p.1, p.1 + p.2) := rfl
    have hNapp : N p = (-p.1, p.2) := rfl
    unfold symmetrizedIntegrand
    simp only [Pi.add_apply, Function.comp_apply, hTapp, hNapp, F, k, Pi.mul_apply,
      add_sub_cancel_left, sub_neg_eq_add, timeDerivative_spacetimeMollifier_neg]
    rw [add_comm p.1 p.2]
    ring
  rw [hp, symmetrizedBilinear, hsym, integral_add' (hT.integrable_comp_of_integrable hF)
    (hN.integrable_comp_of_integrable hF)]
  simp only [Function.comp_def, hT.integral_comp' F, hN.integral_comp' F]
  ring

end

private theorem abs_integral_symmetrized_inner_le {K : ℝ≥0} {w : TimeVelocity d → ℝ} (hw : LipschitzWith K w)
    (x : TimeVelocity d) (k : ℝ) {f g : TimeVelocity d → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ y, k * (w y - w (y + x)) * f y * g (y + x) ∂volume| ≤
      (|k| * (K : ℝ) * ‖x‖) * norm₂ f * norm₂ g := by
  have hshift := measurePreserving_add_right (volume : Measure (TimeVelocity d)) x
  have hgt := hg.comp_measurePreserving hshift
  have hn := Analysis.abs_integral_weighted_mul_le_L2
    (C := |k| * (K : ℝ) * ‖x‖) (q := fun y => k * (w y - w (y + x))) (by positivity)
    (ae_of_all _ fun y => by
      rw [abs_mul]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
      simpa [Real.norm_eq_abs] using hw.norm_sub_le y (y + x))
    hf.coeFn_toLp.symm hgt.coeFn_toLp.symm
  simpa only [Lp.norm_toLp, norm₂, Function.comp_apply, eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hshift]
    using hn

private theorem integrable_norm_mul_abs_timeDerivative_spacetimeMollifier {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : TimeVelocity d =>
      ‖x‖ * |timeDerivative (spacetimeMollifier ε) x|)
      (volume : Measure (TimeVelocity d)) := 
  (continuous_norm.mul (timeDerivative_continuous (spacetimeMollifier_contDiff ε)).abs).integrable_of_hasCompactSupport
    (timeDerivative_compact (spacetimeMollifier_hasCompactSupport hε)).abs.mul_left

private theorem exists_uniform_symmetrized_bilinear_bound (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w) (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ {f g : TimeVelocity d → ℝ}, MemLp f 2 volume → MemLp g 2 volume →
      |symmetrizedBilinear ε w f g| ≤ C * (norm₂ f * norm₂ g) := by
  obtain ⟨K, hw⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hwCompact hwSmooth (by simp)
  obtain ⟨M, hM, hmoment⟩ := exists_uniform_firstMoment_timeDerivative_spacetimeMollifier d
  refine ⟨(K : ℝ) * M, by positivity, ?_⟩
  intro ε hε f g hf hg
  rw [symmetrizedBilinear, integral_prod _ (integrable_symmetrizedIntegrand hε
    (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact) hf hg), ← Real.norm_eq_abs]
  let D := (K : ℝ) * (norm₂ f * norm₂ g)
  have hD : 0 ≤ D := by unfold D norm₂; positivity
  refine (norm_integral_le_of_norm_le
    ((integrable_norm_mul_abs_timeDerivative_spacetimeMollifier hε).const_mul D)
    (ae_of_all _ fun x => ?_)).trans ?_
  · simpa only [symmetrizedIntegrand, Real.norm_eq_abs, D, mul_assoc, mul_left_comm, mul_comm] using
      abs_integral_symmetrized_inner_le hw x (timeDerivative (spacetimeMollifier ε) x) hf hg
  · rw [integral_const_mul]
    simpa only [D, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left (hmoment hε) hD

private theorem symmetrizedBilinear_quadratic_sub {ε : ℝ} (hε : 0 < ε)
    (w q p : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hp : MemLp p (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    symmetrizedBilinear ε w q q - symmetrizedBilinear ε w p p =
      symmetrizedBilinear ε w (q - p) q +
        symmetrizedBilinear ε w p (q - p) := by
  have hint {f g : TimeVelocity d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :=
    integrable_symmetrizedIntegrand hε (hwSmooth.continuous.memLp_of_hasCompactSupport hwCompact) hf hg
  have hqp := hq.sub hp
  unfold symmetrizedBilinear
  rw [← integral_sub (hint hq hq) (hint hp hp), ← integral_add (hint hqp hq) (hint hp hqp)]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [symmetrizedIntegrand, Pi.sub_apply]; ring)

private def weightedPair (w q : TimeVelocity d → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, q z * timeDerivative (spacetimeMollification ε (w * q)) z ∂volume

private theorem exists_uniform_pairing_quadratic_continuity (w : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w) (hwCompact : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε →
      ∀ {q p : TimeVelocity d → ℝ}, MemLp q 2 volume → MemLp p 2 volume →
      norm₂ p ≤ norm₂ q → |weightedPair w q ε - weightedPair w p ε| ≤
        C * norm₂ (p - q) * norm₂ q := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_symmetrized_bilinear_bound w hwSmooth hwCompact
  refine ⟨C, hC, ?_⟩
  intro ε hε q p hq hp hnorm
  unfold weightedPair
  rw [pairing_eq_half_symmetrized hε q w hq hwSmooth hwCompact,
    pairing_eq_half_symmetrized hε p w hp hwSmooth hwCompact, ← mul_sub,
    symmetrizedBilinear_quadratic_sub hε w q p hwSmooth hwCompact hq hp,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hd : norm₂ (q - p) = norm₂ (p - q) := by unfold norm₂; rw [← eLpNorm_neg, neg_sub]
  have h₁ := hbound hε (hq.sub hp) hq
  have h₂ := hbound hε hp (hq.sub hp)
  have h₃ := abs_add_le (symmetrizedBilinear ε w (q - p) q) (symmetrizedBilinear ε w p (q - p))
  have h₄ := mul_le_mul_of_nonneg_right hnorm (show 0 ≤ C * norm₂ (p - q) by unfold norm₂; positivity)
  rw [hd] at h₁ h₂
  nlinarith only [h₁, h₂, h₃, h₄]

private theorem timeDerivative_mul (f g : TimeVelocity d → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : TimeVelocity d) :
    timeDerivative (fun y => f y * g y) z =
      timeDerivative f z * g z + f z * timeDerivative g z := by
  unfold timeDerivative
  change (fderiv ℝ (f * g) z) (1, 0) = _
  rw [fderiv_mul (hf z) (hg z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem tendsto_smooth_pairing_to_half (p w : TimeVelocity d → ℝ)
    (hpSmooth : ContDiff ℝ (⊤ : ℕ∞) p) (hp : MemLp p 2 volume)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w) (hwCompact : HasCompactSupport w) :
    Tendsto (weightedPair w p) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * ∫ z, timeDerivative w z * p z ^ 2 ∂volume)) := by
  let f := w * p
  let df := timeDerivative f
  have hs : ContDiff ℝ (⊤ : ℕ∞) f := hwSmooth.mul hpSmooth
  have hK : HasCompactSupport f := hwCompact.mul_right
  have hf : MemLp f 2 volume := hs.continuous.memLp_of_hasCompactSupport hK
  have hd := timeDerivative_continuous hs
  have hk := timeDerivative_compact hK
  have hdf : MemLp df 2 volume := hd.memLp_of_hasCompactSupport hk
  have hleft : Integrable (fun z => df z * p z) volume := hdf.integrable_mul hp
  have hright : Integrable (fun z => f z * timeDerivative p z) volume :=
    (hs.continuous.mul (timeDerivative_continuous hpSmooth)).integrable_of_hasCompactSupport hK.mul_right
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (TimeVelocity d))) (v := (1, 0)) hleft hright (hf.integrable_mul hp)
    (fun z _ => hs.differentiable (by simp) z) (fun z _ => hpSmooth.differentiable (by simp) z)
  have hsplit : (∫ z, df z * p z - f z * timeDerivative p z ∂volume) =
      ∫ z, timeDerivative w z * p z ^ 2 ∂volume := by
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change timeDerivative (fun z => w z * p z) z * p z - w z * p z * timeDerivative p z = _
      rw [timeDerivative_mul w p (hwSmooth.differentiable (by simp)) (hpSmooth.differentiable (by simp))]
      ring
  rw [integral_sub hleft hright] at hsplit
  change (∫ z, f z * timeDerivative p z ∂volume) = -(∫ z, df z * p z ∂volume) at hibp
  have heq : (1 / 2 : ℝ) * (∫ z, timeDerivative w z * p z ^ 2 ∂volume) =
      ∫ z, p z * df z ∂volume := by
    simp_rw [mul_comm (p _)]
    linarith only [hibp, hsplit]
  rw [heq]
  have hweak : HasWeakTimeDerivOn Set.univ f df :=
    HypoellipticAleksandrov.Parabolic.contDiffOn_one_hasWeakTimeDerivOn
      Set.univ isOpen_univ f ((hs.of_le (by norm_num)).contDiffOn)
  apply ((Analysis.StrongL2Limit.const hp).pairing
    (SpacetimeMollifierL2.spacetimeMollification_strongL2 hdf)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold weightedPair
  rw [SpacetimeMollifier.timeDerivative_spacetimeMollification hε f df
    (hf.locallyIntegrable (by norm_num)) (hdf.locallyIntegrable (by norm_num)) hweak]

private theorem tendsto_weighted_sq_integral (w q : TimeVelocity d → ℝ)
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w)
    (hq : MemLp q (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Tendsto (fun δ : ℝ => ∫ z : TimeVelocity d,
      timeDerivative w z * spacetimeMollification δ q z ^ 2 ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, timeDerivative w z * q z ^ 2 ∂volume)) := by
  have hc := (timeDerivative_continuous hwSmooth).memLp_of_hasCompactSupport
    (timeDerivative_compact hwCompact) (μ := volume) (p := ∞)
  have h := SpacetimeMollifierL2.spacetimeMollification_strongL2 hq
  simpa only [pow_two, mul_assoc] using (h.weight hc).pairing h

/-- Weighted time-energy limit for raw global `L²` data. -/
theorem tendsto_integral_mul_timeDerivative_spacetimeMollification_mul (q w : TimeVelocity d → ℝ)
    (hq : MemLp q (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwCompact : HasCompactSupport w) :
    Tendsto
      (fun ε : ℝ => ∫ z : TimeVelocity d,
        q z * timeDerivative
          (spacetimeMollification ε (fun y => w y * q y)) z
        ∂(volume : Measure (TimeVelocity d)))
      (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * ∫ z : TimeVelocity d,
        timeDerivative w z * q z ^ 2
        ∂(volume : Measure (TimeVelocity d)))) := by
  let R (f : TimeVelocity d → ℝ) := (1 / 2 : ℝ) * ∫ z, timeDerivative w z * f z ^ 2 ∂volume
  let p (δ : ℝ) := spacetimeMollification δ q
  change Tendsto (weightedPair w q) (𝓝[>] 0) (𝓝 (R q))
  obtain ⟨C, hC, hcont⟩ := exists_uniform_pairing_quadratic_continuity w hwSmooth hwCompact
  have hD : Tendsto (fun δ => norm₂ (p δ - q)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [norm₂, p, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
        (SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub q hq)
  have hErr : Tendsto (fun δ => C * norm₂ (p δ - q) * norm₂ q) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hD).mul tendsto_const_nhds
  have hR : Tendsto (R ∘ p) (𝓝[>] 0) (𝓝 (R q)) :=
    tendsto_const_nhds.mul (tendsto_weighted_sq_integral w q hwSmooth hwCompact hq)
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, C * norm₂ (p δ - q) * norm₂ q < η / 3 :=
    hErr (Iio_mem_nhds hη3)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hδErr, hδR⟩ := (hpos.and (he.and
    ((Metric.tendsto_nhds.mp hR) (η / 3) hη3))).exists
  have hδ' : 0 < δ := hδ
  have hp := SpacetimeMollifierL2.spacetimeMollification_memLp hδ' q hq
  have hpNorm : norm₂ (p δ) ≤ norm₂ q := ENNReal.toReal_mono hq.eLpNorm_ne_top
    (SpacetimeMollifierL2.eLpNorm_spacetimeMollification_le hδ' q hq)
  have hP := tendsto_smooth_pairing_to_half (p δ) w
    (contDiff_spacetimeMollification hδ' q (hq.locallyIntegrable (by norm_num))) hp hwSmooth hwCompact
  filter_upwards [(Metric.tendsto_nhds.mp hP) (η / 3) hη3, self_mem_nhdsWithin] with ε hεp hε
  have hb := hcont hε hq hp hpNorm
  have ht := dist_triangle (weightedPair w q ε) (weightedPair w (p δ) ε) (R q)
  have ht' := dist_triangle (weightedPair w (p δ) ε) (R (p δ)) (R q)
  change C * norm₂ (p δ - q) * norm₂ q < η / 3 at hδErr
  change dist (R (p δ)) (R q) < η / 3 at hδR
  rw [Real.dist_eq (weightedPair w q ε) (weightedPair w (p δ) ε)] at ht
  linarith only [ht, ht', hb, hεp, hδR, hδErr]

end

end HypoellipticAleksandrov.Parabolic.SpacetimeMollifierWeightedTimeEnergy
