module

public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
import PDEFoundation.Measure.Jensen
import PDEFoundation.Sobolev.W1p.ConvexApprox.SmoothRepresentative
import PDEFoundation.Measure.ConvolutionContraction

/-!
# Strong convergence of parabolic mollification

This module proves the finite-exponent approximate-identity theorem for the
right convolution fixed by `WeakJetMollifier`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise Topology

section
variable {d : Nat}

theorem parabolicConvolution_eq_leftConvolution
    (f rho : TimeVelocity d → Real) :
    parabolicConvolution f rho =
      rho ⋆[ContinuousLinearMap.lsmul Real Real,
        (volume : Measure (TimeVelocity d))] f := by
  rw [← convolution_flip]
  ext z
  simp only [parabolicConvolution, convolution_def]
  apply integral_congr_ae
  filter_upwards with y
  exact mul_comm _ _

/-- Normalized nonnegative right convolution is contractive in every finite
`Lᵖ` exponent on time--velocity product volume. -/
theorem eLpNorm_parabolicConvolution_le_of_nonneg_integral_one {rho g : TimeVelocity d → Real} {p : ENNReal}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hrhoNonneg : ∀ x, 0 ≤ rho x)
    (hrhoInt : Integrable rho volume)
    (hrhoOne : ∫ x, rho x = 1)
    (hrhoMeas : Measurable rho)
    (hgMeas : AEMeasurable g volume) :
    eLpNorm (parabolicConvolution g rho) p volume ≤ eLpNorm g p volume := by
  rw [parabolicConvolution_eq_leftConvolution]
  exact PDE.eLpNorm_convolution_le_of_integral_one hpOne hpTop hrhoNonneg hrhoInt hrhoOne
    hrhoMeas hgMeas

/-- Every fixed normalized parabolic mollification of an `Lᵖ` function is in
the same finite-exponent `Lᵖ` space. -/
theorem memLp_parabolicConvolution_parabolicMollifier {p : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (TimeVelocity d))) (n : Nat) :
    MemLp (parabolicConvolution f (parabolicMollifier d n)) p
      (volume : Measure (TimeVelocity d)) := by
  exact (eLpNorm_parabolicConvolution_le_of_nonneg_integral_one hpOne hpTop
      (parabolicMollifier_nonneg d n)
      ((contDiff_parabolicMollifier d n).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_parabolicMollifier d n))
      (integral_parabolicMollifier d n)
      (contDiff_parabolicMollifier d n).continuous.measurable
      hf.aemeasurable).trans_lt hf.eLpNorm_lt_top

private theorem tendsto_eLpNorm_parabolicConvolution_sub_of_contDiff_hasCompactSupport {p : ENNReal} {g : TimeVelocity d → Real}
    (hpTop : p ≠ ∞) (hgCompact : HasCompactSupport g)
    (hg : ContDiff Real (⊤ : ℕ∞) g) :
    Tendsto (fun n : Nat =>
      eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z)
        p volume) atTop (nhds 0) := by
  let s : Set (TimeVelocity d) :=
    tsupport g + Metric.closedBall (0 : TimeVelocity d) (1 : Real)
  have hsCompact : IsCompact s :=
    hgCompact.isCompact.add (isCompact_closedBall (0 : TimeVelocity d) (1 : Real))
  have hsMeas : MeasurableSet s := hsCompact.measurableSet
  have hsFinite : (volume : Measure (TimeVelocity d)) s ≠ ∞ :=
    hsCompact.measure_lt_top.ne
  have hpowTop : (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) ≠ ∞ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hsFinite).ne
  let c : Real := ((volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal)).toReal
  have hcNonneg : 0 ≤ c := ENNReal.toReal_nonneg
  have hpow : ENNReal.ofReal c = (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := by
    dsimp only [c]
    exact ENNReal.ofReal_toReal hpowTop
  have hgUniform : UniformContinuous g :=
    hg.continuous.uniformContinuous_of_tendsto_cocompact hgCompact.is_zero_at_infty
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  by_cases hetaTop : eta = ∞
  · exact Eventually.of_forall fun n => by simp [hetaTop]
  let delta : Real := eta.toReal / (c + 1)
  have hetaReal : 0 < eta.toReal := ENNReal.toReal_pos heta.ne' hetaTop
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨eps, hepsPos, heps⟩ := (Metric.uniformContinuous_iff.1 hgUniform) delta hdelta
  have hscale : ∀ᶠ n : Nat in atTop, parabolicMollifierScale n < eps :=
    (tendsto_order.1 tendsto_parabolicMollifierScale_zero).2 eps hepsPos
  filter_upwards [hscale] with n hn
  have hball : ∀ z x, x ∈ Metric.ball z (parabolicMollifierBump d n).rOut →
      dist (g x) (g z) ≤ delta := by
    intro z x hx
    apply (heps (a := x) (b := z) ?_).le
    simpa only [dist_comm, parabolicMollifierBump_rOut] using lt_trans hx hn
  have hpoint : ∀ z,
      dist (parabolicConvolution g (parabolicMollifier d n) z) (g z) ≤ delta := by
    intro z
    rw [parabolicConvolution_eq_leftConvolution]
    exact ContDiffBump.dist_normed_convolution_le
      (φ := parabolicMollifierBump d n) hg.continuous.aestronglyMeasurable (hball z)
  have hsupportKernel : Function.support (parabolicMollifier d n) ⊆
      Metric.closedBall (0 : TimeVelocity d) (1 : Real) := by
    rw [support_parabolicMollifier]
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by simpa using parabolicMollifierScale_le_one n)))
  have hsupportConv : Function.support
      (parabolicConvolution g (parabolicMollifier d n)) ⊆ s := by
    rw [show parabolicConvolution g (parabolicMollifier d n) =
        g ⋆[ContinuousLinearMap.mul Real Real, volume] (parabolicMollifier d n) by rfl]
    exact (support_convolution_subset (ContinuousLinearMap.mul Real Real)).trans
      (add_subset_add (subset_tsupport g) hsupportKernel)
  have hsupportG : Function.support g ⊆ s := by
    intro z hz
    exact ⟨z, subset_tsupport g hz, 0,
      Metric.mem_closedBall_self (by norm_num), by simp⟩
  have hnorm :
      eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤
        ENNReal.ofReal delta * (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := by
    exact eLpNorm_sub_le_of_dist_bdd volume hpTop hsMeas.nullMeasurableSet hdelta.le
      (((contDiff_parabolicConvolution
        (hg.continuous.locallyIntegrable)
        (contDiff_parabolicMollifier d n)
        (hasCompactSupport_parabolicMollifier d n)).continuous.sub
        hg.continuous).aestronglyMeasurable) hpoint hsupportConv hsupportG
  have hdeltaMul : delta * c ≤ eta.toReal := by
    have hfrac : c / (c + 1) ≤ 1 := by
      have hc : c ≤ c + 1 := by linarith
      have hdenom : 0 ≤ c + 1 := by linarith
      simpa only using div_le_one_of_le₀ hc hdenom
    calc
      delta * c = eta.toReal * (c / (c + 1)) := by
        dsimp [delta]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ ≤ eta.toReal * 1 := mul_le_mul_of_nonneg_left hfrac hetaReal.le
      _ = eta.toReal := by ring
  calc
    eLpNorm (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤
        ENNReal.ofReal delta * (volume : Measure (TimeVelocity d)) s ^ (1 / p.toReal) := hnorm
    _ = ENNReal.ofReal (delta * c) := by
      rw [← hpow, ← ENNReal.ofReal_mul]
      exact hdelta.le
    _ ≤ eta := by
      rw [← ENNReal.ofReal_toReal hetaTop]
      exact ENNReal.ofReal_le_ofReal hdeltaMul

private theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_le {p eps : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞) (hf : MemLp f p volume)
    (heps : eps ≠ 0) :
    ∃ g : TimeVelocity d → Real, HasCompactSupport g ∧ ContDiff Real (⊤ : ℕ∞) g ∧
      eLpNorm (f - g) p volume ≤ eps := by
  by_cases hepsTop : eps = ∞
  · refine ⟨0, HasCompactSupport.zero, contDiff_const, ?_⟩
    rw [hepsTop]
    exact le_top
  let r := eps.toReal / 2
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (ENNReal.toReal_pos heps hepsTop) (by norm_num)
  obtain ⟨g, hgCompact, hgSmooth, hg⟩ := hf.exist_eLpNorm_sub_le hpTop hpOne hr
  refine ⟨g, hgCompact, hgSmooth, hg.trans ?_⟩
  rw [show eps = ENNReal.ofReal eps.toReal by
    exact (ENNReal.ofReal_toReal hepsTop).symm]
  apply ENNReal.ofReal_le_ofReal
  dsimp [r]
  exact half_le_self ENNReal.toReal_nonneg

/-- Strong finite-exponent convergence for the right parabolic
convolution against the actual normalized shrinking mollifier sequence. -/
theorem tendsto_eLpNorm_parabolicConvolution_sub {p : ENNReal} {f : TimeVelocity d → Real}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (TimeVelocity d))) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution f (parabolicMollifier d n) z - f z)
      p (volume : Measure (TimeVelocity d))) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro eta heta
  by_cases hetaTop : eta = ∞
  · exact Eventually.of_forall fun n => by simp [hetaTop]
  obtain ⟨eta1, heta1Pos, heta1⟩ :=
    exists_Lp_half (μ := (volume : Measure (TimeVelocity d))) (ε := Real) (p := p) heta.ne'
  obtain ⟨eta2, heta2Pos, heta2⟩ :=
    exists_Lp_half (μ := (volume : Measure (TimeVelocity d))) (ε := Real) (p := p) heta1Pos.ne'
  let eps : ENNReal := min eta1 eta2
  have hepsPos : 0 < eps := lt_min heta1Pos heta2Pos
  obtain ⟨g, hgCompact, hgSmooth, hfg⟩ :=
    exists_contDiff_hasCompactSupport_eLpNorm_sub_le hpOne hpTop hf hepsPos.ne'
  have hgMem : MemLp g p volume :=
    hgSmooth.continuous.memLp_of_hasCompactSupport hgCompact
  have hdiffMem : MemLp (f - g) p volume := hf.sub hgMem
  have hkernelCont (n : Nat) : Continuous (parabolicMollifier d n) :=
    (contDiff_parabolicMollifier d n).continuous
  have hdiffLoc : LocallyIntegrable (f - g) volume := hdiffMem.locallyIntegrable hpOne
  have hgLoc : LocallyIntegrable g volume := hgMem.locallyIntegrable hpOne
  have hlin (n : Nat) :
      parabolicConvolution ((f - g) + g) (parabolicMollifier d n) =
        parabolicConvolution (f - g) (parabolicMollifier d n) +
          parabolicConvolution g (parabolicMollifier d n) := by
    apply ConvolutionExists.add_distrib
    · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
        (ContinuousLinearMap.mul Real Real) hdiffLoc (hkernelCont n)
    · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
        (ContinuousLinearMap.mul Real Real) hgLoc (hkernelCont n)
  have hident (n : Nat) :
      (fun z => parabolicConvolution f (parabolicMollifier d n) z -
        parabolicConvolution g (parabolicMollifier d n) z) =
        parabolicConvolution (f - g) (parabolicMollifier d n) := by
    funext z
    have hz := congrFun (hlin n) z
    dsimp only [Pi.add_apply] at hz
    have hsum : (f - g) + g = f := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    rw [hsum] at hz
    linarith
  have hmiddleTendsto :=
    tendsto_eLpNorm_parabolicConvolution_sub_of_contDiff_hasCompactSupport
      (d := d) (p := p) hpTop hgCompact hgSmooth
  have hfirstEventually : ∀ᶠ n : Nat in atTop, eLpNorm
      (fun z => parabolicConvolution f (parabolicMollifier d n) z -
        parabolicConvolution g (parabolicMollifier d n) z) p volume ≤ eta1 :=
    Filter.Eventually.of_forall fun n => by
      rw [hident n]
      exact (eLpNorm_parabolicConvolution_le_of_nonneg_integral_one hpOne hpTop
        (parabolicMollifier_nonneg d n)
        ((contDiff_parabolicMollifier d n).continuous.integrable_of_hasCompactSupport
          (hasCompactSupport_parabolicMollifier d n))
        (integral_parabolicMollifier d n)
        ((contDiff_parabolicMollifier d n).continuous.measurable)
        hdiffMem.aestronglyMeasurable.aemeasurable).trans
          (hfg.trans (min_le_left _ _))
  have hmiddleEventually : ∀ᶠ n : Nat in atTop, eLpNorm
      (fun z => parabolicConvolution g (parabolicMollifier d n) z - g z) p volume ≤ eta2 :=
    ENNReal.tendsto_nhds_zero.1 hmiddleTendsto eta2 heta2Pos
  filter_upwards [hfirstEventually, hmiddleEventually] with n hfirst hmiddle
  let a : TimeVelocity d → Real := fun z =>
    parabolicConvolution f (parabolicMollifier d n) z -
      parabolicConvolution g (parabolicMollifier d n) z
  let b : TimeVelocity d → Real := fun z =>
    (parabolicConvolution g (parabolicMollifier d n) z - g z) + (g z - f z)
  have hthird : eLpNorm (fun z => g z - f z) p volume ≤ eta2 := by
    change eLpNorm (g - f) p volume ≤ eta2
    rw [eLpNorm_sub_comm]
    exact hfg.trans (min_le_right _ _)
  have hcombo : eLpNorm b p volume < eta1 := by
    exact heta2 _ _ hmiddle hthird
  have hsum : eLpNorm (a + b) p volume < eta := heta1 _ _ hfirst hcombo.le

  have hdecomp :
      (fun z => parabolicConvolution f (parabolicMollifier d n) z - f z) = a + b := by
    funext z
    dsimp [a, b, Pi.add_apply]
    ring
  rw [hdecomp]
  exact hsum.le

end

namespace ParabolicW12Function

section
variable {d : Nat} {p : ENNReal} (w : ParabolicW12Function d Set.univ p) (hpOne : 1 ≤ p)
  (hpTop : p ≠ ∞)
include hpOne hpTop

/-- The stored value representative converges strongly under parabolic
mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_toFun_sub :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution w.toFun (parabolicMollifier d n) z - w.toFun z)
      p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.memLp
      change MemLp w.toFun p ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- The stored time-derivative representative converges strongly under
parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_timeDeriv_sub :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution w.timeDeriv (parabolicMollifier d n) z - w.timeDeriv z)
      p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.timeDeriv_memLp
      change MemLp w.timeDeriv p ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- Each stored velocity-gradient representative converges strongly under
parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_velocityGrad_sub (i : Fin d) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution (fun y => w.velocityGrad y i)
        (parabolicMollifier d n) z - w.velocityGrad z i) p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.velocityGrad_memLp i
      change MemLp (fun z => w.velocityGrad z i) p
        ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

/-- Each stored ordered velocity-Hessian representative converges strongly
under parabolic mollification at every finite exponent. -/
theorem tendsto_eLpNorm_convolution_velocityHessian_sub (i j : Fin d) :
    Tendsto (fun n : Nat => eLpNorm
      (fun z => parabolicConvolution (fun y => w.velocityHessian y i j)
        (parabolicMollifier d n) z - w.velocityHessian z i j) p volume) atTop (nhds 0) :=
  tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop <|
    by
      have h := w.velocityHessian_memLp i j
      change MemLp (fun z => w.velocityHessian z i j) p
        ((volume : Measure (TimeVelocity d)).restrict Set.univ) at h
      simpa only [Measure.restrict_univ] using h

end

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
