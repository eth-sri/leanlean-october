module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.Smooth
public import Mathlib.MeasureTheory.Integral.Prod
public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier

/-!
# Spatial-slice transport for parabolic Poincare

This module identifies the native unit velocity cube with the PDEFoundation
axis cube and proves the private fixed-time gradient-mean affine Poincare
estimate and canonical-projection comparison, then lifts them globally through
the two public spatial inequalities.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocityCube_zero_one_eq_axisCube_neg_one_two (d : Nat) :
    velocityCube (0 : PDE.Vec d) 1 =
      PDE.axisCube (-1 : PDE.Vec d) 2 := by
  ext v
  constructor
  · intro hv i _
    have hvi := hv i
    simp only [Pi.zero_apply, Pi.neg_apply, Pi.one_apply, sub_zero] at hvi ⊢
    grind
  · intro hv i
    have hvi := hv i (Set.mem_univ i)
    simp only [Pi.neg_apply, Pi.one_apply] at hvi
    simp only [Pi.zero_apply, sub_zero]
    grind

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

variable (d : Nat) (u : TimeVelocity d -> Real)

private theorem parabolicExponent_eq_ofReal  :
    parabolicExponent d = ENNReal.ofReal ((d : Real) + 1) := by
  simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
    (ENNReal.ofReal_natCast (d + 1)).symm

private theorem contDiff_velocityGradient_slice
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    ContDiff Real 1 (fun v : PDE.Vec d => velocityGradient u (t, v) i) := (contDiff_pi.mp ((contDiff_velocityGradient hu).comp
    (contDiff_const.prodMk contDiff_id))) i


private theorem classicalGradient_velocityGradient_slice_apply
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (t : Real) (v : PDE.Vec d)
    (i j : Fin d) :
    PDE.classicalGradient
        (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j =
      velocityHessian u (t, v) i j := by
  have hdiff : DifferentiableAt Real (fun z => velocityGradient u z i) _ :=
    ((contDiff_pi.mp (contDiff_velocityGradient hu) i).differentiable
      (by norm_num)) (t, v)
  have hslice := hdiff.hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)
  change (fderiv Real ((fun z => velocityGradient u z i) ∘ Prod.mk t) v)
      _ = velocityHessian u _ i j
  rw [hslice.fderiv]
  calc
    fderiv Real _ _ _ =
        velocityHessian u _ j i :=
      fderiv_velocityGradient_apply hu _
        _ _
    _ = velocityHessian u _ i j := congrFun (congrFun (velocityHessian_isSymm hu _).eq i) j

private theorem velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum
    
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    PDE.eLpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2)
        (parabolicExponent d)
        (fun v => velocityGradient u (t, v) i -
          PDE.integralAverage (PDE.axisCube (-1 : PDE.Vec d) 2)
            (fun w => velocityGradient u (t, w) i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ j : Fin d,
          PDE.eLpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  let p  := (d : Real) + 1
  let V  := PDE.axisCube (-1 : PDE.Vec d) 2
  let g  := fun v => velocityGradient u (t, v) i
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube _ 2)
      (contDiff_velocityGradient_slice hu t i)
  have hp : 1 <= p := by
    grind
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    simp_all
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := PDE.isFiniteMeasure_volumeOn_axisCube _ 2
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp _ (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage
      (PDE.volume_axisCube_pos _ (by norm_num))
      (lt_top_iff_ne_top.mpr
        (PDE.volume_axisCube_ne_top _ 2)))
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => g v - PDE.integralAverage V g := by
    aesop
  have hsubAverageGrad :
      w.subAverage.grad = fun v => PDE.classicalGradient g v := by
    aesop
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => g v - PDE.integralAverage V g) <=
        ENNReal.ofReal (((2)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            (fun v => PDE.classicalGradient g v) := by
    grind
  have hHessianContinuous :
      ∀ j : Fin d, Continuous (fun v => velocityHessian u (t, v) i j) := by
    intro j
    have hContinuous : Continuous
        (fun v => PDE.classicalGradient
          (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j) := by
      simpa only [PDE.classicalGradient_apply] using
        ((contDiff_velocityGradient_slice hu t i).continuous_fderiv
          (by norm_num)).clm_apply continuous_const
    simpa only [classicalGradient_velocityGradient_slice_apply hu] using hContinuous
  let F : PDE.Vec d -> PDE.Vec d :=
    fun v j => velocityHessian u (t, v) i j
  have hGradient :
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) <=
        ∑ j : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityHessian u (t, v) i j) := by
    calc
      PDE.euclideanFieldELpNormOn V _
          _ =
          PDE.euclideanFieldELpNormOn V _ F := by
        apply PDE.euclideanFieldELpNormOn_congr_ae
        filter_upwards with v
        ext j
        exact classicalGradient_velocityGradient_slice_apply hu t v i j
      _ = MeasureTheory.eLpNorm _
          _ _ := rfl
      _ <= MeasureTheory.eLpNorm (fun v => ∑ j : Fin d, |F v j|)
          _ _ := by
        apply MeasureTheory.eLpNorm_mono_ae
          (PDE.continuous_vecEuclideanNorm.comp
            (continuous_pi fun j => hHessianContinuous j)).aestronglyMeasurable
        filter_upwards with v
        have hsumNonneg : 0 <= ∑ j : Fin d, |F v j| :=
          Finset.sum_nonneg fun j _ => abs_nonneg _
        simpa only [Function.comp_def, F, Real.norm_eq_abs,
          abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _),
          abs_of_nonneg hsumNonneg] using
          PDE.vecEuclideanNorm_le_sum_abs _
      _ <= ∑ j : Fin d,
          MeasureTheory.eLpNorm _ _
            _ := by
        rw [← Finset.sum_fn]
        exact MeasureTheory.eLpNorm_sum_le Fact.out
      _ = ∑ j : Fin d,
          PDE.eLpNormOn V _
            _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simpa only [F, PDE.eLpNormOn, Real.norm_eq_abs] using
          (MeasureTheory.eLpNorm_norm
            (μ := PDE.volumeOn V) (p := ENNReal.ofReal p)
            _
            (hHessianContinuous j).aestronglyMeasurable)
  rw [parabolicExponent_eq_ofReal]
  simpa only [p, V, g] using
    hPoincare'.trans (mul_le_mul_right hGradient _)

private theorem velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum
    
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => velocityGradient u (t, v) i -
          PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun w => velocityGradient u (t, w) i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  simpa only [velocityCube_zero_one_eq_axisCube_neg_one_two] using
    velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum d u hu t i

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : TimeVelocity d -> Real)

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le
    
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ i : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityGradient u (t, v) i -
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i)) := by
  let p  := (d : Real) + 1
  let V  := PDE.axisCube (-1 : PDE.Vec d) 2
  let V0  := velocityCube (0 : PDE.Vec d) 1
  let m  := fun i => PDE.integralAverage V0
    (fun w => velocityGradient u (t, w) i)
  let a : PDE.Vec d -> Real := fun v => ∑ i : Fin d, m i * v i
  let g  := fun v => u (t, v) - a v
  have huSlice : ContDiff Real 2 (fun v : PDE.Vec d => u (t, v)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff Real 2 a := by
    fun_prop
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube _ 2)
      ((huSlice.sub ha).of_le (by norm_num))
  have hp : 1 <= p := by
    grind
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    simp_all
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := PDE.isFiniteMeasure_volumeOn_axisCube _ 2
  have hVPos : 0 < volume V := PDE.volume_axisCube_pos _ (by norm_num)
  have hVTop : volume V < ⊤ := lt_top_iff_ne_top.mpr
      (PDE.volume_axisCube_ne_top _ 2)
  have hcomponent : ∀ i : Fin d, Integrable (fun v : PDE.Vec d => m i * v i)
      (volume.restrict V0) := by
    intro i
    have hcont : Continuous (fun v : PDE.Vec d => m i * v i) :=
      continuous_const.mul (continuous_apply i)
    let K  := velocityClosedCube (0 : PDE.Vec d) 1
    have hKcompact : IsCompact K :=
      isCompact_velocityClosedCube (0) 1
    have hsubset : V0 ⊆ K := by
      intro v hv
      change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
      change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
      grind
    exact (hcont.continuousOn.integrableOn_compact hKcompact).mono_set hsubset
  have haIntegrable : Integrable a (volume.restrict V0) := by
    fun_prop
  have haAverage : PDE.integralAverage V a = 0 := by
    have hVV : V = V0 := (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    rw [hVV]
    unfold PDE.integralAverage
    rw [show (fun v : PDE.Vec d => ∑ i : Fin d, m i * v i) =
        fun v => ∑ i ∈ (Finset.univ : Finset _), m i * v i by
          simp,
      integral_finset_sum _
        (fun i _ => hcomponent i), Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    calc
      (volume V0).toReal⁻¹ * (m i * ∫ v in V0, v i) =
          m i * ((volume V0).toReal⁻¹ * ∫ v in V0, v i) := by ring
      _ = 0 := by
        rw [← PDE.integralAverage, parabolicMorreyUnitVelocityAverage_eval]
        ring
  have hwIntegrable : Integrable g (volume.restrict V0) := by
    have hw : Integrable g (volume.restrict V) := by
      simpa only [w, g,
        PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_toFun, IntegrableOn] using
        w.integrableOn
    have hVV : V = V0 := (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    simp_all
  have huIntegrable : Integrable (fun v : PDE.Vec d => u (t, v))
      (volume.restrict V0) := by
    have hsum : g + a = fun v => u (t, v) := by
      aesop
    rw [← hsum]
    fun_prop
  have hgAverage : PDE.integralAverage V g = PDE.integralAverage V0
      (fun v => u (t, v)) := by
    have hVV : V = V0 := (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    rw [hVV]
    calc
      PDE.integralAverage V0 _ =
          PDE.integralAverage V0 (fun v => u _) -
            PDE.integralAverage V0 a := by
        unfold PDE.integralAverage
        rw [integral_sub huIntegrable haIntegrable]
        ring
      _ = PDE.integralAverage V0 _ := by
        simp_all
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp _ (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage hVPos hVTop)
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => u (t, v) -
        (PDE.integralAverage V0 (fun z => u (t, z)) + a v) := by
    funext v
    change g v - PDE.integralAverage V g =
      u _ - (PDE.integralAverage V0 _ + a v)
    linarith
  have hgradient : ∀ v : PDE.Vec d, ∀ i : Fin d,
      PDE.classicalGradient g v i = velocityGradient u (t, v) i - m i := by
    intro v i
    rw [PDE.classicalGradient_apply]
    have huDiff  :=
      huSlice.differentiable (by norm_num) v
    have haDiff  := ha.differentiable (by norm_num) v
    rw [show g = (fun z : PDE.Vec d => u _) - a by rfl,
      fderiv_sub huDiff haDiff]
    have hslice := (hu.differentiable (by norm_num) _).hasFDerivAt.comp v
      (hasFDerivAt_prodMk_right t v)
    have huDeriv : fderiv Real (fun z : PDE.Vec d => u (t, z)) v
        (PDE.basisVec i) = velocityGradient u (t, v) i := by
      change fderiv Real (u ∘ Prod.mk t) v _ =
        velocityGradient u _ i
      rw [hslice.fderiv]
      aesop
    have haFDeriv : HasFDerivAt a
        (∑ j : Fin d, m j • (ContinuousLinearMap.proj j : PDE.Vec d →L[Real] Real)) v := by
      fun_prop
    have haDeriv : fderiv Real a v (PDE.basisVec i) = m i := by
      rw [haFDeriv.fderiv]
      simp
    simp_all
  have hsubAverageGrad :
      w.subAverage.grad = fun v => PDE.classicalGradient g v := by
    aesop
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => u (t, v) -
            (PDE.integralAverage V0 (fun z => u (t, z)) + a v)) <=
        ENNReal.ofReal (((2)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            (fun v => PDE.classicalGradient g v) := by
    grind
  have hgradientContinuous : ∀ i : Fin d, Continuous
      (fun v => velocityGradient u (t, v) i - m i) := by
    intro i
    exact (contDiff_velocityGradient_slice hu t i).continuous.sub continuous_const
  let F : PDE.Vec d -> PDE.Vec d :=
    fun v i => velocityGradient u (t, v) i - m i
  have hGradient :
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) <=
        ∑ i : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityGradient u (t, v) i - m i) := by
    calc
      PDE.euclideanFieldELpNormOn V _
          _ =
          PDE.euclideanFieldELpNormOn V _ F := by
        apply PDE.euclideanFieldELpNormOn_congr_ae
        filter_upwards with v
        grind
      _ = MeasureTheory.eLpNorm _
          _ _ := rfl
      _ <= MeasureTheory.eLpNorm (fun v => ∑ i : Fin d, |F v i|)
          _ _ := by
        apply MeasureTheory.eLpNorm_mono_ae
          (PDE.continuous_vecEuclideanNorm.comp
            (continuous_pi fun i => hgradientContinuous i)).aestronglyMeasurable
        filter_upwards with v
        have hsumNonneg : 0 <= ∑ i : Fin d, |F v i| :=
          Finset.sum_nonneg fun i _ => abs_nonneg _
        simpa only [Function.comp_def, F, Real.norm_eq_abs,
          abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _),
          abs_of_nonneg hsumNonneg] using PDE.vecEuclideanNorm_le_sum_abs _
      _ <= ∑ i : Fin d,
          MeasureTheory.eLpNorm _ _
            _ := by
        rw [← Finset.sum_fn]
        exact MeasureTheory.eLpNorm_sum_le Fact.out
      _ = ∑ i : Fin d,
          PDE.eLpNormOn V _
            _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simpa only [F, PDE.eLpNormOn, Real.norm_eq_abs] using
          (MeasureTheory.eLpNorm_norm (μ := PDE.volumeOn V)
            (p := ENNReal.ofReal p) _
            (hgradientContinuous i).aestronglyMeasurable)
  rw [parabolicExponent_eq_ofReal]
  simpa only [V, V0, m, a, p,
    velocityCube_zero_one_eq_axisCube_neg_one_two] using
    hPoincare'.trans (mul_le_mul_right hGradient _)

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum
    
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
      (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  let K  := ENNReal.ofReal (((2)^d) * (Real.sqrt d * 2))
  have hsum :
      ∑ i : Fin d,
        PDE.eLpNormOn (velocityCube (0) 1)
          (parabolicExponent d)
          (fun v => velocityGradient u (t, v) i -
            PDE.integralAverage (velocityCube (0) 1)
              (fun w => velocityGradient u (t, w) i)) <=
        ∑ i : Fin d, K * ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [K] using
      velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum d u hu t i
  calc
    PDE.eLpNormOn _
        _
        _ <=
        K * ∑ i : Fin d,
          PDE.eLpNormOn _
            _
            _ := by
      simpa only [K] using velocitySlice_sub_gradientMeanAffine_eLpNorm_le d u hu t
    _ <= K * ∑ i : Fin d, K * ∑ j : Fin d,
        PDE.eLpNormOn _
          _
          _ :=
      mul_le_mul_right hsum K
    _ = K^2 * ∑ i : Fin d, ∑ j : Fin d,
        PDE.eLpNormOn (velocityCube (0) 1)
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      ring
    _ = (ENNReal.ofReal _)^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn _
            _
            _ := by rfl

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : TimeVelocity d -> Real)

private theorem velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection
    
    (hu : ContDiff Real 2 u) (t : Real) :
    (fun v : PDE.Vec d =>
      u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      fun v =>
        (u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun w => u (t, w)) + ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) -
        parabolicMorreyUnitVelocityAffineProjection (fun w =>
          u (t, w) - (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun q => u (t, q)) + ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun q => velocityGradient u (t, q) i) * w i)) v := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let f  := fun v => u (t, v)
  let L : PDE.Vec d -> Real := fun v => PDE.integralAverage V f + ∑ i : Fin d,
    PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i
  have hfContinuous : Continuous f :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous L := by
    fun_prop
  have hclosedCompact  :=
    isCompact_velocityClosedCube (0 : PDE.Vec d) 1
  have hsubset : V ⊆ velocityClosedCube (0) 1 := by
    intro v hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
    grind
  have hf : Integrable f (volume.restrict V) :=
    (hfContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hL : Integrable L (volume.restrict V) :=
    (hLContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hfv : ∀ i : Fin d, Integrable (fun v => f v * v i) (volume.restrict V) := by
    intro i
    have hcontinuous  :=
      hfContinuous.mul (continuous_apply i)
    exact (hcontinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hLv : ∀ i : Fin d, Integrable (fun v => L v * v i) (volume.restrict V) := by
    intro i
    have hcontinuous  :=
      hLContinuous.mul (continuous_apply i)
    exact (hcontinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hsub  := by
    simpa using
      parabolicMorreyUnitVelocityAffineProjection_sub f L hf hL hfv hLv
  have hreproduces : parabolicMorreyUnitVelocityAffineProjection L = L := by
    simpa using parabolicMorreyUnitVelocityAffineProjection_reproduces_affine
      _
      _
  have hslice : (fun v : PDE.Vec d => parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      parabolicMorreyUnitVelocityAffineProjection f := by
    simpa using
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection u t
  funext v
  rw [congrFun hslice]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - parabolicMorreyUnitVelocityAffineProjection (f - L) v
  simp_all

private theorem velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum
    
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
        (fun v => u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) <=
      ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let R  := fun v => u (t, v) -
    (PDE.integralAverage V (fun w => u (t, w)) + ∑ i : Fin d,
      PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i)
  have hRMeasurable : AEStronglyMeasurable R (volume.restrict V) := by
    fun_prop
  have hp : (1) <= parabolicExponent d := by
    simpa only [parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have htriangle : PDE.eLpNormOn V (parabolicExponent d)
      (R - parabolicMorreyUnitVelocityAffineProjection R) <=
      PDE.eLpNormOn V (parabolicExponent d) R + PDE.eLpNormOn V (parabolicExponent d)
        (parabolicMorreyUnitVelocityAffineProjection R) := by
    simpa only [PDE.eLpNormOn] using
      MeasureTheory.eLpNorm_sub_le hp
  have hprojection : PDE.eLpNormOn V (parabolicExponent d)
      (parabolicMorreyUnitVelocityAffineProjection R) <=
      ENNReal.ofReal (1 + 3 * d) * PDE.eLpNormOn V (parabolicExponent d) R := by
    simpa only [V] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le R hRMeasurable
  have hfactor : 1 + ENNReal.ofReal (1 + 3 * d) =
      ENNReal.ofReal (2 + 3 * d) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
    ring
  have hS3 := velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum d u hu t
  rw [velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection d u hu]
  calc
    PDE.eLpNormOn V _
        _ <=
        PDE.eLpNormOn V _ R + PDE.eLpNormOn V _
          _ := htriangle
    _ <= PDE.eLpNormOn V _ R +
        ENNReal.ofReal _ * PDE.eLpNormOn V _ R :=
      add_le_add_right hprojection _
    _ = ENNReal.ofReal _ * PDE.eLpNormOn V _ R := by
      rw [← hfactor, add_mul, one_mul]
    _ <= ENNReal.ofReal _ *
        ((ENNReal.ofReal _)^2 *
          ∑ i : Fin d, ∑ j : Fin d, PDE.eLpNormOn V _
            _) := mul_le_mul_right (by omega) _
    _ = ENNReal.ofReal _ *
        (ENNReal.ofReal _)^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn _ _
              _ := by
      ring

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocityHessian_continuous_for_spatial_global
    {d : Nat} {u : TimeVelocity d -> Real} {i j : Fin d}
    (hu : ContDiff Real 2 u) :
    Continuous (fun z => velocityHessian u z i j) := by
  unfold velocityHessian
  fun_prop

private theorem aemeasurable_spatialAffine_residual
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) :
    AEMeasurable
      (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let ν : Measure (PDE.Vec d) := volume.restrict V
  have huStrong : StronglyMeasurable
      (Function.uncurry fun t : Real => fun v : PDE.Vec d => u (t, v)) := hu.continuous.stronglyMeasurable
  have hAverage : StronglyMeasurable (parabolicMorreyUnitVelocityAverage u) := by
    apply stronglyMeasurable_const.mul
    simpa using (huStrong.integral_prod_right (ν := ν))
  have hCoeff : ∀ i : Fin d,
      StronglyMeasurable (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
    intro i
    have huCoordinate : StronglyMeasurable
        (Function.uncurry fun t : Real => fun v : PDE.Vec d => u (t, v) * v i) := by
      fun_prop
    apply stronglyMeasurable_const.mul
    simpa using (huCoordinate.integral_prod_right (ν := ν))
  have hProjection : StronglyMeasurable (parabolicMorreyUnitSpatialAffineProjection u) := by
    unfold parabolicMorreyUnitSpatialAffineProjection
    fun_prop
  fun_prop

variable (d : Nat)

private theorem parabolicMorreyUnitSpatialAffinePoincareELp
     (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d
        (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
        (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal
          ((2 + 3 * (d : Real)) *
            (((2 : Real)^d) * (Real.sqrt d * 2))^2) *
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d
            (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d) := by
  let I  := Set.Ioo (0 : Real) 1
  let V  := velocityCube (0 : PDE.Vec d) 1
  let μ : Measure Real := volume.restrict I
  let p  := parabolicExponent d
  let K  := ENNReal.ofReal (((2)^d) * (Real.sqrt d * 2))
  let B  := ENNReal.ofReal (2 + 3 * d) * K ^ 2
  let R  := fun z =>
    u z - parabolicMorreyUnitSpatialAffineProjection u z
  let q  := fun i j t =>
    PDE.eLpNormOn V p (fun v => velocityHessian u (t, v) i j)
  have hp : (1) <= p := by
    simpa only [p, parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have hRAE : AEMeasurable R (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa only [R] using aemeasurable_spatialAffine_residual hu
  have hHAE : ∀ i j : Fin d,
      AEMeasurable (fun z => velocityHessian u z i j)
        (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i j
    exact (velocityHessian_continuous_for_spatial_global hu).aestronglyMeasurable.aemeasurable
  have hslice : ∀ t : Real,
      PDE.eLpNormOn V p (fun v => R (t, v)) <=
        B * ∑ i : Fin d, ∑ j : Fin d, q i j t := by
    intro t
    simpa only [R, V, p, B, K, q] using
      velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum d u hu t
  have houter : eLpNorm (fun t => PDE.eLpNormOn V p (fun v => R (t, v))) p μ <=
      B * eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (by simpa only [V, p, μ, I] using
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm R hRAE).aestronglyMeasurable) ?_
    simp_all
  have houterSum : eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ <=
      ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
    calc
      eLpNorm _ p μ =
          eLpNorm (∑ i : Fin d, fun t => ∑ j : Fin d, q i j t) p μ := by
        rw [Finset.sum_fn]
      _ <= ∑ i : Fin d, eLpNorm _ p μ := eLpNorm_sum_le hp
      _ <= ∑ i : Fin d, ∑ j : Fin d, eLpNorm _ p μ := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hp
  have hCnonneg : 0 <= 2 + 3 * (d : Real) := by positivity
  have hLnonneg : 0 <= ((2)^d) * (Real.sqrt d * 2) := by positivity
  have hCnormalize :
      ENNReal.ofReal
          ((2 + 3 * d) * (((2)^d) * (Real.sqrt d * 2))^2) = B := by
    rw [ENNReal.ofReal_mul hCnonneg, ENNReal.ofReal_pow hLnonneg]
  calc
    parabolicELpNormOn d R _ =
        eLpNorm _ p μ := by
      simpa only [R, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice R hRAE
    _ <= B * eLpNorm _ p μ := houter
    _ <= B * ∑ i : Fin d, ∑ j : Fin d, eLpNorm _ p μ := mul_le_mul_right houterSum B
    _ = B * ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNormOn d
          _
          _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      simpa only [q, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          _ (hHAE i j)
    _ = ENNReal.ofReal
          _ *
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d
            _
            _ := by
      simp_all

/-- Smooth spatial second-order Poincare inequality on the fixed unit
parabolic box, modulo the per-time canonical velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareELpConst 
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
        ContDiff Real 2 u ->
        parabolicELpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          ENNReal.ofReal C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicELpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := by
  let C  :=
    (2 + 3 * d) * (((2)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · positivity
  · intro u hu
    simpa using parabolicMorreyUnitSpatialAffinePoincareELp d u hu

/-- Real-valued corollary of the smooth spatial second-order Poincare estimate
on the fixed unit parabolic box. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareConst 
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
        ContDiff Real 2 u ->
        parabolicLpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicLpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := by
  let C  :=
    (2 + 3 * d) * (((2)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · positivity
  · intro u hu
    let R : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let H : Fin d -> Fin d -> TimeVelocity d -> Real := fun i j z =>
      velocityHessian u z i j
    have hENN : parabolicELpNormOn d R (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) := by
      simpa using parabolicMorreyUnitSpatialAffinePoincareELp d u hu
    have hHmem : ∀ i j : Fin d,
        MemLp (H i j) (parabolicExponent d)
          (volume.restrict (parabolicMorreyUnitBox d)) := by
      intro i j
      have hContinuous  :=
        velocityHessian_continuous_for_spatial_global (i := i) (j := j) hu
      simpa using Continuous.memLp_parabolicMorreyUnitBox hContinuous
    have hHneTop : ∀ i j : Fin d,
        parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) ≠ ⊤ := by
      intro i j
      exact (hHmem i j).eLpNorm_ne_top
    have hsumNeTop :
        (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)) ≠ ⊤ := by
      simp_all
    have hRhsNeTop :
        ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumNeTop
    have hReal := ENNReal.toReal_mono hRhsNeTop hENN
    have hCnonneg : 0 <= C := by
      positivity
    calc
      (parabolicELpNormOn d R _).toReal <=
          (ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNormOn d _ _).toReal := hReal
      _ = C * (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        simp_all
      _ = C * ∑ i : Fin d, (∑ j : Fin d,
          parabolicELpNormOn d _ _).toReal := by
        congr 1
        exact ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHneTop i j
      _ = C * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d _ _).toReal := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact ENNReal.toReal_sum fun j _ => hHneTop i j

end HypoellipticAleksandrov.Parabolic
