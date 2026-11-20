module

import PDEFoundation.Measure.FiniteVectorConvergence

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
import HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.Smooth
public import Mathlib.MeasureTheory.Integral.Prod
import HypoellipticAleksandrov.Parabolic.ABP
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceCollarCutoff
import HypoellipticAleksandrov.Parabolic.WeakJetMollifier

/-!
# Spatial-slice transport for parabolic Poincare

This module identifies the native unit velocity cube with the PDEFoundation
axis cube and proves the private fixed-time gradient-mean affine Poincare
estimate and canonical-projection comparison, then lifts them globally through
the two public spatial inequalities.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocityCube_zero_one_eq_axisCube_neg_one_two (d : Nat) :
    velocityCube (0 : PDE.Vec d) 1 =
      PDE.axisCube (-1 : PDE.Vec d) 2 := by
  ext v
  simp only [mem_velocityCube_iff, PDE.axisCube, Set.mem_pi]
  constructor
  · intro hv i _
    have hvi := hv i
    rw [abs_lt] at hvi
    simp only [Pi.zero_apply, Pi.neg_apply, Pi.one_apply, sub_zero] at hvi ⊢
    constructor <;> linarith
  · intro hv i
    have hvi := hv i (Set.mem_univ i)
    simp only [Pi.neg_apply, Pi.one_apply] at hvi
    change -1 < v i ∧ v i < -1 + 2 at hvi
    rw [abs_lt]
    simp only [Pi.zero_apply, sub_zero]
    constructor <;> linarith

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : Nat} {u : TimeVelocity d -> Real} (hu : ContDiff Real 2 u) (t : Real)
include hu

private theorem contDiff_velocityGradient_slice (i : Fin d) :
    ContDiff Real 1 (fun v : PDE.Vec d => velocityGradient u (t, v) i) := by
  exact (contDiff_pi.mp ((contDiff_velocityGradient hu).comp
    (contDiff_const.prodMk contDiff_id))) i

private theorem classicalGradient_velocityGradient_slice_apply (v : PDE.Vec d)
    (i j : Fin d) :
    PDE.classicalGradient
        (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j =
      velocityHessian u (t, v) i j := by
  rw [PDE.classicalGradient_apply]
  have hdiff : DifferentiableAt Real (fun z => velocityGradient u z i) (t, v) :=
    ((contDiff_pi.mp (contDiff_velocityGradient hu) i).differentiable
      (by norm_num)) (t, v)
  have hslice := hdiff.hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)
  change (fderiv Real ((fun z => velocityGradient u z i) ∘ Prod.mk t) v)
      (PDE.basisVec j) = velocityHessian u (t, v) i j
  rw [hslice.fderiv]
  change fderiv Real (fun z => velocityGradient u z i) (t, v)
      (0, Pi.single j 1) = velocityHessian u (t, v) i j
  calc
    fderiv Real (fun z => velocityGradient u z i) (t, v) (0, Pi.single j 1) =
        velocityHessian u (t, v) j i :=
      fderiv_velocityGradient_apply hu (t, v)
        (0, Pi.single i 1) (0, Pi.single j 1)
    _ = velocityHessian u (t, v) i j := by
      exact congrFun (congrFun (velocityHessian_isSymm hu (t, v)).eq i) j

end

private theorem unitVelocity_meanPoincare {d : ℕ} {g : PDE.Vec d → ℝ}
    (hg : ContDiff ℝ 1 g) :
    let V := velocityCube (0 : PDE.Vec d) 1
    PDE.eLpNormOn V (parabolicExponent d) (fun v => g v - PDE.integralAverage V g) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * (Real.sqrt d * 2)) *
        ∑ i : Fin d, PDE.eLpNormOn V (parabolicExponent d) (fun v => PDE.classicalGradient g v i) := by
  dsimp only
  rw [velocityCube_zero_one_eq_axisCube_neg_one_two, parabolicExponent_eq_ofReal]
  let V := PDE.axisCube (-1 : PDE.Vec d) 2
  let p : ℝ := (d : ℝ) + 1
  have hp : 1 ≤ p := by dsimp [p]; linarith [Nat.cast_nonneg (α := ℝ) d]
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := PDE.isFiniteMeasure_volumeOn_axisCube _ _
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube (-1 : PDE.Vec d) 2) hg
  have h := PDE.meanZeroPoincare_on_axisCube_unnormalized hp (-1 : PDE.Vec d) (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage (PDE.volume_axisCube_pos _ (by norm_num)) (PDE.volume_axisCube_ne_top _ _).lt_top)
  have hfun : w.subAverage.toFun = fun v => g v - PDE.integralAverage V g :=
    funext fun v => PDE.W1pFunction.subAverage_apply w v
  have hgrad : w.subAverage.grad = PDE.classicalGradient g :=
    funext fun v => PDE.W1pFunction.subAverage_grad w v
  rw [hfun, hgrad] at h
  refine h.trans ?_
  gcongr
  exact PDE.eLpNorm_vecEuclideanNorm_le_sum Fact.out (fun i =>
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)

private theorem velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum
    (d : Nat) (u : TimeVelocity d -> Real)
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
  simpa only [classicalGradient_velocityGradient_slice_apply hu t] using
    unitVelocity_meanPoincare (contDiff_velocityGradient_slice hu t i)

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

section
variable (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) (t : Real)
include hu

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le :
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
  let V := velocityCube (0 : PDE.Vec d) 1
  let m (i : Fin d) := PDE.integralAverage V (fun v => velocityGradient u (t, v) i)
  let a : PDE.Vec d →L[ℝ] ℝ := ∑ i, m i • ContinuousLinearMap.proj i
  let f : PDE.Vec d → ℝ := u ∘ Prod.mk t
  let g := f - ⇑a
  have hf : ContDiff ℝ 1 f := (hu.of_le (by norm_num)).comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ 1 g := hf.sub a.contDiff
  have ha (v : PDE.Vec d) : a v = ∑ i, m i * v i := by simp [a, smul_eq_mul]
  have hmean : PDE.integralAverage V g = PDE.integralAverage V f := by
    rw [show g = f - ⇑a by rfl, unit_velocity_average_sub _ _
      (continuous_integrable_unit_velocity_cube hf.continuous)
      (continuous_integrable_unit_velocity_cube a.continuous), funext ha]
    have hm := unit_velocity_average_affine 0 m
    simp only [zero_add] at hm
    rw [hm, sub_zero]
  have hgrad (v : PDE.Vec d) (i : Fin d) : PDE.classicalGradient g v i = velocityGradient u (t, v) i - m i := by
    have hcomp := (hu.differentiable (by norm_num) (t, v)).hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)
    rw [PDE.classicalGradient_apply, show g = f - ⇑a by rfl, fderiv_sub (hf.differentiable (by simp) v)
      a.differentiableAt, hcomp.fderiv, a.fderiv, ContinuousLinearMap.sub_apply, ha]
    simp [PDE.basisVec, Pi.single_apply, velocityGradient, ContinuousLinearMap.comp_apply]
  have hleft : (fun v => g v - PDE.integralAverage V g) =
      fun v => f v - (PDE.integralAverage V f + ∑ i, m i * v i) := by
    rw [hmean]
    funext v
    change f v - a v - _ = _
    rw [ha]
    ring
  have h := unitVelocity_meanPoincare hg
  dsimp only at h
  rw [← show V = velocityCube (0 : PDE.Vec d) 1 from rfl] at h
  simp only [hleft, hgrad] at h
  exact h

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum :
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
  let K : ENNReal := ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2))
  have hsum :
      ∑ i : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityGradient u (t, v) i -
            PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => velocityGradient u (t, w) i)) <=
        ∑ i : Fin d, K * ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [K] using
      velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum d u hu t i
  calc
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
        K * ∑ i : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityGradient u (t, v) i -
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i)) := by
      simpa only [K] using velocitySlice_sub_gradientMeanAffine_eLpNorm_le d u hu t
    _ <= K * ∑ i : Fin d, K * ∑ j : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) :=
      mul_le_mul_right hsum K
    _ = K^2 * ∑ i : Fin d, ∑ j : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_two]
      ac_rfl
    _ = (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by rfl

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

section
variable (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) (t : Real)
include hu

private theorem velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection :
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
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let f : PDE.Vec d -> Real := fun v => u (t, v)
  let L : PDE.Vec d -> Real := fun v => PDE.integralAverage V f + ∑ i : Fin d,
    PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i
  have hfContinuous : Continuous f :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous L := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hsub := parabolicMorreyUnitVelocityAffineProjection_sub f L
    (continuous_integrable_unit_velocity_cube hfContinuous)
    (continuous_integrable_unit_velocity_cube hLContinuous)
    (fun i => continuous_integrable_unit_velocity_cube (hfContinuous.mul (continuous_apply i)))
    (fun i => continuous_integrable_unit_velocity_cube (hLContinuous.mul (continuous_apply i)))
  have hreproduces : parabolicMorreyUnitVelocityAffineProjection L = L := by
    simpa only [L] using parabolicMorreyUnitVelocityAffineProjection_reproduces_affine
      (PDE.integralAverage V f)
      (fun i => PDE.integralAverage V (fun w => velocityGradient u (t, w) i))
  have hslice : (fun v : PDE.Vec d => parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      parabolicMorreyUnitVelocityAffineProjection f := by
    simpa only [f] using
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection u t
  funext v
  rw [congrFun hslice v]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - parabolicMorreyUnitVelocityAffineProjection (f - L) v
  rw [hsub, hreproduces]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - (parabolicMorreyUnitVelocityAffineProjection f v - L v)
  ring

private theorem velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
        (fun v => u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) <=
      ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let R : PDE.Vec d -> Real := fun v => u (t, v) -
    (PDE.integralAverage V (fun w => u (t, w)) + ∑ i : Fin d,
      PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i)
  have huSlice : Continuous (fun v : PDE.Vec d => u (t, v)) :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous (fun v : PDE.Vec d =>
      PDE.integralAverage V (fun w => u (t, w)) + ∑ i : Fin d,
        PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i) := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hRMeasurable : AEStronglyMeasurable R (volume.restrict V) := by
    simpa only [R, Pi.sub_def] using
      (huSlice.sub hLContinuous).aestronglyMeasurable
  have hProjectionContinuous :
      Continuous (parabolicMorreyUnitVelocityAffineProjection R) := by
    unfold parabolicMorreyUnitVelocityAffineProjection
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hp : (1 : ENNReal) <= parabolicExponent d := by
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
      ENNReal.ofReal (1 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R := by
    simpa only [V] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le R hRMeasurable
  have hfactor : 1 + ENNReal.ofReal (1 + 3 * (d : Real)) =
      ENNReal.ofReal (2 + 3 * (d : Real)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
    rw [show (2 : ENNReal) = 1 + 1 by norm_num]
    ac_rfl
  have hS3 := velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum d u hu t
  rw [velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection d u hu t]
  change PDE.eLpNormOn V (parabolicExponent d)
      (R - parabolicMorreyUnitVelocityAffineProjection R) <= _
  calc
    PDE.eLpNormOn V (parabolicExponent d)
        (R - parabolicMorreyUnitVelocityAffineProjection R) <=
        PDE.eLpNormOn V (parabolicExponent d) R + PDE.eLpNormOn V (parabolicExponent d)
          (parabolicMorreyUnitVelocityAffineProjection R) := htriangle
    _ <= PDE.eLpNormOn V (parabolicExponent d) R +
        ENNReal.ofReal (1 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R :=
      add_le_add_right hprojection _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R := by
      rw [← hfactor, add_mul, one_mul]
    _ <= ENNReal.ofReal (2 + 3 * (d : Real)) *
        ((ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d, PDE.eLpNormOn V (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j)) := by
      exact mul_le_mul_right (by simpa only [R, V] using hS3) _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
      simp only [V]
      ac_rfl

end

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

section
variable (d : Nat)

private theorem spatialAffinePoincareGlobalConst_pos (hd : 1 <= d) :
    0 < (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2 := by
  have hdpos : 0 < (d : Real) := by
    exact_mod_cast hd
  positivity

private theorem parabolicMorreyUnitSpatialAffinePoincareELp (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
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
  let I : Set Real := Set.Ioo (0 : Real) 1
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let μ : Measure Real := volume.restrict I
  let p : ENNReal := parabolicExponent d
  let K : ENNReal := ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2))
  let B : ENNReal := ENNReal.ofReal (2 + 3 * (d : Real)) * K ^ 2
  let R : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyUnitSpatialAffineProjection u z
  let q : Fin d -> Fin d -> Real -> ENNReal := fun i j t =>
    PDE.eLpNormOn V p (fun v => velocityHessian u (t, v) i j)
  have hp : (1 : ENNReal) <= p := by
    simpa only [p, parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have hRAE : AEMeasurable R (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa only [R, Pi.sub_def] using (hu.continuous.sub (continuous_parabolicMorreyUnitSpatialAffineProjection hu.continuous)).aemeasurable
  have hHAE : ∀ i j : Fin d,
      AEMeasurable (fun z => velocityHessian u z i j)
        (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i j
    exact (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_cutoff_continuous hu).aestronglyMeasurable.aemeasurable
  have hqAE : ∀ i j : Fin d, AEMeasurable (q i j) μ := by
    intro i j
    simpa only [q, μ, I, V, p] using
      aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm
        (fun z => velocityHessian u z i j) (hHAE i j)
  have hqASM : ∀ i j : Fin d, AEStronglyMeasurable (q i j) μ := by
    intro i j
    exact (hqAE i j).aestronglyMeasurable
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
    filter_upwards with t
    simpa only [enorm_eq_self] using hslice t
  have houterSum : eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ <=
      ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
    calc
      eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ =
          eLpNorm (∑ i : Fin d, fun t => ∑ j : Fin d, q i j t) p μ := by
        rw [Finset.sum_fn]
      _ <= ∑ i : Fin d, eLpNorm (fun t => ∑ j : Fin d, q i j t) p μ := by
        exact eLpNorm_sum_le hp
      _ <= ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hp
  have hCnonneg : 0 <= 2 + 3 * (d : Real) := by positivity
  have hLnonneg : 0 <= ((2 : Real)^d) * (Real.sqrt d * 2) := by positivity
  have hCnormalize :
      ENNReal.ofReal
          ((2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2) = B := by
    dsimp only [B, K]
    rw [ENNReal.ofReal_mul hCnonneg, ENNReal.ofReal_pow hLnonneg]
  calc
    parabolicELpNormOn d R (parabolicMorreyUnitBox d) =
        eLpNorm (fun t => PDE.eLpNormOn V p (fun v => R (t, v))) p μ := by
      simpa only [R, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice R hRAE
    _ <= B * eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ := houter
    _ <= B * ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
      exact mul_le_mul_right houterSum B
    _ = B * ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNormOn d
          (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      simpa only [q, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (fun z => velocityHessian u z i j) (hHAE i j)
    _ = ENNReal.ofReal
          ((2 + 3 * (d : Real)) *
            (((2 : Real)^d) * (Real.sqrt d * 2))^2) *
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d
            (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d) := by
      rw [hCnormalize]

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
  let C :=
    (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · simpa only [C] using spatialAffinePoincareGlobalConst_pos d hd
  exact fun u hu => id (parabolicMorreyUnitSpatialAffinePoincareELp d u hu)

end

end HypoellipticAleksandrov.Parabolic
