module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.Smooth
public import Mathlib.MeasureTheory.Integral.Prod
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Positivity
import all HypoellipticAleksandrov.Parabolic.ABP
import all HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
import all HypoellipticAleksandrov.Parabolic.WeakJetMollifier

open private HypoellipticAleksandrov.Parabolic.fderiv_velocityGradient_apply from HypoellipticAleksandrov.Parabolic.WeakJetMollifier
open private HypoellipticAleksandrov.Parabolic.velocityHessian_continuous from HypoellipticAleksandrov.Parabolic.ParabolicMorreyNorm
open private HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal from HypoellipticAleksandrov.Parabolic.ABP


/-!
# Spatial-slice transport for parabolic Poincare

This module identifies the native unit velocity cube with the PDEFoundation
axis cube and proves the private fixed-time gradient-mean affine Poincare
estimate and canonical-projection comparison, then lifts them globally through
the two public spatial inequalities.
-/

 public section



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
variable {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiff Real 2 u)

include hu
private theorem contDiff_velocityGradient_slice
     (t : Real) (i : Fin d) :
    ContDiff Real 1 (fun v  => velocityGradient u (t, v) i) := (contDiff_pi.mp ((contDiff_velocityGradient hu).comp
    (contDiff_const.prodMk contDiff_id))) i




private theorem classicalGradient_velocityGradient_slice_apply
     (t : Real) (v : PDE.Vec d)
    (i j : Fin d) :
    PDE.classicalGradient
        (fun w  => velocityGradient u (t, w) i) v j =
      velocityHessian u (t, v) i j := by
  let sharedTerm_0b36443110 := ((fun z => velocityGradient u z i))
  let sharedTerm_b20e72633c := (velocityHessian u (t, v) i j)
  rw [PDE.classicalGradient_apply]
  have hdiff : DifferentiableAt Real sharedTerm_0b36443110 (t, v) :=
    ((contDiff_pi.mp (contDiff_velocityGradient hu) i).differentiable
      (by norm_num)) (t, v)

  change (fderiv Real (sharedTerm_0b36443110 ∘ Prod.mk t) v)
      (PDE.basisVec j) = sharedTerm_b20e72633c
  rw [(hdiff.hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)).fderiv]
  change fderiv Real sharedTerm_0b36443110 (t, v)
      (0, Pi.single j 1) = sharedTerm_b20e72633c
  calc
    fderiv Real sharedTerm_0b36443110 (t, v) (0, Pi.single j 1) =
        velocityHessian u (t, v) j i :=
      _root_.HypoellipticAleksandrov.Parabolic.fderiv_velocityGradient_apply hu (t, v)
        _ _
    _ = sharedTerm_b20e72633c := congrFun (congrFun (velocityHessian_isSymm hu (t, v)).eq i) j
end


variable (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) (t : Real) (i : Fin d)

include hu
private theorem velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum
     :
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
  let p : Real := (d : Real) + 1
  let V  := PDE.axisCube (-1 : PDE.Vec d) 2
  let g  := fun v => velocityGradient u (t, v) i
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube _ 2)
      (contDiff_velocityGradient_slice hu t i)
  have hp : 1 <= p := by
    dsimp [p]

    linarith
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    rw [ENNReal.one_le_ofReal]
    exact hp
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := by
    dsimp [V]
    exact PDE.isFiniteMeasure_volumeOn_axisCube _ 2
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp (-1 : PDE.Vec d) (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage
      (PDE.volume_axisCube_pos (-1 : PDE.Vec d) (by norm_num))
      (lt_top_iff_ne_top.mpr
        (PDE.volume_axisCube_ne_top _ 2)))
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => g v - PDE.integralAverage V g := by
    funext v
    rw [PDE.W1pFunction.subAverage_apply]
    rfl
  have hsubAverageGrad :
      w.subAverage.grad = (PDE.classicalGradient g) := by
    funext v
    rw [PDE.W1pFunction.subAverage_grad]
    rfl
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => g v - PDE.integralAverage V g) <=
        ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            ((PDE.classicalGradient g)) := by
    rw [hsubAverageToFun, hsubAverageGrad] at hPoincare
    exact hPoincare
  have hHessianContinuous :
      ∀ j : Fin d, Continuous (fun v => velocityHessian u (t, v) i j) := by
    intro j
    have hContinuous : Continuous
        (fun v => PDE.classicalGradient
          (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j) := by
      simpa only [PDE.classicalGradient_apply] using
        ((contDiff_velocityGradient_slice hu t i).continuous_fderiv
          (by norm_num)).clm_apply continuous_const
    simpa only [classicalGradient_velocityGradient_slice_apply hu t] using hContinuous
  let F  :=
    fun v j => velocityHessian u (t, v) i j

  rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal]
  simpa only [p, V, g] using
    hPoincare'.trans (mul_le_mul_right (by
          calc
            PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
                ((PDE.classicalGradient g)) =
                PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p) F := by
              apply PDE.euclideanFieldELpNormOn_congr_ae
              filter_upwards with v
              ext j
              exact classicalGradient_velocityGradient_slice_apply hu t v i j
            _ = MeasureTheory.eLpNorm (fun v => PDE.vecEuclideanNorm (F v))
                (ENNReal.ofReal p) (PDE.volumeOn V) := rfl
            _ <= MeasureTheory.eLpNorm (fun v => ∑ j : Fin d, |F v j|)
                (ENNReal.ofReal p) (PDE.volumeOn V) := by
              apply MeasureTheory.eLpNorm_mono_ae
                (PDE.continuous_vecEuclideanNorm.comp
                  (continuous_pi hHessianContinuous)).aestronglyMeasurable
              filter_upwards with v

              simpa only [Function.comp_def, F, Real.norm_eq_abs,
                abs_of_nonneg (PDE.vecEuclideanNorm_nonneg (F v)),
                abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (F v j))] using
                PDE.vecEuclideanNorm_le_sum_abs (F v)
            _ <= ∑ j : Fin d,
                MeasureTheory.eLpNorm (fun v => |F v j|) (ENNReal.ofReal p)
                  (PDE.volumeOn V) := by
              rw [← Finset.sum_fn]
              exact MeasureTheory.eLpNorm_sum_le Fact.out
            _ = ∑ j : Fin d,
                PDE.eLpNormOn V (ENNReal.ofReal p)
                  (fun v => velocityHessian u (t, v) i j) := (Finset.sum_congr rfl fun j x =>
        id
          (MeasureTheory.eLpNorm_norm (fun v => velocityHessian u (t, v) i j)
            (Continuous.aestronglyMeasurable (hHessianContinuous j))))) _)

private theorem velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum
     :
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
  simpa only [velocityCube_zero_one_eq_axisCube_neg_one_two d] using
    velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum d u hu t i

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) (t : Real)

include hu
private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le
     :
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
  let sharedTerm_d83f50f3f2 := ((fun z : PDE.Vec d => u (t, z)))
  let p : Real := (d : Real) + 1
  let V  := PDE.axisCube (-1 : PDE.Vec d) 2
  let V0  := velocityCube (0 : PDE.Vec d) 1
  let m  := fun i => PDE.integralAverage V0
    (fun w => velocityGradient u (t, w) i)
  let a : PDE.ScalarField d := fun v => ∑ i : Fin d, m i * v i
  let g  := fun v => u (t, v) - a v
  have huSlice : ContDiff Real 2 sharedTerm_d83f50f3f2 :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff Real 2 a := by
    exact ContDiff.sum  fun i _ =>
      contDiff_const.mul (contDiff_apply Real Real i)
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube _ 2)
      ((huSlice.sub ha).of_le (by norm_num))
  have hp : 1 <= p := by
    dsimp [p]

    linarith
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    rw [ENNReal.one_le_ofReal]
    exact hp
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := by
    dsimp [V]
    exact PDE.isFiniteMeasure_volumeOn_axisCube _ 2


  have hcomponent : ∀ i : Fin d, Integrable (fun v : PDE.Vec d => m i * v i)
      (volume.restrict V0) := by
    intro i
    have hcont : Continuous (fun v : PDE.Vec d => m i * v i) :=
      continuous_const.mul (continuous_apply i)

    have hKcompact  :=
      isCompact_velocityClosedCube (0 : PDE.Vec d) 1

    exact (hcont.continuousOn.integrableOn_compact hKcompact).mono_set (show V0 ⊆ (velocityClosedCube (0 : PDE.Vec d) 1) by
        intro v hv
        change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
        change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
        intro j
        exact (hv j).le)
  have haIntegrable : Integrable a (volume.restrict V0) := by
    simpa only [a] using integrable_finset_sum (Finset.univ : Finset (Fin d)) fun i _ => hcomponent i
  have haAverage : PDE.integralAverage V a = 0 := by
    have hVV : V = V0 := by
      dsimp [V, V0]
      exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    rw [hVV]
    unfold PDE.integralAverage
    rw [show (fun v : PDE.Vec d => ∑ i : Fin d, m i * v i) =
        fun v => ∑ i ∈ (Finset.univ : Finset (Fin d)), m i * v i by
          ext v
          rfl,
      integral_finset_sum (Finset.univ : Finset (Fin d))
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

  have huIntegrable : Integrable sharedTerm_d83f50f3f2
      (volume.restrict V0) := by
    have hsum : g + a = sharedTerm_d83f50f3f2 := by
      funext v
      dsimp [g]
      ring
    rw [← hsum]
    exact (show Integrable g (volume.restrict V0) by
        have hw : Integrable g (volume.restrict V) := by
          exact w.integrableOn
        have hVV : V = V0 := by
          dsimp [V, V0]
          exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
        simpa only [hVV] using hw).add haIntegrable
  have hgAverage : PDE.integralAverage V g = PDE.integralAverage V0
      sharedTerm_d83f50f3f2 := by
    have hVV : V = V0 := by
      dsimp [V, V0]
      exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    have haAverage0 : PDE.integralAverage V0 a = 0 := by
      simpa only [hVV] using haAverage
    rw [hVV]
    unfold g
    calc
      PDE.integralAverage V0 (fun v => u (t, v) - a v) =
          PDE.integralAverage V0 sharedTerm_d83f50f3f2 -
            PDE.integralAverage V0 a := by
        unfold PDE.integralAverage
        rw [integral_sub huIntegrable haIntegrable]
        ring
      _ = PDE.integralAverage V0 sharedTerm_d83f50f3f2 := by
        rw [haAverage0]
        ring
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp (-1 : PDE.Vec d) (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage (show 0 < volume V by
        dsimp [V]
        exact PDE.volume_axisCube_pos (-1 : PDE.Vec d) (by norm_num)) (show volume V < ⊤ by
        dsimp [V]
        exact lt_top_iff_ne_top.mpr
          (PDE.volume_axisCube_ne_top _ 2)))
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => u (t, v) -
        (PDE.integralAverage V0 sharedTerm_d83f50f3f2 + a v) := by
    funext v
    rw [PDE.W1pFunction.subAverage_apply]
    change g v - PDE.integralAverage V g =
      u (t, v) - (PDE.integralAverage V0 sharedTerm_d83f50f3f2 + a v)
    rw [hgAverage]
    dsimp [g]
    ring

  have hsubAverageGrad :
      w.subAverage.grad = (PDE.classicalGradient g) := by
    funext v
    rw [PDE.W1pFunction.subAverage_grad]
    rfl
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => u (t, v) -
            (PDE.integralAverage V0 sharedTerm_d83f50f3f2 + a v)) <=
        ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            ((PDE.classicalGradient g)) := by
    rw [hsubAverageToFun, hsubAverageGrad] at hPoincare
    exact hPoincare
  have hgradientContinuous : ∀ i : Fin d, Continuous
      (fun v => velocityGradient u (t, v) i - m i) := by
    intro i
    exact (contDiff_velocityGradient_slice hu t i).continuous.sub continuous_const
  let F  :=
    fun v i => velocityGradient u (t, v) i - m i

  rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_eq_ofReal]
  simpa only [V, V0, m, a, p,
    velocityCube_zero_one_eq_axisCube_neg_one_two d] using
    hPoincare'.trans (mul_le_mul_right (show PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          ((PDE.classicalGradient g)) <=
        ∑ i : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityGradient u (t, v) i - m i) by
          calc
            PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
                ((PDE.classicalGradient g)) =
                PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p) F := by
              apply PDE.euclideanFieldELpNormOn_congr_ae
              filter_upwards with v
              ext i
              exact (show ∀ v : PDE.Vec d, ∀ i : Fin d,
            PDE.classicalGradient g v i = velocityGradient u (t, v) i - m i by
                  intro v i
                  rw [PDE.classicalGradient_apply]
                  have huDiff : DifferentiableAt Real sharedTerm_d83f50f3f2 v :=
                    huSlice.differentiable (by norm_num) v
                  have haDiff  := ha.differentiable (by norm_num) v
                  rw [show g = (sharedTerm_d83f50f3f2) - a by rfl,
                    fderiv_sub huDiff haDiff]
                  have hslice := (hu.differentiable (by norm_num) (t, v)).hasFDerivAt.comp v
                    (hasFDerivAt_prodMk_right t v)
                  have huDeriv : fderiv Real sharedTerm_d83f50f3f2 v
                      (PDE.basisVec i) = velocityGradient u (t, v) i := by
                    change fderiv Real (u ∘ Prod.mk t) v (PDE.basisVec i) =
                      velocityGradient u (t, v) i
                    rw [hslice.fderiv]
                    change fderiv Real u (t, v) (0, Pi.single i 1) =
                      velocityGradient u (t, v) i
                    rfl
                  have haFDeriv : HasFDerivAt a
                      (∑ j : Fin d, m j • (ContinuousLinearMap.proj j : PDE.Vec d →L[Real] Real)) v := by
                    have h := HasFDerivAt.sum (u := Finset.univ) fun j _ =>
                      (hasFDerivAt_apply (𝕜 := Real) j v).const_mul (m j)
                    convert h using 1
                    ext x
                    simp only [a, Finset.sum_apply]
                  have haDeriv : fderiv Real a v (PDE.basisVec i) = m i := by
                    rw [haFDeriv.fderiv]
                    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
                      ContinuousLinearMap.proj_apply, PDE.basisVec, Pi.single_apply]
                    simp
                  simp only [ContinuousLinearMap.sub_apply]
                  rw [huDeriv, haDeriv]) v i
            _ = MeasureTheory.eLpNorm (fun v => PDE.vecEuclideanNorm (F v))
                (ENNReal.ofReal p) (PDE.volumeOn V) := rfl
            _ <= MeasureTheory.eLpNorm (fun v => ∑ i : Fin d, |F v i|)
                (ENNReal.ofReal p) (PDE.volumeOn V) := by
              apply MeasureTheory.eLpNorm_mono_ae
                (PDE.continuous_vecEuclideanNorm.comp
                  (continuous_pi hgradientContinuous)).aestronglyMeasurable
              filter_upwards with v

              simpa only [Function.comp_def, F, Real.norm_eq_abs,
                abs_of_nonneg (PDE.vecEuclideanNorm_nonneg (F v)),
                abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (F v i))] using PDE.vecEuclideanNorm_le_sum_abs (F v)
            _ <= ∑ i : Fin d,
                MeasureTheory.eLpNorm (fun v => |F v i|) (ENNReal.ofReal p)
                  (PDE.volumeOn V) := by
              rw [← Finset.sum_fn]
              exact MeasureTheory.eLpNorm_sum_le Fact.out
            _ = ∑ i : Fin d,
                PDE.eLpNormOn V (ENNReal.ofReal p)
                  (fun v => velocityGradient u (t, v) i - m i) := (Finset.sum_congr rfl fun i x =>
        id
          (eLpNorm_norm (fun v => velocityGradient u (t, v) i - m i)
            (Continuous.aestronglyMeasurable (hgradientContinuous i))))) _)

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum
     :
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
  let sharedTerm_276d698fec := ((velocityCube (0 : PDE.Vec d) 1))
  let sharedTerm_7b6b7cba9e := (ENNReal.ofReal (((2 : Real) ^ d) * (Real.sqrt d * 2)))
  let K  := sharedTerm_7b6b7cba9e

  calc
    PDE.eLpNormOn sharedTerm_276d698fec
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage sharedTerm_276d698fec
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage sharedTerm_276d698fec
                (fun w => velocityGradient u (t, w) i) * v i)) <=
        K * ∑ i : Fin d,
          PDE.eLpNormOn sharedTerm_276d698fec
            (parabolicExponent d)
            (fun v => velocityGradient u (t, v) i -
              PDE.integralAverage sharedTerm_276d698fec
                (fun w => velocityGradient u (t, w) i)) := velocitySlice_sub_gradientMeanAffine_eLpNorm_le d u hu t
    _ <= K * ∑ i : Fin d, K * ∑ j : Fin d,
        PDE.eLpNormOn sharedTerm_276d698fec
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) :=
      mul_le_mul_right (by
          apply Finset.sum_le_sum
          intro i _
          exact velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum d u hu t i) K
    _ = K^2 * ∑ i : Fin d, ∑ j : Fin d,
        PDE.eLpNormOn sharedTerm_276d698fec
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_two]
      ac_rfl
    _ = (sharedTerm_7b6b7cba9e)^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn sharedTerm_276d698fec
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := rfl

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable (d : Nat) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) (t : Real)

include hu
private theorem velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection
     :
    (fun v  =>
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
  let L : PDE.ScalarField d := fun v => PDE.integralAverage V f + ∑ i : Fin d,
    PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i
  have hfContinuous : Continuous f :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous L := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hclosedCompact  :=
    isCompact_velocityClosedCube (0 : PDE.Vec d) 1
  have hsubset : V ⊆ velocityClosedCube (0 ) 1 := by
    intro v hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
    intro i
    exact (hv i).le
  have hf : Integrable f (volume.restrict V) :=
    (hfContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hL : Integrable L (volume.restrict V) :=
    (hLContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset


  have hsub : parabolicMorreyUnitVelocityAffineProjection (f - L) =
      parabolicMorreyUnitVelocityAffineProjection f -
        parabolicMorreyUnitVelocityAffineProjection L := by
    exact parabolicMorreyUnitVelocityAffineProjection_sub f L hf hL (show ∀ i : Fin d, Integrable (fun v => f v * v i) (volume.restrict V) by
        intro i

        exact ((hfContinuous.mul (continuous_apply i)).continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset) (by
            intro i

            exact ((hLContinuous.mul (continuous_apply i)).continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset)
  have hreproduces : parabolicMorreyUnitVelocityAffineProjection L = L := by
    exact parabolicMorreyUnitVelocityAffineProjection_reproduces_affine
      (PDE.integralAverage V f)
      (fun i => PDE.integralAverage V (fun w => velocityGradient u (t, w) i))

  funext v
  rw [congrFun (show (fun v  => parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      parabolicMorreyUnitVelocityAffineProjection f by
      exact parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection u t) v]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - parabolicMorreyUnitVelocityAffineProjection (f - L) v
  simp_all

private theorem velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum
     :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
        (fun v => u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) <=
      ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
  let sharedTerm_b152d7c28b := ((ENNReal.ofReal (((2 : Real) ^ d) * (Real.sqrt d * 2))) ^ 2)
  let sharedTerm_673f8c847b := ((fun v : PDE.Vec d => u (t, v)))
  let V  := velocityCube (0 : PDE.Vec d) 1
  let R  := fun v => u (t, v) -
    (PDE.integralAverage V sharedTerm_673f8c847b + ∑ i : Fin d,
      PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i)
  have huSlice : Continuous sharedTerm_673f8c847b :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous (fun v : PDE.Vec d =>
      PDE.integralAverage V sharedTerm_673f8c847b + ∑ i : Fin d,
        PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i) := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)






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
          (parabolicMorreyUnitVelocityAffineProjection R) := (by
              exact MeasureTheory.eLpNorm_sub_le (by
                  simpa only [parabolicExponent] using
                    (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))))
    _ <= PDE.eLpNormOn V (parabolicExponent d) R +
        ENNReal.ofReal (1 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R :=
      add_le_add_right (by
          exact eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le R (by
              simpa only [R, Pi.sub_def] using
                (huSlice.sub hLContinuous).aestronglyMeasurable)) _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R := by
      rw [← hfactor, add_mul, one_mul]
    _ <= ENNReal.ofReal (2 + 3 * (d : Real)) *
        (sharedTerm_b152d7c28b *
          ∑ i : Fin d, ∑ j : Fin d, PDE.eLpNormOn V (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j)) := mul_le_mul_right (hS3) _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) *
        sharedTerm_b152d7c28b *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
      simp only [V]
      ac_rfl

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

variable {d : Nat} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}




private theorem aemeasurable_spatialAffine_residual

    (hu : ContDiff Real 2 u) :
    AEMeasurable
      (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let ν  := volume.restrict V
  have huStrong : StronglyMeasurable
      (Function.uncurry fun t  => fun v : PDE.Vec d => u (t, v)) := by
    change StronglyMeasurable u
    exact hu.continuous.stronglyMeasurable
  have hAverage : StronglyMeasurable (parabolicMorreyUnitVelocityAverage u) := by
    unfold parabolicMorreyUnitVelocityAverage
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huStrong.integral_prod_right (ν := ν))
  have hCoeff : ∀ i : Fin d,
      StronglyMeasurable (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
    intro i

    unfold parabolicMorreyUnitVelocityCoeffAt
    apply stronglyMeasurable_const.mul
    exact ((show StronglyMeasurable
        (Function.uncurry fun t  => fun v : PDE.Vec d => u (t, v) * v i) by
        change StronglyMeasurable (fun z  => u z * z.2 i)
        exact (hu.continuous.mul ((continuous_apply i).comp continuous_snd)).stronglyMeasurable).integral_prod_right )

  exact (hu.continuous.stronglyMeasurable.sub (by
      unfold parabolicMorreyUnitSpatialAffineProjection
      apply (hAverage.comp_measurable measurable_fst).add
      rw [← Finset.sum_fn]
      refine Finset.stronglyMeasurable_sum Finset.univ fun i _ => ?_
      exact ((hCoeff i).comp_measurable measurable_fst).mul
        (((continuous_apply i).comp continuous_snd).stronglyMeasurable))).aestronglyMeasurable.aemeasurable

variable (d : Nat)

private theorem spatialAffinePoincareGlobalConst_pos  (hd : 1 <= d) :
    0 < (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2 := by
  positivity

private theorem parabolicMorreyUnitSpatialAffinePoincareELp
     (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : ContDiff Real 2 u) :
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
  let sharedTerm_b429004453 := ((((2 : Real) ^ d) * (Real.sqrt d * 2)))
  let sharedTerm_2265d860bf := (∑ i : Fin d, ∑ j : Fin d, parabolicELpNormOn d (fun z => velocityHessian u z i j) (parabolicMorreyUnitBox d))
  let sharedTerm_ac4c956007 := ((2 + 3 * (d : Real)))

  let V  := velocityCube (0 : PDE.Vec d) 1
  let μ  := volume.restrict (Set.Ioo (0 : Real) 1)
  let p  := parabolicExponent d
  let K  := ENNReal.ofReal sharedTerm_b429004453
  let B  := ENNReal.ofReal sharedTerm_ac4c956007 * K ^ 2
  let R  := fun z =>
    u z - parabolicMorreyUnitSpatialAffineProjection u z
  let q  := fun i j t =>
    PDE.eLpNormOn V p (fun v => velocityHessian u (t, v) i j)
  have hp : (1 : ENNReal) <= p := by
    simpa only [p, parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have hRAE : AEMeasurable R (volume.restrict (parabolicMorreyUnitBox d)) := by
    exact aemeasurable_spatialAffine_residual hu









  have hCnormalize :
      ENNReal.ofReal
          ((sharedTerm_ac4c956007) * (sharedTerm_b429004453)^2) = B := by
    dsimp only [B, K]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  calc
    parabolicELpNormOn d R (parabolicMorreyUnitBox d) =
        eLpNorm (fun t => PDE.eLpNormOn V p (fun v => R (t, v))) p μ := parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice R hRAE
    _ <= B * eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ := (by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
          ((aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm R hRAE).aestronglyMeasurable) ?_
        filter_upwards with t
        exact (show ∀ t : Real,
      PDE.eLpNormOn V p (fun v => R (t, v)) <=
        B * ∑ i : Fin d, ∑ j : Fin d, q i j t by
            intro t
            exact velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum d u hu t) t)
    _ <= B * ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := mul_le_mul_right (by
        calc
          eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ =
              eLpNorm (∑ i : Fin d, fun t => ∑ j : Fin d, q i j t) p μ := by
            rw [Finset.sum_fn]
          _ <= ∑ i : Fin d, eLpNorm (fun t => ∑ j : Fin d, q i j t) p μ := eLpNorm_sum_le hp
          _ <= ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
            apply Finset.sum_le_sum
            intro i _
            rw [← Finset.sum_fn]
            exact eLpNorm_sum_le hp) B
    _ = B * sharedTerm_2265d860bf := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      exact parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (fun z => velocityHessian u z i j) ((show ∀ i j : Fin d,
      AEMeasurable (fun z => velocityHessian u z i j)
        (volume.restrict (parabolicMorreyUnitBox d)) by
              intro i j
              exact (_root_.HypoellipticAleksandrov.Parabolic.velocityHessian_continuous hu).aestronglyMeasurable.aemeasurable) i j)
    _ = ENNReal.ofReal
          ((sharedTerm_ac4c956007) *
            (sharedTerm_b429004453)^2) *
        sharedTerm_2265d860bf := by
      rw [hCnormalize]

/-- Smooth spatial second-order Poincare inequality on the fixed unit
parabolic box, modulo the per-time canonical velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareELpConst
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d,
        ContDiff Real 2 u ->
        parabolicELpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          ENNReal.ofReal C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicELpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := (Exists.intro ((2 + 3 * ↑d) * (2 ^ d * (√↑d * 2)) ^ 2)
  ⟨spatialAffinePoincareGlobalConst_pos d hd, fun u hu => parabolicMorreyUnitSpatialAffinePoincareELp d u hu⟩)

/-- Real-valued corollary of the smooth spatial second-order Poincare estimate
on the fixed unit parabolic box. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareConst
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d,
        ContDiff Real 2 u ->
        parabolicLpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicLpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := by
  let C : Real :=
    (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · exact spatialAffinePoincareGlobalConst_pos d hd
  · intro u hu
    let R  := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let H  := fun i j z =>
      velocityHessian u z i j

    have hHmem : ∀ i j : Fin d,
        MemLp (H i j) (parabolicExponent d)
          (volume.restrict (parabolicMorreyUnitBox d)) := by
      intro i j
      have hContinuous  :=
        _root_.HypoellipticAleksandrov.Parabolic.velocityHessian_continuous (i := i) (j := j) hu
      exact Continuous.memLp_parabolicMorreyUnitBox hContinuous
    have hHneTop : ∀ i j : Fin d,
        parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) ≠ ⊤ := by
      intro i j
      exact (hHmem i j).eLpNorm_ne_top




    change (parabolicELpNormOn d R (parabolicMorreyUnitBox d)).toReal <=
      C * ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal
    calc
      (parabolicELpNormOn d R (parabolicMorreyUnitBox d)).toReal <=
          (ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := (ENNReal.toReal_mono (by
                exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
                    apply ENNReal.sum_ne_top.mpr
                    intro i _
                    apply ENNReal.sum_ne_top.mpr
                    intro j _
                    exact hHneTop i j)) (show parabolicELpNormOn d R (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) by
                exact parabolicMorreyUnitSpatialAffinePoincareELp d u hu))
      _ = C * (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show _ by
            exact (spatialAffinePoincareGlobalConst_pos d hd).le)]
      _ = C * ∑ i : Fin d, (∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        congr 1
        exact ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHneTop i j
      _ = C * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact ENNReal.toReal_sum fun j _ => hHneTop i j

end HypoellipticAleksandrov.Parabolic
