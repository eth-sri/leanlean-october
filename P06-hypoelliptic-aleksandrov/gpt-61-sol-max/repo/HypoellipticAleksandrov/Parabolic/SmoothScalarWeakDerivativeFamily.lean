module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2Norm
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1WeakLeibniz
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexSplitSuccessor
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
import all HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn from HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
open private HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight from HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants


/-!
# Weak derivative families from smooth scalar functions

This module constructs the canonical finite weak-derivative family of a
classically smooth scalar function whose coordinate derivatives are bounded
on an open set of finite volume.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal Topology




private theorem coordinateIteratedFDeriv_contDiffOn
    {d N m : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiffOn ℝ N f U)
    (alpha : TimeVelocityMultiIndex d) (horder : m + alpha.order ≤ N) :
    ContDiffOn ℝ m
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha f) U := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := (hf.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right
    (m := m) (i := alpha.coordinateList.length) (by
      rw [TimeVelocityMultiIndex.length_coordinateList]
      exact_mod_cast horder)
  exact (contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i ↦ timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi




variable {d L : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} (hUopen : IsOpen U)

include hUopen in
/-- Classical coordinate derivatives satisfy the corresponding weak-family condition. -/
theorem coordinateIteratedFDeriv_memLp

    (hUfinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) U < ∞)
    (B : ParabolicDerivativeIndex d L → ℝ)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiffOn ℝ L f U)
    (hbound : ∀ (alpha : ParabolicDerivativeIndex d L)
      (z : TimeVelocity d), z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z| ≤ B alpha)
    (alpha : ParabolicDerivativeIndex d L) :
    ParabolicMemLpOn U 2
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f) := by
  letI : IsFiniteMeasure (timeVelocityVolumeOn U) :=
    isFiniteMeasure_restrict.mpr hUfinite.ne
  have hcontinuous := _root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hUopen f hf alpha.1
    ((_root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight alpha.1).trans alpha.2)

  apply MemLp.of_bound (hcontinuous.aestronglyMeasurable hUopen.measurableSet) (B alpha)
  filter_upwards [ae_restrict_mem hUopen.measurableSet] with z hz
  exact hbound alpha z hz

section
variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiffOn ℝ L f U) (beta : ParabolicDerivativeIndex d L)

include hUopen hf
/-- Classical coordinate derivatives satisfy the corresponding weak-family condition. -/
theorem coordinateIteratedFDeriv_timeSucc


    (h : beta.1.parabolicWeight + 2 ≤ L) :
    HasWeakTimeDerivOn U
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 f)
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (ParabolicDerivativeIndex.timeSucc beta h).1 f) := by
  have horder : 1 + beta.1.order ≤ L := by
    have hob := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight beta.1
    omega

  have hweak := contDiffOn_one_hasWeakTimeDerivOn U hUopen
    _ (coordinateIteratedFDeriv_contDiffOn hUopen f hf beta.1 horder)
  apply hweak.congr_ae Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hUopen.measurableSet] with z hz
  rw [ParabolicDerivativeIndex.coe_timeSucc_eq_add_single]
  have hadd := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    beta.1 (timeCoord d) f z
      ((hf.contDiffAt (hUopen.mem_nhds hz)).of_le (by
        exact_mod_cast (show beta.1.order + 1 ≤ L by omega)))
  exact hadd.symm

/-- Classical coordinate derivatives satisfy the corresponding weak-family condition. -/
theorem coordinateIteratedFDeriv_velocitySucc

     (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    HasWeakVelocityPartialDerivOn U i
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 f)
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (ParabolicDerivativeIndex.velocitySucc beta i h).1 f) := by
  have horder : 1 + beta.1.order ≤ L := by
    have hob := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight beta.1
    omega

  have hweak := contDiffOn_one_hasWeakVelocityPartialDerivOn U hUopen i
    _ (coordinateIteratedFDeriv_contDiffOn hUopen f hf beta.1 horder)
  apply hweak.congr_ae Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hUopen.measurableSet] with z hz
  rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
  have hadd := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    beta.1 (velocityCoord i) f z
      ((hf.contDiffAt (hUopen.mem_nhds hz)).of_le (by
        exact_mod_cast (show beta.1.order + 1 ≤ L by omega)))
  exact hadd.symm
end


variable (d L : ℕ) (U : HypoellipticAleksandrov.Parabolic.Region d) (hUopen : IsOpen U) (hUfinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) U < ∞) (B : ParabolicDerivativeIndex d L → ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiffOn ℝ L f U) (hbound : ∀ (alpha : ParabolicDerivativeIndex d L) (z : TimeVelocity d), z ∈ U → |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z| ≤ B alpha)

/-- The canonical coherent weak-derivative family of a classically smooth
scalar function with bounded derivatives on a finite-volume open set. -/
def ParabolicWeakDerivativeFamily.ofContDiffOnBounded
     :
    ParabolicWeakDerivativeFamily d L U f where
  representative := fun alpha ↦
    TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f
  memLp := coordinateIteratedFDeriv_memLp hUopen hUfinite B f hf hbound
  zero_ae := Filter.Eventually.of_forall fun z ↦ TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f z
  hasWeakTimeSucc := coordinateIteratedFDeriv_timeSucc hUopen f hf
  hasWeakVelocitySucc := coordinateIteratedFDeriv_velocitySucc hUopen f hf

@[simp] theorem
    ParabolicWeakDerivativeFamily.ofContDiffOnBounded_representative

    (alpha : ParabolicDerivativeIndex d L) :
    (ParabolicWeakDerivativeFamily.ofContDiffOnBounded
      d L U hUopen hUfinite B f hf hbound).representative alpha =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f :=
  rfl

private theorem coordinateIteratedFDeriv_eLpNorm_sq_le
    {d L : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d} (hUopen : IsOpen U)
    (hUfinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) U < ∞)
    (B : ParabolicDerivativeIndex d L → ℝ)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hbound : ∀ (alpha : ParabolicDerivativeIndex d L)
      (z : TimeVelocity d), z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z| ≤ B alpha)
    (hUne : U.Nonempty) (alpha : ParabolicDerivativeIndex d L)
    (hmeas : AEStronglyMeasurable
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f)
      (timeVelocityVolumeOn U)) :
    (ENNReal.toReal (eLpNorm
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f) 2
      (timeVelocityVolumeOn U))) ^ 2 ≤
      volume.real U * (B alpha) ^ 2 := by
  letI : IsFiniteMeasure (timeVelocityVolumeOn U) :=
    isFiniteMeasure_restrict.mpr hUfinite.ne
  obtain ⟨z, hz⟩ := hUne
  have hB : 0 ≤ B alpha :=
    (abs_nonneg (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z)).trans
      (hbound alpha z hz)
  have hpoint : ∀ᵐ z ∂timeVelocityVolumeOn U,
      ‖TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z‖ ≤
        ‖B alpha‖ := by
    filter_upwards [ae_restrict_mem hUopen.measurableSet] with y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound alpha y hy



  calc
    (ENNReal.toReal (eLpNorm
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f) 2
        (timeVelocityVolumeOn U))) ^ 2 ≤
        (ENNReal.toReal (eLpNorm (fun _ : TimeVelocity d ↦ B alpha) 2
          (timeVelocityVolumeOn U))) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (memLp_const _).eLpNorm_ne_top (eLpNorm_mono_ae (p := (2 )) hmeas hpoint)) 2
    _ = volume.real U * (B alpha) ^ 2 := by
      rw [eLpNorm_const' (B alpha) (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_mul, enorm_eq_nnnorm,
        Measure.restrict_apply_univ, one_div, measureReal_def]
      rw [← ENNReal.toReal_rpow, mul_pow]
      norm_num only [ENNReal.toReal_ofNat]
      rw [one_div]
      have hroot : ((volume U).toReal ^ (2 : ℝ)⁻¹) ^ 2 =
          (volume U).toReal := Real.rpow_inv_natCast_pow (x := (volume U).toReal) (n := 2)
          ENNReal.toReal_nonneg (by norm_num)
      rw [hroot]
      simp [Real.norm_eq_abs, abs_of_nonneg hB, mul_comm]

theorem ParabolicWeakDerivativeFamily.squaredL2Norm_ofContDiffOnBounded_le
    (d L : ℕ)
    (U : HypoellipticAleksandrov.Parabolic.Region d)
    (hUopen : IsOpen U)
    (hUfinite :
      (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) U < ∞)
    (B : ParabolicDerivativeIndex d L → ℝ)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ContDiffOn ℝ L f U)
    (hbound :
      ∀ (alpha : ParabolicDerivativeIndex d L)
        (z : TimeVelocity d), z ∈ U →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv
          alpha.1 f z| ≤ B alpha) :
    ParabolicWeakDerivativeFamily.squaredL2Norm
        (ParabolicWeakDerivativeFamily.ofContDiffOnBounded
          d L U hUopen hUfinite B f hf hbound) ≤
      volume.real U *
        ∑ alpha : ParabolicDerivativeIndex d L, (B alpha) ^ 2 := by
  classical
  by_cases hU : U = ∅
  · simp_all [ParabolicWeakDerivativeFamily.squaredL2Norm, timeVelocityVolumeOn]
  ·
    unfold ParabolicWeakDerivativeFamily.squaredL2Norm
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun alpha _ ↦
      coordinateIteratedFDeriv_eLpNorm_sq_le hUopen hUfinite B f hbound (Set.nonempty_iff_ne_empty.mpr hU) alpha
        (coordinateIteratedFDeriv_memLp hUopen hUfinite B f hf hbound alpha).aestronglyMeasurable

end HypoellipticAleksandrov.Parabolic
