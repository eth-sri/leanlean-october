module

public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence
public import PDEFoundation.Measure.LpDominatedConvergence
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence

open private HypoellipticAleksandrov.Parabolic.parabolicConvolution_eq_leftConvolution from HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence


/-!
# Decay of the parabolic convolution commutator

This module proves the finite-`L^p` decay of the residual obtained by
convolving a bounded coefficient field and a matrix field separately.
It contains no equation or solution-theoretic assertion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped Convolution ENNReal Topology

variable {d : Nat}

/-- The entrywise right convolution of a time--velocity matrix field. -/
def parabolicMatrixConvolution
     (H : TimeVelocity d → PDE.Mat d) (n : Nat) :
    TimeVelocity d → PDE.Mat d :=
  fun z i j => parabolicConvolution
    (fun y => H y i j) (parabolicMollifier d n) z

/-- The residual caused by convolving a coefficient and a Hessian separately. -/
def parabolicConvolutionCommutator
     (A : CoefficientField d)
    (H : TimeVelocity d → PDE.Mat d) (n : Nat) : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z =>
    parabolicConvolution
      (fun y => matrixContraction (coefficientAt A y) (H y))
      (parabolicMollifier d n) z -
    matrixContraction
      (coefficientAt (parabolicMollifyCoefficient A n) z)
      (parabolicMatrixConvolution H n z)

/-- A bounded a.e.-convergent multiplier commutes with two strongly
convergent finite-`L^p` approximations. -/
theorem tendsto_eLpNorm_bounded_multiplier_commutator
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ENNReal}
    (hpOne : 1 ≤ p) (hpTop : p ≠ ∞)
    {a h c : α → Real}
    {an hn cn : Nat → α → Real} {M : Real}
    (hM : 0 ≤ M)
    (ha : AEStronglyMeasurable a μ)
    (han : ∀ n, AEStronglyMeasurable (an n) μ)
    (hh : MemLp h p μ)
    (hhn : ∀ n, AEStronglyMeasurable (hn n) μ)
    (hc : c =ᵐ[μ] fun x => a x * h x)
    (hcn : ∀ n, AEStronglyMeasurable (cn n) μ)
    (haBound : ∀ n, ∀ᵐ x ∂μ, |an n x| ≤ M)
    (haLimitBound : ∀ᵐ x ∂μ, |a x| ≤ M)
    (hae : ∀ᵐ x ∂μ,
      Tendsto (fun n => an n x) atTop (nhds (a x)))
    (hhnSub : Tendsto (fun n => eLpNorm (hn n - h) p μ)
      atTop (nhds 0))
    (hcnSub : Tendsto (fun n => eLpNorm (cn n - c) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (cn n - fun x => an n x * hn n x) p μ) atTop (nhds 0) := by
  let sharedTerm_59e9f2fc27 := ((fun n => eLpNorm (fun x => an n x * (hn n x - h x)) p μ))
  let sharedTerm_53f3f2445a := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0)))


  have hmiddleMeas (n : Nat) : AEStronglyMeasurable
      (fun x => (a x - an n x) * h x) μ :=
    (ha.sub (han n)).mul hh.aestronglyMeasurable
  have hmiddleBound (n : Nat) : ∀ᵐ x ∂μ,
      ‖(a x - an n x) * h x‖ ≤ ‖(2 * M) * |h x|‖ := by
    filter_upwards [haLimitBound, haBound n] with x hax hanx
    simp only [Real.norm_eq_abs, abs_mul]

    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hM, abs_abs]

    exact mul_le_mul_of_nonneg_right (by
        calc
          |a x - an n x| ≤ |a x| + |an n x| := abs_sub _ _
          _ ≤ 2 * M := by linarith) (abs_nonneg _)


  have hlastBound (n : Nat) :
      eLpNorm (fun x => an n x * (hn n x - h x)) p μ ≤
        ENNReal.ofReal M * eLpNorm (hn n - h) p μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((han n).mul ((hhn n).sub hh.aestronglyMeasurable)) ?_ _
    filter_upwards [haBound n] with x hx
    simp only [Pi.mul_apply, Pi.sub_apply, Real.norm_eq_abs, abs_mul]
    change |an n x| * |hn n x - h x| ≤ M * |hn n x - h x|
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)



  let r  := fun n x =>
    (cn n x - c x) +
      ((a x - an n x) * h x + an n x * (h x - hn n x))
  have hrBound (n : Nat) : eLpNorm (r n) p μ ≤
      eLpNorm (cn n - c) p μ +
        eLpNorm (fun x => (a x - an n x) * h x) p μ +
        eLpNorm (fun x => an n x * (h x - hn n x)) p μ := by
    change eLpNorm ((cn n - c) +
      ((fun x => (a x - an n x) * h x) +
        fun x => an n x * (h x - hn n x))) p μ ≤ _
    calc
      eLpNorm ((cn n - c) +
          (fun x => (a x - an n x) * h x + an n x * (h x - hn n x))) p μ ≤
          eLpNorm (cn n - c) p μ + eLpNorm
            (fun x => (a x - an n x) * h x + an n x * (h x - hn n x)) p μ :=
        eLpNorm_add_le   hpOne
      _ ≤ _ := (Trans.trans (add_le_add_right (eLpNorm_add_le hpOne) (eLpNorm (cn n - c) p μ))
  (Eq.symm
    (add_assoc (eLpNorm (cn n - c) p μ) (eLpNorm (fun x => (a x - an n x) * h x) p μ)
      (eLpNorm (fun x => an n x * (h x - hn n x)) p μ))))

  have hr : Tendsto (fun n => eLpNorm (r n) p μ) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      sharedTerm_53f3f2445a
      (by
          simpa using (hcnSub.add (by
              simpa using PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated


                hpOne hpTop hmiddleMeas MemLp.zero (hh.abs.const_mul (2 * M)) hmiddleBound (by
                    filter_upwards [hae] with x hx
                    have hdiff :=
                      (tendsto_const_nhds : Tendsto (fun _ : Nat => a x) atTop (nhds (a x))).sub hx

                    simpa using (hdiff.mul_const (h x))))).add (show Tendsto (fun n => eLpNorm
      (fun x => an n x * (h x - hn n x)) p μ) atTop (nhds 0) by
              have hlastEq : (fun n => eLpNorm
                  (fun x => an n x * (h x - hn n x)) p μ) =
                  sharedTerm_59e9f2fc27 := by
                funext n
                rw [show (fun x => an n x * (h x - hn n x)) =
                  -(fun x => an n x * (hn n x - h x)) by
                    funext x
                    simp only [Pi.neg_apply]
                    ring, eLpNorm_neg]
              rw [hlastEq]
              exact (by

                  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
                    sharedTerm_53f3f2445a
                  · exact (by
                      simpa using ENNReal.Tendsto.const_mul hhnSub
                        (a := ENNReal.ofReal M) (Or.inr ENNReal.ofReal_ne_top))
                  · exact Filter.Eventually.of_forall fun n => bot_le
                  · exact Filter.Eventually.of_forall hlastBound)))
    · exact Filter.Eventually.of_forall fun n => bot_le
    · exact Filter.Eventually.of_forall hrBound
  have heq (n : Nat) :
      (cn n - fun x => an n x * hn n x) =ᵐ[μ] r n := by
    filter_upwards [hc] with x hcx
    dsimp [r]
    rw [hcx]
    ring
  have heLp (n : Nat) : eLpNorm (cn n - fun x => an n x * hn n x) p μ =
      eLpNorm (r n) p μ := eLpNorm_congr_ae (heq n)
  simpa only [heLp] using hr

variable {d : Nat}




private theorem abs_parabolicConvolution_le_of_abs_le
     {f : HypoellipticAleksandrov.Parabolic.ScalarField d} {M : Real}
    (hf : LocallyIntegrable f ) (hbound : ∀ z, |f z| ≤ M)
    (n : Nat) (z : TimeVelocity d) :
    |parabolicConvolution f (parabolicMollifier d n) z| ≤ M := by
  have hconstLoc (c : Real) : LocallyIntegrable (fun _ : TimeVelocity d => c)  :=
    locallyIntegrable_const c
  have hexists (g : HypoellipticAleksandrov.Parabolic.ScalarField d) (hg : LocallyIntegrable g ) :
      ConvolutionExistsAt (parabolicMollifier d n) g z
        (ContinuousLinearMap.lsmul Real Real)  :=
    (hasCompactSupport_parabolicMollifier d n).convolutionExists_left
      _
      (contDiff_parabolicMollifier d n).continuous hg z
  rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicConvolution_eq_leftConvolution]
  rw [abs_le]
  constructor
  · have hmono := convolution_mono_right
      (hexists (fun _  => -M) (hconstLoc (-M)))
      (hexists f hf) (parabolicMollifier_nonneg d n)
      (fun y => (abs_le.mp (hbound y)).1)

    exact (show (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
          (fun _  => -M)) z = -M by
        exact ContDiffBump.normed_convolution_eq_right
            (fun _ _ => rfl)).symm.le.trans hmono
  · have hmono := convolution_mono_right (hexists f hf)
      (hexists (fun _  => M) (hconstLoc M))
      (parabolicMollifier_nonneg d n) (fun y => (abs_le.mp (hbound y)).2)

    exact hmono.trans (show (parabolicMollifier d n ⋆[ContinuousLinearMap.lsmul Real Real, volume]
          (fun _  => M)) z = M by
        exact ContDiffBump.normed_convolution_eq_right
            (fun _ _ => rfl)).le

private theorem parabolicConvolution_finset_sum  {ι : Type*}
    (s : Finset ι) (f : ι → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ i ∈ s, LocallyIntegrable (f i) ) (n : Nat) :
    parabolicConvolution (fun z => ∑ i ∈ s, f i z) (parabolicMollifier d n) =
      fun z => ∑ i ∈ s, parabolicConvolution (f i) (parabolicMollifier d n) z := by
  letI : DecidableEq ι := Classical.decEq _
  induction s using Finset.induction_on with
  | empty =>
    rw [_root_.HypoellipticAleksandrov.Parabolic.parabolicConvolution_eq_leftConvolution]
    exact convolution_zero
  | insert a s has ih =>


    have hconv : parabolicConvolution (f a + (fun z => ∑ i ∈ s, f i z))
        (parabolicMollifier d n) =
        parabolicConvolution (f a) (parabolicMollifier d n) +
          parabolicConvolution (fun z => ∑ i ∈ s, f i z) (parabolicMollifier d n) := by
      apply ConvolutionExists.add_distrib
      · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
          _ (hf a (Finset.mem_insert_self _ _))
          (contDiff_parabolicMollifier d n).continuous
      · exact (hasCompactSupport_parabolicMollifier d n).convolutionExists_right
          _ (locallyIntegrable_finset_sum s fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (contDiff_parabolicMollifier d n).continuous
    simp_rw [Finset.sum_insert has]
    change parabolicConvolution (f a + (fun z => ∑ i ∈ s, f i z))
      (parabolicMollifier d n) = _
    rw [hconv, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rfl

variable (A : CoefficientField d) (H : TimeVelocity d → PDE.Mat d)

private theorem parabolicConvolution_matrixContraction_eq_sum

    (hprod : ∀ i j : Fin d,
      LocallyIntegrable (fun z => coefficientAt A z i j * H z i j) )
    (n : Nat) :
    parabolicConvolution (fun z => matrixContraction (coefficientAt A z) (H z))
      (parabolicMollifier d n) =
      fun z => ∑ i : Fin d, ∑ j : Fin d,
        parabolicConvolution (fun y => coefficientAt A y i j * H y i j)
          (parabolicMollifier d n) z := (Trans.trans
  (Trans.trans
    (Eq.refl (parabolicConvolution (fun z => matrixContraction (coefficientAt A z) (H z)) (parabolicMollifier d n)))
    (parabolicConvolution_finset_sum Finset.univ (fun i z => ∑ j, coefficientAt A z i j * H z i j)
      (fun i x => locallyIntegrable_finset_sum Finset.univ fun j x => hprod i j) n))
  (funext fun z =>
    Finset.sum_congr rfl fun i a =>
      congrFun
        (parabolicConvolution_finset_sum Finset.univ (fun j y => coefficientAt A y i j * H y i j) (fun j x => hprod i j)
          n)
        z))

/-- The entrywise parabolic convolution commutator tends to zero in finite
`L^(d + 1)` norm on every compact carrier. -/
theorem tendsto_eLpNorm_parabolicConvolutionCommutator_on_compact

    (K : HypoellipticAleksandrov.Parabolic.Region d) (hK : IsCompact K)
    (M : Real) (hM : 0 ≤ M)
    (hAmeas : ∀ i j : Fin d,
      AEStronglyMeasurable (fun z => coefficientAt A z i j) )
    (hALoc : ∀ i j : Fin d,
      LocallyIntegrable (fun z => coefficientAt A z i j) )
    (hABound : ∀ i j : Fin d, ∀ z,
      |coefficientAt A z i j| ≤ M)
    (hHMem : ∀ i j : Fin d,
      MemLp (fun z => H z i j) (parabolicExponent d) ) :
    Tendsto (fun n => eLpNorm
      (parabolicConvolutionCommutator A H n)
      (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) := by
  let sharedTerm_591a9531e6 := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ENNReal)) atTop (nhds 0)))
  let sharedTerm_7005f9abe2 := (Fin d → Fin d → Nat → HypoellipticAleksandrov.Parabolic.ScalarField d)
  let sharedTerm_5ba068bf11 := (Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
  letI : DecidableEq (Fin d) := Classical.decEq _
  let μK : Measure (TimeVelocity d) := volume.restrict K
  letI : IsFiniteMeasure μK := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let p  := parabolicExponent d
  have hpOne : (1 : ENNReal) ≤ p := by
    change 1 ≤ (d : ENNReal) + 1
    have hd : (0 : ENNReal) ≤ (d : ENNReal) := bot_le
    simpa only [zero_add] using add_le_add_left hd (1 )
  have hpTop : p ≠ ∞ := by
    change (d : ENNReal) + 1 ≠ ∞
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.coe_ne_top, ENNReal.one_ne_top⟩
  let a : sharedTerm_5ba068bf11 :=
    fun i j z => coefficientAt A z i j
  let an : sharedTerm_7005f9abe2 :=
    fun i j n z => parabolicConvolution (a i j) (parabolicMollifier d n) z
  let h : sharedTerm_5ba068bf11 :=
    fun i j z => H z i j
  let hn : sharedTerm_7005f9abe2 :=
    fun i j n z => parabolicConvolution (h i j) (parabolicMollifier d n) z
  let c : sharedTerm_5ba068bf11 :=
    fun i j z => a i j z * h i j z
  let cn : sharedTerm_7005f9abe2 :=
    fun i j n z => parabolicConvolution (c i j) (parabolicMollifier d n) z
  let residual : sharedTerm_7005f9abe2 :=
    fun i j n z => cn i j n z - an i j n z * hn i j n z
  have hprodMem (i j : Fin d) : MemLp (c i j) p  := by
    refine MemLp.of_le_mul (c := M) (hHMem i j) ?_ ?_
    · exact (hAmeas i j).mul (hHMem i j).aestronglyMeasurable
    · filter_upwards with z
      dsimp [c, a, h]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hABound i j z) (abs_nonneg _)
  have hprodLoc (i j : Fin d)  :=
    (hprodMem i j).locallyIntegrable hpOne
  have hconvMatrix (n : Nat) :
      parabolicConvolution
        (fun z => matrixContraction (coefficientAt A z) (H z))
        (parabolicMollifier d n) =
        fun z => ∑ i : Fin d, ∑ j : Fin d,
          cn i j n z := by
    exact parabolicConvolution_matrixContraction_eq_sum A H
        (fun i j => hprodLoc i j) n
  have hhnSub (i j : Fin d) : Tendsto
      (fun n => eLpNorm (hn i j n - h i j) p μK) atTop (nhds 0) := by
    have hglobal := tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop (hHMem i j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      sharedTerm_591a9531e6
      hglobal
    · exact Filter.Eventually.of_forall fun n => bot_le
    · filter_upwards with n
      exact eLpNorm_restrict_le _ p volume K
  have hcnSub (i j : Fin d) : Tendsto
      (fun n => eLpNorm (cn i j n - c i j) p μK) atTop (nhds 0) := by
    have hglobal := tendsto_eLpNorm_parabolicConvolution_sub hpOne hpTop (hprodMem i j)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      sharedTerm_591a9531e6
      hglobal
    · exact Filter.Eventually.of_forall fun n => bot_le
    · filter_upwards with n
      exact eLpNorm_restrict_le _ p volume K
  have haMeas (i j : Fin d) : AEStronglyMeasurable (a i j) μK := by
    exact (hAmeas i j).mono_measure Measure.restrict_le_self
  have hanMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (an i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution (hALoc i j)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hhMem (i j : Fin d) : MemLp (h i j) p μK := (hHMem i j).restrict K
  have hhnMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (hn i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution ((hHMem i j).locallyIntegrable hpOne)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hcnMeas (i j : Fin d) (n : Nat) : AEStronglyMeasurable (cn i j n) μK := by
    exact AEStronglyMeasurable.mono_measure
      ((contDiff_parabolicConvolution (hprodLoc i j)
      (contDiff_parabolicMollifier d n)
      (hasCompactSupport_parabolicMollifier d n)).continuous.aestronglyMeasurable)
      Measure.restrict_le_self
  have hanBound (i j : Fin d) (n : Nat) : ∀ᵐ z ∂μK, |an i j n z| ≤ M := by
    filter_upwards with z
    exact abs_parabolicConvolution_le_of_abs_le (hALoc i j) (hABound i j) n z
  have haLimitBound (i j : Fin d) : ∀ᵐ z ∂μK, |a i j z| ≤ M := by
    exact Filter.Eventually.of_forall (hABound i j)
  have hae (i j : Fin d) : ∀ᵐ z ∂μK,
      Tendsto (fun n => an i j n z) atTop (nhds (a i j z)) := by
    exact Filter.Eventually.filter_mono
      (ae_mono Measure.restrict_le_self)
      (tendsto_ae_parabolicConvolution_of_locallyIntegrable (hALoc i j))
  have hcoord (i j : Fin d) : Tendsto
      (fun n => eLpNorm (residual i j n) p μK) atTop (nhds 0) := tendsto_eLpNorm_bounded_multiplier_commutator hpOne hpTop hM
      (haMeas i j) (hanMeas i j) (hhMem i j) (hhnMeas i j)
      (EventuallyEq.rfl) (hcnMeas i j) (hanBound i j) (haLimitBound i j)
      (hae i j) (hhnSub i j) (hcnSub i j)
  have hreconstruction (n : Nat) : parabolicConvolutionCommutator A H n =
      fun z => ∑ i : Fin d, ∑ j : Fin d, residual i j n z := by
    funext z
    unfold parabolicConvolutionCommutator parabolicMatrixConvolution
    rw [hconvMatrix n]
    change (∑ i : Fin d, ∑ j : Fin d, cn i j n z) -
      ∑ i : Fin d, ∑ j : Fin d, an i j n z * hn i j n z =
      ∑ i : Fin d, ∑ j : Fin d, residual i j n z
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]

  have hsumBound (n : Nat) : eLpNorm (parabolicConvolutionCommutator A H n) p μK ≤
      ∑ i : Fin d, ∑ j : Fin d, eLpNorm (residual i j n) p μK := by
    rw [hreconstruction n, ← Finset.sum_fn]
    calc
      eLpNorm (∑ i : Fin d, fun z => ∑ j : Fin d, residual i j n z) p μK ≤
          ∑ i : Fin d, eLpNorm (fun z => ∑ j : Fin d, residual i j n z) p μK :=
        eLpNorm_sum_le hpOne
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, eLpNorm (residual i j n) p μK := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hpOne

  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    sharedTerm_591a9531e6
    (show _ by
        simpa only [Finset.sum_const_zero] using
          tendsto_finset_sum Finset.univ (fun i _ =>
            tendsto_finset_sum Finset.univ (fun j _ => hcoord i j)))
  · exact Filter.Eventually.of_forall fun n => bot_le
  · exact Filter.Eventually.of_forall hsumBound

end HypoellipticAleksandrov.Parabolic
