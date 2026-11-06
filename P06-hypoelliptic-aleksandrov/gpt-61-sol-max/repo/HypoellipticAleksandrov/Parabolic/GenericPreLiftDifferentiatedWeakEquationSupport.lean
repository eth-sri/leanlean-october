module

public import HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLocality
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
public import HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyShift
import Aesop
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
import Mathlib.Tactic.Bound
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
import all HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
open private HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight from HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants


/-!
# Generic pre-lift differentiated weak equation

This module derives the differentiated scalar equation at the stage immediately
before adjoining the next spatial derivatives to the coherent weak-derivative
family.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

namespace GenericPreLiftDifferentiatedWeakEquationSupport

open MeasureTheory
open scoped BigOperators ENNReal Topology
section
variable {d : ℕ}







private theorem timeDerivative_eq_coordinateIteratedFDeriv
     (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ 1 f z) :
    timeDerivative f z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) f z := by
  have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (timeCoord d) f z
      (by simp_all [TimeVelocityMultiIndex.order, VelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])
  simp only [zero_add, timeVelocityBasis_time] at h
  rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex d) f = f by
    aesop] at h
  exact h.symm
section
variable {beta : TimeVelocityMultiIndex d} (gamma : TimeVelocityMultiIndex.Split beta)

private theorem split_left_eq_zero_of_not_ne
      (h : ¬ gamma.left ≠ 0) :
    gamma.left = 0 := not_ne_iff.mp h
private theorem split_eq_default_of_left_eq_zero
      (h : gamma.left = 0) :
    gamma = default := by
  funext c
  apply Fin.ext
  have hc : (gamma c : ℕ) = gamma.left c := rfl
  rw [hc, h]
  rfl
end

private alias order_le_parabolicWeight := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight

end


section
variable {d M : ℕ}

section
variable (alpha : ParabolicDerivativeIndex d M) (i : Fin d)

private def addVelocityIndex
      :
    ParabolicDerivativeIndex d (M + 1) :=
  ⟨alpha.1 + Pi.single (velocityCoord i) 1, by
    aesop⟩

@[simp] private theorem coe_addVelocityIndex
      :
    (addVelocityIndex alpha i).1 =
      alpha.1 + Pi.single (velocityCoord i) 1 := rfl
end


variable {U : HypoellipticAleksandrov.Parabolic.Region d}

private theorem coordinateDerivative_contDiffOn
      (hU : IsOpen U)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiffOn ℝ (M + 1) f U)
    (i : Fin d) :
    ContDiffOn ℝ M
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) f) U := by
  intro z hz
  let alpha : TimeVelocityMultiIndex d := Pi.single (velocityCoord i) 1
  unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
  have hi := (hf.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right
    (m := M) (i := alpha.coordinateList.length) (by simp [alpha])
  exact ((contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun k ↦ timeVelocityBasis
      (alpha.coordinateList.get k)))).clm_apply
        hi).contDiffWithinAt

private theorem coordinateDerivative_majorant

    (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (B : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hB : ∀ alpha z, z ∈ U →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 f z| ≤ B alpha)
    (i : Fin d) (alpha : ParabolicDerivativeIndex d M)
    (z : TimeVelocity d) (hz : z ∈ U)
    (hf : ContDiffAt ℝ (alpha.1.order + 1) f z) :
    |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single (velocityCoord i) 1) f) z| ≤
      B (addVelocityIndex alpha i) := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at]
  exact hB (addVelocityIndex alpha i) z hz
  exact hf
end


section
variable {d L : ℕ}

private theorem splitRight_default
     (beta : ParabolicDerivativeIndex d L) :
    ParabolicDerivativeIndex.splitRight beta default = beta := rfl

private theorem parabolicWeakMulRepresentative_eq_zero_left_add_proper
     (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    {U : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (Du : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) (z : TimeVelocity d) :
    parabolicWeakMulRepresentative q Du beta z =
      q z * Du.representative beta z +
        ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if _hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
              Du.representative
                (ParabolicDerivativeIndex.splitRight beta gamma) z
          else 0 := by
  classical
  unfold parabolicWeakMulRepresentative
  have hsingle :
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if gamma.left = 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
            Du.representative
              (ParabolicDerivativeIndex.splitRight beta gamma) z
        else 0) = q z * Du.representative beta z := by
    rw [Fintype.sum_eq_single
      (default : TimeVelocityMultiIndex.Split beta.1)]
    · have hleft :
          (default : TimeVelocityMultiIndex.Split beta.1).left = 0 := rfl
      rw [hleft, splitRight_default]
      simp
    · intro gamma hne
      by_cases hleft : gamma.left = 0
      · exact (hne (split_eq_default_of_left_eq_zero gamma hleft)).elim
      · simp [hleft]
  rw [← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro gamma hgamma
  by_cases hproper : gamma.left ≠ 0
  · simp [hproper]
  · simp [split_left_eq_zero_of_not_ne gamma hproper]
end


section
variable {d M : ℕ} (q : HypoellipticAleksandrov.Parabolic.ScalarField d) {U : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (D : ParabolicWeakDerivativeFamily d (M + 1) U u) (beta : ParabolicDerivativeIndex d M)

private def properDiffusionGradientSum
     (j : Fin d) :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z ↦ ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity
            beta gamma hproper j) z
    else 0

variable (j i : Fin d)

private def properDiffusionDerivedCoefficientSum
      :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z ↦ ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (gamma.left + Pi.single (velocityCoord i) 1) q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity
            beta gamma hproper j) z
    else 0

/-- The proper-split diffusion Hessian contribution. -/
def properDiffusionHessianSum
      :
    HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z ↦ ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo
            beta gamma hproper j i) z
    else 0
end


private theorem continuousOn_bounded_mul_memLp
    {d : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (a f : HypoellipticAleksandrov.Parabolic.ScalarField d) (C : ℝ) (hC : 0 ≤ C)
    (ha : ContinuousOn a V) (haBound : ∀ z ∈ V, |a z| ≤ C)
    (hf : ParabolicMemLpOn V 2 f) :
    ParabolicMemLpOn V 2 (fun z ↦ a z * f z) := by



  apply MemLp.of_le_mul hf (show AEStronglyMeasurable (fun z ↦ a z * f z)
      (timeVelocityVolumeOn V) from (ha.aestronglyMeasurable hV.measurableSet).mul hf.aestronglyMeasurable)
  filter_upwards [(show ∀ᵐ z ∂timeVelocityVolumeOn V, |a z| ≤ C by
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      exact haBound z hz)] with z hz
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul hz le_rfl (abs_nonneg (f z)) hC

variable {d M : ℕ}

section
variable {V : HypoellipticAleksandrov.Parabolic.Region d}

section
variable (hV : IsOpen V) (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ContDiffOn ℝ (M + 1) q V) (B : ParabolicDerivativeIndex d (M + 1) → ℝ) (hB : ∀ alpha, 0 ≤ B alpha) (hqBound : ∀ alpha z, z ∈ V → |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha) {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (D : ParabolicWeakDerivativeFamily d (M + 1) V u) (beta : ParabolicDerivativeIndex d M) (j i : Fin d)

include hV hq hB hqBound in
private theorem properDiffusionSums_data
       :
    ParabolicMemLpOn V 2 (properDiffusionGradientSum q D beta j) ∧
    ParabolicMemLpOn V 2 (properDiffusionDerivedCoefficientSum q D beta j i) ∧
    ParabolicMemLpOn V 2 (properDiffusionHessianSum q D beta j i) ∧
    HasWeakVelocityPartialDerivOn V i
      (properDiffusionGradientSum q D beta j)
      (fun z ↦ properDiffusionDerivedCoefficientSum q D beta j i z +
        properDiffusionHessianSum q D beta j i z) := by
  classical
  let val := fun gamma  ↦ fun z ↦
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j) z
    else 0
  let der := fun gamma : TimeVelocityMultiIndex.Split beta.1 ↦ fun z ↦
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i) z +
         TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (gamma.left + Pi.single (velocityCoord i) 1) q z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j) z)
    else 0
  let dval := fun gamma : TimeVelocityMultiIndex.Split beta.1 ↦ fun z ↦
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (gamma.left + Pi.single (velocityCoord i) 1) q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity
            beta gamma hproper j) z
    else 0
  let hval := fun gamma  ↦ fun z ↦
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo
            beta gamma hproper j i) z
    else 0
  have hdata (gamma : TimeVelocityMultiIndex.Split beta.1) :
      ParabolicMemLpOn V 2 (val gamma) ∧
      ParabolicMemLpOn V 2 (dval gamma) ∧
      ParabolicMemLpOn V 2 (hval gamma) ∧
      ParabolicMemLpOn V 2 (der gamma) ∧
      HasWeakVelocityPartialDerivOn V i (val gamma) (der gamma) := by
    by_cases hproper : gamma.left ≠ 0
    · have hleft : gamma.left.order + 1 ≤ M + 1 := by
        have hlo := gamma.order_left_le
        have hob := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight beta.1
        omega
      have hC1 : ContDiffOn ℝ 1
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) V := by
        intro z hz
        unfold TimeVelocityMultiIndex.coordinateIteratedFDeriv
        have ht := (hq.contDiffAt (hV.mem_nhds hz)).iteratedFDeriv_right
          (m := 1) (i := gamma.left.coordinateList.length) (by
            simp only [TimeVelocityMultiIndex.length_coordinateList]
            exact_mod_cast (show 1 + gamma.left.order ≤ M + 1 by omega))
        exact ((contDiffAt_const (c := ContinuousMultilinearMap.apply ℝ _ _
          (fun k ↦ timeVelocityBasis (gamma.left.coordinateList.get k)))).clm_apply
            ht).contDiffWithinAt
      have hrightSucc :
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo
            beta gamma hproper j i) =
          ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j) i
            (by
              simp only [ParabolicDerivativeIndex.coe_properSplitRightVelocity,
                TimeVelocityMultiIndex.parabolicWeight_add,
                TimeVelocityMultiIndex.parabolicWeight_single_velocity]
              have hloss := gamma.parabolicWeight_right_add_one_le hproper
              omega) := by
        apply Subtype.ext
        rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
        rfl
      have hweak := D.hasWeakVelocitySucc
        (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j) i
        (by
          simp only [ParabolicDerivativeIndex.coe_properSplitRightVelocity,
            TimeVelocityMultiIndex.parabolicWeight_add,
            TimeVelocityMultiIndex.parabolicWeight_single_velocity]
          have hloss := gamma.parabolicWeight_right_add_one_le hproper
          omega)
      have hprod := velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
        hV i
        (B (ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1)
          (ParabolicDerivativeIndex.splitLeft beta gamma)))
        (B (addVelocityIndex (ParabolicDerivativeIndex.splitLeft beta gamma) i))
        (hB _) (hB _)
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) hC1
        (by
          intro z hz
          simpa only [ParabolicDerivativeIndex.coe_castLE,
            ParabolicDerivativeIndex.coe_splitLeft] using!
            hqBound (ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1)
              (ParabolicDerivativeIndex.splitLeft beta gamma)) z hz)
        (by
          intro z hz
          rw [show velocityGradient
              (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z i =
              TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (gamma.left + Pi.single (velocityCoord i) 1) q z by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
            · rfl
            · exact (hq.contDiffAt (hV.mem_nhds hz)).of_le (by
                exact_mod_cast hleft)]
          simpa only [coe_addVelocityIndex,
            ParabolicDerivativeIndex.coe_splitLeft] using!
            hqBound (addVelocityIndex
              (ParabolicDerivativeIndex.splitLeft beta gamma) i) z hz)
        (D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity beta gamma hproper j))
        (D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo beta gamma hproper j i))
        (D.memLp _) (D.memLp _) (by simpa only [hrightSucc] using hweak)
      have hs := hprod.2.2.2.1.smul (beta.1.choose gamma.left : ℝ)
      have hgradAE : (fun z ↦ velocityGradient
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q) z i) =ᵐ[
          timeVelocityVolumeOn V] fun z ↦
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (gamma.left + Pi.single (velocityCoord i) 1) q z := by
        filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
        rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
        · rfl
        · exact (hq.contDiffAt (hV.mem_nhds hz)).of_le (by
            exact_mod_cast hleft)
      have hhessian : ParabolicMemLpOn V 2 (fun z ↦
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z) := by
        let sharedTerm_3ae6a2abc0 := ((ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1) (ParabolicDerivativeIndex.splitLeft beta gamma)))
        have hm := continuousOn_bounded_mul_memLp hV
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q)
          (D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i))
          (B sharedTerm_3ae6a2abc0)
          (hB _) hC1.continuousOn
          ((hqBound sharedTerm_3ae6a2abc0))
          (D.memLp _)
        simpa only [mul_assoc] using
          hm.const_mul (beta.1.choose gamma.left : ℝ)
      have hcombined :=
        hprod.2.2.1.const_mul (beta.1.choose gamma.left : ℝ)
      have hderived : ParabolicMemLpOn V 2 (fun z ↦
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (gamma.left + Pi.single (velocityCoord i) 1) q z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z) := by
        apply (memLp_congr_ae ?_).mp (hcombined.sub hhessian)
        filter_upwards [hgradAE] with z hgrad
        simp only [Pi.sub_apply, hgrad]
        ring
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [val, dif_pos hproper, mul_assoc] using
          hprod.2.1.const_mul (beta.1.choose gamma.left : ℝ)
      · simpa only [dval, dif_pos hproper] using hderived
      · simpa only [hval, dif_pos hproper] using hhessian
      · apply (memLp_congr_ae ?_).mp
          (hprod.2.2.1.const_mul (beta.1.choose gamma.left : ℝ))
        filter_upwards [hgradAE] with z hz
        simp only [der, dif_pos hproper, hz]
      · apply hs.congr_ae
        · filter_upwards [] with z
          simp only [val, dif_pos hproper, Pi.smul_apply, smul_eq_mul]
          ring
        · filter_upwards [hgradAE] with z hgrad
          simp only [der, dif_pos hproper, Pi.smul_apply, smul_eq_mul, hgrad]
    · simp only [val, dval, hval, der, dif_neg hproper]
      exact ⟨MemLp.zero', MemLp.zero', MemLp.zero', MemLp.zero',
        HasWeakVelocityPartialDerivOn.zero   ⟩
  let e := Fintype.equivFin (TimeVelocityMultiIndex.Split beta.1)
  have hsum := HasWeakVelocityPartialDerivOn.fin_sum
    (u := fun k ↦ val (e.symm k)) (du := fun k ↦ der (e.symm k))
    (fun k ↦ (hdata (e.symm k)).2.2.2.2)
    (fun k ↦ (hdata (e.symm k)).1.locallyIntegrableOn (by norm_num))
    (fun k ↦ (hdata (e.symm k)).2.2.2.1.locallyIntegrableOn (by norm_num))
  have hvalEq : (fun z ↦ ∑ k, val (e.symm k) z) =
      properDiffusionGradientSum q D beta j := by
    funext z
    exact Equiv.sum_comp e.symm (fun gamma ↦ val gamma z)
  have hder : (fun z ↦ ∑ k, der (e.symm k) z) =
      fun z ↦ properDiffusionDerivedCoefficientSum q D beta j i z +
        properDiffusionHessianSum q D beta j i z := by
    funext z
    rw [Equiv.sum_comp e.symm (fun gamma ↦ der gamma z)]
    simp only [der, properDiffusionDerivedCoefficientSum,
      properDiffusionHessianSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    by_cases hproper : gamma.left ≠ 0
    · simp only [dif_pos hproper]
      ring
    · simp only [dif_neg hproper, add_zero]
  have hvalMem : ParabolicMemLpOn V 2 (fun z ↦ ∑ k, val (e.symm k) z) :=
    memLp_finset_sum Finset.univ (fun k _ ↦ (hdata (e.symm k)).1)



  refine ⟨(by
      simpa only [hvalEq] using hvalMem), (show _ by
      have hm := memLp_finset_sum Finset.univ
        (fun k _ ↦ (hdata (e.symm k)).2.1)
      have heq : (fun z ↦ ∑ k, dval (e.symm k) z) =
          properDiffusionDerivedCoefficientSum q D beta j i := by
        funext z
        exact Equiv.sum_comp e.symm (fun gamma ↦ dval gamma z)
      simpa only [heq] using hm), (show _ by
      have hm := memLp_finset_sum Finset.univ
        (fun k _ ↦ (hdata (e.symm k)).2.2.1)
      have heq : (fun z ↦ ∑ k, hval (e.symm k) z) =
          properDiffusionHessianSum q D beta j i := by
        funext z
        exact Equiv.sum_comp e.symm (fun gamma ↦ hval gamma z)
      simpa only [heq] using hm), ?_⟩
  simpa only [hvalEq, hder] using hsum

include hV hq hB hqBound in
private theorem properDiffusion_compactTest_identity

    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -( ∫ z in V, properDiffusionGradientSum q D beta j z *
        velocityGradient φ z i ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      ∫ z in V, properDiffusionDerivedCoefficientSum q D beta j i z * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) =
      ∫ z in V, properDiffusionHessianSum q D beta j i z * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  have hdata := properDiffusionSums_data hV q hq B hB hqBound D beta j i
  have hraw := hdata.2.2.2 φ hφ hφCompact hφV
  have hφLp : MemLp φ 2 (timeVelocityVolumeOn V) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hderivedInt : Integrable
      (fun z ↦ properDiffusionDerivedCoefficientSum q D beta j i z * φ z)
      (timeVelocityVolumeOn V) := hdata.2.1.integrable_mul hφLp
  have hhessianInt : Integrable
      (fun z ↦ properDiffusionHessianSum q D beta j i z * φ z)
      (timeVelocityVolumeOn V) := hdata.2.2.1.integrable_mul hφLp
  simp only [add_mul] at hraw
  rw [integral_add hderivedInt hhessianInt] at hraw
  linarith
end


/-- Pair the root time component with an iterated compactly supported test. -/
theorem timeComponent_pairing

    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (hM : 2 ≤ M + 1) (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V, D.representative
        (ParabolicDerivativeIndex.castLE hM
          (ParabolicDerivativeIndex.timeOne d)) z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        (-(∫ z in V, D.representative
            (ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1) beta) z *
            timeDerivative φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) := by
  let timeIndex := ParabolicDerivativeIndex.castLE hM
    (ParabolicDerivativeIndex.timeOne d)
  let betaIndex := ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1) beta
  let psi := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  let tau : TimeVelocityMultiIndex d := Pi.single (timeCoord d) 1
  let theta := TimeVelocityMultiIndex.coordinateIteratedFDeriv tau φ
  have hpsi := _root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty beta.1 φ hφ


  have htime := D.integral_representative_mul_test timeIndex psi
    hpsi (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport beta.1 φ hφCompact) ((_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset beta.1 φ).trans hφV)



  have hthetaEq : theta = timeDerivative φ := by
    funext z
    dsimp only [theta, tau]
    exact (timeDerivative_eq_coordinateIteratedFDeriv φ z
      (hφ.contDiffAt.of_le (by norm_num))).symm
  have hbeta := D.integral_representative_mul_test betaIndex theta
    (_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty tau φ hφ) (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport tau φ hφCompact) ((_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset tau φ).trans hφV)
  rw [hthetaEq] at hbeta
  rw [htime, hbeta]
  simp only [timeIndex, betaIndex, ParabolicDerivativeIndex.coe_castLE,
    ParabolicDerivativeIndex.coe_timeOne]
  have hinter :
      (∫ z in V, u z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (TimeVelocityMultiIndex.ofTimeVelocity 1 0) psi z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in V, u z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (timeDerivative φ) z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    congr 1
    rw [← hthetaEq]
    dsimp only [psi, theta, tau]
    have htau : TimeVelocityMultiIndex.ofTimeVelocity 1 0 =
        Pi.single (timeCoord d) 1 := by
      funext c
      rcases c with _ | i <;> rfl
    rw [htau]
    calc
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single (timeCoord d) 1)
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ) z =
          timeDerivative
            (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ) z :=
        (timeDerivative_eq_coordinateIteratedFDeriv _ z
          (hpsi.contDiffAt.of_le (by norm_num))).symm
      _ = TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (beta.1 + Pi.single (timeCoord d) 1) φ z := by
        rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
        · rfl
        · exact contDiff_infty.mp hφ _
      _ = TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (Pi.single (timeCoord d) 1) φ) z :=
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at
          beta.1 (timeCoord d) φ z
            ((contDiff_infty.mp hφ _).contDiffAt)).symm
  rw [hinter]
  have htimeOrder : (TimeVelocityMultiIndex.ofTimeVelocity 1
      (0 : Fin d → ℕ)).order = 1 := by
    simp [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
      TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
      TimeVelocityMultiIndex.ofTimeVelocity, timeCoord, velocityCoord]
  rw [htimeOrder, pow_one]
  have hsquare : ((-1 : ℝ) ^ beta.1.order) *
      ((-1 : ℝ) ^ beta.1.order) = 1 := by
    rw [← pow_two, ← pow_mul]
    simp
  rw [mul_neg, ← mul_assoc, hsquare, one_mul]
  ring

/-- Pair the differentiated source component with a compactly supported test. -/
theorem sourceComponent_pairing

    {F : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (E : ParabolicWeakDerivativeFamily d M V F)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) : type_of% (E.integral_representative_mul_test beta φ hφ hφCompact hφV) :=
  E.integral_representative_mul_test beta φ hφ hφCompact hφV

section
variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

section
variable (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u) (j : Fin d)

private def shiftedVelocityFamily

     :
    ParabolicWeakDerivativeFamily d M V
      (D.representative
        (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
          (ParabolicDerivativeIndex.velocityOne j))) :=
  D.shift
    (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
      (ParabolicDerivativeIndex.velocityOne j))
    (by
      rw [ParabolicDerivativeIndex.coe_castLE,
        ParabolicDerivativeIndex.coe_velocityOne,
        TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
        VelocityMultiIndex.parabolicWeight]
      simp [VelocityMultiIndex.order]
      omega)

private theorem shiftedVelocityFamily_representative

     (beta : ParabolicDerivativeIndex d M) :
    (shiftedVelocityFamily hM D j).representative beta =
      D.representative
        (ParabolicDerivativeIndex.velocitySucc
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
          (by
            change beta.1.parabolicWeight + 1 ≤ M + 1
            omega)) := by
  rw [shiftedVelocityFamily,
    ParabolicWeakDerivativeFamily.shift_representative]
  congr 1
  apply Subtype.ext
  rw [ParabolicDerivativeIndex.coe_addWithin,
    ParabolicDerivativeIndex.coe_castLE,
    ParabolicDerivativeIndex.coe_velocityOne,
    ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single,
    ParabolicDerivativeIndex.coe_castLE]
  ext c
  rcases c with _ | i
  · simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord]
  · by_cases hij : i = j
    · simp_all [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord] <;> ring
    · simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hij]
end


variable (D : ParabolicWeakDerivativeFamily d (M + 1) V u)

private def truncatedValueFamily

     :
    ParabolicWeakDerivativeFamily d M V u :=
  D.truncate (Nat.le_succ M)


end


variable (hV : IsOpen V)

section
variable (q : HypoellipticAleksandrov.Parabolic.ScalarField d)

include hV in
private theorem coefficientProductComponent_pairing

     (hq : ContDiffOn ℝ M q V)
    (Bq : ParabolicDerivativeIndex d M → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (Du : ParabolicWeakDerivativeFamily d M V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V,
        (q z * Du.representative beta z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if _hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
                Du.representative
                  (ParabolicDerivativeIndex.splitRight beta gamma) z
            else 0) * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V, (q z * u z) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let Dqu := ParabolicWeakDerivativeFamily.mulContDiffOn
    hV Bq hBq q hq hqBound u Du
  have hpair := Dqu.integral_representative_mul_test beta φ hφ hφCompact hφV
  rw [show Dqu.representative beta = parabolicWeakMulRepresentative q Du beta by rfl]
    at hpair
  simpa only [parabolicWeakMulRepresentative_eq_zero_left_add_proper] using hpair

include hV in
/-- Pair one differentiated principal component after one velocity integration by parts. -/
theorem principalComponent_pairing

     (hq : ContDiffOn ℝ (M + 1) q V)
    (Bq : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        q z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z *
          velocityGradient φ z i
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1) q z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z *
          φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V,
          (q z *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) -
      ∫ z in V, properDiffusionHessianSum q D beta j i z * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_7e7e79bf7f := ((ParabolicDerivativeIndex.velocitySucc (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
    (by
      change beta.1.parabolicWeight + 1 ≤ M + 1
      omega)))
  let sharedTerm_85b549110f := ((ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1) (ParabolicDerivativeIndex.velocityOne j)))
  let sharedTerm_d2fcffddb9 := ((by omega : 2 ≤ M + 1))
  let Dj := shiftedVelocityFamily hM D j
  let dq := TimeVelocityMultiIndex.coordinateIteratedFDeriv
    (Pi.single (velocityCoord i) 1) q
  let BqM := fun alpha  ↦
    Bq (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
  let Bdq := fun alpha  ↦
    Bq (addVelocityIndex alpha i)
  have hqM : ContDiffOn ℝ M q V := hq.of_le (by exact_mod_cast Nat.le_succ M)
  have hdq : ContDiffOn ℝ M dq V := coordinateDerivative_contDiffOn hV q hq i
  have hBqM : ∀ alpha, 0 ≤ BqM alpha := fun alpha ↦ hBq _
  have hBdq : ∀ alpha, 0 ≤ Bdq alpha := fun alpha ↦ hBq _

  have hdqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 dq z| ≤ Bdq alpha := by
    intro alpha z hz
    exact coordinateDerivative_majorant q Bq hqBound i alpha z hz
      ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by
        exact_mod_cast (show alpha.1.order + 1 ≤ M + 1 by
          have ho := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight alpha.1

          omega)))
  have hgradEq : (fun z ↦ velocityGradient φ z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) φ := by
    funext z
    have h := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) (velocityCoord i) φ z
        (hφ.contDiffAt.of_le (by
          norm_num))
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) φ = φ by
      funext x
      exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero φ x] at h
    simpa [velocityGradient, timeVelocityBasis_velocity, PDE.basisVec] using h.symm
  have hgradSmooth : ContDiff ℝ PDE.smoothOrder (fun z ↦ velocityGradient φ z i) := by
    rw [hgradEq]
    exact _root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty _ φ hφ
  have hgradCompact : HasCompactSupport (fun z ↦ velocityGradient φ z i) := by
    rw [hgradEq]
    exact _root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport _ φ hφCompact

  have hfirst := coefficientProductComponent_pairing hV q hqM BqM hBqM
    (show ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ BqM alpha by
        intro alpha z hz
        exact hqBound (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z hz) Dj beta _
    hgradSmooth hgradCompact (show tsupport (fun z ↦ velocityGradient φ z i) ⊆ V by
        rw [hgradEq]
        exact (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset _ φ).trans hφV)
  have hsecond := coefficientProductComponent_pairing hV dq hdq Bdq hBdq
    hdqBound Dj beta φ hφ hφCompact hφV
  simp only [Dj, shiftedVelocityFamily_representative] at hfirst hsecond
  have hgradSum (z : TimeVelocity d) :
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M)
                  (ParabolicDerivativeIndex.splitRight beta gamma)) j
                (by
                  change gamma.right.parabolicWeight + 1 ≤ M + 1
                  have hloss := gamma.parabolicWeight_right_add_one_le hproper
                  omega)) z
        else 0) = properDiffusionGradientSum q D beta j z := by
    apply Finset.sum_congr rfl
    intro gamma hgamma
    by_cases hproper : gamma.left ≠ 0
    · simp only [dif_pos hproper]
      congr 3
      apply Subtype.ext
      rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single,
        ParabolicDerivativeIndex.coe_castLE,
        ParabolicDerivativeIndex.coe_splitRight,
        ParabolicDerivativeIndex.coe_properSplitRightVelocity]
    · simp only [dif_neg hproper]
  have hderivedSum (z : TimeVelocity d) (hz : z ∈ V) :
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left dq z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M)
                  (ParabolicDerivativeIndex.splitRight beta gamma)) j
                (by
                  change gamma.right.parabolicWeight + 1 ≤ M + 1
                  have hloss := gamma.parabolicWeight_right_add_one_le hproper
                  omega)) z
        else 0) = properDiffusionDerivedCoefficientSum q D beta j i z := by
    apply Finset.sum_congr rfl
    intro gamma hgamma
    by_cases hproper : gamma.left ≠ 0
    · simp only [dif_pos hproper, dq]
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at]
      · congr 3
        apply Subtype.ext
        rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single,
          ParabolicDerivativeIndex.coe_castLE,
          ParabolicDerivativeIndex.coe_splitRight,
          ParabolicDerivativeIndex.coe_properSplitRightVelocity]
      · exact (hq.contDiffAt (hV.mem_nhds hz)).of_le (by
          exact_mod_cast (show gamma.left.order + 1 ≤ M + 1 by
            have hlo := gamma.order_left_le
            have hob := _root_.HypoellipticAleksandrov.Parabolic.order_le_parabolicWeight beta.1
            omega))
    · simp only [dif_neg hproper]
  simp_rw [hgradSum] at hfirst
  have hsecondLhs :
      (∫ z in V,
        (dq z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z +
          properDiffusionDerivedCoefficientSum q D beta j i z) * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (∫ z in V,
        (dq z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left dq z *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M)
                      (ParabolicDerivativeIndex.splitRight beta gamma)) j
                    (by
                      change gamma.right.parabolicWeight + 1 ≤ M + 1
                      have hloss := gamma.parabolicWeight_right_add_one_le hproper
                      omega)) z
            else 0) * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    rw [hderivedSum z hz]
  rw [← hsecondLhs] at hsecond
  have hproper := properDiffusion_compactTest_identity hV q hq Bq hBq hqBound
    D beta j i φ hφ hφCompact hφV
  let rj := ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
    (ParabolicDerivativeIndex.velocityOne j)
  let rji := ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
    (ParabolicDerivativeIndex.velocityTwo j i)
  let zeroM : ParabolicDerivativeIndex d M := ⟨0, by
    simp [TimeVelocityMultiIndex.parabolicWeight,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order]⟩
  have hrji : ParabolicDerivativeIndex.velocitySucc rj i (by
      simp only [rj, ParabolicDerivativeIndex.coe_castLE,
        ParabolicDerivativeIndex.coe_velocityOne,
        TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
        VelocityMultiIndex.parabolicWeight]
      simp [VelocityMultiIndex.order]
      omega) = rji := by
    apply Subtype.ext
    rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
    ext c
    rcases c with _ | k
    · rfl
    · by_cases hki : k = i
      · subst k
        by_cases hij : i = j
        · subst i
          simp [rj, rji, TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord]
        · simp [rj, rji, TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hij]
      · by_cases hkj : k = j
        · subst k
          simp [rj, rji, TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hki]
        · simp [rj, rji, TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord,
            hki, hkj]
  have hqC1 : ContDiffOn ℝ 1 q V := hq.of_le (by
    exact_mod_cast (show 1 ≤ M + 1 by omega))
  have hqZero : ∀ z ∈ V, |q z| ≤ Bq
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM) := by
    intro z hz
    simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
      hqBound (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM) z hz

  have hrootWeak := D.hasWeakVelocitySucc rj i (by
    simp only [rj, ParabolicDerivativeIndex.coe_castLE,
      ParabolicDerivativeIndex.coe_velocityOne,
      TimeVelocityMultiIndex.parabolicWeight_ofTimeVelocity,
      VelocityMultiIndex.parabolicWeight]
    simp [VelocityMultiIndex.order]
    omega)
  rw [hrji] at hrootWeak
  have hrootProduct :=
    (velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le hV i
      (Bq (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM))
      (Bq (addVelocityIndex zeroM i)) (hBq _) (hBq _) q hqC1 hqZero (show ∀ z ∈ V, |velocityGradient q z i| ≤ Bq (addVelocityIndex zeroM i) by
          intro z hz
          have heq := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
            (0 : TimeVelocityMultiIndex d) (velocityCoord i) q z
              ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by
                simp [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
                  TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]))
          rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (0 : TimeVelocityMultiIndex d) q = q by
            funext x
            exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero q x] at heq
          rw [show velocityGradient q z i =
              TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (Pi.single (velocityCoord i) 1) q z by
            simpa [velocityGradient, timeVelocityBasis_velocity, PDE.basisVec] using heq.symm]
          simpa only [coe_addVelocityIndex, zeroM, zero_add] using
            hqBound (addVelocityIndex zeroM i) z hz)
      (D.representative rj) (D.representative rji) (D.memLp _) (D.memLp _)
      hrootWeak).2.2.2.1
  let psi := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  have hpsi := _root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty beta.1 φ hφ
  have hpsiCompact := _root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_hasCompactSupport beta.1 φ hφCompact
  have hpsiV := (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset beta.1 φ).trans hφV
  have hroot := hrootProduct psi hpsi hpsiCompact hpsiV

  simp_rw [congrFun (show (fun z ↦ velocityGradient psi z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
        (fun z ↦ velocityGradient φ z i) by
      funext z
      dsimp only [psi]
      rw [hgradEq]
      calc
        velocityGradient
            (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ) z i =
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (beta.1 + Pi.single (velocityCoord i) 1) φ z := by
          rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
          · rfl
          · exact (contDiff_infty.mp hφ _).contDiffAt
        _ = TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
            (TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1) φ) z :=
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at
            beta.1 (velocityCoord i) φ z
              ((contDiff_infty.mp hφ _).contDiffAt)).symm)] at hroot
  simp only [rj, rji] at hroot
  have hφLp : MemLp φ 2 (timeVelocityVolumeOn V) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hgradLp : MemLp (fun z ↦ velocityGradient φ z i) 2
      (timeVelocityVolumeOn V) :=
    (hgradSmooth.continuous.memLp_of_hasCompactSupport hgradCompact).restrict V
  have hpsiLp : MemLp psi 2 (timeVelocityVolumeOn V) :=
    (hpsi.continuous.memLp_of_hasCompactSupport hpsiCompact).restrict V
  have hqBetaMem : ParabolicMemLpOn V 2 (fun z ↦ q z *
      D.representative
        sharedTerm_7e7e79bf7f z) :=
    continuousOn_bounded_mul_memLp hV q _
      _ (hBq _)
      hqM.continuousOn hqZero (D.memLp _)
  have hdqBetaMem : ParabolicMemLpOn V 2 (fun z ↦ dq z *
      D.representative
        sharedTerm_7e7e79bf7f z) :=
    continuousOn_bounded_mul_memLp hV dq _ (Bq (addVelocityIndex zeroM i))
      (hBq _) hdq.continuousOn (by
        intro z hz
        simpa [zeroM, Bdq,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
          hdqBound zeroM z hz) (D.memLp _)
  have hqHessMem : ParabolicMemLpOn V 2 (fun z ↦ q z *
      D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_d2fcffddb9
          (ParabolicDerivativeIndex.velocityTwo j i)) z) :=
    continuousOn_bounded_mul_memLp hV q _
      _ (hBq _)
      hqM.continuousOn hqZero (D.memLp _)
  have hdqRootMem : ParabolicMemLpOn V 2 (fun z ↦ dq z *
      D.representative
        sharedTerm_85b549110f z) :=
    continuousOn_bounded_mul_memLp hV dq _ (Bq (addVelocityIndex zeroM i))
      (hBq _) hdq.continuousOn (by
        intro z hz
        simpa [zeroM, Bdq,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
          hdqBound zeroM z hz) (D.memLp _)
  have hproperData := properDiffusionSums_data hV q hq Bq hBq hqBound
    D beta j i
  simp only [add_mul] at hfirst hsecond hroot
  have hfirstSplit :
      (∫ z in V,
        q z * D.representative
          sharedTerm_7e7e79bf7f z * velocityGradient φ z i +
        properDiffusionGradientSum q D beta j z * velocityGradient φ z i
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (∫ z in V, q z * D.representative
          sharedTerm_7e7e79bf7f z * velocityGradient φ z i ∂(volume : Measure _)) +
      ∫ z in V, properDiffusionGradientSum q D beta j z *
        velocityGradient φ z i ∂(volume : Measure _) := by
    exact integral_add (hqBetaMem.integrable_mul hgradLp)
      (hproperData.1.integrable_mul hgradLp)
  have hsecondSplit :
      (∫ z in V, dq z * D.representative
          sharedTerm_7e7e79bf7f z * φ z +
        properDiffusionDerivedCoefficientSum q D beta j i z * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (∫ z in V, dq z * D.representative
          sharedTerm_7e7e79bf7f z * φ z ∂(volume : Measure _)) +
      ∫ z in V, properDiffusionDerivedCoefficientSum q D beta j i z * φ z
        ∂(volume : Measure _) := by
    exact integral_add (hdqBetaMem.integrable_mul hφLp)
      (hproperData.2.1.integrable_mul hφLp)
  have hrootSplit :
      (∫ z in V, q z * D.representative
          (ParabolicDerivativeIndex.castLE sharedTerm_d2fcffddb9
            (ParabolicDerivativeIndex.velocityTwo j i)) z * psi z +
        velocityGradient q z i * D.representative
          sharedTerm_85b549110f z * psi z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      (∫ z in V, q z * D.representative
          (ParabolicDerivativeIndex.castLE sharedTerm_d2fcffddb9
            (ParabolicDerivativeIndex.velocityTwo j i)) z * psi z
        ∂(volume : Measure _)) +
      ∫ z in V, velocityGradient q z i * D.representative
          sharedTerm_85b549110f z * psi z
        ∂(volume : Measure _) := by
    exact integral_add (hqHessMem.integrable_mul hpsiLp)
      (by
        apply Integrable.congr (hdqRootMem.integrable_mul hpsiLp)
        filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
        have heq := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
          (0 : TimeVelocityMultiIndex d) (velocityCoord i) q z
            ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by
              simp [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
                TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]))
        rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (0 : TimeVelocityMultiIndex d) q = q by
          funext x
          exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero q x] at heq
        simpa [dq, velocityGradient, timeVelocityBasis_velocity, PDE.basisVec]
          using congrArg (fun x ↦ x * D.representative
            sharedTerm_85b549110f z * psi z) heq)
  rw [hfirstSplit] at hfirst
  rw [hsecondSplit] at hsecond
  rw [hrootSplit] at hroot
  have hrootGradientIntegral :
      (∫ z in V, velocityGradient q z i * D.representative
          sharedTerm_85b549110f z * psi z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in V, dq z * D.representative
          sharedTerm_85b549110f z * psi z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    have heq := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) (velocityCoord i) q z
        ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by
          simp [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
            TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]))
    rw [show TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (0 : TimeVelocityMultiIndex d) q = q by
      funext x
      exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero q x] at heq
    simpa [dq, velocityGradient, timeVelocityBasis_velocity, PDE.basisVec] using
      congrArg (fun x ↦ x * D.representative
        sharedTerm_85b549110f z * psi z) heq.symm
  rw [hrootGradientIntegral] at hroot
  dsimp only [psi] at hroot
  dsimp only [dq] at hsecond ⊢
  linear_combination -hfirst - hsecond - hproper -
    ((-1 : ℝ) ^ beta.1.order) * hroot
end


include hV in
/-- Pair one differentiated drift component with a compactly supported test. -/
theorem driftComponent_pairing

    (b : PDE.TimeVectorField d)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j : Fin d)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V,
        (b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V,
          (b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_938bc418bd := ((fun x : TimeVelocity d ↦ b x.1 x.2 j))
  have hpair := coefficientProductComponent_pairing hV
    sharedTerm_938bc418bd (hb j) (Bb j) (hBb j)
    (hbBound j) (shiftedVelocityFamily hM D j) beta φ hφ hφCompact hφV
  simp only [shiftedVelocityFamily_representative] at hpair
  have hsum (z : TimeVelocity d) :
      (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              sharedTerm_938bc418bd z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M)
                  (ParabolicDerivativeIndex.splitRight beta gamma)) j
                (by
                  change gamma.right.parabolicWeight + 1 ≤ M + 1
                  have hloss := gamma.parabolicWeight_right_add_one_le hproper
                  omega)) z
        else 0) =
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              sharedTerm_938bc418bd z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0 := by
    apply Finset.sum_congr rfl
    intro gamma hgamma
    by_cases hproper : gamma.left ≠ 0
    · simp only [dif_pos hproper]
      congr 3
      apply Subtype.ext
      rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single,
        ParabolicDerivativeIndex.coe_castLE,
        ParabolicDerivativeIndex.coe_splitRight,
        ParabolicDerivativeIndex.coe_properSplitRightVelocity]
    · simp only [dif_neg hproper]
  simp_rw [hsum] at hpair
  exact hpair

include hV in
/-- Pair the differentiated zeroth-order component with a compactly supported test. -/
theorem zerothOrderComponent_pairing

    (c : PDE.TimeScalarField d)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V,
        (c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ c x.1 x.2) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightValue
                    beta gamma hproper) z
            else 0) * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V, (c z.1 z.2 * u z) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := (coefficientProductComponent_pairing hV (fun z => c z.1 z.2) hc Bc hBc hcBound (truncatedValueFamily D) beta φ hφ
  hφCompact hφV)
end


/-- Select one precompact test neighborhood with majorants for all coefficients. -/
theorem exists_precompactOpen_coefficient_majorants
     {U K : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ c z.1 z.2) U) :
    ∃ (V : HypoellipticAleksandrov.Parabolic.Region d)
      (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
      (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
      (Bc : ParabolicDerivativeIndex d M → ℝ),
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) ∧
      (∀ i j alpha, 0 ≤ Ba i j alpha) ∧
      (∀ j alpha, 0 ≤ Bb j alpha) ∧
      (∀ alpha, 0 ≤ Bc alpha) ∧
      (∀ i j alpha z, z ∈ closure V →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha) ∧
      (∀ j alpha z, z ∈ closure V →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha) ∧
      ∀ alpha z, z ∈ closure V →
        |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
          (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha := by
  let qa : Fin d × Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
    fun ij z ↦ a z.1 z.2 ij.1 ij.2
  obtain ⟨W, BA, hW, hKW, hWU, hWc, hBA0, hBA⟩ :=
    exists_precompactOpen_coordinateIteratedFDeriv_majorants
      hU hK hKU qa (fun ij ↦ ha ij.1 ij.2)
  let qbc : Option (Fin d) → HypoellipticAleksandrov.Parabolic.ScalarField d
    | none => fun z ↦ c z.1 z.2
    | some j => fun z ↦ b z.1 z.2 j

  obtain ⟨V, BBC, hV, hKV, hVW, hVc, hBBC0, hBBC⟩ :=
    exists_precompactOpen_coordinateIteratedFDeriv_majorants
      hW hK hKW qbc (show _ by
          intro k
          cases k with
          | none => exact hc.mono (subset_closure.trans hWU)
          | some j => exact (hb j).mono (subset_closure.trans hWU))
  refine ⟨V, fun i j ↦ BA (i, j), fun j ↦ BBC (some j), BBC none,
    hV, hKV, hVW.trans (subset_closure.trans hWU), hVc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j alpha ↦ hBA0 (i, j) alpha
  · exact fun j alpha ↦ hBBC0 (some j) alpha
  · exact (hBBC0 none)
  · intro i j alpha z hz
    exact hBA (i, j) alpha z (subset_closure (hVW hz))
  · intro j alpha z hz
    exact hBBC (some j) alpha z hz
  · intro alpha z hz
    exact hBBC none alpha z hz

end GenericPreLiftDifferentiatedWeakEquationSupport

end HypoellipticAleksandrov.Parabolic
