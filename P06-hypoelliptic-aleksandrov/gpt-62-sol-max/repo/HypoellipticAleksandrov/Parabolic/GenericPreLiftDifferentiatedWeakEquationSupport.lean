module

import HypoellipticAleksandrov.Analysis.L2Pairing

public import HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLocality
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
public import HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyShift

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

open MeasureTheory ParabolicDerivativeIndex HypoellipticAleksandrov.Analysis
open TimeVelocityMultiIndex (coordinateIteratedFDeriv)
open scoped BigOperators ENNReal Topology
private theorem timeDerivative_eq_coordinateIteratedFDeriv
    {d : ℕ} (f : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hf : ContDiffAt ℝ 1 f z) :
    timeDerivative f z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (timeCoord d) 1) f z := (TimeVelocityMultiIndex.coordinateIteratedFDeriv_single_at (timeCoord d) hf).symm

section
variable {d M : ℕ} (alpha : ParabolicDerivativeIndex d M) (i : Fin d)
include alpha i

private def addVelocityIndex :
    ParabolicDerivativeIndex d (M + 1) :=
  ⟨alpha.1 + Pi.single (velocityCoord i) 1, by
    rw [TimeVelocityMultiIndex.parabolicWeight_add,
      TimeVelocityMultiIndex.parabolicWeight_single_velocity]
    omega⟩

@[simp] private theorem coe_addVelocityIndex :
    (addVelocityIndex alpha i).1 =
      alpha.1 + Pi.single (velocityCoord i) 1 := rfl

end

section
variable {d M : ℕ} {U : Set (TimeVelocity d)}

private theorem coordinateDerivative_contDiffOn (hU : IsOpen U)
    (f : TimeVelocity d → ℝ) (hf : ContDiffOn ℝ (M + 1) f U)
    (i : Fin d) :
    ContDiffOn ℝ M
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) f) U := TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiffOn (Pi.single (velocityCoord i) 1)
    hU hf (by simp)

private theorem coordinateDerivative_majorant
    (f : TimeVelocity d → ℝ)
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

private theorem splitRight_default
    {d L : ℕ} (beta : ParabolicDerivativeIndex d L) :
    ParabolicDerivativeIndex.splitRight beta default = beta := rfl

private theorem parabolicWeakMulRepresentative_eq_zero_left_add_proper
    {d L : ℕ} (q : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
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
      · exact (hne (gamma.eq_default_of_left_eq_zero hleft)).elim
      · simp [hleft]
  rw [← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro gamma hgamma
  by_cases hproper : gamma.left ≠ 0
  · simp [hproper]
  · simp [not_ne_iff.mp hproper]

section
variable {d M : ℕ} (q : TimeVelocity d → ℝ) {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
  (D : ParabolicWeakDerivativeFamily d (M + 1) U u) (beta : ParabolicDerivativeIndex d M)
include M q U u D beta

private def properDiffusionGradientSum (j : Fin d) :
    TimeVelocity d → ℝ :=
  fun z ↦ ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocity
            beta gamma hproper j) z
    else 0

private def properDiffusionDerivedCoefficientSum (j i : Fin d) :
    TimeVelocity d → ℝ :=
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
def properDiffusionHessianSum (j i : Fin d) :
    TimeVelocity d → ℝ :=
  fun z ↦ ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
    if hproper : gamma.left ≠ 0 then
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        D.representative
          (ParabolicDerivativeIndex.properSplitRightVelocityTwo
            beta gamma hproper j i) z
    else 0

end

private theorem properDiffusionSums_data
    {d M : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q V)
    (B : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d) :
    ParabolicMemLpOn V 2 (properDiffusionGradientSum q D beta j) ∧
    ParabolicMemLpOn V 2 (properDiffusionDerivedCoefficientSum q D beta j i) ∧
    ParabolicMemLpOn V 2 (properDiffusionHessianSum q D beta j i) ∧
    HasWeakVelocityPartialDerivOn V i
      (properDiffusionGradientSum q D beta j)
      (fun z ↦ properDiffusionDerivedCoefficientSum q D beta j i z +
        properDiffusionHessianSum q D beta j i z) := by
  classical
  let I := TimeVelocityMultiIndex.Split beta.1
  let val (γ : I) (z) := if h : γ.left ≠ 0 then
    (beta.1.choose γ.left : ℝ) * coordinateIteratedFDeriv γ.left q z *
      D.representative (properSplitRightVelocity beta γ h j) z else 0
  let dval (γ : I) (z) := if h : γ.left ≠ 0 then
    (beta.1.choose γ.left : ℝ) * coordinateIteratedFDeriv (γ.left + Pi.single (velocityCoord i) 1) q z *
      D.representative (properSplitRightVelocity beta γ h j) z else 0
  let hval (γ : I) (z) := if h : γ.left ≠ 0 then
    (beta.1.choose γ.left : ℝ) * coordinateIteratedFDeriv γ.left q z *
      D.representative (properSplitRightVelocityTwo beta γ h j i) z else 0
  have hdata (γ : I) : ParabolicMemLpOn V 2 (val γ) ∧ ParabolicMemLpOn V 2 (dval γ) ∧
      ParabolicMemLpOn V 2 (hval γ) ∧
      HasWeakVelocityPartialDerivOn V i (val γ) (dval γ + hval γ) := by
    by_cases h : γ.left ≠ 0
    · let α := splitLeft beta γ
      let α₀ := castLE (Nat.le_succ M) α
      let α₁ := addVelocityIndex α i
      let r := properSplitRightVelocity beta γ h j
      let r' := properSplitRightVelocityTwo beta γ h j i
      let a := coordinateIteratedFDeriv γ.left q
      let a' := α₁.1.coordinateIteratedFDeriv q
      let K : ℝ := beta.1.choose γ.left
      have horder : γ.left.order + 1 ≤ M + 1 :=
        Nat.succ_le_succ (γ.order_left_le.trans (beta.1.order_le_parabolicWeight.trans beta.2))
      have ha := γ.left.coordinateIteratedFDeriv_contDiffOn (m := 1) hV hq
        (by exact_mod_cast (show 1 + γ.left.order ≤ M + 1 by omega))
      have ha' z (hz : z ∈ V) : velocityGradient a z i = a' z :=
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at γ.left (velocityCoord i) q z
          ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast horder))).symm
      have hweight : (r.1 + Pi.single (velocityCoord i) 1).parabolicWeight ≤ M + 1 := r'.2
      have hw : HasWeakVelocityPartialDerivOn V i (D.representative r) (D.representative r') :=
        D.hasWeak_add_single r (velocityCoord i) hweight
      have hp := velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
        hV i (B α₀) (B α₁) (hB _) (hB _) a ha (hqBound α₀)
        (fun z hz => ha' z hz ▸ hqBound α₁ z hz) _ _ (D.memLp _) (D.memLp _) hw
      have hmem (A R : ParabolicDerivativeIndex d (M + 1)) :=
        (coordinateDerivative_mul_memLp hV hq B hB hqBound A (D.memLp R)).const_mul K
      refine ⟨?_, ?_, ?_, (hp.2.2.2.1.smul K).congr_ae ?_ ?_⟩
      · simpa only [val, dif_pos h, α₀, α, K, coe_castLE, coe_splitLeft, mul_assoc] using hmem α₀ r
      · simpa only [dval, dif_pos h, α₁, α, K, coe_addVelocityIndex, coe_splitLeft, mul_assoc] using hmem α₁ r
      · simpa only [hval, dif_pos h, α₀, α, K, coe_castLE, coe_splitLeft, mul_assoc] using hmem α₀ r'
      · exact .of_forall fun z => by simp only [val, dif_pos h, Pi.smul_apply, smul_eq_mul, a, K, r, mul_assoc]
      · filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
        simp only [dval, hval, dif_pos h, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha' z hz,
          a, a', α₁, α, K, r, r', coe_addVelocityIndex, coe_splitLeft, mul_add, mul_assoc]
        rw [add_comm]
    · have hv : val γ = 0 := funext fun z => by simp only [val, dif_neg h, Pi.zero_apply]
      have hd : dval γ = 0 := funext fun z => by simp only [dval, dif_neg h, Pi.zero_apply]
      have hh : hval γ = 0 := funext fun z => by simp only [hval, dif_neg h, Pi.zero_apply]
      rw [hv, hd, hh, add_zero]
      exact ⟨MemLp.zero, MemLp.zero, MemLp.zero, HasWeakVelocityPartialDerivOn.zero⟩
  have hv := memLp_finsetSum Finset.univ fun γ _ => (hdata γ).1
  have hd := memLp_finsetSum Finset.univ fun γ _ => (hdata γ).2.1
  have hh := memLp_finsetSum Finset.univ fun γ _ => (hdata γ).2.2.1
  refine ⟨hv, hd, hh, ?_⟩
  exact (show HasWeakVelocityPartialDerivOn V i (fun z => ∑ γ, val γ z)
      (fun z => ∑ γ, (dval γ + hval γ) z) from
    HasWeakFDerivApplyOn.fintype_sum (e := (0, Pi.single i 1)) (u := val) (du := dval + hval)
      (fun γ => (hdata γ).2.2.2) (fun γ => (hdata γ).1.locallyIntegrableOn (by norm_num))
      (fun γ => ParabolicMemLpOn.locallyIntegrableOn ((hdata γ).2.1.add (hdata γ).2.2.1) (by norm_num))).congr_ae
    .rfl (.of_forall fun z => by simp only [Pi.add_apply, Finset.sum_add_distrib]; rfl)

section
variable {d M : ℕ} {V : Set (TimeVelocity d)}

private theorem properDiffusion_compactTest_identity (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q V)
    (B : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -( ∫ z in V, properDiffusionGradientSum q D beta j z *
        velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) -
      ∫ z in V, properDiffusionDerivedCoefficientSum q D beta j i z * φ z
        ∂(volume : Measure (TimeVelocity d)) =
      ∫ z in V, properDiffusionHessianSum q D beta j i z * φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  have hdata := properDiffusionSums_data hV q hq B hB hqBound D beta j i
  have hφLp : MemLp φ 2 (timeVelocityVolumeOn V) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hraw := hdata.2.2.2 φ hφ hφCompact hφV
  rw [integral_add_mul_L2 hdata.2.1 hdata.2.2.1 hφLp] at hraw
  linarith

/-- Pair the root time component with an iterated compactly supported test. -/
theorem timeComponent_pairing
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (hM : 2 ≤ M + 1) (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V, D.representative
        (ParabolicDerivativeIndex.castLE hM
          (ParabolicDerivativeIndex.timeOne d)) z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
      ∂(volume : Measure (TimeVelocity d))) =
      ((-1 : ℝ) ^ beta.1.order) *
        (-(∫ z in V, D.representative
            (ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1) beta) z *
            timeDerivative φ z ∂(volume : Measure (TimeVelocity d)))) := by
  let timeIndex := ParabolicDerivativeIndex.castLE hM
    (ParabolicDerivativeIndex.timeOne d)
  let betaIndex := ParabolicDerivativeIndex.castLE (by omega : M ≤ M + 1) beta
  let psi := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  let tau : TimeVelocityMultiIndex d := Pi.single (timeCoord d) 1
  let theta := TimeVelocityMultiIndex.coordinateIteratedFDeriv tau φ
  have hpsi := TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiff beta.1 φ hφ
  have hpsiCompact := TimeVelocityMultiIndex.coordinateIteratedFDeriv_hasCompactSupport beta.1 φ hφCompact
  have hpsiV := (TimeVelocityMultiIndex.coordinateIteratedFDeriv_tsupport_subset beta.1 φ).trans hφV
  have htime := D.integral_representative_mul_test timeIndex psi
    hpsi hpsiCompact hpsiV
  have htheta := TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiff tau φ hφ
  have hthetaCompact := TimeVelocityMultiIndex.coordinateIteratedFDeriv_hasCompactSupport tau φ hφCompact
  have hthetaV := (TimeVelocityMultiIndex.coordinateIteratedFDeriv_tsupport_subset tau φ).trans hφV
  have hthetaEq : theta = timeDerivative φ := by
    funext z
    dsimp only [theta, tau]
    exact (timeDerivative_eq_coordinateIteratedFDeriv φ z
      (hφ.contDiffAt.of_le (by norm_num))).symm
  have hbeta := D.integral_representative_mul_test betaIndex theta
    htheta hthetaCompact hthetaV
  rw [hthetaEq] at hbeta
  rw [htime, hbeta]
  simp only [timeIndex, betaIndex, ParabolicDerivativeIndex.coe_castLE,
    ParabolicDerivativeIndex.coe_timeOne]
  have hinter :
      (∫ z in V, u z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (TimeVelocityMultiIndex.ofTimeVelocity 1 0) psi z
        ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V, u z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (timeDerivative φ) z ∂(volume : Measure (TimeVelocity d)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    congr 1
    rw [← hthetaEq]
    dsimp only [psi, theta, tau]
    have htau : TimeVelocityMultiIndex.ofTimeVelocity 1 0 =
        Pi.single (timeCoord d) 1 := by
      funext c
      rcases c with _ | i <;> simp [TimeVelocityMultiIndex.ofTimeVelocity,
        timeCoord]
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
        · simp [timeDerivative, timeVelocityBasis_time]
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

private def shiftedVelocityFamily {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (j : Fin d) :
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

end

section
variable {d M : ℕ} {V : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}

/-- Lift a bounded index by one velocity derivative. -/
abbrev liftVelocity (beta : ParabolicDerivativeIndex d M) (j : Fin d) :=
  velocitySucc (castLE (Nat.le_succ M) beta) j
    (by change beta.1.parabolicWeight + 1 ≤ M + 1; omega)

@[simp] private theorem coe_liftVelocity (beta : ParabolicDerivativeIndex d M) (j : Fin d) :
    (liftVelocity beta j).1 = beta.1 + Pi.single (velocityCoord j) 1 := by
  rw [coe_velocitySucc_eq_add_single, coe_castLE]

private theorem shiftedVelocityFamily_representative
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (j : Fin d) (beta : ParabolicDerivativeIndex d M) :
    (shiftedVelocityFamily hM D j).representative beta =
      D.representative (liftVelocity beta j) := by
  rw [shiftedVelocityFamily, ParabolicWeakDerivativeFamily.shift_representative]
  congr 1
  apply Subtype.ext
  rw [coe_addWithin, coe_castLE, coe_velocityOne, coe_liftVelocity]
  ext c
  rcases c with _ | i
  · simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord]
  · by_cases hij : i = j
    · subst i
      simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord]
      omega
    · simp [TimeVelocityMultiIndex.ofTimeVelocity, velocityCoord, hij]

private theorem properSplitRightVelocity_eq_liftVelocity (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1) (h : gamma.left ≠ 0) (j : Fin d) :
    properSplitRightVelocity beta gamma h j = liftVelocity (splitRight beta gamma) j :=
  Subtype.ext (by rw [coe_properSplitRightVelocity, coe_liftVelocity, coe_splitRight])

private theorem shiftedVelocityProduct_sum
    (q : TimeVelocity d → ℝ) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j : Fin d) (z : TimeVelocity d) :
    (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) * coordinateIteratedFDeriv gamma.left q z *
          D.representative (liftVelocity (splitRight beta gamma) j) z
      else 0) = properDiffusionGradientSum q D beta j z := by
  simp only [properDiffusionGradientSum, properSplitRightVelocity_eq_liftVelocity, dite_eq_ite]

private def truncatedValueFamily
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u) :
    ParabolicWeakDerivativeFamily d M V u :=
  D.truncate (Nat.le_succ M)

end

section
variable {d M : ℕ} {V : Set (TimeVelocity d)}

private theorem truncatedValueFamily_representative {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) :
    (truncatedValueFamily D).representative beta =
      D.representative
        (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) := rfl

private theorem coefficientProductComponent_pairing (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ M q V)
    (Bq : ParabolicDerivativeIndex d M → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
    {u : TimeVelocity d → ℝ}
    (Du : ParabolicWeakDerivativeFamily d M V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
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
      ∂(volume : Measure (TimeVelocity d))) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V, (q z * u z) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d)) := by
  let Dqu := ParabolicWeakDerivativeFamily.mulContDiffOn
    hV Bq hBq q hq hqBound u Du
  have hpair := Dqu.integral_representative_mul_test beta φ hφ hφCompact hφV
  rw [show Dqu.representative beta = parabolicWeakMulRepresentative q Du beta by rfl]
    at hpair
  simpa only [parabolicWeakMulRepresentative_eq_zero_left_add_proper] using hpair

end

section
variable {d M : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
include hV

/-- Pair one differentiated principal component after one velocity integration by parts. -/
theorem principalComponent_pairing
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ (M + 1) q V)
    (Bq : ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBq : ∀ alpha, 0 ≤ Bq alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
    {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j i : Fin d)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        q z *
            D.representative
              (liftVelocity beta j) z *
          velocityGradient φ z i
        ∂(volume : Measure (TimeVelocity d))) -
      ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1) q z *
            D.representative
              (liftVelocity beta j) z *
          φ z
        ∂(volume : Measure (TimeVelocity d)) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V,
          (q z *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d)) -
      ∫ z in V, properDiffusionHessianSum q D beta j i z * φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  let Dj := shiftedVelocityFamily hM D j
  let dq := TimeVelocityMultiIndex.coordinateIteratedFDeriv
    (Pi.single (velocityCoord i) 1) q
  let BqM := fun alpha : ParabolicDerivativeIndex d M ↦
    Bq (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha)
  let Bdq := fun alpha : ParabolicDerivativeIndex d M ↦
    Bq (addVelocityIndex alpha i)
  have hqM : ContDiffOn ℝ M q V := hq.of_le (by exact_mod_cast Nat.le_succ M)
  have hdq : ContDiffOn ℝ M dq V := coordinateDerivative_contDiffOn hV q hq i
  have hBqM : ∀ alpha, 0 ≤ BqM alpha := fun alpha ↦ hBq _
  have hBdq : ∀ alpha, 0 ≤ Bdq alpha := fun alpha ↦ hBq _
  have hqBoundM : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ BqM alpha := by
    intro alpha z hz
    simpa only [BqM, ParabolicDerivativeIndex.coe_castLE] using
      hqBound (ParabolicDerivativeIndex.castLE (Nat.le_succ M) alpha) z hz
  have hdqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 dq z| ≤ Bdq alpha := by
    intro alpha z hz
    exact coordinateDerivative_majorant q Bq hqBound i alpha z hz
      ((hq.contDiffAt (hV.mem_nhds hz)).of_le (by
        exact_mod_cast (show alpha.1.order + 1 ≤ M + 1 by
          have ho := TimeVelocityMultiIndex.order_le_parabolicWeight alpha.1
          have hw := alpha.2
          omega)))
  have hgradEq : (fun z ↦ velocityGradient φ z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord i) 1) φ := by
    exact funext fun z => TimeVelocityMultiIndex.velocityGradient_eq_coordinateIteratedFDeriv i
      (hφ.contDiffAt.of_le (by simp))

  have hgradSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ velocityGradient φ z i) := by
    rw [hgradEq]
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiff _ φ hφ
  have hgradCompact : HasCompactSupport (fun z ↦ velocityGradient φ z i) := by
    rw [hgradEq]
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_hasCompactSupport _ φ hφCompact
  have hgradV : tsupport (fun z ↦ velocityGradient φ z i) ⊆ V := by
    rw [hgradEq]
    exact (TimeVelocityMultiIndex.coordinateIteratedFDeriv_tsupport_subset _ φ).trans hφV
  have hfirst := coefficientProductComponent_pairing hV q hqM BqM hBqM
    hqBoundM Dj beta (velocityGradient φ · i)
    hgradSmooth hgradCompact hgradV
  have hsecond := coefficientProductComponent_pairing hV dq hdq Bdq hBdq
    hdqBound Dj beta φ hφ hφCompact hφV
  simp only [Dj, shiftedVelocityFamily_representative, dite_eq_ite,
    shiftedVelocityProduct_sum] at hfirst hsecond
  have hderivedSum (z) (hz : z ∈ V) :
      properDiffusionGradientSum dq D beta j z = properDiffusionDerivedCoefficientSum q D beta j i z := by
    apply Finset.sum_congr rfl
    intro gamma _
    by_cases h : gamma.left ≠ 0
    · simp only [dif_pos h, dq]
      rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at]
      exact (hq.contDiffAt (hV.mem_nhds hz)).of_le (by
        exact_mod_cast (show gamma.left.order + 1 ≤ M + 1 by
          have := gamma.order_left_le
          have := TimeVelocityMultiIndex.order_le_parabolicWeight beta.1
          have := beta.2
          omega))
    · simp only [dif_neg h]
  replace hsecond :
      (∫ z in V, (dq z * D.representative (liftVelocity beta j) z +
        properDiffusionDerivedCoefficientSum q D beta j i z) * φ z ∂volume) = _ :=
    (integral_congr_ae (by
      filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
      rw [← hderivedSum z hz])).trans hsecond
  have hproper := properDiffusion_compactTest_identity hV q hq Bq hBq hqBound
    D beta j i φ hφ hφCompact hφV
  let rj := ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
    (ParabolicDerivativeIndex.velocityOne j)
  let rji := ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
    (ParabolicDerivativeIndex.velocityTwo j i)
  let zeroM := zero d M
  have hweight : (rj.1 + Pi.single (velocityCoord i) 1).parabolicWeight ≤ M + 1 := by
    have hr : rj.1 + Pi.single (velocityCoord i) 1 = rji.1 := by
      simp only [rj, rji, coe_castLE, velocityTwo, coe_velocitySucc_eq_add_single]
    rw [hr]
    exact rji.2
  have hqC1 : ContDiffOn ℝ 1 q V := hq.of_le (by
    exact_mod_cast (show 1 ≤ M + 1 by omega))
  have hqZero : ∀ z ∈ V, |q z| ≤ Bq
      (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM) := by
    intro z hz
    simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
      hqBound (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM) z hz
  have hdq_eq (z) (hz : z ∈ V) : velocityGradient q z i = dq z :=
    TimeVelocityMultiIndex.velocityGradient_eq_coordinateIteratedFDeriv i
      (hqC1.contDiffAt (hV.mem_nhds hz))
  have hqGrad : ∀ z ∈ V, |velocityGradient q z i| ≤ Bq (addVelocityIndex zeroM i) := by
    intro z hz
    rw [hdq_eq z hz]
    simpa only [dq, coe_addVelocityIndex, zeroM, coe_zero, zero_add] using
      hqBound (addVelocityIndex zeroM i) z hz
  have hrootWeak : HasWeakVelocityPartialDerivOn V i (D.representative rj) (D.representative rji) := by
    have hr : (⟨rj.1 + Pi.single (velocityCoord i) 1, hweight⟩ : ParabolicDerivativeIndex d (M + 1)) = rji := by
      apply Subtype.ext
      simp only [rj, rji, coe_castLE, velocityTwo, coe_velocitySucc_eq_add_single]
    rw [← hr]
    exact D.hasWeak_add_single rj (velocityCoord i) hweight
  have hrootProduct :=
    (velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le hV i
      (Bq (ParabolicDerivativeIndex.castLE (Nat.le_succ M) zeroM))
      (Bq (addVelocityIndex zeroM i)) (hBq _) (hBq _) q hqC1 hqZero hqGrad
      (D.representative rj) (D.representative rji) (D.memLp _) (D.memLp _)
      hrootWeak).2.2.2.1
  let psi := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  have hpsi := TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiff beta.1 φ hφ
  have hpsiCompact := TimeVelocityMultiIndex.coordinateIteratedFDeriv_hasCompactSupport beta.1 φ hφCompact
  have hpsiV := (TimeVelocityMultiIndex.coordinateIteratedFDeriv_tsupport_subset beta.1 φ).trans hφV
  have hroot := hrootProduct psi hpsi hpsiCompact hpsiV
  have hgradPsi : (fun z ↦ velocityGradient psi z i) =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
        (fun z ↦ velocityGradient φ z i) := by
    funext z
    dsimp only [psi]
    rw [hgradEq]
    calc
      velocityGradient
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ) z i =
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (beta.1 + Pi.single (velocityCoord i) 1) φ z := by
        rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at]
        · simp [velocityGradient, timeVelocityBasis_velocity, PDE.basisVec]
        · exact (contDiff_infty.mp hφ _).contDiffAt
      _ = TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
          (TimeVelocityMultiIndex.coordinateIteratedFDeriv
            (Pi.single (velocityCoord i) 1) φ) z :=
        (TimeVelocityMultiIndex.coordinateIteratedFDeriv_comp_single_at
          beta.1 (velocityCoord i) φ z
            ((contDiff_infty.mp hφ _).contDiffAt)).symm
  simp_rw [congrFun hgradPsi] at hroot
  simp only [rj, rji] at hroot
  have hφLp : MemLp φ 2 (timeVelocityVolumeOn V) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hgradLp : MemLp (fun z ↦ velocityGradient φ z i) 2
      (timeVelocityVolumeOn V) :=
    (hgradSmooth.continuous.memLp_of_hasCompactSupport hgradCompact).restrict V
  have hpsiLp : MemLp psi 2 (timeVelocityVolumeOn V) :=
    (hpsi.continuous.memLp_of_hasCompactSupport hpsiCompact).restrict V
  let rb := liftVelocity beta j
  have hqBetaMem := coefficient_mul_memLp hV hq Bq hBq hqBound (D.memLp rb)
  have hdqBetaMem := coefficient_mul_memLp hV hdq Bdq hBdq hdqBound (D.memLp rb)
  have hqHessMem := coefficient_mul_memLp hV hq Bq hBq hqBound (D.memLp rji)
  have hdqRootMem := coefficient_mul_memLp hV hdq Bdq hBdq hdqBound (D.memLp rj)
  have hproperData := properDiffusionSums_data hV q hq Bq hBq hqBound D beta j i
  rw [integral_add_mul_L2 hqBetaMem hproperData.1 hgradLp] at hfirst
  rw [integral_add_mul_L2 hdqBetaMem hproperData.2.1 hφLp] at hsecond
  have hroot' : (∫ z in V, q z * D.representative rj z *
        coordinateIteratedFDeriv beta.1 (velocityGradient φ · i) z ∂volume) =
      -∫ z in V, (q z * D.representative rji z + dq z * D.representative rj z) * psi z ∂volume := by
    refine hroot.trans (congrArg Neg.neg (integral_congr_ae ?_))
    filter_upwards [ae_restrict_mem hV.measurableSet] with z hz
    rw [hdq_eq z hz]
  rw [integral_add_mul_L2 hqHessMem hdqRootMem hpsiLp] at hroot'
  dsimp only [psi, rj, rji, dq] at hroot'
  dsimp only [dq] at hsecond ⊢
  linear_combination -hfirst - hsecond - hproper -
    ((-1 : ℝ) ^ beta.1.order) * hroot'

/-- Pair one differentiated drift component with a compactly supported test. -/
theorem driftComponent_pairing
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M) (j : Fin d)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V,
        (b z.1 z.2 j *
            D.representative
              (liftVelocity beta j) z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z
      ∂(volume : Measure (TimeVelocity d))) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V,
          (b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d)) := by
  have hpair := coefficientProductComponent_pairing hV
    (fun z : TimeVelocity d ↦ b z.1 z.2 j) (hb j) (Bb j) (hBb j)
    (hbBound j) (shiftedVelocityFamily hM D j) beta φ hφ hφCompact hφV
  simpa only [shiftedVelocityFamily_representative, properSplitRightVelocity_eq_liftVelocity,
    dite_eq_ite] using hpair

/-- Pair the differentiated zeroth-order component with a compactly supported test. -/
theorem zerothOrderComponent_pairing
    (c : ℝ → PDE.Vec d → ℝ)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∫ z in V,
        (c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z +
          ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x : TimeVelocity d ↦ c x.1 x.2) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightValue
                    beta gamma hproper) z
            else 0) * φ z
      ∂(volume : Measure (TimeVelocity d))) =
      ((-1 : ℝ) ^ beta.1.order) *
        ∫ z in V, (c z.1 z.2 * u z) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d)) := by
  have hpair := coefficientProductComponent_pairing hV
    (fun z : TimeVelocity d ↦ c z.1 z.2) hc Bc hBc hcBound
    (truncatedValueFamily D) beta φ hφ hφCompact hφV
  have hidx (gamma : TimeVelocityMultiIndex.Split beta.1) (h : gamma.left ≠ 0) :
      properSplitRightValue beta gamma h = castLE (Nat.le_succ M) (splitRight beta gamma) :=
    Subtype.ext rfl
  simpa only [truncatedValueFamily_representative, hidx, dite_eq_ite] using hpair

end

/-- Select one precompact test neighborhood with majorants for all coefficients. -/
theorem exists_precompactOpen_coefficient_majorants
    {d M : ℕ} {U K : Set (TimeVelocity d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ c z.1 z.2) U) :
    ∃ (V : Set (TimeVelocity d))
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
  let qa : Fin d × Fin d → TimeVelocity d → ℝ :=
    fun ij z ↦ a z.1 z.2 ij.1 ij.2
  obtain ⟨W, BA, hW, hKW, hWU, hWc, hBA0, hBA⟩ :=
    exists_precompactOpen_coordinateIteratedFDeriv_majorants
      hU hK hKU qa (fun ij ↦ ha ij.1 ij.2)
  let qbc : Option (Fin d) → TimeVelocity d → ℝ
    | none => fun z ↦ c z.1 z.2
    | some j => fun z ↦ b z.1 z.2 j
  have hqbc : ∀ k, ContDiffOn ℝ M (qbc k) W := by
    intro k
    cases k with
    | none => exact hc.mono (subset_closure.trans hWU)
    | some j => exact (hb j).mono (subset_closure.trans hWU)
  obtain ⟨V, BBC, hV, hKV, hVW, hVc, hBBC0, hBBC⟩ :=
    exists_precompactOpen_coordinateIteratedFDeriv_majorants
      hW hK hKW qbc hqbc
  refine ⟨V, fun i j ↦ BA (i, j), fun j ↦ BBC (some j), BBC none,
    hV, hKV, hVW.trans (subset_closure.trans hWU), hVc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j alpha ↦ hBA0 (i, j) alpha
  · exact fun j alpha ↦ hBBC0 (some j) alpha
  · exact fun alpha ↦ hBBC0 none alpha
  · intro i j alpha z hz
    exact hBA (i, j) alpha z (subset_closure (hVW hz))
  · intro j alpha z hz
    exact hBBC (some j) alpha z hz
  · intro alpha z hz
    exact hBBC none alpha z hz

end GenericPreLiftDifferentiatedWeakEquationSupport

end HypoellipticAleksandrov.Parabolic
