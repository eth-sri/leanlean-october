module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexSplitSuccessor
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1WeakLeibniz
import HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import HypoellipticAleksandrov.Parabolic.WeakDerivativesLocal
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp

/-! # Weak multi-index Leibniz families

This module constructs the finite family of weak parabolic derivatives of a
product between a classical coefficient and a selected weak derivative family.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory ParabolicDerivativeIndex
open TimeVelocityMultiIndex (coordinateIteratedFDeriv)
open scoped ENNReal BigOperators

/-- The literal multi-index Leibniz representative for multiplication of a
selected weak derivative family by a classical coefficient. -/
noncomputable def parabolicWeakMulRepresentative
    {d L : ℕ}
    (q : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (Du : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    TimeVelocity d → ℝ :=
  fun z =>
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      (beta.1.choose gamma.left : ℝ) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
        Du.representative
          (ParabolicDerivativeIndex.splitRight beta gamma) z

private theorem split_zero_eq {d : ℕ}
    (gamma : TimeVelocityMultiIndex.Split (0 : TimeVelocityMultiIndex d)) :
  gamma = default := by
  funext c
  exact Fin.eq_zero _

private theorem representative_zero
    {d L : ℕ} (q : TimeVelocity d → ℝ)
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (Du : ParabolicWeakDerivativeFamily d L U u) :
    parabolicWeakMulRepresentative q Du (ParabolicDerivativeIndex.zero d L) =
      fun z => q z * Du.representative (ParabolicDerivativeIndex.zero d L) z := by
  funext z
  unfold parabolicWeakMulRepresentative
  rw [Fintype.sum_eq_single
    (default : TimeVelocityMultiIndex.Split (ParabolicDerivativeIndex.zero d L).1)]
  · have hleft : (default : TimeVelocityMultiIndex.Split
        (ParabolicDerivativeIndex.zero d L).1).left = 0 := by
      funext c
      rfl
    have hright : ParabolicDerivativeIndex.splitRight
        (ParabolicDerivativeIndex.zero d L) default =
        ParabolicDerivativeIndex.zero d L := by
      rfl
    rw [hleft, hright]
    simp [TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero]
  · intro b hb
    exact (hb (split_zero_eq b)).elim

section
variable {d N : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V) {q f : TimeVelocity d → ℝ}
  (hq : ContDiffOn ℝ N q V) (B : ParabolicDerivativeIndex d N → ℝ) (hB : ∀ α, 0 ≤ B α)
  (hbound : ∀ α z, z ∈ V → |α.1.coordinateIteratedFDeriv q z| ≤ B α)
include N hV hq B hB hbound

/-- Multiplication by a bounded coefficient derivative preserves `L²`. -/
theorem coordinateDerivative_mul_memLp
    (α : ParabolicDerivativeIndex d N) (hf : ParabolicMemLpOn V 2 f) :
    ParabolicMemLpOn V 2 (fun z => α.1.coordinateIteratedFDeriv q z * f z) :=
  continuousOn_bounded_mul_memLp hV _ _ (B α) (hB α)
    (α.1.coordinateIteratedFDeriv_contDiffOn (m := 0) hV hq
      (by simpa using α.1.order_le_parabolicWeight.trans α.2)).continuousOn (hbound α) hf

/-- A bounded coefficient preserves `L²` under multiplication. -/
theorem coefficient_mul_memLp
    (hf : ParabolicMemLpOn V 2 f) : ParabolicMemLpOn V 2 (fun z => q z * f z) := by
  simpa only [coe_zero, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
    coordinateDerivative_mul_memLp hV hq B hB hbound (zero d N) hf

end

section
variable {d L : ℕ} {U : Set (TimeVelocity d)}

/-- A single coordinate successor, expressed by adding its unit multi-index. -/
theorem ParabolicWeakDerivativeFamily.hasWeak_add_single {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d L U u) (β : ParabolicDerivativeIndex d L)
    (c : TimeVelocityCoord d) (h : (β.1 + Pi.single c 1).parabolicWeight ≤ L) :
    HasWeakFDerivApplyOn U (timeVelocityBasis c) (D.representative β)
      (D.representative ⟨β.1 + Pi.single c 1, h⟩) := by
  rcases c with c | i
  · cases c
    change HasWeakFDerivApplyOn U (timeVelocityBasis (timeCoord d)) (D.representative β)
      (D.representative ⟨β.1 + Pi.single (timeCoord d) 1, h⟩)
    change (β.1 + Pi.single (timeCoord d) 1).parabolicWeight ≤ L at h
    have h₂ : β.1.parabolicWeight + 2 ≤ L := by simpa using h
    rw [show (⟨_, h⟩ : ParabolicDerivativeIndex d L) = timeSucc β h₂ from
      Subtype.ext (coe_timeSucc_eq_add_single β h₂).symm]
    exact D.hasWeakTimeSucc β h₂
  · change HasWeakFDerivApplyOn U (timeVelocityBasis (velocityCoord i)) (D.representative β)
      (D.representative ⟨β.1 + Pi.single (velocityCoord i) 1, h⟩)
    change (β.1 + Pi.single (velocityCoord i) 1).parabolicWeight ≤ L at h
    have h₁ : β.1.parabolicWeight + 1 ≤ L := by simpa using h
    rw [show (⟨_, h⟩ : ParabolicDerivativeIndex d L) = velocitySucc β i h₁ from
      Subtype.ext (coe_velocitySucc_eq_add_single β i h₁).symm]
    exact D.hasWeakVelocitySucc β i h₁

private theorem weakMulRepresentative_hasWeak_add_single (hU : IsOpen U)
    {q u : TimeVelocity d → ℝ} (hq : ContDiffOn ℝ L q U)
    (B : ParabolicDerivativeIndex d L → ℝ) (hB : ∀ α, 0 ≤ B α)
    (hbound : ∀ α z, z ∈ U → |α.1.coordinateIteratedFDeriv q z| ≤ B α)
    (D : ParabolicWeakDerivativeFamily d L U u) (β : ParabolicDerivativeIndex d L)
    (c : TimeVelocityCoord d) (h : (β.1 + Pi.single c 1).parabolicWeight ≤ L) :
    HasWeakFDerivApplyOn U (timeVelocityBasis c) (parabolicWeakMulRepresentative q D β)
      (parabolicWeakMulRepresentative q D ⟨β.1 + Pi.single c 1, h⟩) := by
  classical
  let I := TimeVelocityMultiIndex.Split β.1
  let s : TimeVelocityMultiIndex d := Pi.single c 1
  have hleft (γ : I) : (γ.left + s).parabolicWeight ≤ L := by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add] at h ⊢
    exact (Nat.add_le_add_right γ.parabolicWeight_left_le _).trans h
  have hright (γ : I) : (γ.right + s).parabolicWeight ≤ L := by
    simp only [TimeVelocityMultiIndex.parabolicWeight_add] at h ⊢
    exact (Nat.add_le_add_right γ.parabolicWeight_right_le _).trans h
  let val (γ : I) (z) := (β.1.choose γ.left : ℝ) *
    coordinateIteratedFDeriv γ.left q z * D.representative (splitRight β γ) z
  let der (γ : I) (z) := (β.1.choose γ.left : ℝ) *
    (coordinateIteratedFDeriv (γ.left + s) q z * D.representative (splitRight β γ) z +
      coordinateIteratedFDeriv γ.left q z * D.representative ⟨γ.right + s, hright γ⟩ z)
  have hdata (γ : I) : ParabolicMemLpOn U 2 (val γ) ∧ ParabolicMemLpOn U 2 (der γ) ∧
      HasWeakFDerivApplyOn U (timeVelocityBasis c) (val γ) (der γ) := by
    let a := coordinateIteratedFDeriv γ.left q
    let a' := coordinateIteratedFDeriv (γ.left + s) q
    let v := D.representative (splitRight β γ)
    let v' := D.representative ⟨γ.right + s, hright γ⟩
    let K : ℝ := β.1.choose γ.left
    let α := splitLeft β γ
    let α' : ParabolicDerivativeIndex d L := ⟨γ.left + s, hleft γ⟩
    have hw : 1 ≤ s.parabolicWeight := by
      rcases c with c | i
      · cases c
        change 1 ≤ TimeVelocityMultiIndex.parabolicWeight (Pi.single (timeCoord d) 1)
        simp
      · change 1 ≤ TimeVelocityMultiIndex.parabolicWeight (Pi.single (velocityCoord i) 1)
        simp
    have ho : γ.left.order + 1 ≤ L := by
      have hl := hleft γ
      rw [TimeVelocityMultiIndex.parabolicWeight_add] at hl
      have := γ.left.order_le_parabolicWeight
      omega
    have ha := γ.left.coordinateIteratedFDeriv_contDiffOn (m := 1) hU hq
      (by exact_mod_cast (show 1 + γ.left.order ≤ L by omega))
    have hd z (hz : z ∈ U) : fderiv ℝ a z (timeVelocityBasis c) = a' z :=
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at _ c q z
        ((hq.contDiffAt (hU.mem_nhds hz)).of_le (by exact_mod_cast ho))).symm
    have hp := fderivApplyC1_mul_hasWeakFDerivApplyOn_memLp_eLpNorm_le hU (timeVelocityBasis c)
      (B α) (B α') (hB _) (hB _) a ha (hbound α)
      (fun z hz => hd z hz ▸ hbound α' z hz) v v' (D.memLp _) (D.memLp _)
      (D.hasWeak_add_single (splitRight β γ) c (hright γ))
    have hv : (K • (a * v)) = val γ := by ext z; simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, val, K, a, v, mul_assoc]
    have hder : (K • (a * v' + (fun z => fderiv ℝ a z (timeVelocityBasis c)) * v))
        =ᵐ[timeVelocityVolumeOn U] der γ := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
      simp only [Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul, hd z hz, der, v, v', a, a', K]
      rw [add_comm]
    exact ⟨hv ▸ hp.2.1.const_smul K, (memLp_congr_ae hder).mp (hp.2.2.1.const_smul K),
      (hp.2.2.2.1.smul K).congr_ae (.of_forall fun z => congrFun hv z) hder⟩
  have hsum := HasWeakFDerivApplyOn.fintype_sum (u := val) (du := der) (e := timeVelocityBasis c)
    (fun γ => (hdata γ).2.2) (fun γ => (hdata γ).1.locallyIntegrableOn (by norm_num))
    (fun γ => (hdata γ).2.1.locallyIntegrableOn (by norm_num))
  have heq : (fun z => ∑ γ, der γ z) = parabolicWeakMulRepresentative q D ⟨β.1 + s, h⟩ := by
    funext z
    let A (a b : TimeVelocityMultiIndex d) := if hb : b.parabolicWeight ≤ L then
      coordinateIteratedFDeriv a q z * D.representative ⟨b, hb⟩ z else 0
    calc
      (∑ γ, der γ z) = ∑ γ : I, (β.1.choose γ.left : ℝ) *
          (A (γ.left + s) γ.right + A γ.left (γ.right + s)) := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        have hr : γ.right.parabolicWeight ≤ L := (splitRight β γ).2
        simp only [A, der, dif_pos hr, dif_pos (hright γ), coe_splitRight]
        rfl
      _ = ∑ γ : TimeVelocityMultiIndex.Split (β.1 + s),
          ((β.1 + s).choose γ.left : ℝ) * A γ.left γ.right :=
        TimeVelocityMultiIndex.sum_choose_split_add_single β.1 c A
      _ = _ := by
        unfold parabolicWeakMulRepresentative
        refine Finset.sum_congr rfl fun γ _ => ?_
        simp only [A, dif_pos (γ.parabolicWeight_right_le.trans h), mul_assoc]
        rfl
  rw [heq] at hsum
  exact hsum

end

section
variable {d L : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
  (Bq : ParabolicDerivativeIndex d L → ℝ) (hBq : ∀ alpha, 0 ≤ Bq alpha) (q : TimeVelocity d → ℝ)
  (hq : ContDiffOn ℝ L q U)
  (hqBound : ∀ (alpha : ParabolicDerivativeIndex d L) z, z ∈ U → |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ Bq alpha)
  (u : TimeVelocity d → ℝ) (Du : ParabolicWeakDerivativeFamily d L U u)
include hU Bq hBq hq hqBound Du

/-- Multiplication by a bounded finite-order classical coefficient preserves a
coherent weak parabolic derivative family on an arbitrary open carrier. -/
noncomputable def ParabolicWeakDerivativeFamily.mulContDiffOn :
    ParabolicWeakDerivativeFamily d L U (fun z => q z * u z) where
  representative := parabolicWeakMulRepresentative q Du
  memLp beta := memLp_finsetSum Finset.univ fun gamma _ => by
    simpa only [mul_assoc, coe_splitLeft] using
      (coordinateDerivative_mul_memLp hU hq Bq hBq hqBound
        (splitLeft beta gamma) (Du.memLp (splitRight beta gamma))).const_mul
          (beta.1.choose gamma.left : ℝ)
  zero_ae := by
    filter_upwards [Du.zero_ae] with z hz
    rw [representative_zero]
    exact congrArg (fun x => q z * x) hz
  hasWeakTimeSucc beta h := by
    have hb : (beta.1 + Pi.single (timeCoord d) 1).parabolicWeight ≤ L := by simpa using h
    rw [show timeSucc beta h = ⟨_, hb⟩ from Subtype.ext (coe_timeSucc_eq_add_single beta h)]
    exact weakMulRepresentative_hasWeak_add_single hU hq Bq hBq hqBound Du beta (timeCoord d) hb
  hasWeakVelocitySucc beta i h := by
    have hb : (beta.1 + Pi.single (velocityCoord i) 1).parabolicWeight ≤ L := by simpa using h
    rw [show velocitySucc beta i h = ⟨_, hb⟩ from Subtype.ext (coe_velocitySucc_eq_add_single beta i h)]
    exact weakMulRepresentative_hasWeak_add_single hU hq Bq hBq hqBound Du beta (velocityCoord i) hb

/-- The selected representative of `mulContDiffOn` is definitionally the
literal multi-index Leibniz sum. -/
@[simp] theorem ParabolicWeakDerivativeFamily.mulContDiffOn_representative
    (beta : ParabolicDerivativeIndex d L) :
    (Du.mulContDiffOn hU Bq hBq q hq hqBound).representative beta =
      parabolicWeakMulRepresentative q Du beta :=
  rfl

end

end HypoellipticAleksandrov.Parabolic
