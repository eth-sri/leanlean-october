module

public import HypoellipticAleksandrov.Parabolic.SelectedParabolicOperator
import HypoellipticAleksandrov.Analysis.L2Pairing

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport

/-!
# Generic pre-lift differentiated weak equation

This module exposes the source-facing differentiated scalar equation before
the next spatial lift.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory HypoellipticAleksandrov.Analysis ParabolicDerivativeIndex
open scoped BigOperators ENNReal Topology

private theorem properAtom_memLp
    {d M N : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ N q V)
    (B : ParabolicDerivativeIndex d N → ℝ) (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    (hMN : M ≤ N) (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1)
    (f : gamma.left ≠ 0 → TimeVelocity d → ℝ)
    (hf : ∀ hproper, ParabolicMemLpOn V 2 (f hproper)) :
    ParabolicMemLpOn V 2 (fun z ↦
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          f hproper z
      else 0) := by
  classical
  split
  · rename_i hproper
    let α := castLE hMN (splitLeft beta gamma)
    simpa only [mul_assoc, α, coe_castLE, coe_splitLeft] using (coordinateDerivative_mul_memLp hV hq B hB hqBound α
      (hf hproper)).const_mul (beta.1.choose gamma.left : ℝ)
  · exact MemLp.zero'

private theorem originalEquation_integral
    {d M : ℕ} (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    (hEq :
      D.backwardOperator (by omega) a b c
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) :
    (∫ z in V, D.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
            (ParabolicDerivativeIndex.timeOne d)) z *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∑ i, ∑ j, ∫ z in V, (a z.1 z.2 i j *
          D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityTwo j i)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∑ j, ∫ z in V, (b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.velocityOne j)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) +
      (∫ z in V, (c z.1 z.2 * D.representative
          (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
            (ParabolicDerivativeIndex.zeroTwo d)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) =
      ∫ z in V, F z.1 z.2 *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
  classical
  let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ
  have hθSmooth := TimeVelocityMultiIndex.coordinateIteratedFDeriv_contDiff beta.1 φ hφ
  have hθCompact : HasCompactSupport θ :=
    hφCompact.of_isClosed_subset isClosed_closure
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv_tsupport_subset beta.1 φ)
  have hθLp : ParabolicMemLpOn V 2 θ :=
    (hθSmooth.continuous.memLp_of_hasCompactSupport hθCompact).restrict V
  let h₂ : 2 ≤ M + 1 := by omega
  have htLp := D.memLp (castLE h₂ (timeOne d))
  have haLp (i j : Fin d) := coefficient_mul_memLp hV (ha i j) (Ba i j) (hBa i j) (haBound i j)
    (D.memLp (castLE h₂ (velocityTwo j i)))
  have hbLp (j : Fin d) := coefficient_mul_memLp hV (hb j) (Bb j) (hBb j) (hbBound j)
    (D.memLp (castLE h₂ (velocityOne j)))
  have hcLp := coefficient_mul_memLp hV hc Bc hBc hcBound (D.memLp (castLE h₂ (zeroTwo d)))
  have haRowLp i := memLp_finsetSum Finset.univ fun j _ => haLp i j
  have haSumLp := memLp_finsetSum Finset.univ fun i _ => haRowLp i
  have hbSumLp := memLp_finsetSum Finset.univ fun j _ => hbLp j
  have hraw := integral_congr_ae (hEq.mono fun z hz => congrArg (· * θ z) hz)
  simp only [ParabolicWeakDerivativeFamily.backwardOperator] at hraw
  have hlin := integral_add_mul_L2 ((htLp.add haSumLp).add hbSumLp) hcLp hθLp
  have hlin₂ := integral_add_mul_L2 (htLp.add haSumLp) hbSumLp hθLp
  simp only [Pi.add_apply] at hlin hlin₂
  rw [hlin₂, integral_add_mul_L2 htLp haSumLp hθLp,
    integral_sum_mul_L2 haRowLp hθLp, integral_sum_mul_L2 hbLp hθLp] at hlin
  have hrow i := integral_sum_mul_L2 (haLp i) hθLp
  simp_rw [hrow] at hlin
  exact hlin.symm.trans hraw

section
variable {d M : ℕ} {V : Set (TimeVelocity d)} (hV : IsOpen V)
include hV

private theorem principalComponents_pairing_explicit
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    {u : TimeVelocity d → ℝ}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j,
        (-(∫ z in V,
            a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      change beta.1.parabolicWeight + 1 ≤ M + 1
                      omega)) z *
              velocityGradient φ z i
            ∂(volume : Measure (TimeVelocity d))) -
          ∫ z in V,
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
                  (Pi.single (velocityCoord i) 1)
                  (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      change beta.1.parabolicWeight + 1 ≤ M + 1
                      omega)) z *
              φ z
            ∂(volume : Measure (TimeVelocity d)))) =
      ((-1 : ℝ) ^ beta.1.order) *
        (∑ i, ∑ j, ∫ z in V,
          (a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z
        ∂(volume : Measure (TimeVelocity d))) := by
  classical
  have hcomponent (i j : Fin d) := (GenericPreLiftDifferentiatedWeakEquationSupport.principalComponent_pairing hV (fun z : TimeVelocity d ↦ a z.1 z.2 i j) (ha i j) (Ba i j) (hBa i j) (haBound i j) hM D beta j i φ hφ hφCompact hφV)
  calc
    _ = ∑ i, ∑ j,
        (((-1 : ℝ) ^ beta.1.order) *
            ∫ z in V,
              (a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                    (ParabolicDerivativeIndex.velocityTwo j i)) z) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
              ∂(volume : Measure (TimeVelocity d)) -
          ∫ z in V,
            (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
              if hproper : gamma.left ≠ 0 then
                (beta.1.choose gamma.left : ℝ) *
                  TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                    (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
                  D.representative
                    (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                      beta gamma hproper j i) z
              else 0) * φ z
            ∂(volume : Measure (TimeVelocity d))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hcomponent i j
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]

end

set_option maxHeartbeats 700000 in
private theorem integral_genericPreliftDifferentiatedScalarEquationOn
    {d M : ℕ} (hM : 1 ≤ M)
    {V : Set (TimeVelocity d)} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    {u : TimeVelocity d → ℝ}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (E : ParabolicWeakDerivativeFamily d M V
      (fun z : TimeVelocity d ↦ F z.1 z.2))
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (Bb : Fin d → ParabolicDerivativeIndex d M → ℝ)
    (Bc : ParabolicDerivativeIndex d M → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (hBb : ∀ j alpha, 0 ≤ Bb j alpha)
    (hBc : ∀ alpha, 0 ≤ Bc alpha)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V)
    (hc : ContDiffOn ℝ M (fun z : TimeVelocity d ↦ c z.1 z.2) V)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    (hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha)
    (hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha)
    (hEq :
      D.backwardOperator (by omega) a b c
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j, ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1)
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          φ z ∂(volume : Measure (TimeVelocity d))) +
      (∑ j, ∫ z in V,
        b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  change beta.1.parabolicWeight + 1 ≤ M + 1
                  omega)) z *
          φ z ∂(volume : Measure (TimeVelocity d))) +
      (∫ z in V, c z.1 z.2 *
          D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          φ z ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in V,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  classical
  let s : ℝ := (-1 : ℝ) ^ beta.1.order
  let A : TimeVelocity d → ℝ := fun z ↦
    ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i) z
      else 0
  let B : TimeVelocity d → ℝ := fun z ↦
    ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocity
              beta gamma hproper j) z
      else 0
  let C : TimeVelocity d → ℝ := fun z ↦
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ c x.1 x.2) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightValue
              beta gamma hproper) z
      else 0
  have hφLp : ParabolicMemLpOn V 2 φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have horiginal := originalEquation_integral hM hV a b c F D Ba Bb Bc
    hBa hBb hBc ha hb hc haBound hbBound hcBound hEq beta φ hφ hφCompact
  have htime := GenericPreLiftDifferentiatedWeakEquationSupport.timeComponent_pairing
    D (by omega : 2 ≤ M + 1) beta φ hφ hφCompact hφV
  have hprincipal := principalComponents_pairing_explicit hV a ha Ba hBa haBound
    hM D beta φ hφ hφCompact hφV
  have hsource := E.integral_representative_mul_test beta φ hφ hφCompact hφV
  have hdrift (j : Fin d) :=
    GenericPreLiftDifferentiatedWeakEquationSupport.driftComponent_pairing
      hV b hb Bb hBb hbBound hM D beta j φ hφ hφCompact hφV
  have hzero :=
    GenericPreLiftDifferentiatedWeakEquationSupport.zerothOrderComponent_pairing
      hV c hc Bc hBc hcBound D beta φ hφ hφCompact hφV
  have hsquare : s * s = 1 := by
    dsimp only [s]
    rw [← pow_two, ← pow_mul]
    simp
  have hAijLp (i j : Fin d) := memLp_finsetSum Finset.univ fun gamma _ =>
    properAtom_memLp hV _ (ha i j) (Ba i j) (hBa i j) (haBound i j) (Nat.le_succ M) beta gamma
      (fun h => D.representative (properSplitRightVelocityTwo beta gamma h j i)) (fun _ => D.memLp _)
  have hBjLp (j : Fin d) := memLp_finsetSum Finset.univ fun gamma _ =>
    properAtom_memLp hV _ (hb j) (Bb j) (hBb j) (hbBound j) (le_refl M) beta gamma
      (fun h => D.representative (properSplitRightVelocity beta gamma h j)) (fun _ => D.memLp _)
  have hCLp : ParabolicMemLpOn V 2 C := memLp_finsetSum Finset.univ fun gamma _ =>
    properAtom_memLp hV _ hc Bc hBc hcBound (le_refl M) beta gamma
      (fun h => D.representative (properSplitRightValue beta gamma h)) (fun _ => D.memLp _)
  have hAiLp i := memLp_finsetSum Finset.univ fun j _ => hAijLp i j
  have hALp : ParabolicMemLpOn V 2 A := memLp_finsetSum Finset.univ fun i _ => hAiLp i
  have hBLp : ParabolicMemLpOn V 2 B := memLp_finsetSum Finset.univ fun j _ => hBjLp j
  have hbRootLp (j : Fin d) := coefficient_mul_memLp hV (hb j) (Bb j) (hBb j) (hbBound j)
    (D.memLp (velocitySucc (castLE (Nat.le_succ M) beta) j
      (by change beta.1.parabolicWeight + 1 ≤ M + 1; omega)))
  have hcRootLp := coefficient_mul_memLp hV hc Bc hBc hcBound (D.memLp (castLE (Nat.le_succ M) beta))
  have hdrift' j := (integral_add_mul_L2 (hbRootLp j) (hBjLp j) hφLp).symm.trans (hdrift j)
  have hdriftSum := Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hdrift' j)
  have hzero' := (integral_add_mul_L2 hcRootLp hCLp hφLp).symm.trans hzero
  have hAExpand := (integral_sum_mul_L2 hAiLp hφLp).trans
    (Finset.sum_congr rfl fun i _ => integral_sum_mul_L2 (hAijLp i) hφLp)
  have hBExpand := integral_sum_mul_L2 hBjLp hφLp
  have hresidual :
      (∫ z in V, properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z ∂volume) =
      (∫ z in V, E.representative beta z * φ z ∂volume) -
        (∫ z in V, A z * φ z ∂volume) - (∫ z in V, B z * φ z ∂volume) -
        (∫ z in V, C z * φ z ∂volume) := by
    change (∫ z in V, ((E.representative beta z - A z - B z) - C z) * φ z ∂volume) = _
    have hE := E.memLp beta
    have h₁ := integral_sub_mul_L2 ((hE.sub hALp).sub hBLp) hCLp hφLp
    have h₂ := integral_sub_mul_L2 (hE.sub hALp) hBLp hφLp
    simp only [Pi.sub_apply] at h₁ h₂
    rw [h₁, h₂, integral_sub_mul_L2 hE hALp hφLp]
  have hzeroRootEq :
      (∫ z in V, (c z.1 z.2 * u z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) =
      ∫ z in V, (c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
          (ParabolicDerivativeIndex.zeroTwo d)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    apply integral_congr_ae
    filter_upwards [D.zero_ae] with z hz
    have hindex : ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
        (ParabolicDerivativeIndex.zeroTwo d) =
        ParabolicDerivativeIndex.zero d (M + 1) := by
      apply Subtype.ext
      simp [ParabolicDerivativeIndex.zeroTwo, ParabolicDerivativeIndex.zero]
    rw [hindex, hz]
  rw [hresidual]
  dsimp only [A, B]
  rw [hAExpand, hBExpand]
  rw [hzeroRootEq] at hzero'
  simp only [Finset.sum_add_distrib] at hdriftSum
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hprincipal
  rw [← Finset.mul_sum] at hdriftSum
  have htime' := congrArg (fun x : ℝ ↦ s * x) htime
  change s * _ = s * _ at htime'
  rw [← mul_assoc, hsquare, one_mul] at htime'
  dsimp only [s] at htime hprincipal hsource hdriftSum hzero' hsquare ⊢
  linear_combination
    ((-1 : ℝ) ^ beta.1.order) * horiginal - htime' + hprincipal +
      hdriftSum + hzero' - hsource

/-- The differentiated scalar equation tested before the next spatial lift.
The principal second-order term is integrated once in its first velocity
coordinate, retaining both the coefficient and coefficient-derivative terms. -/
theorem integral_genericPreliftDifferentiatedScalarEquation
    {d M : ℕ}
    (hM : 1 ≤ M)
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (u : TimeVelocity d → ℝ)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z : TimeVelocity d => F z.1 z.2))
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d => c z.1 z.2) U)
    (hEq :
      D.backwardOperator (by omega) a b c
        =ᵐ[timeVelocityVolumeOn U]
      (fun z => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M)
    (φ : TimeVelocity d → ℝ)
    (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ U) :
    -(∫ z in U,
        D.representative
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) z *
          timeDerivative φ z
        ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j,
        ∫ z in U,
          a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    change beta.1.parabolicWeight + 1 ≤ M + 1
                    omega)) z *
            velocityGradient φ z i
          ∂(volume : Measure (TimeVelocity d))) -
      (∑ i, ∑ j,
        ∫ z in U,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (Pi.single (velocityCoord i) 1)
                (fun x : TimeVelocity d => a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    change beta.1.parabolicWeight + 1 ≤ M + 1
                    omega)) z *
            φ z
          ∂(volume : Measure (TimeVelocity d))) +
      (∑ j,
        ∫ z in U,
          b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    change beta.1.parabolicWeight + 1 ≤ M + 1
                    omega)) z *
            φ z
          ∂(volume : Measure (TimeVelocity d))) +
      (∫ z in U,
        c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE
                (Nat.le_succ M) beta) z *
          φ z
        ∂(volume : Measure (TimeVelocity d))) =
      ∫ z in U,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z *
          φ z
        ∂(volume : Measure (TimeVelocity d)) := by
  classical
  obtain ⟨V, Ba, Bb, Bc, hV, hφV, hclosureVU, _hVCompact,
      hBa, hBb, hBc, haBoundClosure, hbBoundClosure, hcBoundClosure⟩ :=
    GenericPreLiftDifferentiatedWeakEquationSupport.exists_precompactOpen_coefficient_majorants
      hU hφCompact hφSupport a b c ha hb hc
  have hVU : V ⊆ U := subset_closure.trans hclosureVU
  let DV := D.restrict hVU
  let EV := E.restrict hVU
  have haV : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V :=
    fun i j ↦ (ha i j).mono hVU
  have hbV : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ b z.1 z.2 j) V :=
    fun j ↦ (hb j).mono hVU
  have hcV : ContDiffOn ℝ M
      (fun z : TimeVelocity d ↦ c z.1 z.2) V := hc.mono hVU
  have haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha :=
    fun i j alpha z hz ↦ haBoundClosure i j alpha z (subset_closure hz)
  have hbBound : ∀ j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ b x.1 x.2 j) z| ≤ Bb j alpha :=
    fun j alpha z hz ↦ hbBoundClosure j alpha z (subset_closure hz)
  have hcBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ c x.1 x.2) z| ≤ Bc alpha :=
    fun alpha z hz ↦ hcBoundClosure alpha z (subset_closure hz)
  have hEqV := ae_restrict_of_ae_restrict_of_subset hVU hEq
  have hlocal := integral_genericPreliftDifferentiatedScalarEquationOn hM hV
    a b c F DV EV Ba Bb Bc hBa hBb hBc haV hbV hcV haBound hbBound hcBound
    (by
      filter_upwards [hEqV] with z hz
      simpa only [DV, ParabolicWeakDerivativeFamily.backwardOperator, ParabolicWeakDerivativeFamily.restrict_representative] using hz)
    beta φ hφSmooth hφCompact hφV
  have htimeSupport : tsupport (timeDerivative φ) ⊆ V :=
    (timeDerivative_tsupport φ).trans hφV
  have htime :
      (∫ z in U, D.representative
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in V, D.representative
          (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂(volume : Measure (TimeVelocity d)) :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _ htimeSupport
  have hprincipal (i j : Fin d) :
      (∫ z in U, (a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            (by change beta.1.parabolicWeight + 1 ≤ M + 1; omega)) z) *
          velocityGradient φ z i ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in V, (a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            (by change beta.1.parabolicWeight + 1 ≤ M + 1; omega)) z) *
          velocityGradient φ z i ∂(volume : Measure (TimeVelocity d)) :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _
      ((velocityGradient_tsupport (i := i) φ).trans hφV)
  have hphiMul (f : TimeVelocity d → ℝ) :
      (∫ z in U, f z * φ z ∂(volume : Measure (TimeVelocity d))) =
        ∫ z in V, f z * φ z ∂(volume : Measure (TimeVelocity d)) :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU f φ hφV
  simpa only [DV, EV, ParabolicWeakDerivativeFamily.restrict_representative,
    htime, hprincipal, hphiMul, properDifferentiatedScalarCommutatorResidual] using hlocal

end HypoellipticAleksandrov.Parabolic
