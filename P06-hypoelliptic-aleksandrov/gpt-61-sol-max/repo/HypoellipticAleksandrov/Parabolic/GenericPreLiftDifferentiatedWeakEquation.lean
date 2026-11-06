module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.Bound
import all HypoellipticAleksandrov.Parabolic.CrossVelocityWeakDerivativeCommutation
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientEnergyIdentity
import all HypoellipticAleksandrov.Parabolic.GenericPreLiftSpatialDifferenceQuotientFixedDirection
import all HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
import all HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation
import all HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp from HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn from HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
open private HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_tsupport_subset from HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyPairing
open private HypoellipticAleksandrov.Parabolic.splitLeft_order_le from HypoellipticAleksandrov.Parabolic.GenericProperCommutatorResidual
section
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
private alias _semanticProof_77a760a65596 := HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset
end
section
open private HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport_subset from HypoellipticAleksandrov.Parabolic.MixedTimeVelocityWeakDerivativeCommutation
private alias _semanticProof_2e5cb35f552a := HypoellipticAleksandrov.Parabolic.timeDerivative_tsupport_subset
end


/-!
# Generic pre-lift differentiated weak equation

This module exposes the source-facing differentiated scalar equation before
the next spatial lift.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal Topology

section
variable {d : ℕ}




private theorem setIntegral_mul_eq_of_tsupport_subset
     {V U : HypoellipticAleksandrov.Parabolic.Region d} (hU : MeasurableSet U)
    (hVU : V ⊆ U) (f g : HypoellipticAleksandrov.Parabolic.ScalarField d) (hgV : tsupport g ⊆ V) :
    (∫ z in U, f z * g z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in V, f z * g z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU hVU
  intro z hz
  have hgz : g z = 0 := by
    by_contra hn
    exact hz.2 (hgV (subset_closure hn))
  simp [hgz]

section
variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : ContDiff ℝ PDE.smoothOrder f)

include hf in
private theorem timeDerivative_tsupport_subset
      :
    tsupport (timeDerivative f) ⊆ tsupport f := _semanticProof_2e5cb35f552a

include hf in
private theorem velocityGradient_tsupport_subset

    (i : Fin d) :
    tsupport (fun z ↦ velocityGradient f z i) ⊆ tsupport f := _semanticProof_77a760a65596
end







end








private theorem properAtom_memLp
    {d M N : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ContDiffOn ℝ N q V)
    (B : ParabolicDerivativeIndex d N → ℝ) (hB : ∀ alpha, 0 ≤ B alpha)
    (hqBound : ∀ alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 q z| ≤ B alpha)
    (hMN : M ≤ N) (beta : ParabolicDerivativeIndex d M)
    (gamma : TimeVelocityMultiIndex.Split beta.1)
    (f : gamma.left ≠ 0 → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hf : ∀ hproper, ParabolicMemLpOn V 2 (f hproper)) :
    ParabolicMemLpOn V 2 (fun z ↦
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left q z *
          f hproper z
      else 0) := by
  classical
  by_cases hproper : gamma.left ≠ 0
  · simp only [dif_pos hproper]
    let alpha  :=
      ParabolicDerivativeIndex.castLE hMN
        (ParabolicDerivativeIndex.splitLeft beta gamma)
    apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _
      ((beta.1.choose gamma.left : ℝ) * B alpha)
      (mul_nonneg (Nat.cast_nonneg _) (hB alpha))
    · exact continuousOn_const.mul
        (_root_.HypoellipticAleksandrov.Parabolic.coordinateIteratedFDeriv_continuousOn hV q hq gamma.left
          ((_root_.HypoellipticAleksandrov.Parabolic.splitLeft_order_le beta gamma).trans hMN))
    · intro z hz
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact hqBound alpha z hz
    · exact hf hproper
  · simp only [dif_neg hproper]
    exact MemLp.zero'

private theorem properCommutatorComponents_memLp
    {d M : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
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
    (beta : ParabolicDerivativeIndex d M) :
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z
        else 0) ∧
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0) ∧
    ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ c x.1 x.2) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightValue
                beta gamma hproper) z
        else 0) := (⟨memLp_finset_sum Finset.univ fun i x =>
    memLp_finset_sum Finset.univ fun j x =>
      memLp_finset_sum Finset.univ fun gamma x =>
        properAtom_memLp hV (fun z => a z.1 z.2 i j) (ha i j) (Ba i j) (hBa i j) (haBound i j) (Nat.le_succ M) beta
          gamma (fun hproper => D.representative (beta.properSplitRightVelocityTwo gamma hproper j i)) fun hproper =>
          D.memLp (beta.properSplitRightVelocityTwo gamma hproper j i),
  ⟨memLp_finset_sum Finset.univ fun j x =>
      memLp_finset_sum Finset.univ fun gamma x =>
        properAtom_memLp hV (fun z => b z.1 z.2 j) (hb j) (Bb j) (hBb j) (hbBound j) (le_refl M) beta gamma
          (fun hproper => D.representative (beta.properSplitRightVelocity gamma hproper j)) fun hproper =>
          D.memLp (beta.properSplitRightVelocity gamma hproper j),
    memLp_finset_sum Finset.univ fun gamma x =>
      properAtom_memLp hV (fun z => c z.1 z.2) hc Bc hBc hcBound (le_refl M) beta gamma
        (fun hproper => D.representative (beta.properSplitRightValue gamma hproper)) fun hproper =>
        D.memLp (beta.properSplitRightValue gamma hproper)⟩⟩)

private theorem originalEquation_integral
    {d M : ℕ} (hM : 1 ≤ M)
    {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (E : ParabolicWeakDerivativeFamily d M V
      (fun z  ↦ F z.1 z.2))
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
      (fun z ↦
        D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j, a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j, b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
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
  let sharedTerm_3b19dc29b2 := ((by omega : 2 ≤ M + 1))
  classical
  let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ

  have hθCompact : HasCompactSupport θ :=
    hφCompact.of_isClosed_subset isClosed_closure
      (coordinateIteratedFDeriv_tsupport_subset beta.1 φ)
  have hθLp : ParabolicMemLpOn V 2 θ :=
    ((coordinateIteratedFDeriv_contDiff beta.1 φ hφ).continuous.memLp_of_hasCompactSupport hθCompact).restrict V
  let zeroM1  :=
    ParabolicDerivativeIndex.zero d (M + 1)
  let zeroM  := ParabolicDerivativeIndex.zero d M
  have haLp (i j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityTwo j i)) z) := by
    apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _ (Ba i j zeroM1) (hBa i j zeroM1)
    · exact (ha i j).continuousOn
    · intro z hz
      simpa [zeroM1, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        haBound i j zeroM1 z hz
    · exact D.memLp _
  have hbLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityOne j)) z) := by
    apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _ (Bb j zeroM) (hBb j zeroM)
    · exact (hb j).continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hbBound j zeroM z hz
    · exact D.memLp _

  have htInt : Integrable (fun z ↦ D.representative
      (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
        (ParabolicDerivativeIndex.timeOne d)) z * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using
      (D.memLp (ParabolicDerivativeIndex.castLE
        sharedTerm_3b19dc29b2
        (ParabolicDerivativeIndex.timeOne d))).integrable_mul hθLp
  have haInt (i j : Fin d) := (haLp i j).integrable_mul hθLp
  have hbInt (j : Fin d) := (hbLp j).integrable_mul hθLp
  have haInt' (i j : Fin d) : Integrable (fun z ↦
      a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityTwo j i)) z * θ z)
      (timeVelocityVolumeOn V) := by
    exact haInt i j
  have hbInt' (j : Fin d) : Integrable (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityOne j)) z * θ z)
      (timeVelocityVolumeOn V) := by
    exact hbInt j

  have haSumInt : Integrable (fun z ↦
      (∑ i, ∑ j, a z.1 z.2 i j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityTwo j i)) z) * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun i _ ↦
        integrable_finset_sum Finset.univ (fun j _ ↦ haInt' i j))
  have hbSumInt : Integrable (fun z ↦
      (∑ j, b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
          (ParabolicDerivativeIndex.velocityOne j)) z) * θ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Finset.sum_mul] using
      integrable_finset_sum Finset.univ (fun j _ ↦ hbInt' j)



  have hraw := integral_congr_ae (show (fun z ↦
      (D.representative
            (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
              (ParabolicDerivativeIndex.timeOne d)) z +
        (∑ i, ∑ j, a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
            (ParabolicDerivativeIndex.velocityTwo j i)) z) +
        (∑ j, b z.1 z.2 j * D.representative
          (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
            (ParabolicDerivativeIndex.velocityOne j)) z) +
        c z.1 z.2 * D.representative
          (ParabolicDerivativeIndex.castLE sharedTerm_3b19dc29b2
            (ParabolicDerivativeIndex.zeroTwo d)) z) * θ z) =ᵐ[
      timeVelocityVolumeOn V] fun z ↦ F z.1 z.2 * θ z by
      filter_upwards [hEq] with z hz
      rw [hz])
  simp only [add_mul] at hraw
  rw [integral_add, integral_add, integral_add] at hraw
  · simp only [Finset.sum_mul] at hraw
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ (fun j _ ↦ haInt' i j))] at hraw
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ haInt' _ j)] at hraw
    rw [integral_finset_sum Finset.univ (fun j _ ↦ hbInt' j)] at hraw
    dsimp only [θ] at hraw ⊢
    exact hraw
  · exact htInt
  · exact haSumInt
  · exact htInt.add haSumInt
  · exact hbSumInt
  · exact (htInt.add haSumInt).add hbSumInt
  · exact ((MemLp.integrable_mul (by
      apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _ (Bc zeroM) (hBc zeroM)
      · exact hc.continuousOn
      · intro z hz
        simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
          hcBound zeroM z hz
      · exact D.memLp _) hθLp))


private alias principalComponent_pairing_explicit := _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.principalComponent_pairing

private theorem principalComponents_pairing_explicit
    {d M : ℕ} {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (a : CoefficientField d)
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d ↦ a z.1 z.2 i j) V)
    (Ba : Fin d → Fin d → ParabolicDerivativeIndex d (M + 1) → ℝ)
    (hBa : ∀ i j alpha, 0 ≤ Ba i j alpha)
    (haBound : ∀ i j alpha z, z ∈ V →
      |TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1
        (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z| ≤ Ba i j alpha)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hM : 1 ≤ M) (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    (∑ i, ∑ j,
        (-(∫ z in V,
            a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      bound)) z *
              velocityGradient φ z i
            ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
          ∫ z in V,
            TimeVelocityMultiIndex.coordinateIteratedFDeriv
                  (Pi.single (velocityCoord i) 1)
                  (fun x  ↦ a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.velocitySucc
                    (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                    (by
                      bound)) z *
              φ z
            ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) =
      ((-1 : ℝ) ^ beta.1.order) *
        (∑ i, ∑ j, ∫ z in V,
          (a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      (∑ i, ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x  ↦ a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) := by
  classical
  have hcomponent (i j : Fin d) := principalComponent_pairing_explicit hV
    (fun z  ↦ a z.1 z.2 i j) (ha i j) (Ba i j)
    (hBa i j) (haBound i j) hM D beta j i φ hφ hφCompact hφV
  calc
    _ = ∑ i, ∑ j,
        (((-1 : ℝ) ^ beta.1.order) *
            ∫ z in V,
              (a z.1 z.2 i j *
                D.representative
                  (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                    (ParabolicDerivativeIndex.velocityTwo j i)) z) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z
              ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) -
          ∫ z in V,
            (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
              if hproper : gamma.left ≠ 0 then
                (beta.1.choose gamma.left : ℝ) *
                  TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                    (fun x  ↦ a x.1 x.2 i j) z *
                  D.representative
                    (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                      beta gamma hproper j i) z
              else 0) * φ z
            ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hcomponent i j
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]

private theorem integral_genericPreliftDifferentiatedScalarEquationOn
    {d M : ℕ} (hM : 1 ≤ M)
    {V : HypoellipticAleksandrov.Parabolic.Region d} (hV : IsOpen V)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d (M + 1) V u)
    (E : ParabolicWeakDerivativeFamily d M V
      (fun z  ↦ F z.1 z.2))
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
      (fun z ↦
        D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j, a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j, b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 * D.representative
            (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn V] fun z ↦ F z.1 z.2)
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    -(∫ z in V,
        D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          timeDerivative φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      (∑ i, ∑ j, ∫ z in V,
        a z.1 z.2 i j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z *
          velocityGradient φ z i ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      (∑ i, ∑ j, ∫ z in V,
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (Pi.single (velocityCoord i) 1)
              (fun x  ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z *
          φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) +
      (∑ j, ∫ z in V,
        b z.1 z.2 j *
            D.representative
              (ParabolicDerivativeIndex.velocitySucc
                (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
                (by
                  bound)) z *
          φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) +
      (∫ z in V, c z.1 z.2 *
          D.representative
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) z *
          φ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in V,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_6d161793a7 := ((by omega : 2 ≤ M + 1))
  let sharedTerm_c9cad725b3 := ((ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta))
  let sharedTerm_1d7cff950d := ((by
    change beta.1.parabolicWeight + 1 ≤ M + 1
    omega))
  let sharedTerm_4576f3c2c7 := ((-1 : ℝ) ^ beta.1.order)
  classical
  let s : ℝ := sharedTerm_4576f3c2c7
  let A  := fun z ↦
    ∑ i, ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocityTwo
              beta gamma hproper j i) z
      else 0
  let B  := fun z ↦
    ∑ j, ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightVelocity
              beta gamma hproper j) z
      else 0
  let C  := fun z ↦
    ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
      if hproper : gamma.left ≠ 0 then
        (beta.1.choose gamma.left : ℝ) *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
            (fun x : TimeVelocity d ↦ c x.1 x.2) z *
          D.representative
            (ParabolicDerivativeIndex.properSplitRightValue
              beta gamma hproper) z
      else 0
  have hproperLp := properCommutatorComponents_memLp hV a b c D Ba Bb Bc
    hBa hBb hBc ha hb hc haBound hbBound hcBound beta
  have hφLp : ParabolicMemLpOn V 2 φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict V
  have hAInt : Integrable (fun z ↦ A z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [A, Pi.mul_def] using hproperLp.1.integrable_mul hφLp
  have hBInt : Integrable (fun z ↦ B z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [B, Pi.mul_def] using hproperLp.2.1.integrable_mul hφLp
  have hCInt : Integrable (fun z ↦ C z * φ z) (timeVelocityVolumeOn V) := by
    simpa only [C, Pi.mul_def] using hproperLp.2.2.integrable_mul hφLp
  have hEInt : Integrable (fun z ↦ E.representative beta z * φ z)
      (timeVelocityVolumeOn V) := by
    simpa only [Pi.mul_def] using (E.memLp beta).integrable_mul hφLp
  have horiginal := originalEquation_integral hM hV a b c F D E Ba Bb Bc
    hBa hBb hBc ha hb hc haBound hbBound hcBound hEq beta φ hφ hφCompact
  have htime := GenericPreLiftDifferentiatedWeakEquationSupport.timeComponent_pairing
    D sharedTerm_6d161793a7 beta φ hφ hφCompact hφV
  have hprincipal := principalComponents_pairing_explicit hV a ha Ba hBa haBound
    hM D beta φ hφ hφCompact hφV
  have hsource := GenericPreLiftDifferentiatedWeakEquationSupport.sourceComponent_pairing
    E beta φ hφ hφCompact hφV
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
  have hAijLp (i j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ a x.1 x.2 i j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                beta gamma hproper j i) z
        else 0) := by
    exact memLp_finset_sum Finset.univ fun gamma _ ↦
      properAtom_memLp hV _ (ha i j)
        (Ba i j) (hBa i j) (haBound i j) (Nat.le_succ M) beta gamma
        _ (fun hproper ↦ D.memLp _)
  have hBjLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      ∑ gamma : TimeVelocityMultiIndex.Split beta.1,
        if hproper : gamma.left ≠ 0 then
          (beta.1.choose gamma.left : ℝ) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
              (fun x : TimeVelocity d ↦ b x.1 x.2 j) z *
            D.representative
              (ParabolicDerivativeIndex.properSplitRightVelocity
                beta gamma hproper j) z
        else 0) := memLp_finset_sum Finset.univ fun gamma _ ↦
      properAtom_memLp hV _ (hb j)
        (Bb j) (hBb j) (hbBound j) (le_refl M) beta gamma
        _ (fun hproper ↦ D.memLp _)
  let zeroM  := ParabolicDerivativeIndex.zero d M
  have hbRootLp (j : Fin d) : ParabolicMemLpOn V 2 (fun z ↦
      b z.1 z.2 j * D.representative
        (ParabolicDerivativeIndex.velocitySucc
          sharedTerm_c9cad725b3 j
          sharedTerm_1d7cff950d) z) := by
    apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _ (Bb j zeroM) (hBb j zeroM)
    · exact (hb j).continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hbBound j zeroM z hz
    · exact D.memLp _
  have hcRootLp : ParabolicMemLpOn V 2 (fun z ↦
      c z.1 z.2 * D.representative
        sharedTerm_c9cad725b3 z) := by
    apply _root_.HypoellipticAleksandrov.Parabolic.GenericPreLiftDifferentiatedWeakEquationSupport.continuousOn_bounded_mul_memLp hV _ _ (Bc zeroM) (hBc zeroM)
    · exact hc.continuousOn
    · intro z hz
      simpa [zeroM, TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero] using
        hcBound zeroM z hz
    · exact D.memLp _
  have hdrift' (j : Fin d) :
      (∫ z in V, b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.velocitySucc
              sharedTerm_c9cad725b3 j
              sharedTerm_1d7cff950d) z * φ z ∂volume) +
        (∫ z in V,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z ∂volume) =
        (sharedTerm_4576f3c2c7) *
          ∫ z in V, (b z.1 z.2 j * D.representative
            (ParabolicDerivativeIndex.castLE sharedTerm_6d161793a7
              (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    have h := hdrift j
    simp only [add_mul] at h
    rw [integral_add] at h
    · exact h
    · simpa only [Pi.mul_def] using (hbRootLp j).integrable_mul hφLp
    · simpa only [Pi.mul_def] using (hBjLp j).integrable_mul hφLp
  have hdriftSum :
      (∑ j, ((∫ z in V, b z.1 z.2 j *
          D.representative
            (ParabolicDerivativeIndex.velocitySucc
              sharedTerm_c9cad725b3 j
              sharedTerm_1d7cff950d) z * φ z ∂volume) +
        ∫ z in V,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z ∂volume)) =
        ∑ j, (sharedTerm_4576f3c2c7) *
          ∫ z in V, (b z.1 z.2 j * D.representative
            (ParabolicDerivativeIndex.castLE sharedTerm_6d161793a7
              (ParabolicDerivativeIndex.velocityOne j)) z) *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    exact Finset.sum_congr rfl fun j _ ↦ hdrift' j
  have hzero' := hzero
  simp only [add_mul] at hzero'


  rw [integral_add (by
      simpa only [Pi.mul_def] using hcRootLp.integrable_mul hφLp) (hCInt)] at hzero'
  have hAExpand : (∫ z in V, A z * φ z ∂volume) =
      ∑ i, ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x  ↦ a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                  beta gamma hproper j i) z
          else 0) * φ z ∂volume := by
    calc
      _ = ∫ z in V, ∑ i, ∑ j,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ a x.1 x.2 i j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocityTwo
                    beta gamma hproper j i) z
            else 0) * φ z ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp only [A]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
      _ = _ := by
        rw [integral_finset_sum Finset.univ (fun i _ ↦
          integrable_finset_sum Finset.univ fun j _ ↦ by exact (MemLp.integrable_mul (hAijLp i j) hφLp))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finset_sum Finset.univ (fun j _ ↦ by exact (MemLp.integrable_mul (hAijLp i j) hφLp))]
  have hBExpand : (∫ z in V, B z * φ z ∂volume) =
      ∑ j, ∫ z in V,
        (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
          if hproper : gamma.left ≠ 0 then
            (beta.1.choose gamma.left : ℝ) *
              TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                (fun x  ↦ b x.1 x.2 j) z *
              D.representative
                (ParabolicDerivativeIndex.properSplitRightVelocity
                  beta gamma hproper j) z
          else 0) * φ z ∂volume := by
    calc
      _ = ∫ z in V, ∑ j,
          (∑ gamma : TimeVelocityMultiIndex.Split beta.1,
            if hproper : gamma.left ≠ 0 then
              (beta.1.choose gamma.left : ℝ) *
                TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.left
                  (fun x  ↦ b x.1 x.2 j) z *
                D.representative
                  (ParabolicDerivativeIndex.properSplitRightVelocity
                    beta gamma hproper j) z
            else 0) * φ z ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with z
          dsimp only [B]
          rw [Finset.sum_mul]
      _ = _ := by
        rw [integral_finset_sum Finset.univ (fun j _ ↦ by exact (MemLp.integrable_mul (hBjLp j) hφLp))]
  have hresidual :
      (∫ z in V,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z * φ z
        ∂volume) =
      (∫ z in V, E.representative beta z * φ z ∂volume) -
        (∫ z in V, A z * φ z ∂volume) -
        (∫ z in V, B z * φ z ∂volume) -
        (∫ z in V, C z * φ z ∂volume) := by
    unfold properDifferentiatedScalarCommutatorResidual
    change (∫ z in V, (((E.representative beta z - A z) - B z) - C z) * φ z
      ∂volume) = _
    simp only [sub_mul]
    change (∫ z, ((((fun z ↦ E.representative beta z * φ z) -
      (fun z ↦ A z * φ z)) - (fun z ↦ B z * φ z)) -
      (fun z ↦ C z * φ z)) z ∂(timeVelocityVolumeOn V)) = _
    simp only [Pi.sub_apply]
    rw [integral_sub, integral_sub, integral_sub] <;>
      first | exact hEInt | exact hAInt | exact hBInt | exact hCInt |
        exact hEInt.sub hAInt | exact (hEInt.sub hAInt).sub hBInt
  have hzeroRootEq :
      (∫ z in V, (c z.1 z.2 * u z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume) =
      ∫ z in V, (c z.1 z.2 * D.representative
        (ParabolicDerivativeIndex.castLE sharedTerm_6d161793a7
          (ParabolicDerivativeIndex.zeroTwo d)) z) *
        TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1 φ z ∂volume := by
    apply integral_congr_ae
    filter_upwards [D.zero_ae] with z hz
    have hindex : ParabolicDerivativeIndex.castLE sharedTerm_6d161793a7
        (ParabolicDerivativeIndex.zeroTwo d) =
        ParabolicDerivativeIndex.zero d (M + 1) := by
      apply Subtype.ext
      rfl
    rw [hindex, hz]
  rw [hresidual, hAExpand, hBExpand]
  rw [hzeroRootEq] at hzero'
  simp only [Finset.sum_add_distrib] at hdriftSum
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hprincipal
  rw [← Finset.mul_sum] at hdriftSum
  have htime' := congrArg (fun x  ↦ s * x) htime
  change s * _ = s * _ at htime'
  rw [← mul_assoc, hsquare, one_mul] at htime'
  dsimp only [s] at htime hprincipal hsource hdriftSum hzero' hsquare ⊢
  linear_combination
    (sharedTerm_4576f3c2c7) * horiginal - htime' + hprincipal +
      hdriftSum + hzero' - hsource

/-- The differentiated scalar equation tested before the next spatial lift.
The principal second-order term is integrated once in its first velocity
coordinate, retaining both the coefficient and coefficient-derivative terms. -/
theorem integral_genericPreliftDifferentiatedScalarEquation
    {d M : ℕ}
    (hM : 1 ≤ M)
    (U : HypoellipticAleksandrov.Parabolic.Region d) (hU : IsOpen U)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (D : ParabolicWeakDerivativeFamily d (M + 1) U u)
    (E : ParabolicWeakDerivativeFamily d M U
      (fun z  => F z.1 z.2))
    (ha : ∀ i j, ContDiffOn ℝ (M + 1)
      (fun z : TimeVelocity d => a z.1 z.2 i j) U)
    (hb : ∀ j, ContDiffOn ℝ M
      (fun z : TimeVelocity d => b z.1 z.2 j) U)
    (hc : ContDiffOn ℝ M
      (fun z : TimeVelocity d => c z.1 z.2) U)
    (hEq :
      (fun z =>
        D.representative
            (ParabolicDerivativeIndex.castLE
              (by omega : 2 ≤ M + 1)
              (ParabolicDerivativeIndex.timeOne d)) z +
          (∑ i, ∑ j,
            a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityTwo j i)) z) +
          (∑ j,
            b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.castLE
                  (by omega : 2 ≤ M + 1)
                  (ParabolicDerivativeIndex.velocityOne j)) z) +
          c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE
                (by omega : 2 ≤ M + 1)
                (ParabolicDerivativeIndex.zeroTwo d)) z)
        =ᵐ[timeVelocityVolumeOn U]
      (fun z => F z.1 z.2))
    (beta : ParabolicDerivativeIndex d M)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hφSmooth : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ U) :
    -(∫ z in U,
        D.representative
            (ParabolicDerivativeIndex.castLE
              (Nat.le_succ M) beta) z *
          timeDerivative φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      (∑ i, ∑ j,
        ∫ z in U,
          a z.1 z.2 i j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    bound)) z *
            velocityGradient φ z i
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) -
      (∑ i, ∑ j,
        ∫ z in U,
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
                (Pi.single (velocityCoord i) 1)
                (fun x  => a x.1 x.2 i j) z *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    bound)) z *
            φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) +
      (∑ j,
        ∫ z in U,
          b z.1 z.2 j *
              D.representative
                (ParabolicDerivativeIndex.velocitySucc
                  (ParabolicDerivativeIndex.castLE
                    (Nat.le_succ M) beta) j
                  (by
                    bound)) z *
            φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) +
      (∫ z in U,
        c z.1 z.2 *
            D.representative
              (ParabolicDerivativeIndex.castLE
                (Nat.le_succ M) beta) z *
          φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in U,
        properDifferentiatedScalarCommutatorResidual a b c D E beta z *
          φ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let sharedTerm_0a49a1053d := ((by change beta.1.parabolicWeight + 1 ≤ M + 1; omega))
  classical
  obtain ⟨V, Ba, Bb, Bc, hV, hφV, hclosureVU, _hVCompact,
      hBa, hBb, hBc, haBoundClosure, hbBoundClosure, hcBoundClosure⟩ :=
    GenericPreLiftDifferentiatedWeakEquationSupport.exists_precompactOpen_coefficient_majorants
      hU hφCompact hφSupport a b c ha hb hc
  have hVU : V ⊆ U := subset_closure.trans hclosureVU
  let DV := D.restrict hVU
  let EV := E.restrict hVU







  have hlocal := integral_genericPreliftDifferentiatedScalarEquationOn hM hV
    a b c F DV EV Ba Bb Bc hBa hBb hBc (fun i j ↦ (ha i j).mono hVU) (fun j ↦ (hb j).mono hVU) (hc.mono hVU) (fun i j alpha z hz ↦ haBoundClosure i j alpha z (subset_closure hz)) (fun j alpha z hz ↦ hbBoundClosure j alpha z (subset_closure hz)) (fun alpha z hz ↦ hcBoundClosure alpha z (subset_closure hz))
    ((ae_restrict_of_ae_restrict_of_subset hVU hEq))
    beta φ hφSmooth hφCompact hφV


  have hprincipal (i j : Fin d) :
      (∫ z in U, (a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            sharedTerm_0a49a1053d) z) *
          velocityGradient φ z i ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        ∫ z in V, (a z.1 z.2 i j * D.representative
          (ParabolicDerivativeIndex.velocitySucc
            (ParabolicDerivativeIndex.castLE (Nat.le_succ M) beta) j
            sharedTerm_0a49a1053d) z) *
          velocityGradient φ z i ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _
      ((velocityGradient_tsupport_subset φ hφSmooth i).trans hφV)
  have hphiMul (f : HypoellipticAleksandrov.Parabolic.ScalarField d)  :=
    setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU f φ hφV
  simpa only [DV, EV, ParabolicWeakDerivativeFamily.restrict_representative,
    (setIntegral_mul_eq_of_tsupport_subset hU.measurableSet hVU _ _ ((timeDerivative_tsupport_subset φ hφSmooth).trans hφV)), hprincipal, hphiMul, properDifferentiatedScalarCommutatorResidual] using hlocal

end HypoellipticAleksandrov.Parabolic
