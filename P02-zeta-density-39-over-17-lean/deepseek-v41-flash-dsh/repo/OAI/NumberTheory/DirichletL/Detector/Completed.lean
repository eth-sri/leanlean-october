module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Detector.Phase

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3

def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0

def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))

theorem completedCorrection_eq_phase (I J : Ideal O) :
    completedCorrection I J = rayMask (completedIndex I J) *
      star (ProbePhase.G (completedIndex I J)) := rfl

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)

def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J

def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J

def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2

def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2

def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ

theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]

theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)

theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring

theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])

theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])

theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]

end SevenEighths.ProbeCompleted
end

end OAI
