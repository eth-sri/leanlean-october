module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Descent.Completion
public import OAI.NumberTheory.DirichletL.Descent.Poisson

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand



theorem completed_summand_primary_support (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (X : ℝ)  I J  (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    simp_all [summand, columnWeight, squarefreeGaussCoefficient]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  exact mul_ne_zero hI (pow_ne_zero _ hJ)

theorem markedCompletedT_congr_primary  Ψ   W   X 
     d e  (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  · simp only [hz, zero_mul]
  solve_by_elim [completed_summand_primary_support]

theorem finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ)  h  :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]


end SevenEighths.InverseMoment

end OAI
