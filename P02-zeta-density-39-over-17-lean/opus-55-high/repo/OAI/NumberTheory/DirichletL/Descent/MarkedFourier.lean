module
public import OAI.NumberTheory.DirichletL.Descent.Completion
public import OAI.NumberTheory.DirichletL.Descent.Poisson

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section
variable (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
include Ψ W X
theorem completed_summand_primary_support (I J : Ideal Eis) (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    apply h
    simp [summand, columnWeight, squarefreeGaussCoefficient, hz]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  simp_all

theorem markedCompletedT_congr_primary
    (d e : Ideal Eis → ℂ) (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  grind
  · rw [h (I * J ^ 3) (completed_summand_primary_support Ψ W X I J hz)]
end

theorem finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

end
end SevenEighths.InverseMoment

end OAI
