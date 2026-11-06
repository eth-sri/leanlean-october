module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationSourceError
public import OAI.NumberTheory.DirichletL.Moments.SecondChildProfile
public import OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentAmplificationFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

def amplificationPhase (p : ActualEisensteinCubic.O) (k : ℕ) (r : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (ActualEisensteinCoordinates.residue p)
    (QuadraticGaussRay.residueQuotientFour r):ℂ)^k

theorem amplificationPhase_mk (p u : ActualEisensteinCubic.O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  simp only [amplificationPhase,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem amplificationPhase_norm (p : ActualEisensteinCubic.O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  unfold amplificationPhase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> cases k <;> simp

theorem amplificationPhase_expansion (p u : ActualEisensteinCubic.O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayCharacter χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he

theorem original_column_family (η : Character) (m p : ActualEisensteinCubic.O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal ActualEisensteinCubic.O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal ActualEisensteinCubic.O) (hI : Supported I) (β : Ideal ActualEisensteinCubic.O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];ring

end SevenEighths.CenteredMomentAmplificationFamily

end

end OAI
