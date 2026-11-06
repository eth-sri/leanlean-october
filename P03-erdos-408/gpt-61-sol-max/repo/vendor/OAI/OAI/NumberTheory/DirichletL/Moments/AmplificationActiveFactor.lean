module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy
public import OAI.NumberTheory.DirichletL.Moments.AmplificationSourcePool

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow


def errorMovingExponent (n : ℕ)  := if n=5 then 0 else 1

section
variable (p u : ActualEisensteinCubic.O) (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u})) (hcop : IsCoprime p u)
include p u hp hu hcop

theorem residual_six_unit  
       
      : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  grind

theorem residual_seven_unit  
       
      : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  grind

theorem error_residual_factor  
       
       n  (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

end

section
variable (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p)
include S p hp

theorem residualColumns_coprime      
    (k : ℕ)  I  (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active      
    (hs : Supported (Ideal.span {p}))  n  (hn : n=0 ∨ n=5 ∨ n=6)
     I  (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end OAI
