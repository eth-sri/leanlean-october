module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.AmplificationSource

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationAllocation CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentLiveDomain


def residualIdeal (p : ActualEisensteinCubic.O) (hp : Prime p) (I : Ideal ActualEisensteinCubic.O)  :=
  if hI : Supported I then Ideal.span {(primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI))} else 0

section
variable (p : ActualEisensteinCubic.O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1) (I : Ideal ActualEisensteinCubic.O) (hI : Supported I)

include hI in
theorem residualIdeal_supported         :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];exact hI)

include hpp in
theorem residualIdeal_generator      
        :
    primaryGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) := by
  rw [residualIdeal,dite_eq_left hI]
  apply primaryGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dite_eq_left hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).2

include hI in
theorem residualIdeal_reconstruct         :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dite_eq_left hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

end

def valuationColumns (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (k : ℕ)  :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)

def residualColumns (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ)  :=
  (valuationColumns S p k).image (residualIdeal p hp)

section
variable (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ) (I : Ideal ActualEisensteinCubic.O)

theorem valuationColumns_supported      
      (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualIdeal_injOn         :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  simp_all

theorem residualColumns_supported        
      (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  solve_by_elim [residualIdeal_supported, valuationColumns_supported]

theorem residual_column_sum        
    (c f : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [hi]

end

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI
