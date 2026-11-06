module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentAmplificationSourceDomain
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal
open CenteredMomentAmplificationAllocation
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow

def residualIdeal (p : ActualEisensteinCubic.O) (hp : Prime p) (I : Ideal ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O :=
  if hI : Supported I then Ideal.span {(primeRemainder p hp (primaryGenerator I)
    (supported_primaryGenerator_ne_zero I hI))} else 0

theorem residualIdeal_supported (p : ActualEisensteinCubic.O) (hp : Prime p) (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    Supported (residualIdeal p hp I) := by
  rw [residualIdeal,dite_eq_left hI]
  exact primeRemainder_supported p hp (primaryGenerator I)
    (by rw [primary_span_supported I hI];omega)

theorem residualIdeal_generator (p : ActualEisensteinCubic.O) (hp : Prime p) (hpp : goodLambda^2 ∣ p-1)
    (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    primaryGenerator (residualIdeal p hp I) =
      primeRemainder p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI) := by
  rw [residualIdeal,dite_eq_left hI]
  apply primaryGenerator_span
  · apply supported_element_ne_zero
    simpa only [residualIdeal,dite_eq_left hI] using residualIdeal_supported p hp I hI
  · exact primeRemainder_primary p hp hpp (primaryGenerator I)
      (by rw [primary_span_supported I hI];omega)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).2

theorem residualIdeal_reconstruct (p : ActualEisensteinCubic.O) (hp : Prime p) (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    (Ideal.span {p})^(multiplicity p (primaryGenerator I))*residualIdeal p hp I=I := by
  rw [residualIdeal,dite_eq_left hI,Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton,
    ← (primeRemainder_spec p hp (primaryGenerator I) (supported_primaryGenerator_ne_zero I hI)).1]
  exact primary_span_supported I hI

def valuationColumns (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (k : ℕ) : Finset (Ideal ActualEisensteinCubic.O) :=
  (supportedColumns S).filter (fun I => multiplicity p (primaryGenerator I)=k)

def residualColumns (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ) : Finset (Ideal ActualEisensteinCubic.O) :=
  (valuationColumns S p k).image (residualIdeal p hp)

theorem valuationColumns_supported (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (k : ℕ)
    (I : Ideal ActualEisensteinCubic.O) (hI : I∈valuationColumns S p k) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem residualIdeal_injOn (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ) :
    Set.InjOn (residualIdeal p hp) (valuationColumns S p k) := by
  intro I hI J hJ he
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  have hj := residualIdeal_reconstruct p hp J (valuationColumns_supported S p k J hJ)
  rw [(Finset.mem_filter.mp hI).2] at hi
  rw [(Finset.mem_filter.mp hJ).2] at hj
  simp_all

theorem residualColumns_supported (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ)
    (I : Ideal ActualEisensteinCubic.O) (hI : I∈residualColumns S p hp k) : Supported I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_supported p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_sum (S : Finset (Ideal ActualEisensteinCubic.O)) (p : ActualEisensteinCubic.O) (hp : Prime p) (k : ℕ)
    (c f : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑ I∈valuationColumns S p k,c I*f (residualIdeal p hp I))=
      ∑ I∈residualColumns S p hp k,c ((Ideal.span {p})^k*I)*f I := by
  rw [residualColumns,Finset.sum_image (residualIdeal_injOn S p hp k)]
  apply Finset.sum_congr rfl
  intro I hI
  have hi := residualIdeal_reconstruct p hp I (valuationColumns_supported S p k I hI)
  rw [(Finset.mem_filter.mp hI).2] at hi
  simp_all

end SevenEighths.CenteredMomentAmplificationSourceDomain

end

end OAI
