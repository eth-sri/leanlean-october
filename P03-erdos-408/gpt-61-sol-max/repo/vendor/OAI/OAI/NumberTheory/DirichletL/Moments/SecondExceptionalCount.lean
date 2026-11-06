module

public import OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
public import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentSupport UniqueFactorizationMonoid
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow


lemma common_prime_dvd_left (C D:Ideal ActualEisensteinCubic.O) (P:CommonIndex C D) : P.val∣C :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

lemma common_prime_prime  C D  (hC:Supported C)  P  :
    Prime (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact prime_of_normalized_factor _ (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)

end SevenEighths.CenteredMomentSecondExceptionalCount



end OAI
