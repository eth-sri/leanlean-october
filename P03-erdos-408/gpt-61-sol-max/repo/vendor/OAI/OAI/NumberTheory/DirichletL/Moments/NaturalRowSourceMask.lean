module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FixedRowMask
public import OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge


lemma support_prime (R P : Ideal HeckeFamily.O) (hP : P∈primeSupport R) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma coprime_support_iff  I R  (hR : R≠0) :
    (∀P∈primeSupport R,IsCoprime I P) ↔ IsCoprime I R := { mp := fun h => Eq.mpr (congrArg (IsCoprime I) (Eq.symm (Ideal.prod_normalizedFactors_eq_self hR))) (Multiset.induction_on (UniqueFactorizationMonoid.normalizedFactors R) (fun a => Eq.mpr (congrArg (IsCoprime I) Ideal.one_eq_top) (Eq.mp (congrArg (IsCoprime I) Ideal.one_eq_top) isCoprime_one_right)) (fun a s ih hs => Eq.mpr (congrArg (IsCoprime I) (Multiset.prod_cons a s)) (IsCoprime.mul_right (hs a (Multiset.mem_cons_self a s)) (ih fun P hP => hs P (Multiset.mem_cons_of_mem hP)))) fun P hP => h P (Multiset.mem_toFinset.mpr hP)), mpr := fun h P hP => IsCoprime.of_isCoprime_of_dvd_right h (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)) }

def excluded (χ : Character) (R : Ideal HeckeFamily.O)  :=
  χ.excludePrimes (primeSupport R) (support_prime R)

lemma excluded_ideal  χ   R  (hR : R≠0)  I  :
    idealCoeff (excluded χ R) I=if IsCoprime I R then idealCoeff χ I else 0 := by
  simp only [excluded,idealCoeff_excludePrimes,coprime_support_iff I R hR]

lemma excluded_element  χ  (hχ0 : elementCoeff χ 0=0)
     R  (hR : R≠0)  n  :
    elementCoeff (excluded χ R) n=
      if IsCoprime (Ideal.span {n}) R then elementCoeff χ n else 0 := by
  by_cases hn : n=0
  · subst n
    have hh : elementCoeff (excluded χ R) 0=0 := by
      rw [excluded,Character.excludePrimes,elementCoeff_refineModulus,hχ0]
      split_ifs <;> rfl
    rw [hh,hχ0]
    split_ifs <;> rfl
  · rw [←idealCoeff_span _ hn,excluded_ideal χ R hR,idealCoeff_span χ hn]

lemma excluded_element_generator  χ  (hχ0 : elementCoeff χ 0=0)
     R  (hR : R≠0)  n  :
    elementCoeff (excluded χ R) n=
      if IsCoprime n (idealGenerator R) then elementCoeff χ n else 0 := by
  rw [excluded_element χ hχ0 R hR]
  conv_lhs => rw [←span_idealGenerator R,Ideal.isCoprime_span_singleton_iff]

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
