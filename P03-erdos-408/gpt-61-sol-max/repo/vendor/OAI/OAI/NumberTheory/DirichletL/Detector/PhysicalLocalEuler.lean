module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
public import OAI.NumberTheory.DirichletL.Detector.SourceLocal

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal


lemma outerQuotient_mk  s H  :
    outerQuotient s (Ideal.Quotient.mk _ H)=idealRowHom H (Ideal.span {s}) := by
  unfold outerQuotient
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

theorem bareCongruenceCoefficient_all_prime_powers  p   hp 
    [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal] (hg : goodLambda∉Ideal.span {p})  t k j  :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [ite_eq_left rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [ite_eq_right hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    rfl

end SevenEighths.ProbePhysical


end OAI
