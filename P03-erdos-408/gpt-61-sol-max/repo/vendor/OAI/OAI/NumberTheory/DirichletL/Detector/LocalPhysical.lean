module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
public import OAI.NumberTheory.DirichletL.Detector.ScalarTable

@[expose] public section

namespace OAI


open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

section
variable (p : O)
include p

lemma outerQuotient_prime_power   [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p})  k  (hk : k≠0)  d  :
    outerQuotient (p^k) d =
      (actualSextic (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

section
variable (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
include hp hg

lemma sexticGauss_prime_power      
       n   H  :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(n+1)) n H := by
  have he : sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) H =
      quotientFourier p (p^(n+1)) (pow_ne_zero _ hp.ne_zero)
        (actualSextic (Ideal.span {p}) hg^(n+1)) H := by
    unfold sexticGauss quotientFourier
    apply tsum_congr
    intro d
    have hc := outerQuotient_prime_power p hg (n+1) (by omega) d
    change idealRowHom (representative (p^(n+1)) d) (Ideal.span {p^(n+1)}) = _ at hc
    rw [hc]
    rw [(Ideal.Quotient.mk (Ideal.span {p^(n+1)})).map_mul, representative_spec]
  rw [he, primePowerGauss_eq_quotientFourier]
  apply quotientFourier_congr
  exact pow_succ' p n

theorem bareCongruenceCoefficient_prime_power_pos    
       
     n k j  (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, ite_eq_right hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  · ring

end

end

lemma sexticGauss_one  H  : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (O ⧸ Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  let : Unique (O ⧸ Ideal.span {(1:O)}) := uniqueOfSubsingleton 0
  let : Fintype (O ⧸ Ideal.span {(1:O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have hrow (d : O ⧸ Ideal.span {(1:O)}) :
      idealRowHom (representative 1 d) (Ideal.span {(1:O)})=1 := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  simp only [hrow, one_mul]
  have ht (d : O ⧸ Ideal.span {(1:O)}) :
      quotientTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  simp_all

section
variable (A : O) (hA : A≠0) (H : O)
include A hA H

lemma barePhysicalFourier_outer_one       :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (mul_ne_zero hA one_ne_zero) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one       :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  simp_all [barePhysicalFourier_outer_one]

end

theorem bareCongruenceCoefficient_prime_power (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})  n k j  :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · simp_all [bareCongruenceCoefficient_outer_one, sexticGauss_prime_power]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one  s  (hs : s≠0)  H  :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_all

end SevenEighths.ProbePhysical


end OAI
