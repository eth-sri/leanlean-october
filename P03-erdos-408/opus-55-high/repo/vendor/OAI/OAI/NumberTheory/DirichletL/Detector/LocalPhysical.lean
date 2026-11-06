module

public import OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
public import OAI.NumberTheory.DirichletL.Detector.ScalarTable

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss ConcretePrimeRowBridge CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ConcreteTraceCRT

lemma outerQuotient_prime_power (p : ActualEisensteinCubic.O) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (k : ℕ) (hk : k≠0) (d : ActualEisensteinCubic.O ⧸ Ideal.span {p^k}) :
    outerQuotient (p^k) d =
      (actualSextic (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

lemma sexticGauss_prime_power (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (n : ℕ) (H : ActualEisensteinCubic.O) :
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
  ring

theorem bareCongruenceCoefficient_prime_power_pos (p : ActualEisensteinCubic.O) (hp : Prime p)
    [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (n k j : ℕ) (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, ite_eq_right hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  simp

lemma sexticGauss_one (H : ActualEisensteinCubic.O) : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) := by
    simp
  let : Unique (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) := uniqueOfSubsingleton 0
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have hrow (d : ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) :
      idealRowHom (representative 1 d) (Ideal.span {(1:ActualEisensteinCubic.O)})=1 := by
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  simp only [hrow, one_mul]
  have ht (d : ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) :
      quotientTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  simp_all

lemma barePhysicalFourier_outer_one (A : ActualEisensteinCubic.O) (hA : A≠0) (H : ActualEisensteinCubic.O) :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (by grind) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one (A : ActualEisensteinCubic.O) (hA : A≠0) (H : ActualEisensteinCubic.O) :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  rw [barePhysicalFourier_outer_one] at he
  simp_all

theorem bareCongruenceCoefficient_prime_power (p : ActualEisensteinCubic.O) (hp : Prime p)
    [(Ideal.span {p}:Ideal ActualEisensteinCubic.O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (n k j : ℕ) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · subst k
    rw [pow_zero, bareCongruenceCoefficient_outer_one, sexticGauss_prime_power p hp hg,
      positiveScalar_kzero]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one (s : ActualEisensteinCubic.O) (hs : s≠0) (H : ActualEisensteinCubic.O) :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finite_quotient_span hs
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : ActualEisensteinCubic.O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : ActualEisensteinCubic.O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_all

end SevenEighths.ProbePhysical
end

end OAI
