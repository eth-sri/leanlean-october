module

public import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
public import OAI.NumberTheory.DirichletL.Detector.Sextic
public import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
public import OAI.NumberTheory.DirichletL.Moments.Unequal

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentAmplification
open CompletedGauss
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal

theorem gauss_prime_power_one (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) 1 =
      if n = 0 then primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg]
  have ht := actualSextic_primePowerGauss_at_pow p hp hg hc (n+1) n 0
  simp only [pow_zero] at ht
  rw [ht]
  by_cases hn : n = 0
  · simp_all
  grind

theorem gauss_prime_power_six (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^6) =
      if n = 5 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^5 *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1)
      else if n = 6 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^6 *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg,actualSextic_primePowerGauss_at_pow p hp hg hc]
  have h6 :=
    (actualSextic_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl
  by_cases hn5 : n = 5
  · subst n
    grind
  · by_cases hn6 : n = 6
    · subst n
      simp only [hn5, show ¬6 ∣ 6+1 by decide, ite_false, pow_succ (actualSextic (Ideal.span {p}) hg) 6, h6, one_mul]
    grind

theorem gauss_prime_power_unchanged (p : ActualEisensteinCubic.O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn0 : n ≠ 0) (hn5 : n ≠ 5) (hn6 : n ≠ 6) (h : ActualEisensteinCubic.O) (hph : ¬p ∣ h) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (h*p^6) =
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h := by
  have hcop : IsCoprime h (p^(n+1)) :=
    (hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right
  have hsp := supported_power p hs (n+1)
  rw [sexticGauss_unit_scale _ hsp h (p^6) hcop,
    ← mul_one h, sexticGauss_unit_scale _ hsp h 1 hcop,
    gauss_prime_power_six p hp hg hc,gauss_prime_power_one p hp hg hc]
  simp_all

theorem gauss_sixth_frequency (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a}))
    (p h : ActualEisensteinCubic.O) (hcop : IsCoprime p a) :
    sexticGauss a (supportedElement_ne_zero a ha) (p^6*h) =
      sexticGauss a (supportedElement_ne_zero a ha) h := by
  rw [sexticGauss_unit_scale a ha (p^6) h hcop.pow_left,
    supported_sixth_value a p ha hcop.symm,inv_one,one_mul]

end SevenEighths.CenteredMomentAmplification

end

end OAI
