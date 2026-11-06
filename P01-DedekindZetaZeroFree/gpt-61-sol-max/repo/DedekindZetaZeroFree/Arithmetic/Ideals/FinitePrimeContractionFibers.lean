module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.LargeSieve.IdealEuler

open scoped NumberField Classical
open IsDedekindDomain

variable {F E : Type} [Field F] [Field E] [NumberField F] [NumberField E]
    [Algebra F E]

theorem under_eq_iff_liesOver (Q : HeightOneSpectrum (𝓞 E))
    (p : HeightOneSpectrum (𝓞 F)) :
    Q.under (𝓞 F) = p ↔ Q.asIdeal.LiesOver p.asIdeal := by
  simp_all [Ideal.liesOver_iff, IsDedekindDomain.HeightOneSpectrum.under_asIdeal] <;> aesop

theorem finite_prime_liesOver (p : HeightOneSpectrum (𝓞 F)) :
    Finite {Q : HeightOneSpectrum (𝓞 E) // Q.asIdeal.LiesOver p.asIdeal} := by
  haveI  := p.isMaximal
  let f : {Q : HeightOneSpectrum (𝓞 E) // Q.asIdeal.LiesOver p.asIdeal} →
      p.asIdeal.primesOver (𝓞 E) :=
    fun Q => ⟨Q.1.asIdeal, Q.1.isPrime, Q.2⟩
  have hf : Function.Injective f := by
    intro Q1 Q2 h
    have h2 : Q1.1.asIdeal = Q2.1.asIdeal := congrArg Subtype.val h
    apply Subtype.ext <;> aesop
  exact Finite.of_injective f hf

theorem finite_prime_under_fiber (p : HeightOneSpectrum (𝓞 F)) :
    Finite {Q : HeightOneSpectrum (𝓞 E) // Q.under (𝓞 F) = p} := by
  haveI := finite_prime_liesOver (F := F) (E := E) p
  exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun Q => (under_eq_iff_liesOver Q p)).symm

end DedekindZetaZeroFree.LargeSieve.IdealEuler
