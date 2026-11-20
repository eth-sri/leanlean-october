module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses

@[expose] public section

noncomputable section

open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.AbelianQuotient

variable (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)

theorem narrowModulus_support_iff (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ (narrowIdealModulus K m hm).finitePart.support ↔ m ≤ v.asIdeal := by
  rw [Finsupp.mem_support_iff, narrowIdealModulus_finitePart, Multiset.count_ne_zero,
    Ideal.mem_normalizedFactors_iff hm]
  exact ⟨fun h => h.2, fun h => ⟨v.isPrime, h⟩⟩

theorem mem_ideal_iff_narrow_primePowers (r : 𝓞 K) :
    r ∈ m ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (narrowIdealModulus K m hm).finitePart.support →
        r ∈ v.asIdeal ^ ((narrowIdealModulus K m hm).finitePart v) := by
  have hprime : ∀ P ∈ (normalizedFactors m).toFinset, Prime P := by
    intro P hP
    have hmem := Multiset.mem_toFinset.mp hP
    refine Ideal.prime_of_isPrime ?_ ((Ideal.mem_normalizedFactors_iff hm).mp hmem).1
    intro h
    refine hm (le_bot_iff.mp ?_)
    rw [h] at hmem
    exact ((Ideal.mem_normalizedFactors_iff hm).mp hmem).2
  have hinf :
      ∏ P ∈ (normalizedFactors m).toFinset,
        P ^ Multiset.count P (normalizedFactors m) =
      ((normalizedFactors m).toFinset.inf
        fun P => P ^ Multiset.count P (normalizedFactors m)) := by
    simpa using (IsDedekindDomain.inf_pow_eq_prod_of_prime
      (s := (normalizedFactors m).toFinset) (f := fun P => P)
      (e := fun P => Multiset.count P (normalizedFactors m)) hprime (fun _ _ _ _ hij => hij)).symm
  have key : ∀ r : 𝓞 K, r ∈ m ↔ ∀ P ∈ (normalizedFactors m).toFinset,
      r ∈ P ^ Multiset.count P (normalizedFactors m) := by
    intro r
    conv_lhs => rw [((Ideal.prod_normalizedFactors_eq_self hm).symm.trans ((Finset.prod_multiset_count (normalizedFactors m)).trans hinf))]
    rw [← Ideal.span_singleton_le_iff_mem, Finset.le_inf_iff]
    simp
  constructor
  · intro hr v hv
    simpa [narrowIdealModulus_finitePart] using (key r).mp hr v.asIdeal (Multiset.mem_toFinset.mpr (Multiset.count_ne_zero.mp (by
      exact Finsupp.mem_support_iff.mp hv)))
  · intro hr
    refine (key r).mpr fun P hP => ?_
    have hv : (HeightOneSpectrum.ofPrime (hprime P hP)) ∈
        (narrowIdealModulus K m hm).finitePart.support := by
      rw [Finsupp.mem_support_iff, narrowIdealModulus_finitePart, Multiset.count_ne_zero]
      exact (Multiset.mem_toFinset.mp hP)
    simpa [narrowIdealModulus_finitePart] using hr (HeightOneSpectrum.ofPrime (hprime P hP)) hv

end DedekindZetaZeroFree.AbelianQuotient

end
