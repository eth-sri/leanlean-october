module

public import OAI.NumberTheory.DirichletL.Detector.PhysicalMellinCoefficient
public import OAI.NumberTheory.DirichletL.Detector.RadialSpectral

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
open ProbeCompleted ProbeRow

lemma supported_of_source_exclusions (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hS : ∀P∈S,¬P∣I) : Supported I := by
  refine ⟨hI,?_⟩
  intro P hP
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hS P (hbad hb) (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)

lemma spectralSummand_support (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes⊆S)
    (D I J : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) :
    Squarefree I ∧ Supported I ∧ Supported J := by
  have hI : I≠0 := by
    intro hz
    subst I
    exact h (by simp [spectralSummand])
  have hJ : J≠0 := by
    intro hz
    subst J
    exact h (by simp [spectralSummand])
  have hsf : Squarefree I := by
    by_contra hn
    exact h (by simp [spectralSummand,columnWeight,squarefreeGaussCoefficient,hn])
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hex : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · simp_all
    · simp_all
  refine ⟨hsf,supported_of_source_exclusions S hbad I hI ?_,
    supported_of_source_exclusions S hbad J hJ ?_⟩
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_left hd _)
  · intro P hP hd
    exact hex P hP (dvd_mul_of_dvd_right (hd.trans (by simp)) _)

end SevenEighths.ProbePhysical
end

end OAI
