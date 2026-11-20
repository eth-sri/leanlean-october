module

public import OAI.IdealNorm
public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows

@[expose] public section

namespace OAI

noncomputable section

namespace InitialMeanSquare

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex
open scoped Classical
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding
open ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set



section



open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Ideal.one_le_absNorm_of_ne_bot (hQ.ne_zero)
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

end


open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [OAI.PrincipalFamily.Maximal p]
  (hcop : OAI.PrincipalFamily.Coprime p)
  (hg : OAI.PrincipalFamily.Avoids p lambda)
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end InitialMeanSquare

end

end OAI
