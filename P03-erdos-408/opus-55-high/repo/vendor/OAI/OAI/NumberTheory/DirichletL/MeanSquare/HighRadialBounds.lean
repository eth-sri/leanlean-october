module

public import OAI.NumberTheory.DirichletL.MeanSquare.DiagonalDensity

@[expose] public section

namespace OAI

noncomputable section

namespace InitialMeanSquare

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open Filter
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open Filter Asymptotics MeasureTheory
open MeasureTheory Real
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Set
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical

section

open scoped Classical
open CanonicalQuadraticSieve (Admissible)

end

section

open scoped Classical

end

section

open scoped Classical

section

end

open ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
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

section

open scoped Classical

section
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open scoped Classical
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end InitialMeanSquare

end

end OAI
