module

public import OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics
open scoped ContDiff FourierTransform SchwartzMap BigOperators Classical
open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid

namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

theorem outsideSquarefree_admissible (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) : ∀ I ∈ outsideSquarefreeIdeals S D, Admissible I := by
  intro I hI
  obtain ⟨ho,hs⟩ := Finset.mem_filter.mp hI
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  refine ⟨hn,hs,?_⟩
  intro P hP
  obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hPb
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P (hbad hPb) hd

theorem outside_pool_product_not_dvd (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)

theorem selectedIdealTest_outside (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · rw [ite_eq_left]
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD

end InitialMeanSquare

end

end OAI
