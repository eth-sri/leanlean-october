module
public import OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

section
variable (S : Finset (Ideal O)) (D : ℕ)
include S D
theorem outsideSquarefree_admissible
    (hbad : fixedBadPrimes ⊆ S) : ∀ I ∈ outsideSquarefreeIdeals S D, Admissible I := by
  pm_161 I hI ho hs Finset.mem_filter.mp
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  refine ⟨hn,hs,?_⟩
  intro P hP
  obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  pm_3439
  intro hPb
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P (hbad hPb) hd

theorem outside_pool_product_not_dvd
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

theorem selectedIdealTest_outside
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
end

end InitialMeanSquare

end

end OAI
