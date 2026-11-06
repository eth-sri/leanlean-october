module

public import OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap


open MeasureTheory
namespace CanonicalRowCompletion

section
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

def rowFamilyEnergy (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

theorem rowFamilyEnergy_eq_sum (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) :
    rowFamilyEnergy labels P K =
      ∑ I ∈ labels, ∑ z ∈ (firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖eisEmbedding z‖^2/K)).re * ‖P I z‖^2 := by
  unfold rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_exact_disk _ K hK, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem rowFamilyEnergy_integral_polynomial
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0 < K)
    (b : ℝ → ℂ) (φ : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ I z, Integrable (fun t => b t*φ I z t))
    (hbound : ∀ t, rowFamilyEnergy labels (fun I z => φ I z t) K ≤ E*(1+|t|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ∫ t : ℝ, b t*φ I z t) K ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : ActualEisensteinCubic.O → ℝ := fun z => Real.sqrt ((rowMajorant (‖eisEmbedding z‖^2/K)).re)
  have hw (z : ActualEisensteinCubic.O) : 0 ≤ w z := Real.sqrt_nonneg _
  have hw2 (z : ActualEisensteinCubic.O) : (w z)^2 = (rowMajorant (‖eisEmbedding z‖^2/K)).re :=
    Real.sq_sqrt (rowMajorant_nonneg _)
  have hsum (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ) :
      (∑ x : labels × R, ‖(w x.2.val : ℂ)*P x.1.val x.2.val‖^2) = rowFamilyEnergy labels P K := by
    rw [rowFamilyEnergy_eq_sum labels P K hK]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort (s := labels)
      (f := fun I : Ideal ActualEisensteinCubic.O => ∑ z : R, ‖(w z.val : ℂ)*P I z.val‖^2)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.sum_coe_sort (s := R) (f := fun z : ActualEisensteinCubic.O => ‖(w z : ℂ)*P I z‖^2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw z),mul_pow,hw2]
  let ψ : labels × R → ℝ → ℂ := fun x t => (w x.2.val : ℂ)*φ x.1.val x.2.val t
  have hψ (x : labels × R) : Integrable (fun t => b t*ψ x t) := by
    convert (hφ x.1.val x.2.val).const_mul (w x.2.val : ℂ) using 1
    funext t
    dsimp only [ψ]
    ring
  have hψbound (t : ℝ) : (∑ x : labels × R, ‖ψ x t‖^2) ≤ E*(1+|t|)^(2*d) := by
    change (∑ x : labels × R, ‖(w x.2.val : ℂ)*φ x.1.val x.2.val t‖^2) ≤ _
    rw [hsum (fun I z => φ I z t)]
    exact hbound t
  have hi (x : labels × R) :
      (∫ t : ℝ, b t*ψ x t) = (w x.2.val : ℂ)*(∫ t : ℝ, b t*φ x.1.val x.2.val t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [ψ]
    ring
  have hm := finite_integral_energy_polynomial b ψ d E hE hb hψ hψbound
  simp_rw [hi] at hm
  rwa [hsum (fun I z => ∫ t : ℝ, b t*φ I z t)] at hm

theorem rowFamilyEnergy_const_mul (labels : Finset (Ideal ActualEisensteinCubic.O)) (P : Ideal ActualEisensteinCubic.O → ActualEisensteinCubic.O → ℂ)
    (K : ℝ) (hK : 0 < K) (c : ℂ) :
    rowFamilyEnergy labels (fun I z => c*P I z) K = ‖c‖^2*rowFamilyEnergy labels P K := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro z hz
  ring

end
section

open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end


open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

end CanonicalRowCompletion

namespace SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProduct)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
