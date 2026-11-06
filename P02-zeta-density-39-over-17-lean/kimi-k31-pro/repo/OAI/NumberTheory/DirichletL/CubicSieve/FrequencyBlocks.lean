module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools

@[expose] public section

namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inputConjugateRow_smoothed_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
    ∑ G ∈ F.powerset,
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
      ∑ E : G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
        ∑' k : O,
          secondFrequencyKernel p hp hg hinj F Ψ Ψ m
            (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  change secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y = _
  rw [secondOverlapBlock_eq_modes p hp hg hinj F G Ψ m c d H W Y hY]
  congr 1
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  apply tsum_congr
  intro k
  exact residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d
    (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

lemma nonzeroRowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => if z = 0 then 0 else
      rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz]
  simp

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

theorem finite_nonzero_row_energy_le_majorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤ (nonzeroRowMajorantSum P Y).re := by
  have hs := nonzeroRowMajorant_summable P Y hY
  unfold nonzeroRowMajorantSum
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (if z = 0 then (0 : ℂ) else
        rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [ite_eq_right (hT0 z hz), rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      split_ifs
      · norm_num
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma aLabel_dvd_primeProduct (B : Finset ι) (v : ι → ℕ) (ε : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : aLabel p B ε ∣ primeProduct p B v := by
  unfold aLabel primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  cases h : ε i <;> simp only [bit, h, Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.zero_le _
  · exact hv i hi

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

def actualSecondRow (D E : Finset ι) (k : O) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) D *
    primeSubsetGenerator (fun i => Ideal.span {p i}) E * k

end

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
