module

public import OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid


namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem sqrt_product_column_shell (N i j : ℝ) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    simpa only [pow_two] using mul_le_mul hi.1 hj.1 (by linarith : 0 ≤ N / 2) hi0.le
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

theorem dual_truncation_reference_bounds (M F b N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    0 < N * Real.sqrt (F / (M * b)) ∧
      (N * Real.sqrt (F / (M * b))) / 2 ≤ Real.sqrt (F * i * j / (M * b)) ∧
      Real.sqrt (F * i * j / (M * b)) ≤ 2 * (N * Real.sqrt (F / (M * b))) := by
  have hr : 0 < Real.sqrt (F / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (F * i * j / (M * b)) = Real.sqrt (F / (M * b)) * Real.sqrt (i * j) := by
    rw [← Real.sqrt_mul (show 0 ≤ F / (M * b) by positivity)]
    congr 1
    ring
  obtain ⟨hlo, hhi⟩ := sqrt_product_column_shell N i j hN hi hj
  refine ⟨mul_pos hN hr, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlo hr.le]
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hhi hr.le, mul_pos hN hr]

theorem dual_truncation_prefactor_bound (M F N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

variable {m n : Type*} [Fintype m] [Fintype n]

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

end

end OAI
