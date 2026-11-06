module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
public import OAI.NumberTheory.DirichletL.QuadraticSieve.MaskedPrincipalBounds

@[expose] public section

namespace OAI



open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 

 
namespace CanonicalQuadraticSieve



open     ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

section
variable (M F b N i j : ℝ) (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N) (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N)


include hN hi hj in
theorem sqrt_product_column_shell    
        :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    nlinarith
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

include hM hF hb hN hi hj in
theorem dual_truncation_reference_bounds  
           
        :
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

include hM hF hN hi hj in
theorem dual_truncation_prefactor_bound  
         
        :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

end

variable {m n : Type*} [Fintype m] [Fintype n]

end CanonicalQuadraticSieve

namespace SecondPassArithmetic





 
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

 
 
namespace SecondPassArithmetic
 
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic



end OAI
