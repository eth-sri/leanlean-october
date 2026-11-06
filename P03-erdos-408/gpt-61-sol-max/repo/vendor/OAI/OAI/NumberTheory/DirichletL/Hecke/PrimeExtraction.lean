module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities

@[expose] public section

namespace OAI

noncomputable section

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
 
 
 
 
 
 
 

namespace ShortDraftHeckeBridge

end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)



noncomputable def fiber (n : ℕ)  :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

theorem mem_fiber  {n}   {I}  : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]

 

 



end FiniteSFactor
namespace ShortDraftHeckeBridge

end ShortDraftHeckeBridge

namespace DyadicTransfer

noncomputable def annularCutoff (φ : ℝ → ℂ) (y : ℝ)  :=
  φ y - φ (2 * y)

theorem annularCutoff_eq_zero_of_le_half  φ 
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
     {y}  (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  grind [annularCutoff]

theorem annularCutoff_eq_zero_of_two_le  φ 
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
     {y}  (hy : 2 ≤ y) : annularCutoff φ y = 0 := by
  grind [annularCutoff]

theorem partial_partition  φ   x   K  :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ (x / (2 : ℝ) ^ k)) =
      φ (x / (2 : ℝ) ^ K) - φ (2 * x) := by
  induction K with
  | zero =>
      simp [annularCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      grind [annularCutoff]

end DyadicTransfer

open Ideal      

namespace FiniteSFactor

end FiniteSFactor

end

end OAI
