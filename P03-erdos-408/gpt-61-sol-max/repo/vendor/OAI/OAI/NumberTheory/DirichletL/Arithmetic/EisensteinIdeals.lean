module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap

noncomputable section

namespace ActualEisensteinSieve

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def omega  :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

def lambdaIdeal  := Ideal.span {lambda}

theorem lambda_prime : Prime lambda := IsPrimitiveRoot.zeta_sub_one_prime' (IsCyclotomicExtension.zeta_spec 3 ℚ OAI.ActualEisensteinSieve.K)

theorem lambda_maximal : lambdaIdeal.IsMaximal := Ideal.IsPrime.isMaximal (Ideal.isPrime_span_singleton_of_prime OAI.ActualEisensteinSieve.lambda_prime) ((Iff.not Ideal.span_singleton_eq_bot).mpr (Prime.ne_zero OAI.ActualEisensteinSieve.lambda_prime))

theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

instance : lambdaIdeal.IsMaximal := lambda_maximal

theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  let : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  norm_num at hcard

end ActualEisensteinSieve

end

end OAI
