module
public import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
public import OAI.NumberTheory.DirichletL.Hecke.Family
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

noncomputable section

namespace ActualEisensteinSieve

export OAI.SevenEighths.HeckeFamily (omega K O)

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def lambda : O := omega - 1

def lambdaIdeal : Ideal O := Ideal.span {lambda}

private theorem lambda_prime : Prime lambda := by
  pm_3517

theorem lambda_maximal : lambdaIdeal.IsMaximal := by
  have hp : lambdaIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime lambda_prime
  have hne : lambdaIdeal ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero
  exact hp.isMaximal hne

theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  pm_5037
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

instance : lambdaIdeal.IsMaximal := lambda_maximal

theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  pm_4892 O lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  grind

end ActualEisensteinSieve

end

end OAI
