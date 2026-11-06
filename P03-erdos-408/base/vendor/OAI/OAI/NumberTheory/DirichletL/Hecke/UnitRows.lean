module

public import OAI.NumberTheory.DirichletL.Hecke.RowClosure
public import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open ActualEisensteinCubic CubicRamified ConcreteTraceCRT
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "ω" => HeckeFamily.omega
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_unit_thirty_six (n : O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using hs.2)
  have h2 : IsCoprime n (2 : O) := (hneg2.of_isCoprime_of_dvd_left ⟨-1, by ring⟩).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : Oˣ) : unitSupplement u (v : O) = 1 := by
  have hspan : (Ideal.span {(v : O)} : Ideal O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : Supported (1 : Ideal O) := ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact False.elim (Multiset.notMem_zero P hP)⟩
  change (if Supported (Ideal.span {(v : O)}) then idealRowHom (u : O) (Ideal.span {(v : O)}) else 0) = 1
  rw [hspan, ite_eq_left hs, map_one]

theorem unitSupplement_factorsModulo (u : Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : Oˣ) (n : O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [ite_eq_right (fun hs => hn (supported_unit_thirty_six n hs))]

end SevenEighths.HeckeUnitRows

end

end OAI
