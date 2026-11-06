module

public import OAI.NumberTheory.DirichletL.Hecke.RowClosure
public import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeUnitRows
open HeckeFamily CanonicalUnitEuler CanonicalRowCompletion
open CanonicalQuadraticSieve

theorem supported_unit_thirty_six (n : HeckeFamily.O) (hn : Supported (Ideal.span {n})) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(36 : HeckeFamily.O)}) n) := by
  have hs := (supported_span_iff n).mp hn
  have hneg2 : IsCoprime (-2 : HeckeFamily.O) n := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simp_all)
  have h2 : IsCoprime n (2 : HeckeFamily.O) := (hneg2.of_isCoprime_of_dvd_left (by simp)).symm
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n hs.1).symm
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, Ideal.isCoprime_span_singleton_iff]
  convert (h2.pow_right : IsCoprime n ((2 : HeckeFamily.O)^2)).mul_right h9 using 1 ; norm_num

theorem unitSupplement_unit (u v : HeckeFamily.Oˣ) : unitSupplement u (v : HeckeFamily.O) = 1 := by
  have hspan : (Ideal.span {(v : HeckeFamily.O)} : Ideal HeckeFamily.O) = 1 := by
    simpa only [Ideal.one_eq_top] using Ideal.span_singleton_eq_top.mpr v.isUnit
  have hs : Supported (1 : Ideal HeckeFamily.O) := ⟨one_ne_zero, by
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    simp_all⟩
  change (if Supported (Ideal.span {(v : HeckeFamily.O)}) then idealRowHom (u : HeckeFamily.O) (Ideal.span {(v : HeckeFamily.O)}) else 0) = 1
  grind

theorem unitSupplement_factorsModulo (u : HeckeFamily.Oˣ) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36 : HeckeFamily.O)}) (unitSupplement u) :=
  unitSupplement_periodic u

def character (u : HeckeFamily.Oˣ) : Character :=
  HeckeRowClosure.rowCharacter (Ideal.span {(36 : HeckeFamily.O)})
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)) (unitSupplement u)
    (unitSupplement_factorsModulo u) (unitSupplement_unit u)

theorem elementCoeff_character (u : HeckeFamily.Oˣ) (n : HeckeFamily.O) :
    elementCoeff (character u) n = unitSupplement u n := by
  rw [character, HeckeRowClosure.elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · change 0 = if Supported (Ideal.span {n}) then _ else 0
    rw [ite_eq_right (fun hs => hn (supported_unit_thirty_six n hs))]

end SevenEighths.HeckeUnitRows

end

end OAI
