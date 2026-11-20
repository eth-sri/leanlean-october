module

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Moments.Lattice

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimary
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)

def primaryIdealCharacter (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    Ideal O →* ℂ :=
  χ.toMonoidHom.comp ((Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom.comp
    primaryGeneratorHom.toMonoidHom)

@[simp] theorem primaryIdealCharacter_apply (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    primaryIdealCharacter c χ I =
      χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator I)) := rfl

theorem primaryIdealCharacter_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    ‖primaryIdealCharacter c χ I‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact QuadraticInitialBound.norm_finite_character_le_one χ _

end SevenEighths.CenteredMomentPrimary
end

end OAI
