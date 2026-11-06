module

public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.Moments.Lattice

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimary
open ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)

def primaryIdealCharacter (c : ActualEisensteinCubic.O) (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ) :
    Ideal ActualEisensteinCubic.O →* ℂ :=
  χ.toMonoidHom.comp ((Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom.comp
    primaryGeneratorHom.toMonoidHom)

@[simp] theorem primaryIdealCharacter_apply (c : ActualEisensteinCubic.O)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ) (I : Ideal ActualEisensteinCubic.O) :
    primaryIdealCharacter c χ I =
      χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator I)) := rfl

theorem primaryIdealCharacter_norm_le_one (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {c}) ℂ) (I : Ideal ActualEisensteinCubic.O) :
    ‖primaryIdealCharacter c χ I‖ ≤ 1 := by
  let : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact QuadraticInitialBound.norm_finite_character_le_one χ _

end SevenEighths.CenteredMomentPrimary
end

end OAI
