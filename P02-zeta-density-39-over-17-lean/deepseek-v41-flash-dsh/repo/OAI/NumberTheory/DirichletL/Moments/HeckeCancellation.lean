module
public import OAI.NumberTheory.DirichletL.Moments.HeckeVolume
public import OAI.NumberTheory.DirichletL.Moments.Cancellation

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

lemma volumeControl_nonneg (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pvControl_nonneg W)

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI
