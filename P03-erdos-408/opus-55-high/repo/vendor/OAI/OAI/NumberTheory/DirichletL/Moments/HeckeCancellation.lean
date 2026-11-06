module

public import OAI.NumberTheory.DirichletL.Moments.HeckeVolume
public import OAI.NumberTheory.DirichletL.Moments.Cancellation

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume
open IdealMobiusDivisorSum QuadraticInitialBound

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal ActualEisensteinCubic.O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal ActualEisensteinCubic.O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (ActualEisensteinCubic.O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

lemma volumeControl_nonneg (Q : Ideal ActualEisensteinCubic.O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (by positivity) (pvControl_nonneg W)

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI
