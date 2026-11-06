module

public import OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
public import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K)

theorem heightCoeff_mul (τ : Character) (t : ℝ) (I J : Ideal O) :
    heightCoeff τ t (I*J)=heightCoeff τ t I*heightCoeff τ t J := by
  have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t)=
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I):(0:ℝ)≤Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J):(0:ℝ)≤Ideal.absNorm J) (Complex.I*t)
  simp only [heightCoeff,map_mul,Nat.cast_mul,hpow]
  ring

end SevenEighths.CenteredMomentSecondSourceEnergy

end

end OAI
