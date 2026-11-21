module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.MellinIdentity
public import DedekindZetaZeroFree.Analysis.ContourIntegration.GammaShiftNorm

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorShift

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def smoothedSum (F : Type) [Field F] [NumberField F] (U β γ : ℝ)
    (ω : Detector.PrimitiveFrequencyCharacter F) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    if n ≠ ⊥ then
      (DetectorDef.a F U n : ℂ) * ω.character n *
        (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
        (Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℂ)
    else 0


end

end DedekindZetaZeroFree.Quantitative.DetectorShift
