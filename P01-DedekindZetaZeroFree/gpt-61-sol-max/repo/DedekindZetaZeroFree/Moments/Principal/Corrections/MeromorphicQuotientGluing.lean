module

public import DedekindZetaZeroFree.LFunctions.Hecke.MaskedMeromorphicContinuation
public import DedekindZetaZeroFree.Moments.Principal.Corrections.CoordinateHolomorphy
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.SeparatedHeckeFactors

@[expose] public section

open scoped NumberField Classical Topology

noncomputable section
namespace DedekindZetaZeroFree.MeromorphicSeparationGluing
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors MaskedHeckeMeromorphic FrequencyCharacterMasks

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}


 def c₁ : ℝ := (499 / 500 : ℝ) - 1 / 100000

end DedekindZetaZeroFree.MeromorphicSeparationGluing

end
