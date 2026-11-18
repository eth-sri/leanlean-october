module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.Quantitative.SpectralFunction

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.MellinTransform

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def g (Z : ℝ) : ℂ :=
  if 0 < Z then (Z : ℂ) ^ (61 / 100 : ℂ) * Spectral.f D Z else 0

def T (s : ℂ) : ℂ := mellin (g D) (-s)

end

end DedekindZetaZeroFree.Quantitative.MellinTransform
