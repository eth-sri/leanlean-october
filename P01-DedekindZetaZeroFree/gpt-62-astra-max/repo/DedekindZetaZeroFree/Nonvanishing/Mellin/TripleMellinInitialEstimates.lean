module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PrincipalSpectralResidueEstimate

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps

open MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.PrincipalMellinComparison.ContinuationSteps

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison

open Filter Asymptotics MeasureTheory
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.PrincipalMellinComparison

end

section

namespace DedekindZetaZeroFree.PrincipalMellin

open Filter Asymptotics

variable {F : Type} [Field F] [NumberField F]

namespace ActualRecipe

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem mellinWeight_ne_zero (R : ActualRecipe S η) : R.W.M (1 / 6) ≠ 0 :=
  R.probe.nonzeroMellin

theorem realMellinWeight_ne_zero (R : ActualRecipe S η) : R.W.W1Hat 1 ≠ 0 :=
  probeRealWeightMellin_one_ne_zero R.probe.W1

end ActualRecipe

end DedekindZetaZeroFree.PrincipalMellin

end
