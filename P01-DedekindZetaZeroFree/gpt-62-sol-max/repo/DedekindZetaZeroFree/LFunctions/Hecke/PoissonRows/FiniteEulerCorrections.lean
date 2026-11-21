module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.FixedData.Row

open DedekindZetaZeroFree NumberField in

noncomputable def ideal {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus} {D : FixedData S η}
    (u : D.Row) : D.recipe.A.Exterior :=
  PrincipalProbeConstruction.Inputs.rowIdeal D.recipe.A u.u u.u_ne_zero

end DedekindZetaZeroFree.Quantitative.FixedData.Row

namespace DedekindZetaZeroFree.Quantitative.EulerDeletion

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rowPrimes (u : D.Row) : Finset (Ideal (NumberField.RingOfIntegers F)) :=
  (UniqueFactorizationMonoid.normalizedFactors
    (Subtype.val (DedekindZetaZeroFree.Quantitative.FixedData.Row.ideal u) : Ideal (NumberField.RingOfIntegers F))).toFinset












end

end DedekindZetaZeroFree.Quantitative.EulerDeletion
