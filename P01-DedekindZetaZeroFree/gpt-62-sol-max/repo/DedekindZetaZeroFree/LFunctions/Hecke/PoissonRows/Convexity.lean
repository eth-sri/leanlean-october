module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConductorNormalization
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Nonprincipality
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConvexityData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Convex

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)







end

end DedekindZetaZeroFree.Quantitative.Convex
