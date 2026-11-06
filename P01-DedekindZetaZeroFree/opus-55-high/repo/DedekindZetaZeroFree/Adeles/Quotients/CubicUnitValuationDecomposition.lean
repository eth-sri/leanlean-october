module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.IdeleUnitValuationPairing

@[expose] public section

open scoped NumberField Classical BigOperators

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw

noncomputable section

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] exteriorValuationsTopology

namespace CubicIdeleDecomposition

variable (S : Finset (KPHilbert.Place F))

attribute [local instance] exteriorValuationsTopology

end CubicIdeleDecomposition

end

end DedekindZetaZeroFree.RepresentationTheory.KPGlobalCubicIdelePairingRaw
