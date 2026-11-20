module
public import OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal
public import OAI.NumberTheory.DirichletL.Hecke.PrimeScale
public import OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda


variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI
