module

public import OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceDictionary
public import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRelativeSlots
public import OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
public import OAI.NumberTheory.DirichletL.Hecke.PrimeScale

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse

lemma relativeCharacter_ideal (η₀ : Character) (θ : RayQuotient.Characters M H) (I : Ideal HeckeFamily.O) :
    idealCoeff (relativeCharacter M H hH η₀ θ) I=
      idealCoeff (HeckeRayQuotient.character M H hH θ) I*idealCoeff η₀.inverse I :=
  idealCoeff_product _ _ _

lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal HeckeFamily.O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
