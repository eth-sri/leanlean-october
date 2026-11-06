module
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
public import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
public import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

section Dictionary
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end Dictionary

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI
