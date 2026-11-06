module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentCommonRadialData
open CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal ActualEisensteinCubic.O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)

end SevenEighths.CenteredMomentFirstNonexceptionalWeightSum

end

end OAI
