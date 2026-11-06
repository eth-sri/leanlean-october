module
public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalPrefactor
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNonexceptionalWeightSum
open ActualEisensteinCubic



open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSecondBlockAggregate

open CenteredMomentSourceMass

open scoped EisensteinO
variable {ι:Type*}[Fintype ι][DecidableEq ι]

local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev Labels (s:Input ι)(R seed:Ideal O):=
  ActiveLabel (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)






