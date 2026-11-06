module

public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstPhysicalSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstCanonicalDataDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
