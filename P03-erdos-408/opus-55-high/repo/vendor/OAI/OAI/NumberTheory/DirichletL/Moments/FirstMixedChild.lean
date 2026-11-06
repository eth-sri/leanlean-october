module

public import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
public import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstMixedChild
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

end SevenEighths.CenteredMomentFirstMixedChild

end

end OAI
