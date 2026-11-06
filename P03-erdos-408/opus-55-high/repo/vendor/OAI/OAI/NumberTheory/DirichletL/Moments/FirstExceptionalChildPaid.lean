module

public import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPaidScales
public import OAI.NumberTheory.DirichletL.Moments.FirstChildLower

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstExceptionalChildPaid
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

end SevenEighths.CenteredMomentFirstExceptionalChildPaid

end

end OAI
