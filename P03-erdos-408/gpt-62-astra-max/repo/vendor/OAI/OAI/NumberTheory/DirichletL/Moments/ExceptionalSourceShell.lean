module

public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalSourceShell
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedDetectorAmplitude
open CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentExceptionalSourceShell

end

end OAI
