module

public import OAI.NumberTheory.DirichletL.Moments.SecondSourcePowerDescent
public import OAI.NumberTheory.DirichletL.Moments.SecondFrozenUniformSubset
public import OAI.NumberTheory.DirichletL.Moments.SecondChildPowerBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
public import OAI.NumberTheory.DirichletL.Moments.SecondSourceRemainder
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalLiveSource

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondFrozenPowerDescent
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _





end SevenEighths.CenteredMomentSecondFrozenPowerDescent

end

end OAI
