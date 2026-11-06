module

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalDyadic
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBudget
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving
public import OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
