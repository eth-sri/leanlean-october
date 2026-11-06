module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonWindow
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalWindow
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowHeight

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
