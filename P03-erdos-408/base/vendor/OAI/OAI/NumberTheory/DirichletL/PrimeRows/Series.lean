module

public import OAI.NumberTheory.DirichletL.PrimeRows.Agreement
public import OAI.NumberTheory.DirichletL.Hecke.Reciprocal

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

end SevenEighths.ProbeHighRowFamily

end

end OAI
