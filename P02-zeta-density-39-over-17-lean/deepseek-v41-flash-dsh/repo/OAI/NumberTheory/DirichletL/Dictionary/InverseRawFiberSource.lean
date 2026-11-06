module
public import OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.DetectorDictionaryInverseRawFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorCoefficientTransfer InverseInitialPhysicalSlots InverseInitialDetectorSource InverseInitialRawDictionary InverseInitialConjugateEnergy HeckeDetectorPhysicalSelection
local notation "O"=>HeckeFamily.O

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

end SevenEighths.DetectorDictionaryInverseRawFiberSource

end

end OAI
