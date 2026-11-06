module

public import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceEnergy

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer InverseInitialConjugateEnergy
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
