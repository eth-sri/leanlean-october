/- Finite-coordinate representation for the native word table. -/
module
public import Glennie.Native.Statements
public import Glennie.Compact.ObservationScript

@[expose] public section
namespace Glennie.Compact.NativeWordTableR01
noncomputable section
open Glennie
def marks : Fin 3 → Albert := ![witnessX,witnessY,witnessZ]
def nativeWords : Fin 27 → Albert := SubmissionR03.wordValues 1 marks jordan


end
end Glennie.Compact.NativeWordTableR01
