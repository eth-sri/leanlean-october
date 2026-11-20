module
public import AlbertRecognition.Reference
public import Glennie.Hilbert
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
namespace AlbertRecognition
open Glennie
noncomputable section

instance : FiniteDimensional ℝ V := inferInstanceAs (FiniteDimensional ℝ traceLinear.ker)

end
end AlbertRecognition
