module

public import Mathlib

public import Mathlib.Tactic

@[expose] public section


noncomputable section
open scoped BigOperators
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity





 def compactTensor (q : Fin 6 → Fin 6 → ℂ)  :=
  -(q 1 1 + (q 2 2 - q 2 4 - q 4 2 + q 4 4) +
    (q 3 3 + q 3 5 + q 5 3 + q 5 5))

end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.FullSixCoercivity

end
