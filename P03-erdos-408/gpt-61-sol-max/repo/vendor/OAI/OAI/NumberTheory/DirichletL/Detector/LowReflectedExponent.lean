module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths

@[expose] public section

namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

lemma hybrid_half_with_error  {v za ε}  (hv : -ε≤v) (hε : 0≤ε)
    (hu : hybridSaving v za≠za) : v/2-ε/2≤hybridSaving v za := by
  grind [hybridSaving, min]



end SevenEighths.ProbeLowReflected

end OAI
