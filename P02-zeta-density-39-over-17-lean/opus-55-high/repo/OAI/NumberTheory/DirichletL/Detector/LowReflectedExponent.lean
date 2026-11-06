module
public import OAI.NumberTheory.DirichletL.Inversion.TerminalWidths

@[expose] public section

namespace OAI

namespace SevenEighths.ProbeLowReflected
open InverseTerminalWidths

lemma hybrid_half_with_error {v za ε : ℝ} (hv : -ε≤v) (hε : 0≤ε)
    (hu : hybridSaving v za≠za) : v/2-ε/2≤hybridSaving v za := by
  unfold hybridSaving at *
  rcases le_total v (min za ((v+za)/3)) with h|h
  grind
  grind

lemma retained_kernel_quarter (Td y : ℝ) : Td/4≤y/4+max 0 (Td-y)/2 := by grind

end SevenEighths.ProbeLowReflected

end OAI
