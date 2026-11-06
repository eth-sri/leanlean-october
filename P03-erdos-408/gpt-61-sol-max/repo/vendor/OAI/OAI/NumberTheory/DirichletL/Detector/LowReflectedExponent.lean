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
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total za ((v+za)/3) with hz|hz
    · exact (hu (min_eq_left hz)).elim
    · rw [min_eq_right hz]
      have hzv := min_le_left za ((v+za)/3)
      rw [min_eq_right hz] at hzv
      linarith

lemma retained_kernel_quarter (Td y : ℝ) : Td/4≤y/4+max 0 (Td-y)/2 := by
  have h0 := le_max_left 0 (Td-y)
  have h1 := le_max_right 0 (Td-y)
  linarith

end SevenEighths.ProbeLowReflected

end OAI
