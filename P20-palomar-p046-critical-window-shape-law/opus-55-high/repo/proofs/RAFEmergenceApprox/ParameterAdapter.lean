module

public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.RAF.Concrete.UniformModel

public section

namespace RAFEmergenceApprox
open RAF.Polymer RAF.Concrete HordijkSteelThreshold unitInterval

/-- The inherited lambda parametrization covers every homogeneous probability
at every nontrivial finite source size. -/
theorem catalysisP_covers_probability (n : ℕ) (hn : 2 ≤ n) (p : I) :
    catalysisP n ((p:ℝ) * Fintype.card (Reaction n) / n) = p := by
  have hj : 0 < Fintype.card (Reaction n) := by rw [card_reactions_exact hn]; omega
  apply Subtype.ext
  have he : rawCatalysisP n (p * Fintype.card (Reaction n) / n) = p := by
    unfold rawCatalysisP
    field_simp
  change min 1 (max 0 $ rawCatalysisP n _) = p
  grind

end RAFEmergenceApprox
