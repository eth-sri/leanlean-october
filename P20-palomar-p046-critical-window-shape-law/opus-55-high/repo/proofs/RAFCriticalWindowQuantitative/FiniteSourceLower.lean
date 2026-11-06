module

public import proofs.RAFCriticalWindowQuantitative.FiniteSeedEvaluation
public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound
public import proofs.RAFReactionQuotient.SourceBounds

public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

theorem _root_.HordijkSteelThreshold.SplitModel.food_seed_mass (M : SplitModel) (N L m : ℕ) (a : I) :
    M.μ N a {x | binaryFood N L ⊆ M.cl N 2 x} ≤
      M.μ N a {x | (m-1)*Fintype.card (Molecule N) ≤ m*(M.cl N 2 x).card} +
      M.μ N a {x | m*(M.cl N L x).card < (m-1)*Fintype.card (Molecule N)} := by
  refine (measure_mono fun x hseed => ?_).trans $ measure_union_le _ _
  by_cases hb : m*(M.cl N L x).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  exact Or.inl $ (Nat.le_of_not_gt hb).trans $ Nat.mul_le_mul_left m $ Finset.card_le_card
    (temporaryReactionClosure_seed_transfer Finset.Subset.rfl fun x hx =>
      hseed $ Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)

end RAFCriticalWindowQuantitative
