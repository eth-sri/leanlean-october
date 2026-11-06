module

public import NearlyMinimax.DesignProjection
public import NearlyMinimax.ModelRegularity

@[expose] public section

open Matrix MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace NearlyMinimax

/-- The actual empirical projection fixes every vector in the column
range, rather than accepting this fitting property as a hypothesis. -/
theorem empirical_design_fixes_evaluation {ι κ : Type*} [Fintype ι]
    [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ) (a : κ → ℝ) :
    empiricalDesignProjection B *ᵥ (B *ᵥ a) = B *ᵥ a := by
  have hs := empirical_design_projection_spec B
  have hq : B *ᵥ a ∈ LinearMap.range (empiricalDesignProjection B).mulVecLin := by
    rw [hs.2.2]
    exact ⟨a, rfl⟩
  rcases hq with ⟨v, hv⟩
  change empiricalDesignProjection B *ᵥ v = B *ᵥ a at hv
  rw [← hv, mulVec_mulVec, hs.2.1]

end NearlyMinimax
