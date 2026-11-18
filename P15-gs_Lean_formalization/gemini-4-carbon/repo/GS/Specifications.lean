module

public import GS.OriginalLocalModel

@[expose] public section

namespace GS.Specifications

def ConeProductNonManifoldGoal : Prop :=
  ∀ (d e : ℕ), 3 ≤ d →
    ¬ EuclideanAtSubset
      ({p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | Matrix.rank p.2 ≤ 1})
      (0, 0)

end GS.Specifications
