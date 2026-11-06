module

public import GS.Core
public import GS.OriginalLocalModel
public import GS.M4Necessary

@[expose] public section


/-!
# Theorem specifications -- definitions alone are not proofs

The Goal definitions specify propositions; definitions alone do not prove them.
The final two theorems link the m=4 proofs to their specifications. Extensions,
Continuation, and NonmanifoldClosure prove the other original specifications.
The public interface is `GSResults`; the scope is described in docs/RESULTS.md.
The suffix `Goal` labels a specification, not an assertion that it is proved.
-/

noncomputable section
namespace GS.Specifications






/-- The cone product obstruction after the local model. It is proved in
`GS.NonmanifoldTopology.coneProductNonManifold` using a topological argument;
the optional sphere-homology computation is not needed. -/
def ConeProductNonManifoldGoal : Prop :=
  ∀ (d e : ℕ), 3 ≤ d →
    ¬ EuclideanAtSubset
      ({p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | Matrix.rank p.2 ≤ 1})
      (0,0)

end GS.Specifications
