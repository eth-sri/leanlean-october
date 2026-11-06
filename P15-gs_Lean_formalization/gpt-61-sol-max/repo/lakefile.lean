import Lake
open Lake DSL

package gs_formalization where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

def gsRoots : Array Lean.Name := #[`GS, `GSExtensions, `GSContinuation, `GSLieAction, `GSCayleyCharts,
    `GSRevisionAlgebra, `GSRevision, `GSNonmanifold,
    `GSNonmanifoldMembership, `GSNonmanifoldCoverage, `GSNonmanifoldCompletion,
    `GSNonmanifoldSphereRetract, `GSNonmanifoldOpenGerms, `GSHomologyFunctor,
    `GSNonmanifoldBridge, `GSNonmanifoldHomology, `GSNonmanifoldBallHomology,
    `GSNonmanifoldClosure, `GSDifferentiableObstruction, `GSManifoldCompletion,
    `GSNonmanifoldTopology, `GSResults]

lean_lib GS where
  roots := gsRoots
  globs := #[.submodules `GS] ++ gsRoots.map Glob.one

-- The default entry point includes all project modules and the unconditional
-- nonmanifold theorem. `lake build GS` also verifies the full source collection.
@[default_target]
lean_lib GSChecked

lean_lib Challenge

lean_lib Solution
