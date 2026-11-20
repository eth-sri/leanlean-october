/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
@[expose] public section

namespace BN
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
-- Keep the Hermitian proof shared with the ordered definition, as in the benchmark.
/-- Adjacency eigenvalues indexed by vertices, counting algebraic multiplicity. -/
noncomputable def adjacencyEigenvalues :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues
/-- Adjacency eigenvalues in nonincreasing order, with multiplicity. -/
noncomputable def adjacencyEigenvalues₀ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀
/-- The largest adjacency eigenvalue. -/
noncomputable def lambda1 [Nonempty V] :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩
/-- The second largest ordered adjacency eigenvalue. -/
noncomputable def lambda2 [Nontrivial V] :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩
end BN
