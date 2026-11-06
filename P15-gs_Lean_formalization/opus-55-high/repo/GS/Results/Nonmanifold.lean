module

public import GS.NonmanifoldClosure.TopologicalClosure

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Topological singularities of the original three-factor GS family

The public statements here use the scalar perfect shuffle and consecutive
block sizes `2, q, 2` from `GS.localFamily`.  A point is non-Euclidean in the
actual subspace topology; no differentiability or homology assumption is
made.

The general theorem does not require determinant one.  An explicit
Householder matrix supplies a non-Euclidean point in every size `2q`, `q ≥ 3`.
Thus the conclusion is instantiated for all dimensions in the theorem, not
only for the first example `q = 3`.
-/


noncomputable section

open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion
open GS.NonmanifoldObstruction GS.NonmanifoldFinal

namespace GS.Results

/-- The rank-at-most-one locus for two rows has a topological singularity at
zero, even after taking a product with any finite-dimensional real space. -/
theorem cone_rankOne_not_euclidean (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) :=
  fun hE => GS.NonmanifoldTopology.cone_not_euclidean e d hd
    ((euclideanAt_homeomorph flattenConeProduct productZero).mpr ((euclideanAtSubset_iff _ _ hE.1).mp hE))

/-- The original GS family is not locally Euclidean at `Q₀ ⊗ I₂` whenever
`q ≥ 3` and the orthogonal matrix `Q₀` has no zero entries.

The determinant-one condition in the original manuscript specification is
unnecessary for this conclusion. -/
theorem gs_not_euclidean_at {q : ℕ} (hq : 3 ≤ q)
    (Q₀ : Mat q) (hQ₀ : Orthogonal Q₀) (hentries : ∀ i j, Q₀ i j ≠ 0) :
    ¬ EuclideanAtSubset (localFamily q) (basePoint Q₀) :=
  fun hE => model_not_euclidean_of_cone_goal GS.NonmanifoldTopology.coneProductNonManifold q hq
    ((euclideanAt_pointedOpenModel (original_pointed_open_model (by omega) Q₀ hQ₀ hentries).some).mp
      ((euclideanAtSubset_iff _ _ hE.1).mp hE))

section
variable (q : ℕ)
/-- Reflection perpendicular to the all-ones vector: `I - (2/q) J`.
The formula is defined also for `q = 0`; its uses below assume `q > 0`. -/
def reflectionBase : Mat q :=
  fun i j => (if i = j then 1 else 0) - 2 / (q : ℝ)

/-- Orthogonality is certified by an exact matrix identity, without numerical
approximation or a dimension-specific computation. -/
theorem reflectionBase_orthogonal (hq : 0 < q) : Orthogonal (reflectionBase q) := by
  refine Orthogonal.of_transpose_mul ?_
  ext i j
  simp [reflectionBase, Matrix.mul_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, eq_comm]
  field_simp
  ring

theorem reflectionBase_entries_ne_zero (hq : 3 ≤ q) (i j : Fin q) : reflectionBase q i j ≠ 0 := by
  have : (3 : ℝ) ≤ q := by exact_mod_cast hq
  simp only [reflectionBase]
  split_ifs <;> intro hz <;> field_simp at hz <;> linarith

/-- Every three-factor family of the specified size has a topological
singularity. In particular, it cannot be a topological manifold without
boundary with its induced matrix topology. -/
theorem exists_nonEuclidean_point (hq : 3 ≤ q) :
    ∃ M : Mat (q * 2), M ∈ localFamily q ∧
      ¬ EuclideanAtSubset (localFamily q) M :=
  ⟨_, basePoint_mem_localFamily _ (reflectionBase_orthogonal q (by omega)),
    gs_not_euclidean_at hq _ (reflectionBase_orthogonal q (by omega)) (reflectionBase_entries_ne_zero q hq)⟩

end

end GS.Results
