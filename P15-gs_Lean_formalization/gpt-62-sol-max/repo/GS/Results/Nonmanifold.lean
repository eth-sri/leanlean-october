module

public import GS.Topology.RankCone


public import GS.NonmanifoldFinal.EuclideanTransport

public import GS.Core

public import GS.OriginalLocalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

set_option autoImplicit false

noncomputable section

open Matrix GS GS.NonmanifoldCompletion
open GS.NonmanifoldObstruction GS.NonmanifoldFinal

namespace GS.Results

/-- The rank-at-most-one locus for two rows has a topological singularity at
zero, even after taking a product with any finite-dimensional real space. -/
theorem _root_.GSPalomar.rank_one_cone_singularity (d e : ℕ) (hd : 2 ≤ d) :
    ¬ EuclideanAtSubset
      {p : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ | p.2.rank ≤ 1} (0, 0) := by
  intro hE
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  have hz : ((0, 0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by
    simp [S]
  have hsub : EuclideanAt (⟨(0, 0), hz⟩ : S) :=
    (euclideanAtSubset_iff S (0, 0) hz).mp hE
  let h : ((Fin e → ℝ) × RankOne 1 (Fin d)) ≃ₜ S := flattenConeProduct
  apply GS.NonmanifoldTopology.cone_not_euclidean e d hd
  exact (euclideanAt_homeomorph h (0,rankZero)).mpr hsub

/-- Reflection perpendicular to the all-ones vector: `I - (2/q) J`.
The formula is defined also for `q = 0`; its uses below assume `q > 0`. -/
def reflectionBase (q : ℕ) : Mat q :=
  fun i j => (if i = j then 1 else 0) - 2 / (q : ℝ)

theorem reflectionBase_apply (q : ℕ) (i j : Fin q) :
    reflectionBase q i j = (if i = j then 1 else 0) - 2 / (q : ℝ) := by
  simp [reflectionBase, Matrix.one_apply]

theorem reflectionBase_symmetric (q : ℕ) :
    (reflectionBase q)ᵀ = reflectionBase q := by
  ext i j
  simp [reflectionBase_apply, eq_comm]

theorem reflectionBase_mul_self (q : ℕ) (hq : 0 < q) :
    reflectionBase q * reflectionBase q = 1 := by
  let C : Mat q := fun _ _ => 2 / (q : ℝ)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hC : C * C = C + C := by
    ext i j
    simp [C, Matrix.mul_apply]
    field_simp [hqR]
    ring
  change (1 - C) * (1 - C) = 1
  grind [sub_mul, mul_sub, one_mul, mul_one]

/-- Orthogonality is certified by an exact matrix identity, without numerical
approximation or a dimension-specific computation. -/
theorem reflectionBase_orthogonal (q : ℕ) (hq : 0 < q) :
    Orthogonal (reflectionBase q) := by
  grind [Orthogonal.of_transpose_mul, reflectionBase_symmetric, reflectionBase_mul_self]

theorem reflectionBase_entries_ne_zero (q : ℕ) (hq : 3 ≤ q)
    (i j : Fin q) : reflectionBase q i j ≠ 0 := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  rw [reflectionBase_apply]
  split_ifs <;> intro hz
  all_goals field_simp [hq0] at hz
  all_goals linarith

end GS.Results
