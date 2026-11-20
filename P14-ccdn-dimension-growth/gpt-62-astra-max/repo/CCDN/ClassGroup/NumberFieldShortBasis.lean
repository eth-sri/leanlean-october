/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NumberFieldEuclideanLattice
import CCDN.ClassGroup.EuclideanNumberFieldBasis
import CCDN.ClassGroup.LatticeMinimaFlag
import CCDN.ClassGroup.LatticeMinimaProduct
import CCDN.ClassGroup.LatticeGreedyMinima
import CCDN.ClassGroup.MultiplicationPairingProduct

/-! Short independent algebraic integers. Minkowski's flag bound controls the product
of the successive minima; multiplication in the field bounds each minimum in terms of
this same product. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module MeasureTheory NumberField
open scoped NumberField

private theorem greedy_lattice_product_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ E) (hb : GreedyLatticeFamily L b) :
    (∏ i, ‖b i‖) ≤ (n : ℝ) ^ n * ZLattice.covolume L := by
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  exact lattice_flag_minima_product_le hn L c _ (fun i => norm_pos_iff.mpr (b.ne_zero i)) hb.monotone
    (by simpa [hflag] using hb.norm_le)

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A basis of integral lattice vectors, uniformly short in terms of the discriminant. -/
theorem exists_numberField_short_basis :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 2 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  let n := Module.finrank ℚ K
  let D := |(discr K : ℝ)|
  let L := mixedEmbedding.euclidean.integerLattice K
  have hn : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 ≤ D := abs_nonneg _
  obtain ⟨b, hb⟩ := exists_greedy_lattice_basis L (mixedEmbedding.euclidean.finrank K)
  obtain ⟨v, q, hq, hmap⟩ := exists_field_basis_of_euclidean_lattice_basis K b hb.mem
  have hcov : ZLattice.covolume L ≤ Real.sqrt D := by
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hp :=
    (greedy_lattice_product_le L hn b hb).trans (mul_le_mul_of_nonneg_left hcov (by positivity))
  refine ⟨b, hb.mem, fun k => ?_⟩
  have hw (i j) (h : q.coord k (q i * q j) ≠ 0)  := by
    apply (hb.norm_le k (euclideanNumberFieldEmbedding K (q i * q j)) ?_ ?_).trans
    · simpa [hmap] using euclideanNumberFieldEmbedding_norm_mul_le K (q i) (q j)
    · simpa [hq] using
        euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v j)
    · exact euclidean_notMem_basis_span_of_coordinate_ne_zero K b q hmap h (lt_irrefl k)
  have hmin := field_basis_minimum_product q k (fun i => ‖b i‖) (norm_nonneg _) hw
  rw [Fintype.card_fin] at hmin
  apply le_of_pow_le_pow_left₀ hn.ne' (by positivity)
  apply hmin.trans
  convert (sq_le_sq₀ (by positivity) (by positivity)).mpr hp using 1
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 n, Real.sq_sqrt hD,
    ← Real.rpow_mul_natCast hD, one_div_mul_cancel hnR.ne', Real.rpow_one]

end
end CCDN
