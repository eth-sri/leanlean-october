/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NumberFieldEuclideanLattice
public import CCDN.ClassGroup.LatticeGreedyBasis
import CCDN.ClassGroup.EuclideanNumberFieldBasis
import CCDN.ClassGroup.LatticeMinimaFlag
import CCDN.ClassGroup.LatticeMinimaProduct
import CCDN.ClassGroup.MultiplicationPairingProduct

/-! The product-of-minima bound and the nondegenerate multiplication pairing
bound the last minimum, hence every vector of a greedy basis. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module NumberField
open scoped NumberField
open Classical

/-- A real basis of integral lattice vectors with a bound depending only on the degree and
absolute discriminant. -/
theorem exists_numberField_short_basis (K : Type*) [Field K] [NumberField K]
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 2 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  let n := finrank ℚ K
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  let D := |(discr K : ℝ)|
  let L := mixedEmbedding.euclidean.integerLattice K
  obtain ⟨b, hmem, hmin⟩ := exists_greedy_lattice_basis L (mixedEmbedding.euclidean.finrank K)
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  have hmono : Monotone (fun i => ‖b i‖) := fun _ j hij =>
    hmin _ (b j) (hmem j) (b.linearIndependent.notMem_span_image (not_lt_of_ge hij))
  have hprod := lattice_flag_minima_product_le hn L c (fun i => ‖b i‖)
    (fun i => norm_pos_iff.mpr (b.linearIndependent.ne_zero i)) hmono
    (fun i x hx hxU => hmin i x hx (by simpa only [hflag] using hxU))
  let j : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨v, q, hq, he⟩ := exists_field_basis_of_euclidean_lattice_basis K b hmem
  have hminMul (i k : Fin n) (hik : q.coord j (q i * q k) ≠ 0) : ‖b j‖ ≤ ‖b i‖ * ‖b k‖ := by
    rw [← he i, ← he k]
    apply le_trans _ (euclideanNumberFieldEmbedding_norm_mul_le K (q i) (q k))
    refine hmin j _ ?_ (euclidean_notMem_basis_span_of_coordinate_ne_zero K b q he hik (by simp))
    simpa only [hq, map_mul, RingOfIntegers.coe_eq_algebraMap] using
      euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v k)
  have hpow := basis_multiplication_product q j (fun i => ‖b i‖) (norm_nonneg _) hminMul
  rw [Fintype.card_fin] at hpow
  have hcov : ZLattice.covolume L ≤ Real.sqrt D := by
    dsimp only [L, D]
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hlast : ‖b j‖ ≤ (n : ℝ) ^ 2 * D ^ (1 / (n : ℝ)) := by
    apply le_of_pow_le_pow_left₀ hn.ne' (by positivity)
    calc
      _ ≤ ((n : ℝ) ^ n * Real.sqrt D) ^ 2 := hpow.trans (pow_le_pow_left₀ (by positivity)
        (hprod.trans (mul_le_mul_of_nonneg_left hcov (by positivity))) 2)
      _ = _ := by
        rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow,
          ← Real.rpow_mul_natCast (by positivity : 0 ≤ D), one_div_mul_cancel hnR.ne', Real.rpow_one,
          ← pow_mul, ← pow_mul, Nat.mul_comm n 2]
  exact ⟨b, hmem, fun i => (hmono (by change i.val ≤ n - 1; omega : i ≤ j)).trans hlast⟩

end
end CCDN
