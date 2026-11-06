/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.LatticePrescribedMinima
public import CCDN.ClassGroup.NumberFieldEuclideanLattice
import CCDN.ClassGroup.EuclideanNumberFieldBasis
import CCDN.ClassGroup.FieldBasisMultiplicationProduct
import CCDN.ClassGroup.LatticeMinimaFlag
import CCDN.ClassGroup.LatticeMinimaProduct

/-!
Short independent algebraic integers at the uniform discriminant-root
scale, from greedy lattice vectors, the multiplication pairing, and the
covolume estimate.

The product-of-lengths bound for a prescribed first lattice vector.
Each later vector is shortest outside the preceding span, and the covolume
bound for positive monotone flag thresholds applies.

Numerical conversion of a lattice norm-product bound into the uniform
discriminant-root scale for its largest minimum.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Module NumberField MeasureTheory
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- A real basis of integral lattice vectors with an explicit
constant depending only on the field degree. -/
theorem exists_numberField_short_basis
    (hd : 2 ≤ Module.finrank ℚ K) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℝ (mixedEmbedding.euclidean.mixedSpace K),
      (∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K) ∧
      ∀ i, ‖b i‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank ℚ K = n + 2 := ⟨Module.finrank ℚ K - 2, by omega⟩
  rw [hn]
  let m := n + 2
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := mod_cast hm0
  have hm1 : (1 : ℝ) ≤ m := mod_cast hm0
  let L := mixedEmbedding.euclidean.integerLattice K
  let w := euclideanNumberFieldEmbedding K 1
  have hw : w ∈ L := euclideanNumberFieldEmbedding_mem_integerLattice K 1
  have hw0 : w ≠ 0 := (map_ne_zero (euclideanNumberFieldEmbedding K)).mpr one_ne_zero
  have hdim : Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K) = (n + 1) + 1 := by
    rw [mixedEmbedding.euclidean.finrank, hn]
  obtain ⟨b, hb⟩ := exists_prescribed_greedy_lattice_basis L w hw hw0 hdim
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  have hlower (x) (hx : x ∈ L) (hx0 : x ≠ 0) : (1 : ℝ) ≤ ‖x‖ :=
    one_le_euclidean_integerLattice_norm K hx hx0
  have hprod_flag := lattice_flag_minima_product_le (n := n + 1 + 1) (by omega) L c
    (prescribedLatticeMinima b 1) (hb.minima_pos one_pos) (hb.minima_mono hlower)
    (fun i x hx hxU => hb.minima_outside hlower i x hx (by rwa [← hflag i]))
  have hprod : (∏ i, ‖b i‖) ≤ ‖w‖ * (m : ℝ) ^ m * ZLattice.covolume L := by
    rw [prescribedLatticeMinima_prod b hb.first_eq one_ne_zero, div_one]
    simpa only [m, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show n + 1 + 1 = n + 2 by omega, show (n : ℝ) + 1 + 1 = n + 2 by ring, mul_assoc] using
      mul_le_mul_of_nonneg_left hprod_flag (norm_nonneg w)
  let D := |(discr K : ℝ)|
  have hD : 1 ≤ D := by
    have hz : (0 : ℤ) < |discr K| := abs_pos.mpr (discr_ne_zero K)
    dsimp only [D]
    exact_mod_cast (by omega : (1 : ℤ) ≤ |discr K|)
  have hcov : ZLattice.covolume L ≤ Real.sqrt D := by
    change ZLattice.covolume (mixedEmbedding.euclidean.integerLattice K) ≤ _
    rw [euclidean_integerLattice_covolume]
    exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))
  have hwbound : ‖w‖ ≤ Real.sqrt m := by
    simpa only [hn] using euclideanNumberFieldEmbedding_one_norm_le K
  let P := ∏ i, ‖b i‖
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg (b i)
  have hprod' : P ≤ Real.sqrt m * (m : ℝ) ^ m * Real.sqrt D :=
    hprod.trans (mul_le_mul (mul_le_mul_of_nonneg_right hwbound (by positivity)) hcov
      (ZLattice.covolume_pos L _).le (by positivity))
  have hmin_pow : ‖b (Fin.last (n + 1))‖ ^ m ≤ P ^ 2 := by
    obtain ⟨v, q, hq, hmap⟩ := exists_field_basis_of_euclidean_lattice_basis K b hb.mem
    have hpq : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := fun he => by
      have := congrArg Fin.val he; simp at this
    have hq0 : q 0 = 1 :=
      euclideanNumberFieldEmbedding_injective K (by rw [hmap, hb.first_eq])
    have hunit : 1 ≤ ‖euclideanNumberFieldEmbedding K (q 0)‖ := by
      rw [hq0]; exact one_le_euclidean_norm_integer K (x := 1) one_ne_zero
    have hmin (i j : {i : Fin (n + 2) // i ≠ 0 ∧ i ≠ Fin.last (n + 1)})
        (hij : q.coord (Fin.last (n + 1)) (q i * q j) ≠ 0) :
        ‖euclideanNumberFieldEmbedding K (q (Fin.last (n + 1)))‖ ≤
          ‖euclideanNumberFieldEmbedding K (q i * q j)‖ := by
      rw [hmap]
      refine hb.norm_le hpq.symm ?_
        (euclidean_notMem_basis_span_of_coordinate_ne_zero K b q hmap hij (by simp))
      simpa only [hq, RingOfIntegers.coe_eq_algebraMap, map_mul] using
        euclideanNumberFieldEmbedding_mem_integerLattice K (v i * v j)
    simpa only [Fintype.card_fin, hmap] using field_basis_multiplication_minimum_product q 0
      (Fin.last (n + 1)) hpq hq0 (fun x => ‖euclideanNumberFieldEmbedding K x‖)
      (fun _ => norm_nonneg _) (euclideanNumberFieldEmbedding_norm_mul_le K) hunit hmin
  have hlast : ‖b (Fin.last (n + 1))‖ ≤ (m : ℝ) ^ 3 * D ^ (1 / (m : ℝ)) := by
    have hsq : P ^ 2 ≤ (m : ℝ) ^ (2 * m + 1) * D := by
      convert (sq_le_sq₀ hP (by positivity)).mpr hprod' using 1
      rw [mul_pow, mul_pow, Real.sq_sqrt hmR.le, Real.sq_sqrt (by positivity), pow_succ, pow_mul]
      ring
    have hroot : (D ^ (1 / (m : ℝ))) ^ m = D := by
      rw [← Real.rpow_mul_natCast (by positivity), one_div_mul_cancel hmR.ne', Real.rpow_one]
    apply le_of_pow_le_pow_left₀ hm0.ne' (by positivity)
    rw [mul_pow, ← pow_mul, hroot]
    exact hmin_pow.trans (hsq.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hm1 (by omega : 2 * m + 1 ≤ 3 * m)) (by positivity)))
  refine ⟨b, hb.mem, fun i => ?_⟩
  change ‖b i‖ ≤ (m : ℝ) ^ 3 * D ^ (1 / (m : ℝ))
  by_cases hi : i = 0
  · rw [hi, hb.first_eq]
    have hsqrt : Real.sqrt m ≤ (m : ℝ) :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hmR.le).mp (by rw [Real.sq_sqrt hmR.le]; nlinarith)
    have hcube : (m : ℝ) ≤ (m : ℝ) ^ 3 := by simpa using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 3)
    have hroot1 : 1 ≤ D ^ (1 / (m : ℝ)) := Real.one_le_rpow hD (by positivity)
    exact hwbound.trans ((hsqrt.trans hcube).trans
      (by simpa using mul_le_mul_of_nonneg_left hroot1 (by positivity : 0 ≤ (m : ℝ) ^ 3)))
  · exact (hb.norm_le hi (hb.mem _)
      (b.linearIndependent.notMem_span_image (not_lt_of_ge (Fin.le_last i)))).trans hlast

end
end CCDN
