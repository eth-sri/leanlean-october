/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.CurvePrimitivePair
import CCDN.Projection.InfinityParameterReduction
import CCDN.Projection.BoundedInfinityAvoidance
import CCDN.Projection.InfinityChartCardinality
import CCDN.Projection.InfinityScaling

/-! Finite normalized charts give a bounded integral moment parameter
avoiding every nonzero infinity direction. -/

namespace CCDN
section
open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

lemma momentCoordinate_aeval
    (k : ℕ) (z : Fin n → L) :
    aeval z (momentCoordinate K n k) = ∑ j : Fin n, z j * (k : L) ^ j.val := by
  simp [momentCoordinate, mul_comm]

/-- The first coordinate can be chosen with an explicit bound n²*d on its
integer moment parameter. The overlap between normalized charts is harmless. -/
theorem exists_bounded_infinity_parameter
    [CharZero L] (I : Ideal (MvPolynomial (Fin n) K)) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d) :
    ∃ k : ℕ, k ≤ n ^ 2 * d ∧
      ∀ z ∈ MvPolynomial.zeroLocus L
        (leadingInfinityIdeal I ⊔ Ideal.span {momentCoordinate K n k}), z = 0 := by
  choose S hcard hS using (fun j => exists_finite_infinity_chart (L := L) I d hdegree j)
  let T := (j : Fin n) × {z : Fin n → L // z ∈ S j}
  let v (t : T) := t.2.val
  have hv (t : T) : v t ≠ 0 := by aesop
  have hT : Fintype.card T ≤ n * d := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _j : Fin n, d := Finset.sum_le_sum (fun j _ => by simp_all)
      _ = _ := by simp
  obtain ⟨k, hk, hnon⟩ := exists_bounded_moment_nonvanishing v hv
  refine ⟨k, hk.trans (by nlinarith), ?_⟩
  intro z hz
  by_contra hzne
  obtain ⟨j, hj⟩ : ∃ j : Fin n, z j ≠ 0 := by
    by_contra! he
    exact hzne (funext he)
  have hzI :=
    fun f hf => hz f ((le_sup_left : leadingInfinityIdeal I ≤
      leadingInfinityIdeal I ⊔ Ideal.span {momentCoordinate K n k}) hf)
  let w : Fin n → L := fun i => (z j)⁻¹ * z i
  have hw := (hS j w).mpr
    ⟨infinity_zeroLocus_scale I z hzI (z j)⁻¹, by grind⟩
  let t : T := ⟨j, w, hw⟩
  have hwzero : aeval w (momentCoordinate K n k) = 0 := by
    rw [homogeneous_aeval_scale _ (momentCoordinate_homogeneous K n k)]
    have hz0 := hz (momentCoordinate K n k)
      ((le_sup_right : Ideal.span {momentCoordinate K n k} ≤
        leadingInfinityIdeal I ⊔ Ideal.span {momentCoordinate K n k})
        (Ideal.subset_span (Set.mem_singleton _)))
    grind
  apply hnon t
  rwa [momentCoordinate_aeval] at hwzero

