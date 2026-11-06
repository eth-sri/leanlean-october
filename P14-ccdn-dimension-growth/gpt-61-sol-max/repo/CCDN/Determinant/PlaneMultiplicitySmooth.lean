/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.SingularReduction
import CCDN.Determinant.PlaneSingularities

/-! Multiplicity greater than one forces a singular point. -/

public section
namespace CCDN
open MvPolynomial

variable {K σ : Type*} [Field K]


variable (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ}

/-- Only singular points can have local order at least two. -/
theorem singular_of_origin_order_ge_two 
     (hμ : 2 ≤ μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ) :
    ∀ j, eval a (pderiv j f) = 0 := by
  intro j
  rw [← eval_zero_originShift, ← pderiv_originShift]
  exact (by
          classical
          rw [mem_pow_idealOfVars_iff'] at hf
          have hc := hf (Finsupp.single j 1)
            (by simp; omega)
          simpa only [eval_zero, constantCoeff_eq, coeff_pderiv, zero_add,
            Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one] using hc)

/-- In particular, every positive order at a smooth point is one. -/
theorem origin_order_eq_one_of_smooth 
     (hμ : 0 < μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ)
    (hs : ∃ j, eval a (pderiv j f) ≠ 0) : μ = 1 := by
  by_contra h
  obtain ⟨j, hj⟩ := hs
  exact hj (singular_of_origin_order_ge_two f a (by omega) hf j)

private lemma planeResidueMultiplicity_singular {p : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial 2) (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (a : PlaneResidue f p) (ha : 2 ≤ planeResidueMultiplicity f p hf a) :
    ∀ j, eval a.val (pderiv j (map (Int.castRingHom (ZMod p)) f)) = 0 := by
  have hp := (planeResidueMultiplicity_spec f p hf a).2.2.1
  rw [originShift_map] at hp
  have he : (fun j => (Int.castRingHom (ZMod p)) (planeResidueLift a j)) = a.val := by
    simp_all [cast_planeResidueLift]
  rw [he] at hp
  exact singular_of_origin_order_ge_two _ a.val ha hp

/-- The multiplicity correction costs only a degree-dependent constant.
The leading term remains the number of finite-field points. -/
theorem planeTotalMultiplicity_le_card_add_correction {p : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial 2)
    (hf : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hpos : 0 < (map (Int.castRingHom (ZMod p)) f).totalDegree)
    (hchar : f.totalDegree < p) :
    planeTotalMultiplicity f p hf.ne_zero ≤
      Fintype.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1) := by
  classical
  let S :=
    Finset.univ.filter (fun a => 2 ≤ planeResidueMultiplicity f p hf.ne_zero a)
  have hd : (map (Int.castRingHom (ZMod p)) f).totalDegree ≤ f.totalDegree := by
    grind [map_eq_eval₂Hom_C_comp, linear_eval₂_totalDegree_le, totalDegree_X]
  have hS : S.card ≤ f.totalDegree * (f.totalDegree - 1) := by
    have hc := plane_singular_points_card_le  _ hf hpos (hd.trans_lt hchar)
      (fun a : S => a.val.val)
      (fun a b h => Subtype.ext (Subtype.ext h))
      (fun a => by grind [eval_map])
      (fun a j => planeResidueMultiplicity_singular f hf.ne_zero a.val
        (Finset.mem_filter.mp a.property).2 j)
    have hc' : S.card ≤ (map (Int.castRingHom (ZMod p)) f).totalDegree *
        ((map (Int.castRingHom (ZMod p)) f).totalDegree - 1) := by simpa using hc
    exact hc'.trans (Nat.mul_le_mul hd (Nat.sub_le_sub_right hd 1))
  have hpoint (a : PlaneResidue f p) : planeResidueMultiplicity f p hf.ne_zero a ≤
      1 + if a ∈ S then f.totalDegree else 0 := by
    grind [CCDN.planeResidueMultiplicity]
  have hsum : planeTotalMultiplicity f p hf.ne_zero ≤
      Fintype.card (PlaneResidue f p) + S.card * f.totalDegree := by
    calc _ ≤ ∑ a : PlaneResidue f p, (1 + if a ∈ S then f.totalDegree else 0) :=
           Finset.sum_le_sum fun a _ => hpoint a
         _ = _ := by simp [Finset.sum_add_distrib]
  nlinarith

end CCDN
