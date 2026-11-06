/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Integral

/-! Positive Hilbert growth forces any parameter generating the eventual
filtration recurrence to be transcendental. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A parameter giving eventual filtered generation on a positive-degree
curve cannot satisfy a polynomial over the ground field. -/
theorem recurrence_parameter_transcendental {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ) (hd : 0 < d)
    (hdegree : HasFilteredCurveDegree I d)
    (l : MvPolynomial σ K) (N : ℕ)
    (hrec : ∀ m ≥ N, filteredCoordinateSpace I (m + 1) =
      filteredCoordinateSpace I m ⊔ (filteredCoordinateSpace I m).map
        (LinearMap.mulLeft K ((Ideal.Quotient.mk I) l))) :
    Transcendental K ((Ideal.Quotient.mk I) l) := by
  intro ha
  let u := (Ideal.Quotient.mk I) l
  let S := Algebra.adjoin K {u}
  let W := S.toSubmodule * filteredCoordinateSpace I N
  let : Module.Finite K W := Module.Finite.of_fg
    (ha.isIntegral.fg_adjoin_singleton.mul (Submodule.FG.of_finite (N := filteredCoordinateSpace I N)))
  have hstable : W.map (LinearMap.mulLeft K u) ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mul_induction_on hx (fun s hs x hx => ?_) (fun x y hx hy => ?_)
    · rw [show LinearMap.mulLeft K u (s * x) = (u * s) * x from (mul_assoc _ _ _).symm]
      exact Submodule.mul_mem_mul
        (S.mul_mem (Algebra.subset_adjoin (Set.mem_singleton u)) hs) hx
    · rw [map_add]; exact W.add_mem hx hy
  have hmem (m : ℕ) : filteredCoordinateSpace I (N + m) ≤ W := by
    induction m with
    | zero =>
      intro x hx
      simpa only [Nat.add_zero, one_mul] using
        Submodule.mul_mem_mul (show (1 : MvPolynomial σ K ⧸ I) ∈ S.toSubmodule from S.one_mem) hx
    | succ m hm =>
      rw [Nat.add_succ, hrec (N + m) (by omega)]
      exact sup_le hm ((Submodule.map_mono hm).trans hstable)
  let D := Module.finrank K W
  obtain ⟨M, c, hM⟩ := hdegree
  let m := D + c.natAbs + M + 1
  have he := hM (N + m) (by dsimp [m]; omega)
  push_cast at he
  have hb : (d : ℤ) * (N + m) + c ≤ D := by
    rw [← he]
    exact_mod_cast Submodule.finrank_mono (hmem m)
  have hd1 : (1 : ℤ) ≤ d := mod_cast hd
  have hc : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at hh; omega
  have hm : (m : ℤ) = D + c.natAbs + M + 1 := by simp [m]
  nlinarith

end
end CCDN
