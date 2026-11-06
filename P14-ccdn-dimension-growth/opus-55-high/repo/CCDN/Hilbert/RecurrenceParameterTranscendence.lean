/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredIntersection
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Integral

/-! Positive Hilbert growth forces any parameter generating the eventual
filtration recurrence to be transcendental. -/

namespace CCDN
section

lemma algebraic_parameter_recurrence_bounded {K A : Type*} [Field K]
    [CommRing A] [Algebra K A] (u : A) (hu : IsAlgebraic K u)
    (V : ℕ → Submodule K A) [∀ m, Module.Finite K (V m)]
    (N : ℕ) (hrec : ∀ m ≥ N, V (m + 1) = V m ⊔ (V m).map (LinearMap.mulLeft K u)) :
    ∃ D : ℕ, ∀ m : ℕ, Module.finrank K (V (N + m)) ≤ D := by
  let S := Algebra.adjoin K {u}
  let W := S.toSubmodule * V N
  let : Module.Finite K W := Module.Finite.of_fg
    (hu.isIntegral.fg_adjoin_singleton.mul (Submodule.FG.of_finite))
  have hbase : V N ≤ W := by
    intro x hx
    have hh :=
      Submodule.mul_mem_mul (show (1 : A) ∈ S.toSubmodule from S.one_mem) hx
    grind
  have hmem (m : ℕ) : V (N + m) ≤ W := by
    induction m with
    | zero => simpa using hbase
    | succ m hm =>
      rw [Nat.add_succ, hrec (N + m) (by omega)]
      exact sup_le hm ((Submodule.map_mono hm).trans (by
        rintro _ ⟨x, hx, rfl⟩
        change u * x ∈ W
        refine Submodule.mul_induction_on hx ?_ ?_
        · intro s hs x hx
          rw [← mul_assoc]
          exact Submodule.mul_mem_mul
            (show u * s ∈ S.toSubmodule from
              S.mul_mem (Algebra.subset_adjoin (Set.mem_singleton u)) hs) hx
        · intro x y hx hy
          rw [mul_add]
          exact W.add_mem hx hy))
  exact ⟨Module.finrank K W, fun m => Submodule.finrank_mono (hmem m)⟩

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
  obtain ⟨D, hD⟩ := algebraic_parameter_recurrence_bounded ((Ideal.Quotient.mk I) l)
    ha (filteredCoordinateSpace I) N hrec
  obtain ⟨M, c, hM⟩ := hdegree
  let m := D + c.natAbs + M + 1
  have he := hM (N + m) (by grind)
  push_cast at he
  have hb : d * (N + m) + c ≤ D := by
    rw [← he]
    exact_mod_cast hD m
  have hd1 : (1 : ℤ) ≤ d := mod_cast hd
  have hc : -(c.natAbs : ℤ) ≤ c := by grind
  have hm : (m : ℤ) = D + c.natAbs + M + 1 := by grind
  nlinarith

