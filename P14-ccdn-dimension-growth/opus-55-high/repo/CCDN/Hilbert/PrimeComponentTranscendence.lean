/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.ForMathlib.KrullHeight
import CCDN.Hilbert.FilteredIntersection
import CCDN.Hilbert.FilteredHilbertLinearity
import Mathlib.FieldTheory.Minpoly.Basic

/-! A point on a prime component forces a transcendental coordinate and
 positive eventual Hilbert slope in codimension two. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ)

/-- Evaluate the first `n` coordinates, leaving all later coordinates free. -/
def partialCoordinateEval :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  eval₂Hom C (fun j => if j.val < n then C (c j) else X j)

/-- `partialCoordinateEval c n` fixes constants. -/
@[simp] lemma partialCoordinateEval_C (a : K) :
    partialCoordinateEval c n (C a) = C a := by simp [partialCoordinateEval]

/-- `partialCoordinateEval c n` replaces `X j` by `c j` for `j < n` and fixes the other variables.
-/
@[simp] lemma partialCoordinateEval_X (j : Fin 3) :
    partialCoordinateEval c n (X j) = if j.val < n then C (c j) else X j := by
  simp [partialCoordinateEval]

end

section
variable {K : Type*} (c : Fin 3 → K)

lemma partialCoordinateEval_comp [CommRing K]
    {m n : ℕ} (hmn : m ≤ n) :
    (partialCoordinateEval c n).comp (partialCoordinateEval c m) = partialCoordinateEval c n := by
  apply MvPolynomial.ringHom_ext
  · simp_all
  · intro j
    by_cases hj : j.val < m
    · have hn := hj.trans_le hmn
      simp_all
    · simp [hj]

lemma partialCoordinateEval_ker_lt [Field K]
    {n : ℕ} (hn : n < 3) :
    RingHom.ker (partialCoordinateEval c n) < RingHom.ker (partialCoordinateEval c (n + 1)) := by
  have hle : RingHom.ker (partialCoordinateEval c n) ≤
      RingHom.ker (partialCoordinateEval c (n + 1)) := by
    intro f hf
    have hcomp := congrArg (fun φ => φ f)
      (partialCoordinateEval_comp c (show n ≤ n + 1 by omega))
    change partialCoordinateEval c (n + 1) (partialCoordinateEval c n f) = _ at hcomp
    rw [hf, map_zero] at hcomp
    exact hcomp.symm
  apply lt_of_le_of_ne hle
  intro heq
  let j : Fin 3 := ⟨n, hn⟩
  have hmem : X j - C (c j) ∈ RingHom.ker (partialCoordinateEval c (n + 1)) := by aesop
  rw [← heq] at hmem
  have hzero : (X j - C (c j) : MvPolynomial (Fin 3) K) = 0 := by
    simpa [RingHom.mem_ker, j] using hmem
  have hc := congrArg (fun p => p.coeff (Finsupp.single j 1)) hzero
  have hsingle : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h
    have := DFunLike.congr_fun h j
    grind
  simp [hsingle] at hc

end

/-- An algebraic element detected by a base-field-valued point is scalar. -/
lemma algebraic_eq_scalar_of_point {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K) {y : A} (hy : IsAlgebraic K y) :
    algebraMap K A (φ y) = y := by
  have hi := hy.isIntegral
  have hroot : (minpoly K y).IsRoot (φ y) := by
    have he := Polynomial.aeval_algHom_apply φ y (minpoly K y)
    rw [minpoly.aeval, map_zero] at he
    tauto
  have hassoc := (Polynomial.irreducible_X_sub_C (φ y)).associated_of_dvd
    (minpoly.irreducible hi) (Polynomial.dvd_iff_isRoot.mpr hroot)
  have he : Polynomial.aeval y (Polynomial.X - Polynomial.C (φ y)) = 0 := by
    obtain ⟨r, hr⟩ := hassoc.symm.dvd
    simp_all
  simpa using (sub_eq_zero.mp (by simp_all)).symm

section
variable {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p)

/-- Evaluation at a rational point descends to its prime coordinate ring. -/
def coordinatePoint
    :
    (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
  Ideal.Quotient.liftₐ p (MvPolynomial.aeval z) (by
    intro f hf
    simpa [MvPolynomial.aeval_eq_eval] using hz f hf)

/-- Evaluation at the point `z` sends the class of `f` to `f(z)`. -/
@[simp] lemma coordinatePoint_mk
    (f : MvPolynomial σ K) :
    coordinatePoint p z hz ((Ideal.Quotient.mk p) f) = MvPolynomial.eval z f := by
  simp [coordinatePoint, Ideal.Quotient.liftₐ_apply]

end

variable {K : Type*} [Field K] (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2) (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p)
include hp hz

/-- A height-two prime in three variables containing a rational point retains a
transcendental coordinate over its base field. -/
theorem height_two_transcendental_coordinate_of_point
    :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  by_contra h
  push Not at h
  have ha (j : Fin 3) : IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) := by
    simpa [Transcendental, not_not] using h j
  have hc (j : Fin 3) : algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (z j) =
      (Ideal.Quotient.mk p) (X j) := by
    simpa using algebraic_eq_scalar_of_point (coordinatePoint p z hz) (ha j)
  have hcomp : (Ideal.Quotient.mk p).comp (partialCoordinateEval z 3) = Ideal.Quotient.mk p := by aesop
  have hle : RingHom.ker (partialCoordinateEval z 3) ≤ p := by
    intro f hf
    have he := congrArg (fun φ => φ f) hcomp
    change (Ideal.Quotient.mk p) (partialCoordinateEval z 3 f) = _ at he
    rw [hf, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  have hd := (show 3 ≤ (RingHom.ker (partialCoordinateEval z 3)).height by
      let inst (n : ℕ) : (RingHom.ker (partialCoordinateEval z n)).IsPrime := RingHom.ker_isPrime _
      have h0 := Ideal.height_add_one_le_of_lt_of_isPrime
        (partialCoordinateEval_ker_lt z (n := 0) (by omega))
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
        (partialCoordinateEval_ker_lt z (n := 1) (by omega))
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
        (partialCoordinateEval_ker_lt z (n := 2) (by omega))
      have h01 : (1 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval z 1)).height := by
        calc
          1 = (0 : ℕ∞) + 1 := by norm_num
          _ ≤ (RingHom.ker (partialCoordinateEval z 0)).height + 1 := by simp_all
          _ ≤ _ := h0
      have h12 : (2 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval z 2)).height := by
        calc
          2 = (1 : ℕ∞) + 1 := by norm_num
          _ ≤ (RingHom.ker (partialCoordinateEval z 1)).height + 1 := by gcongr
          _ ≤ _ := h1
      calc
        3 = (2 : ℕ∞) + 1 := by norm_num
        _ ≤ (RingHom.ker (partialCoordinateEval z 2)).height + 1 := by gcongr
        _ ≤ _ := h2).trans (Ideal.height_mono hle)
  rw [hp] at hd
  norm_num at hd

/-- A height-two component with a base-field point has positive slope in
 any eventual linear Hilbert formula, independently of its cutoff. -/
theorem height_two_eventual_slope_pos_of_point
    {d : ℕ}
    (hlinear : HasFilteredCurveDegree p d) :
    0 < d := by
  obtain ⟨N, c, hlinear⟩ := hlinear
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  by_contra h
  have hd0 : d = 0 := by omega
  have hlo := transcendental_coordinate_filtered_lower p hj (N + c.natAbs)
  have hhi := hlinear (N + c.natAbs) (by omega)
  rw [hd0] at hhi
  simp at hhi
  have habs : c ≤ c.natAbs := Int.le_natAbs
  have hlo' : ((N + c.natAbs + 1 : ℕ) : ℤ) ≤
      (Module.finrank K (filteredCoordinateSpace p (N + c.natAbs)) : ℤ) := mod_cast hlo
  push_cast at hlo'
  omega

