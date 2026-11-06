/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.ForMathlib.KrullHeight
public import CCDN.Hilbert.FilteredIntersection
import CCDN.Hilbert.FilteredHilbertLinearity
import Mathlib.FieldTheory.Minpoly.Basic

/-! A point on a prime component forces a transcendental coordinate and
 positive eventual Hilbert slope in codimension two. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluate the first `n` coordinates, leaving all later coordinates free. -/
def partialCoordinateEval {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  eval₂Hom C (fun j => if j.val < n then C (c j) else X j)

/-- `partialCoordinateEval c n` fixes constants. -/
@[simp] lemma partialCoordinateEval_C {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (a : K) :
    partialCoordinateEval c n (C a) = C a := by simp [partialCoordinateEval]

/-- `partialCoordinateEval c n` replaces `X j` by `c j` for `j < n` and fixes the other variables.
-/
@[simp] lemma partialCoordinateEval_X {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (j : Fin 3) :
    partialCoordinateEval c n (X j) = if j.val < n then C (c j) else X j := by
  simp [partialCoordinateEval]

/-- An algebraic element detected by a base-field-valued point is scalar. -/
lemma algebraic_eq_scalar_of_point {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K) {y : A} (hy : IsAlgebraic K y) :
    algebraMap K A (φ y) = y := by
  have hroot : (minpoly K y).IsRoot (φ y) := by
    have he := Polynomial.aeval_algHom_apply φ y (minpoly K y)
    rw [minpoly.aeval, map_zero] at he
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using he
  obtain ⟨r, hr⟩ := ((Polynomial.irreducible_X_sub_C (φ y)).associated_of_dvd
    (minpoly.irreducible hy.isIntegral) (Polynomial.dvd_iff_isRoot.mpr hroot)).symm.dvd
  have he : Polynomial.aeval y (Polynomial.X - Polynomial.C (φ y)) = 0 := by
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  simpa using (sub_eq_zero.mp (by simpa using he)).symm

/-- Evaluation at a rational point descends to its prime coordinate ring. -/
def coordinatePoint {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p) :
    (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
  Ideal.Quotient.liftₐ p (MvPolynomial.aeval z) fun f hf => by
    simpa only [MvPolynomial.aeval_eq_eval] using hz f hf

/-- Evaluation at the point `z` sends the class of `f` to `f(z)`. -/
@[simp] lemma coordinatePoint_mk {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p)
    (f : MvPolynomial σ K) :
    coordinatePoint p z hz ((Ideal.Quotient.mk p) f) = MvPolynomial.eval z f := by
  simp [coordinatePoint, Ideal.Quotient.liftₐ_apply]

/-- A height-two prime in three variables containing a rational point retains a
transcendental coordinate over its base field. -/
theorem height_two_transcendental_coordinate_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  classical
  by_contra! h
  have hlt {n : ℕ} (hn : n < 3) :
      RingHom.ker (partialCoordinateEval z n) < RingHom.ker (partialCoordinateEval z (n + 1)) := by
    have hcomp : (partialCoordinateEval z (n + 1)).comp (partialCoordinateEval z n) =
        partialCoordinateEval z (n + 1) :=
      MvPolynomial.ringHom_ext (fun _ => by simp) fun j => by
        by_cases hj : j.val < n <;> simp [hj, show j.val < n → j.val < n + 1 by omega]
    refine lt_of_le_of_ne (fun f hf => ?_) fun heq => ?_
    · have h := RingHom.congr_fun hcomp f
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero] at h
      exact h.symm
    · let j : Fin 3 := ⟨n, hn⟩
      have hmem : X j - C (z j) ∈ RingHom.ker (partialCoordinateEval z n) := by
        rw [heq]; simp [RingHom.mem_ker, j]
      have hc := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single j 1))
        (by simpa [RingHom.mem_ker, j] using hmem : (X j - C (z j) : MvPolynomial (Fin 3) K) = 0)
      simp [show (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 from fun h0 => by
        simpa using DFunLike.congr_fun h0 j] at hc
  have ha (j : Fin 3) : IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) := by
    simpa only [Transcendental, not_not] using h j
  have hc (j : Fin 3) : algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (z j) =
      (Ideal.Quotient.mk p) (X j) := by
    simpa using algebraic_eq_scalar_of_point (coordinatePoint p z hz) (ha j)
  have hcomp : (Ideal.Quotient.mk p).comp (partialCoordinateEval z 3) = Ideal.Quotient.mk p :=
    MvPolynomial.ringHom_ext (fun _ => by simp) fun j => by
      simp only [RingHom.comp_apply, partialCoordinateEval_X, ite_eq_left j.isLt]
      exact hc j
  have hle : RingHom.ker (partialCoordinateEval z 3) ≤ p := fun f hf => by
    have he := RingHom.congr_fun hcomp f
    rw [RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  let inst (n : ℕ) : (RingHom.ker (partialCoordinateEval z n)).IsPrime := RingHom.ker_isPrime _
  have h01 : (1 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval z 1)).height :=
    (by gcongr; exact bot_le : (0 : ℕ∞) + 1 ≤ _).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (hlt (n := 0) (by omega)))
  have h12 : (2 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval z 2)).height :=
    (by gcongr : (1 : ℕ∞) + 1 ≤ _).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (hlt (n := 1) (by omega)))
  have hd : (3 : ℕ∞) ≤ p.height :=
    ((by gcongr : (2 : ℕ∞) + 1 ≤ _).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (hlt (n := 2) (by omega)))).trans
      (Ideal.height_mono hle)
  rw [hp] at hd
  norm_num at hd

/-- A height-two component with a base-field point has positive slope in
 any eventual linear Hilbert formula, independently of its cutoff. -/
theorem height_two_eventual_slope_pos_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) {d : ℕ}
    (hlinear : HasFilteredCurveDegree p d) :
    0 < d := by
  obtain ⟨N, c, hlinear⟩ := hlinear
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  by_contra! hd0
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hlo : ((N + c.natAbs + 1 : ℕ) : ℤ) ≤
      (Module.finrank K (filteredCoordinateSpace p (N + c.natAbs)) : ℤ) := by
    exact_mod_cast transcendental_coordinate_filtered_lower p hj (N + c.natAbs)
  have hhi := hlinear (N + c.natAbs) (by omega)
  rw [Nat.le_zero.mp hd0] at hhi
  simp only [Nat.cast_zero, zero_mul, zero_add] at hhi
  rw [hhi] at hlo
  push_cast at habs hlo
  omega

end
end CCDN
