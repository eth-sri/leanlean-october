/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Determinant.HeightDeterminant
public import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryDegree
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryLargeHeight
import CCDN.Determinant.PolynomialMapDeterminant

/-!
Auxiliary nonmultiples and explicit degree choices for polynomial images
of the original integer plane curve. Sharp finite-field counts remain explicit.

Explicit integer degree choices for both coefficient-height ranges.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- For nonnegative reals `l` and `R`, there is an integer `M` with `d ≤ M`, `l ≤ M`, `R < M` and
`M ≤ d + l + R + 2`. -/
lemma auxiliary_integer_degree_selection (d : ℕ) {l R : ℝ} (hl : 0 ≤ l) (hR : 0 ≤ R) :
    ∃ M : ℕ, d ≤ M ∧ l ≤ M ∧ R < M ∧ (M : ℝ) ≤ d + l + R + 2 := by
  refine ⟨d + ⌈l⌉₊ + ⌊R⌋₊ + 1, by omega, ?_, ?_, ?_⟩
  · push_cast
    linarith [Nat.le_ceil l, show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌊R⌋₊ by positivity]
  · push_cast
    linarith [Nat.lt_floor_add_one R, show (0 : ℝ) ≤ d by positivity, show (0 : ℝ) ≤ ⌈l⌉₊ by positivity]
  · push_cast
    linarith [Nat.ceil_lt_add_one hl, Nat.floor_le hR]

/-- Small-height auxiliary form for polynomial images of a plane curve: if the points `τ (z i)` are
images of integral points `z i` on a bounded plane curve `q` of degree `d` and are integral zeros
of the degree-`d` form `f` in a box of radius `B`, the leading coefficient of `f` has logarithm
at most `4 d log B`, and `q` satisfies the residue count bound with constant `C`, then there is
an auxiliary form of explicitly bounded degree `M` through all of them. -/
theorem polynomial_map_auxiliary_small_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ M : ℕ, (M : ℝ) ≤ d + Real.log B +
      2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
        (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
          |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) + 2 ∧
      ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  classical
  let R := 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
    (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
      |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2)
  have hB := himage.one_le_radius
  have hH := hq.one_le_height
  have hlogH := Real.log_nonneg hH
  have hB0 : 0 ≤ B := by linarith
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨M, hdM, hML, hth, hM⟩ := auxiliary_integer_degree_selection d (Real.log_nonneg hB) hR
  refine ⟨M, hM, ?_⟩
  by_contra hnone
  obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hq τ z hz himage hC (dvd_of_not_exists_isPointAuxiliary hnone) hcount
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| :=
    mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound hd hdM hr hB hL hML hheight hc
  exact (not_lt_of_ge (plane_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith) (by linarith) (by positivity) hlog)) hth

/-- Large-height auxiliary form for polynomial images of a plane curve: if the points `τ (z i)` are
images of integral points `z i` on a bounded plane curve `q` of degree `d` and height `H` and are
integral zeros of the degree-`d` form `f` in a box of radius `B`, with `4 d log B ≤ log H`, `H`
at most the leading coefficient of `f` times `exp (T d²)`, and `q` satisfying the residue count
bound with constant `C`, then there is an auxiliary form through all of them of degree at most
`(34 + 8 exp (heightDeterminantError C + 6 + T)) d³`. -/
theorem polynomial_map_auxiliary_large_height_degree
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => MvPolynomial.eval (z i) (τ j)))
    (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ M : ℕ, (M : ℝ) ≤ (34 + 8 * Real.exp (heightDeterminantError C + 6 + T)) * (d : ℝ) ^ 3 ∧
      ∃ g, IsPointAuxiliary f g M (fun i j => MvPolynomial.eval (z i) (τ j)) := by
  classical
  let R := 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨M, hMlarge, _, hth, hM⟩ := auxiliary_integer_degree_selection (32 * d)
    (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  refine ⟨M, ?_, ?_⟩
  · dsimp only [R] at hM; push_cast at hM
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  · by_contra hnone
    have hdM : d ≤ M := by omega
    obtain ⟨s, _, _, hr, hc⟩ := polynomial_map_no_auxiliary_height_comparison
      order f hf hf0 hd hdM hq τ z hz himage hC (dvd_of_not_exists_isPointAuxiliary hnone) hcount
    have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| :=
      mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
    have hlog := plane_auxiliary_large_height_log_bound hd hMlarge hr
      himage.one_le_radius hL hq.one_le_height hT hheight hposition hc
    exact (not_lt_of_ge (plane_large_degree_bound_of_log_bound hd
      (lt_of_lt_of_le hd hdM) hlog)) hth

end
end CCDN
