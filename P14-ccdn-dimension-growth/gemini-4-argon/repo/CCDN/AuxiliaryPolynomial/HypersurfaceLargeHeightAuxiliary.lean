/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
public import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary

/-! Auxiliary polynomials in the large-height range. The degree is
O_{n,T}(d^(4-1/(n+1))); the leading-coefficient positioning cost is explicit. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Select a bounded integer degree in the large-height range. The bound is
independent of the box radius and the equation's coefficient height. -/
theorem hypersurface_auxiliary_large_height_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 2 * d * (n + 2 : ℝ) * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * degreeRoot n d) :
    ∃ M : ℕ, (M : ℝ) ≤
      (8 * (n + 2 : ℝ) +
          Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) + 2) *
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  let R := Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) *
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨M, hMlarge, _, hthreshold, hbound⟩ := auxiliary_integer_degree_selection (8 * d * (n + 2))
    (show (0 : ℝ) ≤ 0 from le_rfl) hR
  have hdPow : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
  have hPow1 := hd1.trans hdPow
  have hex : ∃ g, IsPointAuxiliary f g M z := by
    have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
    have hdM : d ≤ M := by nlinarith
    by_contra hnone
    obtain ⟨s, _, hr, hc⟩ := hypersurface_no_auxiliary_normalized_comparison order f hf hd hdM hir
      H hH hcoeff ⟨⟨hB, hz, hbox⟩, hprim⟩ (dvd_of_not_exists_isPointAuxiliary hnone)
    have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
    have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hlog := hypersurface_large_height_log_degree_bound (r := n + 1) (by omega) hd hMlarge hr
      B |((order.leadingCoeff f : ℤ) : ℝ)| H (hypersurfaceNormalizedError n) T hB hL hH hT
      (by simpa only [Nat.cast_add, Nat.cast_one, hnR] using hheight)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hposition)
      (by simpa only [Nat.cast_add, Nat.cast_one, hnR] using hc)
    have hb := hypersurface_large_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM) hlog
    have hb' : (M : ℝ) ≤ R := by simpa only [R, Nat.cast_add, Nat.cast_one] using hb
    exact (not_lt_of_ge hb') hthreshold
  obtain ⟨g, hg⟩ := hex
  refine ⟨M, ?_, g, isPointAuxiliary_iff.mp hg⟩
  dsimp only [R] at hbound
  push_cast at hbound
  have hh := mul_le_mul_of_nonneg_left hdPow (show 0 ≤ 8 * (n + 2 : ℝ) by positivity)
  nlinarith

end
end CCDN
