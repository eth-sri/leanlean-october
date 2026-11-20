/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.Determinant.HypersurfaceMultiplicityEstimate
import CCDN.Determinant.SmoothProjectiveCongruence

/-!
The global determinant bound with simultaneous smooth congruence
conditions. Bad reductions and local exponents are derived from the equation.

Congruence-refined global hypersurface determinant bounds.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The global determinant contribution and all prescribed smooth-prime
contributions hold simultaneously. -/
theorem smooth_congruence_determinant_log_lower
    {n s N d M : ℕ} (hs : 0 < s)
    (f : IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (bad : Finset ℕ) (hbad : ∀ p, stepanovThreshold d < p → HypersurfaceBadReduction f p → p ∈ bad)
    {F : Fin N → IntegerPolynomial (n + 3)} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ → Fin (n + 3)) (a : ℕ → Fin (n + 2) → ℤ)
    (ha : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p))
      (projectiveHypersurfaceChart (k p) f) = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p)) (pderiv j
      (residueEquation p (projectiveHypersurfaceChart (k p) f))) ≠ 0)
    (hunit : ∀ p ∈ P, ∀ i, IsCoprime (p : ℤ) (z i (k p)))
    (hres : ∀ p ∈ P, ∀ i j, (p : ℤ) ∣
      z i (Equiv.swap 0 (k p) j.succ) - a p j * z i (k p)) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad ∪ P, Real.log p / p) +
        (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) *
          (∑ p ∈ P, Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (valueMatrix z F)) := by
  classical
  have hcong (p : ℕ) (hp : p ∈ P) :
      (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
        Int.Matrix.minorGcd (valueMatrix z F) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    exact smooth_projective_hypersurface_congruence_minorGcd f hf F hev.isHomogeneous z
      (k p) (a p) (ha p hp) (hsmooth p hp) (hunit p hp) (hres p hp) hev.eval_eq_zero
  have hh := hypersurface_determinant_log_lower_at_rank_congruence hs f hf hd hev
    (bad ∪ P) P subset_union_right hP
    (fun _ => hypersurfaceMultiplicityExponent (n + 1) 1 s) hcong ?_
  · have he : hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s ≤
        (hypersurfaceMultiplicityExponent (n + 1) 1 s : ℝ) := by
      have he := hypersurfaceMultiplicityExponent_lower_bound (n + 1) s (by omega)
        (show 0 < (1 : ℕ) by omega)
      simpa only [Nat.cast_one, div_one, hypersurfaceDeterminantMain,
        Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using he
    have hsum : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) :=
      sum_nonneg fun p _ => Real.log_natCast_nonneg p
    have hmul := mul_le_mul_of_nonneg_right he hsum
    rw [← mul_sum] at hh
    exact (add_le_add le_rfl hmul).trans hh
  · intro p hpprime hp hcut
    apply hypersurface_good_reduction f p
    intro hb
    exact (mem_sdiff.mp hp).2 (mem_union_left P (hbad p (by exact_mod_cast hcut) hb))

end
end CCDN
