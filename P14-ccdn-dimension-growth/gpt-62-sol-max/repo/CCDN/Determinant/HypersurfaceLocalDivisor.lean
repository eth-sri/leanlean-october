/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Determinant.HypersurfaceMultiplicityEstimate
public import CCDN.Hypersurface.ProjectiveHypersurfaceCount
import CCDN.ForMathlib.MvPolynomial

/-! CCDN Lemma 2.8 and Corollary 2.9, including the finite-field count.
All constants depend only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The main local coefficient for projective hypersurfaces of dimension n+1. -/
def hypersurfaceDeterminantMain (n s : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (n + 1 : ℝ) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ))

/-- The main coefficient `hypersurfaceDeterminantMain n s` is nonnegative. -/
lemma hypersurfaceDeterminantMain_nonneg (n s : ℕ) : 0 ≤ hypersurfaceDeterminantMain n s := by
  unfold hypersurfaceDeterminantMain
  positivity

/-- A point-count error of H times P^(m-1) increases the mth root by at most H.
There is no degree or multiplicity loss in this normalization. -/
private theorem hypersurface_count_root_bound (m : ℕ) (hm : 0 < m)
    {P H T : ℝ} (hP : 0 ≤ P) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hcount : T ≤ P ^ m + H * P ^ (m - 1)) :
    T ^ (1 / (m : ℝ)) ≤ P + H := by
  have hmajor : P ^ m + H * P ^ (m - 1) ≤ (P + H) ^ m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simp only [Nat.succ_sub_one, pow_succ]
    have hpow := pow_le_pow_left₀ hP (show P ≤ P + H by linarith) n

    nlinarith
  calc
    _ ≤ ((P + H) ^ m) ^ (1 / (m : ℝ)) :=
      Real.rpow_le_rpow hT (hcount.trans hmajor) (by positivity)
    _ = P + H := by
      rw [one_div, Real.pow_rpow_inv_natCast (add_nonneg hP hH) (Nat.ne_of_gt hm)]

/-- CCDN Corollary 2.9: the sharp single-prime divisor of every maximal minor
of a common-degree homogeneous evaluation matrix. The residue count, local
multiplicities and projective reduction are constructed from f and z. -/
theorem projective_hypersurface_minorGcd_dvd {n s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) :
    ∃ e : ℕ,
      hypersurfaceDeterminantMain n s /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) - (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ minorGcd
        (Matrix.of fun i j => MvPolynomial.eval (z i) (F j)) := by
  have hf0 := (mvPolynomial_irreducible_of_field_map _ _ hir).ne_zero
  obtain ⟨hpos, e, hcut, hdvd⟩ := projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
  have hroot := hypersurface_count_root_bound (n + 1) (by omega)
    (Nat.cast_nonneg p) (H := hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p)
    (by have := hypersurfaceCountConstant_nonneg n; positivity) (Nat.cast_nonneg _)
    (by simpa only [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using
      projective_hypersurface_totalMultiplicity_bound f hf hd hir hsize)
  exact ⟨e, by
    simpa only [hypersurfaceDeterminantMain, Nat.cast_add, Nat.cast_one,
      show (n : ℝ) + 1 + 1 = n + 2 by ring, mul_assoc] using
      local_exponent_separated_lower_bound (n + 1) s e (by omega) hpos hroot hcut, hdvd⟩

end
end CCDN
