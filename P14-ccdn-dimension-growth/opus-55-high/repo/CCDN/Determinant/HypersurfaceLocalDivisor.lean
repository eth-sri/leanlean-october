/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.DegreeBound
import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Plane.FiniteFieldConstants
import CCDN.Determinant.HypersurfaceCountNormalization
import CCDN.Hypersurface.ProjectiveHypersurfaceCount

/-! CCDN Lemma 2.8 and Corollary 2.9, including the finite-field count.
All constants depend only on dimension. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable (n : ℕ)

/-- Explicit dimension-only constant for the projective multiplicity count
(`projective_hypersurface_totalMultiplicity_bound`) in `n + 3` coordinates: the projective
point count contributes `projectiveHypersurfaceResidueConstant = 330`, and the multiplicities
of the singular points contribute `(n + 3) (n + 4)ⁿ`
(`projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error`). -/
def hypersurfaceCountConstant : ℝ :=
  projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)

/-- The constant `hypersurfaceCountConstant n` is nonnegative. -/
lemma hypersurfaceCountConstant_nonneg : 0 ≤ hypersurfaceCountConstant n :=
  add_nonneg projectiveHypersurfaceResidueConstant_pos.le (Nat.cast_nonneg _)

end

section
variable (n s : ℕ)

/-- The main local coefficient for projective hypersurfaces of dimension n+1. -/
def hypersurfaceDeterminantMain : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (n + 1 : ℝ) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ))

/-- The local exponent of `projective_hypersurface_minorGcd_dvd` in terms of
`hypersurfaceDeterminantMain`. -/
lemma hypersurfaceDeterminantMain_div (m : ℝ) :
    factorialRoot n / m * (n + 1 : ℝ) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) = hypersurfaceDeterminantMain n s / m := by
  unfold hypersurfaceDeterminantMain
  ring

end

/-- CCDN Corollary 2.9: the sharp single-prime divisor of every maximal minor
of a common-degree homogeneous evaluation matrix. The residue count, local
multiplicities and projective reduction are constructed from f and z. -/
theorem projective_hypersurface_minorGcd_dvd {n s N p d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) :
    ∃ e : ℕ,
      factorialRoot n /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd
        (Matrix.of fun i j => MvPolynomial.eval (z i) (F j)) := by
  by_cases hs : 0 < s
  · obtain ⟨hpos, e, hcut, hd'⟩ :=
      projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
    have hroot := hypersurface_count_root_bound (n + 1) (by omega) (Nat.cast_nonneg p)
      (mul_nonneg (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg (d : ℝ)))
        (Real.sqrt_nonneg p))
      (Nat.cast_nonneg (projectiveHypersurfaceTotalMultiplicity f hf hf0)) (by
        simpa [hypersurfaceCountConstant, mul_assoc, mul_left_comm, mul_comm, Nat.add_sub_cancel] using
          projective_hypersurface_totalMultiplicity_bound f hf hd hf0 hir hsize)
    refine ⟨e, ?_, hd'⟩
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      local_exponent_separated_lower_bound_of_root_bound (n + 1) s e (by omega) hpos hroot hcut
  · have hs0 : s = 0 := by omega
    refine ⟨0, ?_, by simp⟩
    simp only [hs0, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, sub_zero, le_refl]

