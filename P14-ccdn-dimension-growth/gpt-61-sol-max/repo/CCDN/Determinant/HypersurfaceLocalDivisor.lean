/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Determinant.HypersurfaceCountNormalization
import CCDN.Hypersurface.ProjectiveHypersurfaceCount

/-! CCDN Lemma 2.8 and Corollary 2.9, including the finite-field count.
All constants depend only on dimension. -/

@[expose] public section
namespace CCDN
open MvPolynomial

/-- Explicit dimension-only constant for the projective multiplicity count
(`projective_hypersurface_totalMultiplicity_bound`) in `n + 3` coordinates: the projective
point count contributes `projectiveHypersurfaceResidueConstant = 330`, and the multiplicities
of the singular points contribute `(n + 3) (n + 4)ⁿ`
(`projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error`). -/
noncomputable def hypersurfaceCountConstant (n : ℕ)  :=
  projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)

/-- The constant `hypersurfaceCountConstant n` is nonnegative. -/
lemma hypersurfaceCountConstant_nonneg (n : ℕ) : 0 ≤ hypersurfaceCountConstant n := by
  solve_by_elim [add_nonneg, Nat.cast_nonneg]

/-- The main local coefficient for projective hypersurfaces of dimension n+1. -/
noncomputable def hypersurfaceDeterminantMain (n s : ℕ)  :=
  factorialRoot n * (n + 1 : ℝ) / (n + 2 : ℝ) *
    ↑s ^ (1 + 1 / (n + 1 : ℝ))

/-- The main coefficient `hypersurfaceDeterminantMain n s` is nonnegative. -/
lemma hypersurfaceDeterminantMain_nonneg (n s : ℕ) : 0 ≤ hypersurfaceDeterminantMain n s := by
  unfold hypersurfaceDeterminantMain
  positivity

/-- The local exponent of `projective_hypersurface_minorGcd_dvd` in terms of
`hypersurfaceDeterminantMain`. -/
lemma hypersurfaceDeterminantMain_div (n s : ℕ) (m : ℝ) :
    factorialRoot n / m * (n + 1 : ℝ) / (n + 2 : ℝ) *
      ↑s ^ (1 + 1 / (n + 1 : ℝ)) = hypersurfaceDeterminantMain n s / m := by
  unfold hypersurfaceDeterminantMain
  ring

/-- CCDN Corollary 2.9: the sharp single-prime divisor of every maximal minor
of a common-degree homogeneous evaluation matrix. The residue count, local
multiplicities and projective reduction are constructed from f and z. -/
theorem projective_hypersurface_minorGcd_dvd {n s N p d M : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p)
    (F : Fin N → CCDN.IntegerPolynomial (n + 3)) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, MvPolynomial.eval (z i) f = 0) :
    ∃ e : ℕ,
      factorialRoot n /
        (p + hypersurfaceCountConstant n * ↑d ^ 2 * Real.sqrt p) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * ↑s ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd
        (Matrix.of fun i j => MvPolynomial.eval (z i) (F j)) := by
  apply projective_hypersurface_minorGcd_of_count_bound f hf hf0 F hF z hprim hz
  · simp_all [mul_nonneg, hypersurfaceCountConstant_nonneg, sq_nonneg, Real.sqrt_nonneg]
  · simpa only [hypersurfaceCountConstant, mul_assoc, mul_left_comm, mul_comm] using
      projective_hypersurface_totalMultiplicity_bound f hf hd hf0 hir hsize

end CCDN
