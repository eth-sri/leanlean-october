/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Determinant.ResidueAggregation

/-! The residue partition and local multiplicities of a homogeneous
plane curve supply a global single-prime determinant divisor. The residue
points and their multiplicities are the case `n = 0` of the hypersurface
construction in `ProjectiveHypersurfaceResidueDeterminant`. -/

namespace CCDN
section
open MvPolynomial

/-- Primitive integer zeros determine the residue partition, unit chart
coordinates and positive local multiplicities. The divisor's leading
quadratic constant uses their total multiplicity. -/
theorem projective_reduction_minorGcd {s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    0 < projectiveHypersurfaceTotalMultiplicity f hf hf0 ∧ ∃ e : ℕ,
      (s : ℝ) ^ 2 / (2 * projectiveHypersurfaceTotalMultiplicity f hf hf0) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  obtain ⟨hpos, e, hK, hdiv⟩ := projective_hypersurface_reduction_minorGcd hs f hf hf0 F hF z hprim hz
  exact ⟨hpos, e, cutoff_exponent_lower hpos hK, hdiv⟩
