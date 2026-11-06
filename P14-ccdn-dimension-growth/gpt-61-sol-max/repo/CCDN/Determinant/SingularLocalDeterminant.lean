/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfaceLocalDeterminant

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.LocalDeterminant
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.Determinant.SingularApproximation
import CCDN.Determinant.SingularTangent
import CCDN.ForMathlib.Matrix

/-! Singular plane-curve local determinant divisibility, obtained from
finite-precision homogeneous generators of the local maximal-ideal filtration. -/

public section
namespace CCDN
open MvPolynomial


variable {p μ s : ℕ} [Fact p.Prime] (f : CCDN.IntegerPolynomial 2) (hf : map (Int.castRingHom (ZMod p)) f ∈ idealOfVars (Fin 2) (ZMod p) ^ μ) (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) f) ≠ 0) (x : Fin s → CCDN.IntPoint 2) (hx : ∀ i j, ↑p ∣ x i j)

include hf hμ hx in
/-- Every square evaluation determinant of integral zeros in one singular
residue class has the repeated-weight multiplicity exponent. The curve's
multiplicity is determined by its reduction. -/
theorem singular_plane_pow_dvd_det_mod 
    (hfx : ∀ i, (p : ℤ) ^ multiplicityExponent s μ ∣ eval (x i) f)
    (F : Fin s → CCDN.IntegerPolynomial 2) :
    (p : ℤ) ^ multiplicityExponent s μ ∣ (Matrix.of fun i j => eval (x i) (F j)).det := by
  by_cases hm : μ = 0
  · simp [hm, multiplicityExponent]
  · rw [← hypersurfaceMultiplicityExponent_one μ s (Nat.pos_of_ne_zero hm)] at hfx ⊢
    exact hypersurface_pow_dvd_det_mod f hf hμ x hx hfx F


end CCDN
