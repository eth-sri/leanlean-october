/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.ProjectiveHypersurfaceLocal

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.SingularPlaneChart
import CCDN.Determinant.BlockDeterminant
import CCDN.ForMathlib.Matrix
import CCDN.Height.ProjectiveZeroLocus

/-! Local divisibility for homogeneous evaluation matrices at projective
points. Normalize a unit coordinate modulo the required prime power,
apply the singular affine estimate to the resulting approximate zeros,
then cancel the invertible row factors. -/

@[expose] public section
namespace CCDN
open MvPolynomial




/-- Move coordinate `k` to the first position before taking the affine chart. -/
noncomputable def projectivePlaneChart (k : Fin 3) (f : CCDN.IntegerPolynomial 3)  :=
  affineChart 2 (rename (Equiv.swap 0 k) f)


/-- Assemble local projective residue classes in their own coordinate charts.
Every maximal minor acquires the sum of their local multiplicity exponents. -/
theorem projective_plane_residue_minorGcd {p c s N d M : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial 3) (hfhom : f.IsHomogeneous d)
    (F : Fin N → CCDN.IntegerPolynomial 3) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → CCDN.IntPoint 3) (label : Fin s → Fin c)
    (k : Fin c → Fin 3) (a : Fin c → CCDN.IntPoint 2) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f)) ∈
        idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime ↑p (z i (k (label i))))
    (hres : ∀ i j, ↑p ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {j : Fin s // label j = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  refine dvd_trans (pow_dvd_pow _ ?_)
    (projective_hypersurface_residue_minorGcd (n := 0) f hfhom F hF z label k a μ
      hf hμ hunit hres hz)
  apply Finset.sum_le_sum
  intro i _
  by_cases hm : μ i = 0
  · simp [hm, multiplicityExponent]
  · exact (hypersurfaceMultiplicityExponent_one (μ i) _ (Nat.pos_of_ne_zero hm)).symm.le

end CCDN
