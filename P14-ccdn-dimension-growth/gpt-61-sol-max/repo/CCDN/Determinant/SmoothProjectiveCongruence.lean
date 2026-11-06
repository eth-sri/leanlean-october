/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.ProjectiveHypersurfaceLocal
import CCDN.Determinant.BlockDeterminant
import CCDN.Determinant.PlaneMultiplicitySmooth

/-!
Smooth projective congruence classes give simultaneous divisors
for homogeneous evaluation matrices.

At a nonsingular reduced point the translated hypersurface
equation has multiplicity one.
-/

public section
namespace CCDN
open MvPolynomial


end CCDN

namespace CCDN
open MvPolynomial

/-- If integer zeros `z i` of a homogeneous `f` all have their `k`-th coordinate prime to `p` and
reduce, in the affine chart `k`, to the same nonsingular point `a` of `f mod p`, then for forms `F
j` of a common degree `M` the power `p ^ hypersurfaceMultiplicityExponent (n + 1) 1 s` divides the
gcd of the maximal minors of the evaluation matrix `(F j (z i))`. -/
theorem smooth_projective_hypersurface_congruence_minorGcd {p n s N d M : ℕ}
    [Fact p.Prime] (f : CCDN.IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d)
    (F : Fin N → CCDN.IntegerPolynomial (n + 3)) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (k : Fin (n + 3)) (a : CCDN.IntPoint (n + 2))
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p))
      (projectiveHypersurfaceChart k f) = 0)
    (hs : ∃ j, eval (fun i => (a i : ZMod p)) (pderiv j
      (map (Int.castRingHom (ZMod p)) (projectiveHypersurfaceChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime ↑p (z i k))
    (hres : ∀ i j, ↑p ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) 1 s ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  obtain ⟨hpow, hcomp⟩ := (show (map (Int.castRingHom (ZMod p))) ((originShift a) (projectiveHypersurfaceChart k f)) ∈
                                idealOfVars (Fin (n + (2 : ℕ))) (ZMod p) ^ (1 : ℕ) ∧
                              (homogeneousComponent (1 : ℕ))
                                  ((map (Int.castRingHom (ZMod p))) ((originShift a) (projectiveHypersurfaceChart k f))) ≠
                                (0 : MvPolynomial (Fin (n + (2 : ℕ))) (ZMod p)) from (by
                            let inline_f := projectiveHypersurfaceChart k f
                            have hf : map (Int.castRingHom (ZMod p)) inline_f ≠ 0 := by
                              aesop
                            obtain ⟨μ, hμ, _, hpow, hcomp⟩ := exists_hypersurface_reduction_multiplicity inline_f a hf ha
                            have he := by
                              rw [originShift_map] at hpow
                              exact origin_order_eq_one_of_smooth _ _ hμ hpow hs
                            subst μ
                            exact ⟨hpow, hcomp⟩))
  rw [minorGcd_eq_gcd_plucker]
  apply Finset.dvd_gcd
  intro S _
  rw [Matrix.plucker_row_eq_det_submatrix]
  exact projective_hypersurface_local_det_divisibility f hf _
    (fun j => hF _) z k a hpow hcomp hunit hres hz

end CCDN
