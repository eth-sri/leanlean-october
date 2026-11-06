/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.Determinant.HypersurfaceLocalDeterminant
import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.BlockDeterminant
import CCDN.Determinant.ProjectiveLocalDeterminant
import CCDN.ForMathlib.Matrix
import CCDN.Height.ProjectiveZeroLocus

/-!
Projective hypersurface determinants in all positive dimensions.
Unit normalization modulo prime powers transfers the local affine
bound to homogeneous evaluation matrices of a common degree.

Singular local determinant bounds at a residue point in arbitrary
dimension. Multiplicity is obtained from the first nonzero translated homogeneous
component.
-/

namespace CCDN
section
open MvPolynomial


/-- The local projective divisor is available in every coordinate chart. -/
theorem projective_hypersurface_local_det_divisibility {p n μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (projectivePlaneChart k f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (projectivePlaneChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  have h := projective_chart_det_divisibility
    (rename (Equiv.swap 0 k) f) hfhom.rename_isHomogeneous
    (fun j => rename (Equiv.swap 0 k) (F j)) (fun j => (hF j).rename_isHomogeneous)
    (fun i => z i ∘ Equiv.swap 0 k) a (fun x hx hxf => by
      simpa [eval_sub_originShift] using origin_filtration_pow_dvd_det_mod
        (originShift a (projectivePlaneChart k f))
        (fun i j => x i j - a j) hx (hypersurfaceMultiplicityExponent_le_origin _ hf hμ)
        (fun i => by simpa [eval_sub_originShift, projectivePlaneChart] using hxf i)
        (fun j => originShift a (affineChart (n + 2) (rename (Equiv.swap 0 k) (F j)))))
    (fun i => by grind)
    (fun i j => by grind)
    (fun i => by simp_all [eval_swap_plane_coordinates])
  simpa [eval_swap_plane_coordinates] using h

