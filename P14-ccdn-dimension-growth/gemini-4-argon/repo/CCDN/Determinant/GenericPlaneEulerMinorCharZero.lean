/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfacePositioning
public import CCDN.Noether.EulerPairBasis
import CCDN.Determinant.GenericPlaneMinor
import CCDN.Noether.EulerPairBasisValues
import CCDN.Noether.EulerPairSpecialization
import CCDN.Noether.ShearNormalization

/-! Nonzero Euler minors in smooth generic-plane families. The order is
exactly d²−1, and the smooth-point argument constructs the geometric
irreducibility needed by the characteristic-zero closed-form theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix MvPolynomial

/-- Over an algebraically closed field of characteristic zero, every irreducible polynomial `f` of
degree `k + 2` admits an affine coordinate change, given by `a` and `b` with `b none ≠ 0` and the
top-degree form of `f` nonvanishing at `b`, after which the Euler closed-form coefficient matrix of
the generic plane section has a nonzero minor of order `(k + 2) ^ 2 - 1`. -/
theorem exists_positioned_genericPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (eulerClosedFormCoefficientMatrix k
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          ((k + 2) ^ 2 - 1) := by
  obtain ⟨a, b, hb, hdir, hg⟩ :=
    exists_monic_smooth_hypersurface_coordinates f hf (by omega) (.of_charZero _)
  obtain ⟨hgi, hgz, hgs, hgm, hgd⟩ := genericPlaneMap_smooth_monic (k + 2) (by omega) _
    hg.irreducible hg.monic (hd ▸ hg.natDegree_eq) hg.eval_zero hg.pderiv_ne_zero
  let F := FractionRing (MvPolynomial σ K)
  let L := AlgebraicClosure F
  let φ : F →+* L := algebraMap F L
  let q := bivariateMap φ (bivariatePolynomialEquiv F
    (genericPlaneMap K F σ (normalizedHypersurfaceCoordinates a b hb f)))
  have hqi : Irreducible q := by
    dsimp only [q]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff (f := bivariatePolynomialEquiv L)]
    exact irreducible_map_of_smooth_plane_point _ hgi 0 0 hgz hgs
  have hqm : q.Monic := bivariateMap_monic φ hgm
  obtain ⟨rows, cols, hdet⟩ := exists_eulerClosedForm_nonzero_minor k q hqi
    1 one_ne_zero (by simpa using hqm.leadingCoeff)
    (by rw [bivariateMap_natDegree_of_monic φ hgm, hgd])
  refine ⟨a, b, hb, hdir, rows, cols, fun he => hdet ?_⟩
  rw [← eulerClosedForm_minor_map, genericPlaneMap_bivariate, ← eulerClosedForm_minor_map,
    he, map_zero, map_zero]

end
end CCDN
