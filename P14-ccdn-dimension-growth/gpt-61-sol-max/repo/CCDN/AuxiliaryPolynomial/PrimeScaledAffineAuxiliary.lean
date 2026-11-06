/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import CCDN.Algebra.ScaledHomogenization
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
import CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.Height.ProjectiveIntegerHeight

/-! The affine auxiliary polynomial obtained from a prime-scaled
homogeneous model. All point and nondivisibility transports are proved. -/

public section
namespace CCDN
open MvPolynomial

/-- For any prime p<=B avoiding the constant coefficient, construct an
affine auxiliary nonmultiple. The degree retains the exact height and bad-prime
factor of the scaled model, ready for their quantitative estimates. -/
theorem prime_scaled_affine_auxiliary {n : ℕ}
    (f : CCDN.IntegerPolynomial (n + 2)) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ ↑p ∣ f.coeff 0)
    {B : ℝ} (hB : 1 ≤ B) (hpB : ↑p ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      ↑g.totalDegree ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree ↑p f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree ↑p f) : ℝ) := by
  let F := scaledHomogenize f.totalDegree ↑p f
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  have hFir := scaledHomogenize_integer_irreducible f hprim hir hd hp hp0
  obtain ⟨M, hM, G, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd hFir hB
  let g := homogeneousSlice (n + 2) ↑p G
  have hgndQ := scaled_auxiliary_rational_not_dvd f hir.ne_zero hprim hp hp0 G hGhom hGnd
  have hgnd : ¬ f ∣ g := fun h => hgndQ (map_dvd (CCDN.rationalPolynomial) h)
  refine ⟨g, ⟨hgnd, ?_⟩, ?_⟩
  swap
  · have hgM : (g.totalDegree : ℝ) ≤ M := by exact_mod_cast homogeneousSlice_degree_le ↑p hGhom
    exact hgM.trans hM
  · exact scaled_auxiliary_vanishes f G hGhom
      (by exact_mod_cast hp.ne_zero) (by simpa using hpB) hGzero

end CCDN
