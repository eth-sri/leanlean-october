/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import CCDN.Determinant.ProjectivePlaneResidueDeterminant
public import CCDN.Determinant.SingularReduction
import CCDN.Algebra.ProjectiveAffineChart
import CCDN.Plane.ProjectivePlaneBezout

/-! Projective finite-field points consist of the standard affine chart and
at most d points at infinity. The infinity bound is proved by projective
Bezout and introduces no extra leading multiple of p. -/

public section
namespace CCDN
open MvPolynomial

variable {p d : ℕ} [Fact p.Prime] (f : CCDN.IntegerPolynomial 3) (hf : f.IsHomogeneous d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f)) (hproper : ¬ map (Int.castRingHom (ZMod p)) f ∣ X 0)

include hf hir hproper in
private theorem projectivePlaneResidue_infinity_card_le  :
    Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0} ≤ d := by
  classical
  let S := {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0}
  have h := projective_plane_common_zeros_card_le (map (Int.castRingHom (ZMod p)) f)
    (X 0) (hf.map _) hir (isHomogeneous_X _ _) hproper
    (fun r : S => r.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    (fun r => r.val.property)
    (fun r => by change eval r.val.val.rep (X 0) = 0; simpa using r.property)
  simpa only [mul_one] using h


include hf hir hproper in
/-- The projective correction is at most d, preserving the leading p term
in the already proved affine finite-field estimate. -/
theorem projectivePlaneResidue_card_le_affine_add_degree  :
    Fintype.card (ProjectivePlaneResidue f p) ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) + d := by
  classical
  have htotal : Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 ≠ 0} =
      Fintype.card (ProjectivePlaneResidue f p) -
        Fintype.card {r : ProjectivePlaneResidue f p // r.val.rep 0 = 0} :=
    Fintype.card_subtype_compl (fun r : ProjectivePlaneResidue f p => r.val.rep 0 = 0)
  have hi := projectivePlaneResidue_infinity_card_le f hf hir hproper
  have ha := (by
               classical
               let S := {r : ProjectivePlaneResidue f p // r.val.rep 0 ≠ 0}
               let ψ : S → PlaneResidue (affineChart 2 f) p := fun r =>
                 ⟨projectiveAffineCoordinates r.val.val, by
                   have h := projectiveAffineCoordinates_zero (map (Int.castRingHom (ZMod p)) f)
                     (hf.map _) r.val.val r.property r.val.property
                   rw [affineChart_map, eval_map] at h
                   exact h⟩
               apply Fintype.card_le_of_injective ψ
               intro r t he
               apply Subtype.ext
               apply Subtype.ext
               exact projectiveAffineCoordinates_injective r.property t.property (congrArg Subtype.val he))
  omega

end CCDN
