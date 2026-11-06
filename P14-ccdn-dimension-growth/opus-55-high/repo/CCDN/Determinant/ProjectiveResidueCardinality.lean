/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectivePlaneResidueDeterminant
import CCDN.Determinant.SingularReduction
import CCDN.Algebra.ProjectiveAffineChart
import CCDN.Plane.ProjectivePlaneBezout

/-! Projective finite-field points consist of the standard affine chart and
at most d points at infinity. The infinity bound is proved by projective
Bezout and introduces no extra leading multiple of p. -/

namespace CCDN
section
open MvPolynomial

variable {p d : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
include hf

theorem projectivePlaneResidue_infinity_card_le
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hproper : ¬ map (Int.castRingHom (ZMod p)) f ∣ X 0) :
    Fintype.card {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 = 0} ≤ d := by
  classical
  let S := {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 = 0}
  have h := projective_plane_common_zeros_card_le (map (Int.castRingHom (ZMod p)) f)
    (X 0) (hf.map _) hir (isHomogeneous_X _ _) hproper
    (fun r : S => r.val.val) (Subtype.val_injective.comp Subtype.val_injective)
    (fun r => r.val.property)
    (fun r => by change eval r.val.val.rep (X 0) = 0; simpa using r.property)
  simpa using h

theorem projectivePlaneResidue_affine_card_le
    :
    Fintype.card {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 ≠ 0} ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) := by
  let S := {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 ≠ 0}
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
  exact projectiveAffineCoordinates_injective r.property t.property (congrArg Subtype.val he)

/-- The projective correction is at most d, preserving the leading p term
in the already proved affine finite-field estimate. -/
theorem projectivePlaneResidue_card_le_affine_add_degree
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hproper : ¬ map (Int.castRingHom (ZMod p)) f ∣ X 0) :
    Fintype.card (ProjectiveHypersurfaceResidue f p) ≤
      Fintype.card (PlaneResidue (affineChart 2 f) p) + d := by
  have htotal : Fintype.card {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 ≠ 0} =
      Fintype.card (ProjectiveHypersurfaceResidue f p) -
        Fintype.card {r : ProjectiveHypersurfaceResidue f p // r.val.rep 0 = 0} :=
    Fintype.card_subtype_compl (fun r : ProjectiveHypersurfaceResidue f p => r.val.rep 0 = 0)
  have hle := Fintype.card_subtype_le
    (fun r : ProjectiveHypersurfaceResidue f p => r.val.rep 0 = 0)
  have hi := projectivePlaneResidue_infinity_card_le f hf hir hproper
  have ha := projectivePlaneResidue_affine_card_le (p := p) f hf
  omega

