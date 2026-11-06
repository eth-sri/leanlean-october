/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Plane.FiniteFieldConstants
import CCDN.Algebra.FiniteFieldProjectiveCone
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.ProjectiveHypersurfaceMultiplicity
import CCDN.Hypersurface.FiniteFieldCount

/-! The sharp projective finite-field count and its singular
multiplicity correction. This discharges the count in CCDN Lemma 2.7. -/

namespace CCDN
section
open MvPolynomial

/-- CCDN Lemma 2.7 for the total multiplicity of the projective residue
space. The constant depends only on dimension, and all counting inputs are
proved. Degree one is included using the exact multiplicity bounds. -/
theorem projective_hypersurface_totalMultiplicity_bound {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤ (p : ℝ) ^ (n + 1) +
      (projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)) * (d : ℝ) ^ 2 *
        (p : ℝ) ^ n * Real.sqrt p := by
  have hi := mvPolynomial_irreducible_of_field_map _ _ hir
  have hc : (Nat.card (projectiveZeroLocus (map (Int.castRingHom (ZMod p)) f)) : ℝ) ≤ p ^ (n + 1) +
      projectiveHypersurfaceResidueConstant * d ^ 2 * p ^ n * Real.sqrt p := by
    rw [(show projectiveHypersurfaceResidueConstant = 330 from rfl)]
    have hi := mvPolynomial_irreducible_of_field_map _ (map (Int.castRingHom (ZMod p)) f) hir
    have hdeg := (hf.map _).totalDegree hi.ne_zero
    let e := finSuccEquiv' (n := n + 2) 0
    have hd' : (rename e (map (Int.castRingHom (ZMod p)) f)).totalDegree = d := hdeg ▸ totalDegree_renameEquiv e (map (Int.castRingHom (ZMod p)) f)
    have hcone := affine_hypersurface_finite_field_bound_option p (rename e (map (Int.castRingHom (ZMod p)) f))
      (by
        rw [map_rename]
        exact (MulEquiv.irreducible_iff (f := renameEquiv (AlgebraicClosure (ZMod p)) e)).mpr hir)
      (hd' ▸ hsize)
    rw [hd', polynomial_zero_card_renameEquiv, hypersurfaceResidueConstant_eq] at hcone
    have h := homogeneous_projective_count_of_cone_bound (map (Int.castRingHom (ZMod p)) f) (hf.map _) hd
      (H := 164 * (d : ℝ) ^ 2 * Real.sqrt p) (by positivity) (by grind [ZMod.card, mul_assoc, mul_left_comm, mul_comm])
    simp at h
    have hp : (1 : ℝ) ≤ p := mod_cast (Fact.out : p.Prime).one_le
    have hs : 1 ≤ Real.sqrt (p : ℝ) := Real.le_sqrt_of_sq_le (by grind)
    have hdR : (1 : ℝ) ≤ d := mod_cast hd
    have hd2 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
    have hds : (1 : ℝ) ≤ d ^ 2 * Real.sqrt p := by nlinarith
    have he : 2 * (164 * d ^ 2 * Real.sqrt p + 1) ≤
        330 * d ^ 2 * Real.sqrt p := by nlinarith
    have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ (p : ℝ) ^ n by positivity)
    apply h.trans
    nlinarith
  change (Nat.card (ProjectiveHypersurfaceResidue f p) : ℝ) ≤ _ at hc
  rw [Nat.card_eq_fintype_card] at hc
  by_cases hd2 : 2 ≤ d
  · have hpN : 27 * d ^ 4 < p := mod_cast hsize
    have hm := projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error f hf hd2 hi (by
      have hh : d ^ 2 ≤ d ^ 4 := by bound
      nlinarith)
    grind
  · have hd1 : d = 1 := by omega
    subst d
    have hm := (projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0).2
    rw [Nat.mul_one] at hm
    have hmR : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
        Fintype.card (ProjectiveHypersurfaceResidue f p) := mod_cast hm
    have he : (0 : ℝ) ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * p ^ n * Real.sqrt p := by
      positivity
    nlinarith

