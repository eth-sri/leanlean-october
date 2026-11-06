/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.ProjectiveHypersurfaceResidueDeterminant
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Algebra.FiniteFieldProjectiveCone
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.ProjectiveHypersurfaceMultiplicity
import CCDN.Hypersurface.FiniteFieldCount

/-! The sharp projective finite-field count and its singular
multiplicity correction. This discharges the count in CCDN Lemma 2.7. -/

public section
namespace CCDN
open MvPolynomial


/-- CCDN Lemma 2.7 for the total multiplicity of the projective residue
space. The constant depends only on dimension, and all counting inputs are
proved. Degree one is included using the exact multiplicity bounds. -/
theorem projective_hypersurface_totalMultiplicity_bound {n p d : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p) :
    (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤ ↑p ^ (n + 1) +
      (projectiveHypersurfaceResidueConstant + ((n + 3) * (n + 4) ^ n : ℕ)) * ↑d ^ 2 *
        ↑p ^ n * Real.sqrt p := by
  have hi := mvPolynomial_irreducible_of_field_map _ _ hir
  have hc := (show ↑(Nat.card ↑(projectiveZeroLocus ((map (Int.castRingHom (ZMod p))) f))) ≤
                 ↑p ^ (n + (1 : ℕ)) + projectiveHypersurfaceResidueConstant * ↑d ^ (2 : ℕ) * ↑p ^ n * √↑p from (by
               let inline_f := (map (Int.castRingHom (ZMod p))) f
               let inline_hf : ((map (Int.castRingHom (ZMod p))) f).IsHomogeneous d := IsHomogeneous.map hf (Int.castRingHom (ZMod p))
               rw [projectiveHypersurfaceResidueConstant]
               have hdeg := inline_hf.totalDegree hi.ne_zero
               have hcone := affine_hypersurface_finite_field_bound p inline_f hir (hdeg ▸ hsize)
               rw [hdeg, hypersurfaceResidueConstant] at hcone
               have h := homogeneous_projective_count_of_cone_bound inline_f inline_hf hd
                 (H := 164 * ↑d ^ 2 * Real.sqrt p) (by positivity) (by
                   simp_all [ZMod.card, mul_assoc,  mul_comm])
               simp only [ZMod.card] at h
               have hp : 1 ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
               have hs : 1 ≤ Real.sqrt ↑p := Real.le_sqrt_of_sq_le (by simpa using hp)
               have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
               have he : 2 * (164 * ↑d ^ 2 * Real.sqrt p + 1) ≤
                   330 * ↑d ^ 2 * Real.sqrt p := by nlinarith
               have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ ↑p ^ n by positivity)
               apply h.trans
               nlinarith))
  change (Nat.card (ProjectiveHypersurfaceResidue f p) : ℝ) ≤ _ at hc
  rw [Nat.card_eq_fintype_card] at hc
  by_cases hd2 : 2 ≤ d
  · have hpN : 27 * d ^ 4 < p := by exact_mod_cast hsize
    have hs : d ^ 2 < p := by
      have hh : d ^ 2 ≤ d ^ 4 := by nlinarith [Nat.le_mul_self (d ^ 2)]
      nlinarith
    have hm := projectiveHypersurfaceTotalMultiplicity_le_card_add_sqrt_error f hf hd2 hi hs
    have hh := hm.trans (add_le_add hc le_rfl)
    convert hh using 1
    ring
  · have hd1 : d = 1 := by omega
    subst d
    have hm := (projectiveHypersurfaceTotalMultiplicity_bounds f hf hf0).2
    rw [Nat.mul_one] at hm
    have hmR : (projectiveHypersurfaceTotalMultiplicity f hf hf0 : ℝ) ≤
        Fintype.card (ProjectiveHypersurfaceResidue f p) := by exact_mod_cast hm
    have he : 0 ≤ (((n + 3) * (n + 4) ^ n : ℕ) : ℝ) * ↑p ^ n * Real.sqrt p := by
      positivity
    nlinarith

end CCDN
