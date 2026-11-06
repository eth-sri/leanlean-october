/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfacePositioning
import CCDN.Noether.EulerPairBasis
import CCDN.Determinant.GenericPlaneMinor
import CCDN.Noether.EulerPairBasisValues
import CCDN.Noether.EulerPairSpecialization
import CCDN.Noether.ShearNormalization

/-! Nonzero Euler minors in smooth generic-plane families. The order is
exactly d²−1, and the smooth-point argument constructs the geometric
irreducibility needed by the characteristic-zero closed-form theorem. -/

namespace CCDN
section
open Polynomial Matrix MvPolynomial

theorem exists_euler_minor_of_smooth_plane_point_charZero
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0)
    (hm : (bivariatePolynomialEquiv K f).Monic)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k (bivariatePolynomialEquiv K f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  let L := AlgebraicClosure K
  let φ : K →+* L := algebraMap K L
  let g := bivariateMap φ (bivariatePolynomialEquiv K f)
  have hgi : Irreducible g := by
    dsimp [g]
    rw [bivariatePolynomialEquiv_map, MulEquiv.irreducible_iff]
    exact irreducible_map_of_smooth_plane_point f hf z j hz hj
  have hgm := bivariateMap_monic φ hm
  have hgd : g.natDegree = k + 2 := by
    rw [bivariateMap_natDegree_of_monic φ hm, hdeg]
  obtain ⟨a, c, hdet⟩ := Matrix.hasNonzeroMinor_of_le_rank _
    (eulerClosedFormCoefficientMatrix_rank k g hgi 1 one_ne_zero (by aesop) hgd).ge
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [← eulerClosedForm_minor_map, he, map_zero]

variable {K σ : Type*} [Field K] [CharZero K] (k : ℕ)

theorem exists_genericPlane_euler_minor_charZero
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hm : (optionEquivLeft K σ f).Monic)
    (hdeg : (optionEquivLeft K σ f).natDegree = k + 2)
    (hz : eval (0 : Option σ → K) f = 0)
    (hs : eval (0 : Option σ → K) (pderiv none f) ≠ 0) :
    (eulerClosedFormCoefficientMatrix k (genericPlanePolynomial f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  obtain ⟨hgi, hgz, hgs, hgm, hgd⟩ := genericPlaneMap_smooth_monic (k + 2) (by omega) f hf hm
    hdeg hz hs
  obtain ⟨a, c, hdet⟩ := exists_euler_minor_of_smooth_plane_point_charZero
    k _ hgi 0 0 hgz hgs hgm hgd
  refine ⟨a, c, ?_⟩
  intro he
  apply hdet
  rw [genericPlaneMap_bivariate, ← eulerClosedForm_minor_map, he, map_zero]

