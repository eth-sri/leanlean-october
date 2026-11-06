/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes
import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.ProjectivePrimeDeterminant

/-! Coefficient-controlled bad primes for homogeneous projective evaluation
matrices. Good reduction of a full-degree affine chart implies good reduction
of the entire projective equation. -/

namespace CCDN
section
open MvPolynomial Finset

theorem homogeneous_irreducible_reduction_of_not_hypersurfaceBadReduction
    {d p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hdeg : (affineChart 2 f).totalDegree = d)
    (hgood : ¬HypersurfaceBadReduction (affineChart 2 f) p) :
    Irreducible (map (Int.castRingHom (ZMod p)) f) := by
  let K := AlgebraicClosure (ZMod p)
  obtain ⟨hdegree, hir⟩ := (not_hypersurfaceBadReduction_iff (affineChart 2 f) p).mp hgood
  have hc : affineChart 2 (map (Int.castRingHom K) f) =
      map (Int.castRingHom K) (affineChart 2 f) := affineChart_map _ f
  have hf0 : map (Int.castRingHom K) f ≠ 0 := by
    intro h
    apply hir.ne_zero
    rw [← hc, h, map_zero]
  have hhom := hf.map (Int.castRingHom K)
  have hi : Irreducible (map (Int.castRingHom K) f) := by
    apply irreducible_of_affineChart_irreducible
    · rw [hc, hdegree, hdeg, hhom.totalDegree hf0]
    · aesop
  apply mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) K)
  have he : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom K := by aesop
  simpa [MvPolynomial.map_map, he] using hi

