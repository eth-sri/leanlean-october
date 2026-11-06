/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.AffineCurveDegree
import CCDN.Hilbert.PlaneHilbert
import CCDN.Plane.NonabsolutePlaneCount
import CCDN.Projection.PlaneProjectionKernel

/-! The irreducible image equation has degree at most the original affine
Hilbert degree. This is an upper bound; the degree need not be preserved. -/

namespace CCDN
section
open MvPolynomial

variable {K τ : Type*} [Field K] [Fintype τ] (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ)
include ha

/-- A principal image equation of a linear projection has degree at most the
source's affine Hilbert degree. -/
theorem plane_projection_equation_degree_le
    (hdegree : HasFilteredCurveDegree I d)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  apply eventual_linear_slope_le
    (fun M => Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M))
    (fun M => Module.finrank K (filteredCoordinateSpace I M)) f.totalDegree d
    ⟨f.totalDegree, f.totalDegree - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf hM⟩ hdegree
  intro M
  rw [← hker]
  exact linear_projection_filtered_finrank_le I a ha M

/-- A linear plane projection with a transcendental coordinate has an
irreducible equation of positive degree at most d and no extra kernel relations. -/
theorem exists_plane_projection_equation_degree_le
    [I.IsPrime]
    (hdegree : HasFilteredCurveDegree I d)
    (j : Fin 2) (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    ∃ f : MvPolynomial (Fin 2) K, Irreducible f ∧ f.totalDegree ≤ d ∧
      ∀ g, aeval a g ∈ I ↔ f ∣ g := by
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree j hj
  refine ⟨f, hf,
    plane_projection_equation_degree_le I a ha d hdegree f hf.ne_zero hker, ?_⟩
  intro g
  have hh : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) :=
    Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hh, hker, Ideal.mem_span_singleton]

