/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Hilbert.LinearProjectionFiltration
import CCDN.ForMathlib.MvPolynomial
import CCDN.Projection.HomogeneousFilteredProjection
import CCDN.Projection.PlaneRelationSpace

/-! The principal equation of the image of a homogeneous linear
projection is homogeneous. -/

namespace CCDN
section
open MvPolynomial

/-- For a homogeneous ideal `I` and homogeneous linear forms `a`, the kernel of the projection by
`a` is closed under taking homogeneous components. -/
theorem projection_kernel_homogeneousComponent_mem
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K))
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (p : MvPolynomial σ K) (hp : p ∈ RingHom.ker (projectionCoordinateMap I a)) (N : ℕ) :
    homogeneousComponent N p ∈ RingHom.ker (projectionCoordinateMap I a) := by
  change (Ideal.Quotient.mk I) (aeval a (homogeneousComponent N p)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← homogeneousComponent_aeval_linear a ha]
  apply hI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hp

/-- A nonzero generator of a principal ideal that is closed under homogeneous components is
homogeneous of its total degree. -/
theorem principal_generator_isHomogeneous
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hgen : I = Ideal.span {f}) :
    f.IsHomogeneous f.totalDegree := by
  have ht := hI f (by simp_all) f.totalDegree
  rw [hgen, Ideal.mem_span_singleton] at ht
  obtain ⟨c, hc⟩ := eq_scalar_mul_of_dvd_of_totalDegree_le f
    (homogeneousComponent f.totalDegree f) hf ht
    (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree_le
  have hcne : c ≠ 0 := by
    intro hz
    apply homogeneousComponent_totalDegree_ne_zero hf
    simp_all
  have hh := (homogeneousComponent_isHomogeneous f.totalDegree f).C_mul c⁻¹
  rw [hc, ← smul_eq_C_mul] at hh
  simpa [smul_smul, inv_mul_cancel₀ hcne, one_smul] using hh

