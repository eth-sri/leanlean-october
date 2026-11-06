/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Algebra.SectionImageRank
import CCDN.Algebra.PointSeparation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A sharp affine curve intersection bound from the Hilbert function.
Bounds intersections with arbitrary section polynomials. No projective intersection theorem or
point-counting axiom is used. -/

namespace CCDN
section

variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]

/-- A proper polynomial section of a prime curve contains at most the product
of the curve's affine Hilbert degree and the section degree many distinct points. -/
theorem polynomial_section_card_le_degree
    (d : ℕ)
    (hdegree : HasFilteredCurveDegree p d)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d * m := by
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  refine section_image_rank_le p d hdegree (AlgHom.pi fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i)) (by aesop)) h ?_ l hl m hld (funext fun i => by simpa [Ideal.Quotient.liftₐ_apply] using hzl i)
  convert (Pi.basisFun K ι).linearIndependent with i
  funext j
  simp [Ideal.Quotient.liftₐ_apply, hsep, Pi.single_apply]
