/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.SectionImageRank
import CCDN.Algebra.PointSeparation
import Mathlib.LinearAlgebra.StdBasis

/-! A sharp affine curve intersection bound from the Hilbert function.
Bounds intersections with arbitrary section polynomials. No projective intersection theorem or
point-counting axiom is used. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A proper polynomial section of a prime curve contains at most the product
of the curve's affine Hilbert degree and the section degree many distinct points. -/
theorem polynomial_section_card_le_degree {K σ ι : Type*} [Field K] [Fintype σ]
    [Fintype ι] [DecidableEq ι]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (d : ℕ)
    (hdegree : HasFilteredCurveDegree p d)
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzp : ∀ i, z i ∈ idealZeroLocus p) (hzl : ∀ i, MvPolynomial.eval (z i) l = 0) :
    Fintype.card ι ≤ d * m := by
  obtain ⟨h, hsep⟩ := exists_point_separators z hz
  let φ :=
    AlgHom.pi fun i => Ideal.Quotient.liftₐ p (MvPolynomial.aeval (z i))
      (fun f hf => by tauto)
  have hφ (i : ι) (f : MvPolynomial σ K) :
      φ (Ideal.Quotient.mk p f) i = MvPolynomial.eval (z i) f := by
    rfl
  refine section_image_rank_le p d hdegree φ h ?_ l hl m hld ?_
  · convert Pi.linearIndependent_single_one ι K using 1
    funext j i
    rw [hφ, hsep, Pi.single_apply]
  · funext i
    exact (hφ i l).trans (hzl i)

end
end CCDN
