module

public import HypoellipticAleksandrov.Parabolic.SpatialDirectionalDifferenceQuotientBound

/-!
# Spatial-slice difference-quotient bounds

This module transfers fixed-time spatial derivative bounds to the totalized
spacetime spatial difference quotient.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Convex

/-- Fixed-time spatial derivative bounds on a containing spatial set give
uniform signed spatial difference-quotient bounds on a product carrier. -/
theorem abs_spatialDifferenceQuotient_le_of_spatialSliceFDeriv_bound
    {d : ℕ} {I : Set ℝ} {S Q : Set (PDE.Vec d)}
    {f : TimeVelocity d → ℝ} {δ M : ℝ}
    (hseg : ∀ (k : Fin d) (h : ℝ) (y : PDE.Vec d),
      |h| ≤ δ → y ∈ S →
        [y -[ℝ] y + h • PDE.basisVec k] ⊆ Q)
    (hdiff : ∀ r ∈ I, ∀ y ∈ Q,
      DifferentiableAt ℝ (fun x => f (r, x)) y)
    (hdir : ∀ r ∈ I, ∀ (k : Fin d) (y : PDE.Vec d), y ∈ Q →
      |(fderiv ℝ (fun x => f (r, x)) y) (PDE.basisVec k)| ≤ M) :
    ∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d),
      |h| ≤ δ → z ∈ I ×ˢ S →
        |spatialDifferenceQuotient k h f z| ≤ M := by
  intro k h z hh hz
  rcases z with ⟨r, y⟩
  have hyr : y ∈ S := hz.2
  have hr : r ∈ I := hz.1
  let g  := fun x => f (r, x)
  by_cases hzero : h = 0
  · subst h
    have hyQ : y ∈ Q := hseg k 0 y hh hyr
      (left_mem_segment ℝ y (y + 0 • PDE.basisVec k))
    have hMnonneg : 0 ≤ M :=
      (abs_nonneg ((fderiv ℝ g y) (PDE.basisVec k))).trans
        (hdir r hr k y hyQ)
    simp_all
  · obtain ⟨w, hw, hMVT⟩ :=
      domain_mvt (s := [y -[ℝ] y + h • PDE.basisVec k])
        (f := g) (f' := fderiv ℝ g)
        (fun x hx =>
          (hdiff r hr x (hseg k h y hh hyr hx)).hasFDerivAt.hasFDerivWithinAt)
        (convex_segment y (y + h • PDE.basisVec k))
        (left_mem_segment ℝ y (y + h • PDE.basisVec k))
        (right_mem_segment ℝ y (y + h • PDE.basisVec k))
    aesop

end HypoellipticAleksandrov.Parabolic
