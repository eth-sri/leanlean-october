module

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Cellular boundaries are the intersection radical

For a capped boundary, its corner primitive differs from the boundary-cycle value
by one potential per primal vertex. Its intersection coefficient is therefore a
vertex coboundary and pairs to zero with every conserved flow.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (f : diamondCycleSpace hN hM A)
    (F : RibbonBoundaryComponent hN hM A → ℚ) (d : DirectedDart (checkerArrows N M))

theorem ribbonBoundaryOf_pairing :
    ribbonBoundaryOf hN hM A (ribbonEdgePairing hN hM A d) =
      ribbonBoundaryOf hN hM A ((faceRotation hN hM).symm d) := by
  have he := ribbonBoundaryOf_step hN hM A ((faceRotation hN hM).symm d)
  change ribbonBoundaryOf hN hM A
    (ribbonEdgePairing hN hM A (faceRotation hN hM ((faceRotation hN hM).symm d))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact he

theorem ribbonHalfFlow_faceBoundary :
    ribbonHalfFlow hN hM (ribbonFaceBoundary hN hM A F) d =
      F (ribbonBoundaryOf hN hM A (ribbonEdgePairing hN hM A d)) -
        F (ribbonBoundaryOf hN hM A d) := by
  obtain ⟨⟨v, b⟩, rfl⟩ := (ribbonEndEquiv hN hM).surjective d
  rw [ribbonHalfFlow_end, ribbonEdgePairing_end]
  cases ha : A v
  · simp [extendDiamondChain_closed _ ha, neg_zero, ite_self, Bool.false_xor, sub_self]
  · rw [extendDiamondChain_open _ ha]
    have hc : ribbonFaceBoundary hN hM A F ⟨v, ha⟩ =
        F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, true))) -
          F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, false))) := rfl
    grind

theorem exists_intersection_potential_of_faceBoundary (hF : ribbonFaceBoundary hN hM A F = f.val) :
    ∃ g : FaceVertex N M true → ℚ,
      diamondCoboundary hN hM A g = ribbonIntersectionCoefficient f := by
  let H := fun d => ribbonCornerPrimitive f d - F (ribbonBoundaryOf hN hM A d)
  have hi : ∀ d, H ((faceRotation hN hM).symm d) = H d := by
    intro d
    have hr := ribbonCornerPrimitive_rotation_sub f d
    have hb := ribbonHalfFlow_faceBoundary hN hM A F d
    rw [hF, ribbonBoundaryOf_pairing] at hb
    linarith
  have hs : ∀ d, H (faceRotation hN hM d) = H d := by
    grind [Equiv.symm_apply_apply]
  let g := fun v => H (ribbonVertexDart hN hM v)
  have hg : ∀ d, H d = g (ribbonFace hN hM d) := by
    intro d
    apply sameCycle_invariant hs
    apply (sameCycle_faceRotation hN hM _ _).mpr
    rfl
  refine ⟨g, ?_⟩
  funext e
  have h₀ := hg (ribbonEndEquiv hN hM (e.val, false))
  have h₁ := hg (ribbonEndEquiv hN hM (e.val, true))
  simp only [ribbonFace_end] at h₀ h₁
  have he := congrFun hF e
  change F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
    F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false))) = f.val e at he
  change g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false) =
    ribbonCornerPrimitive f (ribbonEndEquiv hN hM (e.val, true)) -
      ribbonCornerPrimitive f (ribbonEndEquiv hN hM (e.val, false)) - f.val e
  linarith

/-- Every actual capped boundary pairs to zero with every conserved indexed flow. -/
theorem ribbonIntersection_zero_of_mem_boundary {hN : Even N} {hM : Even M}
    {A : RCConfig N M} (f g : diamondCycleSpace hN hM A)
    (hf : f ∈ ribbonBoundarySpace hN hM A) : ribbonIntersection f g = 0 := by
  obtain ⟨F, he⟩ := hf
  have hF := congrArg Subtype.val he
  obtain ⟨p, hp⟩ := exists_intersection_potential_of_faceBoundary hN hM A f F hF
  unfold ribbonIntersection
  rw [← hp]
  have he := diamondBoundary_pairing hN hM p g.val
  have hz := g.property
  rw [hz] at he
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at he
  exact he.symm

end PottsDiscontinuity.Torus
