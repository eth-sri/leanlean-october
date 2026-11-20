module

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.LoopClusterProjection

/-! Boundary-loop chains span the primal conserved chains whenever the
horizontal displacement vanishes on all primal cycles. This replaces the
planar-lift separation argument by the proved exact cellular radical theorem. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}
noncomputable section

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (j : Fin M) (A : RCConfig N M)
    (hX : ∀ f : diamondCycleSpace hN hM A, diamondHorizontalDisplacement f.val = 0)
    (hzero : ∀ q : Loop hN hM (rcSmoothing A),
      loopVertical j q = 0) (f : diamondCycleSpace hN hM A)
    (F : RibbonBoundaryComponent hN hM A → ℚ)

include F in
/-- Transport a boundary-component function to the actual medial-loop carrier. -/
def loopBoundaryLabel : Loop hN hM (rcSmoothing A) → ℚ :=
  Quotient.lift (fun d => F (ribbonBoundaryOf hN hM A d)) (fun _ _ h => by
    apply congrArg F
    apply Quotient.sound
    rwa [ribbonBoundary_eq_directedStep])

/-- Expand a genuine cellular face boundary into individual medial-loop shadows. -/
theorem ribbonFaceBoundary_eq_sum_loopBoundaryCycles :
    ribbonFaceBoundary hN hM A F =
      ∑ q : Loop hN hM (rcSmoothing A),
        loopBoundaryLabel hN hM A F q • (loopBoundaryCycle q).val := by
  classical
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,loopBoundaryCycle,
    ribbonFaceBoundary,LinearMap.coe_mk,AddHom.coe_mk,loopBoundaryFunction_corner,
    mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rfl

include hzero in
/-- Vanishing vertical winding on all loops kills the vertical displacement
of every actual cellular boundary. -/
theorem boundary_vertical_displacement_zero_of_loops_zero (hf : f ∈ ribbonBoundarySpace hN hM A) :
    diamondVerticalDisplacement f.val = 0 := by
  classical
  obtain ⟨F,hF⟩ := hf
  have hF' : ribbonFaceBoundary hN hM A F = f.val := congrArg Subtype.val hF
  rw [← hF',ribbonFaceBoundary_eq_sum_loopBoundaryCycles,diamondVerticalDisplacement]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm,← Finset.sum_neg_distrib]
  apply Finset.sum_eq_zero
  intro q _
  rw [← Finset.mul_sum]
  have hq : -(∑ e, (loopBoundaryCycle q).val e) = 0 := by
    change diamondVerticalDisplacement (loopBoundaryCycle q).val = 0
    simp [loopBoundaryCycle_displacement_y, loop_vertical_displacement _ j q, hzero q, mul_zero]
  grind

include hNp hMp hX in
/-- When all primal cycles are vertically aligned, each is an actual ribbon
boundary, by the exact intersection-radical theorem. -/
theorem mem_boundary_of_horizontal_displacement_zero : f ∈ ribbonBoundarySpace hN hM A := by
  apply mem_ribbonBoundarySpace_of_intersection_zero hN hM A f
  intro g
  apply (ribbonIntersection_eq_zero_iff_windingDeterminant_zero hNp hMp f g).2
  simp [diamondWindingDeterminant, hX f, hX g, zero_mul, mul_zero, sub_self]

include hNp hMp hX in
/-- A nonzero vertical primal cycle with no horizontal primal homology forces
an actual vertically winding medial loop. -/
theorem exists_vertical_loop_of_aligned_vertical_cycle
    (hY : ∃ f : diamondCycleSpace hN hM A, diamondVerticalDisplacement f.val ≠ 0) :
    ∃ q : Loop hN hM (rcSmoothing A),
      loopVertical j q ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨f,hf⟩ := hY
  exact hf (boundary_vertical_displacement_zero_of_loops_zero hN hM j A hn f
    (mem_boundary_of_horizontal_displacement_zero hN hM hNp hMp A hX f))

end
end PottsDiscontinuity.TorusTopology
