module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonFaces
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # The classical operator at a closed-cylinder maximum outside the exit faces -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set
open scoped Topology

variable {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)

/-- The velocity of a non-exit point is strictly inside the velocity ball. -/
theorem comparison_velocity_interior  {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR) :
    P.velocity ∈ PDE.euclideanBall Z₀.velocity R := (id
  (fun hb =>
    id
      (lt_of_le_of_ne
        (Eq.mp (congrFun' (congrArg LE.le (congrArg PDE.vecNormSq (sub_zero (P.velocity - Z₀.velocity)))) (R ^ 2)) hb)
        fun heq => hnot ((mem_exitBoundary_iff Z₀ P R hR).mpr ⟨hP, Or.inr (Or.inl heq)⟩)))
  (closure_forwardCylinder_bounds Z₀ R hR hP).right.right)

variable {D : Set (KineticPoint d)} (hD : IsOpen D) (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D) {u : HypoellipticAleksandrov.KineticScalarField d} (hu : IsKineticC112On u D) (A : FullKineticCoefficient d)

include hD hQD hu
/-- At a non-exit closed-cylinder maximum, transport plus diffusion is nonpositive.
Only the source anisotropic regularity on an open neighbourhood is used. -/
theorem comparison_operator_nonpos_at_max
     {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR)
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P)
    (hA : (A P.time P.position P.velocity).PosSemidef) :
    forwardKineticOperator A u P ≤ 0 := by
  have htransport := hasDerivAt_freeTransport hD hu (hQD hP)
  obtain ⟨η,hη,hstay⟩ := comparison_freeTransport_stays Z₀ R hR hP hnot

  have ht := deriv_nonpos_of_future_localMax htransport.differentiableAt (by
      filter_upwards [Iio_mem_nhds hη] with h hh hhn
      simpa only [mem_ofPred_eq,add_zero,zero_smul] using hmax (hstay h hhn hh))
  rw [htransport.deriv] at ht

  have hdiff := matrixContraction_sliceHessian_nonpos_of_localMax
    (hu.velocitySlice_contDiffAt (hQD hP)) (by

        filter_upwards [(PDE.isOpen_euclideanBall Z₀.velocity R).mem_nhds (comparison_velocity_interior Z₀ R hR hP hnot)] with v hv
        apply hmax
        rw [comparison_closure_forwardCylinder_eq]
        have hb := closure_forwardCylinder_bounds Z₀ R hR hP
        change (Z₀.time ≤ P.time ∧ P.time ≤ Z₀.time + R ^ 2) ∧
          relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
          v - Z₀.velocity ∈ PDE.euclideanClosedBall 0 R
        refine ⟨hb.1,hb.2.1,?_⟩

        simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using (PDE.euclideanBall_subset_euclideanClosedBall _ _ hv)) hA
  rw [forwardKineticOperator_apply, kineticVelocityHessian_eq_sliceHessian]
  exact add_nonpos ht hdiff

/-- A positive maximum of a strict subsolution is on the exit boundary. -/
theorem comparison_inner_maximum_exclusion

    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    {P : KineticPoint d} (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P) (hpos : 0 < u P) :
    P ∈ exitBoundary Z₀ R hR := by
  by_contra hnot
  exact (not_le.mpr (hstrict P (hQD hP) hpos))
    (comparison_operator_nonpos_at_max Z₀ R hR hD hQD hu A hP hnot hmax (hA P (hQD hP)))

end HypoellipticAleksandrov.KineticAleksandrov
