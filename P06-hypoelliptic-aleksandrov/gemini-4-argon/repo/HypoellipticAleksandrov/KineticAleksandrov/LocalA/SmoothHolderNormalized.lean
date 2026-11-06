module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ScalingSlices
public import HypoellipticAleksandrov.Parabolic.LocalHolder.Holder
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIteration
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationDyadic
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometric
import HypoellipticAleksandrov.Parabolic.LocalHolder.ForcedIterationGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderExponent
import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderGeometry
import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillation
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationGeometry
import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationScaling
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementForward
import HypoellipticAleksandrov.Statements.ParabolicHarnack
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Combine parabolic slice regularity with spatial control

The first-derivative premise of the internal combination lemma is discharged by the
exact spatial-bound input in SmoothHolder. Amplitude is the literal outer oscillation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder
open LocalHolder KineticAleksandrov.LocalA HypoellipticAleksandrov.Parabolic.LocalHolder HypoellipticAleksandrov.Parabolic
open scoped Matrix.Norms.Elementwise
open Filter
open scoped Topology

/- The transport forcing is bounded by the physical position differential. -/
theorem abs_position_transport_le {d } (u : KineticPoint d → ℝ)
    (P : KineticPoint d) (v : PDE.Vec d) :
    |PDE.vecDot v (kineticPositionGradient u P)| ≤
      ‖fderiv ℝ (physicalPositionSlice u P) P.position‖ * PDE.vecEuclideanNorm v := by
  have he : PDE.vecDot v (kineticPositionGradient u P) =
      fderiv ℝ (physicalPositionSlice u P) P.position v := by
    rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he, ← Real.norm_eq_abs]
  exact ((fderiv ℝ (physicalPositionSlice u P) P.position).le_opNorm v).trans
    (mul_le_mul_of_nonneg_left (PDE.norm_le_vecEuclideanNorm v) (norm_nonneg _))

/- The spatial displacement term is bounded by its kinetic Hölder power on the unit ball. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
