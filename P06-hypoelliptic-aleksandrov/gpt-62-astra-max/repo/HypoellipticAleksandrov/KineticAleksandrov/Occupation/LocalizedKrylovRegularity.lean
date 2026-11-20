module

public import HypoellipticAleksandrov.KineticAleksandrov.Hormander
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus

/-!
# Closure regularity and nonnegativity of the localized source solution

For the classical solution `V` of `∂_r V + B : D_v² V = -F` on `(α, 1) × B_R(v_*)`
with zero terminal and lateral data (proof of the companion paper, Proposition 4.2), the weak
maximum principle proves `V ≥ 0`. Jet congruence on open sets is also recorded here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

section Congruence

variable {V W : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}

section
variable (hD : IsOpen D) {z : TimeVelocity d} (hW : IsScalarC12On W D) (hz : z ∈ D)
    (hVW : EqOn V W D)
include hD

include hz in
private theorem eventually_slice_time :
    ∀ᶠ r in 𝓝 z.1, (r, z.2) ∈ D := by
  have hcont : Continuous (fun r : ℝ => (r, z.2)) := by fun_prop
  exact hcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)

include hz in
private theorem eventually_slice_space :
    ∀ᶠ y in 𝓝 z.2, (z.1, y) ∈ D := by
  have hcont : Continuous (fun y : PDE.Vec d => (z.1, y)) := by fun_prop
  exact hcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)

include hVW in
/-- Two functions agreeing on an open set have the same `C^{1,2}` jets there. -/
theorem scalarJet_eqOn_of_eqOn_open :
    EqOn (scalarTimeDerivative V) (scalarTimeDerivative W) D ∧
    EqOn (scalarSpatialGradient V) (scalarSpatialGradient W) D ∧
    EqOn (scalarSpatialHessian V) (scalarSpatialHessian W) D := by
  have hgrad : EqOn (scalarSpatialGradient V) (scalarSpatialGradient W) D := by
    intro z hz
    have hs : (fun y => V (z.1, y)) =ᶠ[𝓝 z.2] (fun y => W (z.1, y)) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hVW hy
    unfold scalarSpatialGradient PDE.classicalGradient
    rw [hs.fderiv_eq (𝕜 := ℝ)]
  refine ⟨?_, hgrad, ?_⟩
  · intro z hz
    have ht : (fun r => V (r, z.2)) =ᶠ[𝓝 z.1] (fun r => W (r, z.2)) := by
      filter_upwards [eventually_slice_time hD hz] with r hr using hVW hr
    exact ht.deriv_eq
  · intro z hz
    have hg : (fun y => PDE.classicalGradient (fun w => V (z.1, w)) y) =ᶠ[𝓝 z.2]
        (fun y => PDE.classicalGradient (fun w => W (z.1, w)) y) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hgrad hy
    unfold scalarSpatialHessian
    rw [hg.fderiv_eq (𝕜 := ℝ)]

include hW hVW in
/-- `C^{1,2}` regularity on an open set is invariant under equality on that set. -/
theorem isScalarC12On_congr_open : IsScalarC12On V D := by
  obtain ⟨ht, hg, hh⟩ := scalarJet_eqOn_of_eqOn_open hD hVW
  refine ⟨hW.continuousOn.congr hVW, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h : (fun r => V (r, z.2)) =ᶠ[𝓝 z.1] (fun r => W (r, z.2)) := by
      filter_upwards [eventually_slice_time hD hz] with r hr using hVW hr
    exact (hW.timeSlice_differentiableAt hz).congr_of_eventuallyEq h
  · intro z hz
    have h : (fun y => V (z.1, y)) =ᶠ[𝓝 z.2] (fun y => W (z.1, y)) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hVW hy
    exact (hW.spatialSlice_contDiffAt hz).congr_of_eventuallyEq h
  · exact hW.continuousOn_scalarTimeDerivative.congr ht
  · exact hW.continuousOn_scalarSpatialGradient.congr hg
  · exact hW.continuousOn_scalarSpatialHessian.congr hh

end

end Congruence

section Solution

variable {lam Lam : ℝ} {B : CoefficientField d} {F : TimeVelocity d → ℝ}
  {α : ℝ} {vStar : PDE.Vec d} {R : ℝ}

variable (hlam : 0 < lam) (hF0 : ∀ z, 0 ≤ F z) (hα1 : α < 1) (hR : 0 < R)
    (hsmooth : IsSmoothCoefficient B) (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
include hlam hlow

end Solution

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
