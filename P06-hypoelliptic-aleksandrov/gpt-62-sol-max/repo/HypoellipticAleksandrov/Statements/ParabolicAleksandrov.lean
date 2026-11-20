module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import HypoellipticAleksandrov.Parabolic.KrylovEstimate.Assembly

/-!
# Parabolic Aleksandrov estimate (Krylov)

Companion paper, Theorem 4.1: Krylov's parabolic Aleksandrov estimate.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic

/-- Krylov's parabolic Aleksandrov estimate, uniformly over location and height. -/
theorem parabolic_aleksandrov
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t₀ : ℝ) (v₀ : PDE.Vec N) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (a : TimeVelocity N → PDE.Mat N) (f u : TimeVelocity N → ℝ),
        ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀,
          lam • (1 : PDE.Mat N) ≤ a z ∧ a z ≤ Lam • (1 : PDE.Mat N)) →
        MemLp f (parabolicExponent N) (volume.restrict (krylovCylinder t₀ h v₀)) →
        IsScalarC12UpTo u (krylovCylinder t₀ h v₀) (krylovClosedCylinder t₀ h v₀) →
        (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
          scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
            ≤ f z) →
        (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
        ∀ z ∈ krylovCylinder t₀ h v₀,
          u z ≤ C * parabolicLpNormOn N f (krylovCylinder t₀ h v₀) := by
  obtain ⟨C, hC, hK⟩ := parabolic_aleksandrov_of_lower_ellipticity N hN lam hlam
  refine ⟨C, hC, ?_⟩
  intro t₀ v₀ h hh hh1 a f u ha _ hell hf hu
  exact hK t₀ v₀ h hh hh1 a f u ha (fun z hz => (hell z hz).1) hf
    hu.isScalarC12On hu.continuousOn

end HypoellipticAleksandrov.Parabolic
