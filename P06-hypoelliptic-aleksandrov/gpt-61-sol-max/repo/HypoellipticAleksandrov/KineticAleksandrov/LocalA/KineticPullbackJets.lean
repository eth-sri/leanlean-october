module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullbackTime
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Calculus
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
import Mathlib.Tactic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

section
open private HypoellipticAleksandrov.Parabolic.KrylovEstimate.gradient_affine from HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
private alias _sharedProof_320_1 := HypoellipticAleksandrov.Parabolic.KrylovEstimate.gradient_affine
end


/-! # Classical jets under kinetic affine normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic Scaling


variable {d : ℕ}

/-- Pull a physical solution back to the centered unit coordinates. -/
def kineticPullback  (u : HypoellipticAleksandrov.KineticScalarField d) (P₀ : KineticPoint d) (R : ℝ) :=
  u ∘ kineticAffine P₀ R

/-- The coordinate gradient of an affine slice scales by its linear factor. -/
theorem classicalGradient_affine  {f : PDE.ScalarField d}
    (a : PDE.Vec d) (c : ℝ) (x : PDE.Vec d)
    (hf : DifferentiableAt ℝ f (a + c • x)) :
    PDE.classicalGradient (fun y => f (a + c • y)) x =
      c • PDE.classicalGradient f (a + c • x) := (_sharedProof_320_1 f a c x hf)


variable {u : HypoellipticAleksandrov.KineticScalarField d} {D : Set (KineticPoint d)}

section
variable (hu : IsKineticC112On u D) (P₀ : KineticPoint d) (R : ℝ) (P : KineticPoint d) (hp : kineticAffine P₀ R P ∈ D)

include hu hp
/-- Position jets acquire the cubic spatial dilation. -/
theorem kineticPullback_positionGradient    :
    kineticPositionGradient (kineticPullback u P₀ R) P =
      R ^ 3 • kineticPositionGradient u (kineticAffine P₀ R P) := by
  let a := P₀.position + (R ^ 2 * P.time) • P₀.velocity
  have he : (fun x => kineticPullback u P₀ R ⟨P.time, x, P.velocity⟩) =
      (fun x => u ⟨P₀.time + R ^ 2 * P.time, a + R ^ 3 • x,
        P₀.velocity + R • P.velocity⟩) := by
    funext x
    simp only [kineticPullback, Function.comp_def, kineticAffine, a]
    congr 1
    abel_nf
  unfold kineticPositionGradient
  rw [he]
  have hpos : (kineticAffine P₀ R P).position = a + R ^ 3 • P.position := by
    dsimp [kineticAffine, a]
    abel_nf
  have hf := hu.positionSlice_contDiffAt hp
  rw [hpos] at hf ⊢
  exact classicalGradient_affine a (R ^ 3) P.position
    (hf.differentiableAt (by norm_num))

/-- Velocity jets acquire the linear velocity dilation. -/
theorem kineticPullback_velocityGradient    :
    kineticVelocityGradient (kineticPullback u P₀ R) P =
      R • kineticVelocityGradient u (kineticAffine P₀ R P) := by
  unfold kineticVelocityGradient kineticPullback
  exact classicalGradient_affine P₀.velocity R P.velocity
    ((hu.velocitySlice_contDiffAt hp).differentiableAt (by norm_num))

/-- Velocity Hessians acquire the quadratic dilation. -/
theorem kineticPullback_velocityHessian    :
    kineticVelocityHessian (kineticPullback u P₀ R) P =
      R ^ 2 • kineticVelocityHessian u (kineticAffine P₀ R P) := by
  rw [kineticVelocityHessian_eq_sliceHessian, kineticVelocityHessian_eq_sliceHessian]
  exact sliceHessian_affine (hu.velocitySlice_contDiffAt hp)
end


variable (hD : IsOpen D) (hu : IsKineticC112On u D) (P₀ : KineticPoint d) (R : ℝ) (P : KineticPoint d) (hp : kineticAffine P₀ R P ∈ D)

include hD hu hp
/-- Time dilation also differentiates the Galilean translation of position. -/
theorem kineticPullback_time_hasDerivAt    :
    HasDerivAt (fun t => kineticPullback u P₀ R ⟨t, P.position, P.velocity⟩)
      (R ^ 2 * (kineticTimeDerivative u (kineticAffine P₀ R P) +
        PDE.vecDot P₀.velocity (kineticPositionGradient u (kineticAffine P₀ R P))))
      P.time := by
  have he : ∀ t : ℝ, t • (R ^ 2 • P₀.velocity) =
      (R ^ 2 * t) • P₀.velocity := by
    intro t
    rw [smul_smul, mul_comm]
  have h := kinetic_moving_time_hasDerivAt hD hu P₀.time (R ^ 2)
    (P₀.position + R ^ 3 • P.position) (R ^ 2 • P₀.velocity)
    (P₀.velocity + R • P.velocity) P.time (by simpa only [he, kineticAffine] using hp)
  simp only [he] at h
  simp only [kineticPullback, Function.comp_def, kineticAffine]
  convert h using 1
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

/-- The exact time jet of the normalized solution. -/
theorem kineticPullback_timeDerivative    :
    kineticTimeDerivative (kineticPullback u P₀ R) P =
      R ^ 2 * (kineticTimeDerivative u (kineticAffine P₀ R P) +
        PDE.vecDot P₀.velocity (kineticPositionGradient u (kineticAffine P₀ R P))) :=
  (kineticPullback_time_hasDerivAt hD hu P₀ R P hp).deriv

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
