module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
public import HypoellipticAleksandrov.Parabolic.TimeReversal
import Mathlib.Analysis.Calculus.Deriv.Shift
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

open private HypoellipticAleksandrov.Parabolic.KrylovEstimate.gradient_affine from HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine


/-!
# Reflect-and-rescale calculus for the localized occupation estimate

The proof of the companion paper, Proposition 4.2, applies Krylov's estimate to
`u(t, y) = V(1 - R² t, v_* + R y)`.  This file proves the slice calculus of that map for the
anisotropic carriers `IsScalarC12On` and `IsScalarC12UpTo`: the map factors as the time
reflection `(r, y) ↦ (1 - r, y)` followed by the parabolic affine map
`(t, y) ↦ (R² t, v_* + R y)`, and the derivative identities
`u_t = -R² V_r`, `D_y u = R D_v V`, `D_y² u = R² D_v² V` hold.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set


variable {d : ℕ}

variable (R : ℝ) (vStar : PDE.Vec d)

/-- The reflect-and-rescale map `(t, y) ↦ (1 - R² t, v_* + R y)`. -/
def reflectScale  (z : TimeVelocity d) : TimeVelocity d :=
  (1 - R ^ 2 * z.1, vStar + R • z.2)

/-- The reflect-and-rescale map is the time reflection of a parabolic affine map. -/
theorem reflectScale_eq  :
    reflectScale R vStar = timeReflection ∘ parabolicAffine 0 vStar R := by
  ext <;> simp_all [reflectScale, timeReflection, parabolicAffine] <;> ring

/-- The reflect-and-rescale map is continuous. -/
theorem continuous_reflectScale  :
    Continuous (reflectScale R vStar) := by
  unfold reflectScale
  fun_prop

variable (V : TimeVelocity d → ℝ) (z : TimeVelocity d)

/-- Reflection reverses the scalar time derivative. -/
theorem scalarTimeDerivative_timeReflectedScalar  :
    scalarTimeDerivative (timeReflectedScalar V) z =
      -scalarTimeDerivative V (timeReflection z) := (id (id (id (deriv_comp_const_sub (fun r => V (r, z.2)) 1 z.1))))

/-- Reflection preserves the scalar spatial gradient. -/
theorem scalarSpatialGradient_timeReflectedScalar  :
    scalarSpatialGradient (timeReflectedScalar V) z =
      scalarSpatialGradient V (timeReflection z) :=
  rfl

/-- Reflection preserves the scalar spatial Hessian. -/
theorem scalarSpatialHessian_timeReflectedScalar  :
    scalarSpatialHessian (timeReflectedScalar V) z =
      scalarSpatialHessian V (timeReflection z) :=
  rfl

/-- Scalar `C^{1,2}` regularity transfers through the time reflection. -/
theorem isScalarC12On_timeReflectedScalar {V : TimeVelocity d → ℝ} {D : HypoellipticAleksandrov.Parabolic.Region d}
    (hV : IsScalarC12On V D) :
    IsScalarC12On (timeReflectedScalar V) (timeReflection ⁻¹' D) := by
  have hm : MapsTo (timeReflection (d := d)) (timeReflection ⁻¹' D) D := fun _ hz => hz
  have hc : ContinuousOn (timeReflection (d := d)) (timeReflection ⁻¹' D) :=
    continuous_timeReflection.continuousOn
  refine ⟨hV.continuousOn.comp hc hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz



    exact (show DifferentiableAt ℝ (fun r  => V (r, z.2)) (1 - z.1) from (hV.timeSlice_differentiableAt  hz)).comp z.1 (show DifferentiableAt ℝ (fun r : ℝ => 1 - r) z.1 by fun_prop)
  · intro z hz
    exact hV.spatialSlice_contDiffAt  hz
  · refine ((hV.continuousOn_scalarTimeDerivative.comp hc hm).neg).congr ?_
    intro z _
    exact scalarTimeDerivative_timeReflectedScalar V z
  · exact hV.continuousOn_scalarSpatialGradient.comp hc hm
  · exact hV.continuousOn_scalarSpatialHessian.comp hc hm




/-- The spatial gradient under a parabolic affine pullback. -/
theorem scalarSpatialGradient_parabolicAffine (u : TimeVelocity d → ℝ) (b : ℝ)
    (v : PDE.Vec d) (ρ : ℝ) (z : TimeVelocity d)
    (hu : DifferentiableAt ℝ (fun y : PDE.Vec d => u (b + ρ ^ 2 * z.1, y)) (v + ρ • z.2)) :
    scalarSpatialGradient (u ∘ parabolicAffine b v ρ) z =
      ρ • scalarSpatialGradient u (parabolicAffine b v ρ z) :=
  _root_.HypoellipticAleksandrov.Parabolic.KrylovEstimate.gradient_affine (fun y => u (b + ρ ^ 2 * z.1, y)) v ρ z.2 hu

variable {V : TimeVelocity d → ℝ} {D : HypoellipticAleksandrov.Parabolic.Region d} (hD : IsOpen D) (hV : IsScalarC12On V D) {R : ℝ} (hR : 0 < R) (vStar : PDE.Vec d)

include hD hV hR
/-- `C^{1,2}` regularity and the derivative identities for `V ∘ reflectScale`. -/
theorem isScalarC12On_reflectScale  :
    IsScalarC12On (fun z => V (reflectScale R vStar z)) (reflectScale R vStar ⁻¹' D) ∧
    ∀ z ∈ reflectScale R vStar ⁻¹' D,
      scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z =
        -R ^ 2 * scalarTimeDerivative V (reflectScale R vStar z) ∧
      scalarSpatialGradient (fun w => V (reflectScale R vStar w)) z =
        R • scalarSpatialGradient V (reflectScale R vStar z) ∧
      scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z =
        R ^ 2 • scalarSpatialHessian V (reflectScale R vStar z) := by

  have hV' := isScalarC12On_timeReflectedScalar hV
  have hfun : (fun z => V (reflectScale R vStar z)) =
      timeReflectedScalar V ∘ parabolicAffine 0 vStar R := by
    funext z
    simp only [Function.comp_apply, timeReflectedScalar_apply]
    exact congrArg V (congrFun (reflectScale_eq R vStar) z)
  have hpre : parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) =
      reflectScale R vStar ⁻¹' D := by
    rw [reflectScale_eq, Set.preimage_comp]
  obtain ⟨hC, hform⟩ := KrylovEstimate.scalarC12On_affine_pullback (hD.preimage continuous_timeReflection)
    _ hV' 0 vStar hR
  rw [hpre] at hC hform
  rw [hfun]
  refine ⟨hC, ?_⟩
  intro z hz

  have hΦ : reflectScale R vStar z = timeReflection (parabolicAffine 0 vStar R z) :=
    congrFun (reflectScale_eq R vStar) z
  obtain ⟨ht, hh⟩ := hform z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, scalarTimeDerivative_timeReflectedScalar, hΦ]
    ring
  ·
    rw [scalarSpatialGradient_parabolicAffine _ 0 vStar R z ((hV'.spatialSlice_contDiffAt (show z ∈ parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) by
        rw [hpre]; exact hz)).differentiableAt (by norm_num)),
      scalarSpatialGradient_timeReflectedScalar, hΦ]
  · rw [hh, scalarSpatialHessian_timeReflectedScalar, hΦ]

/-- The scaled backward operator: `u_t - a : D² u = -R² (V_r + B : D² V)` at `reflectScale`. -/
theorem scaled_operator_eq
    (B : CoefficientField d) {z : TimeVelocity d} (hz : z ∈ reflectScale R vStar ⁻¹' D) :
    scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z -
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z) =
      -R ^ 2 * (scalarTimeDerivative V (reflectScale R vStar z) +
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian V (reflectScale R vStar z))) := by
  obtain ⟨-, hform⟩ := isScalarC12On_reflectScale hD hV hR vStar
  obtain ⟨h1, -, h3⟩ := hform z hz
  rw [h1, h3, HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
