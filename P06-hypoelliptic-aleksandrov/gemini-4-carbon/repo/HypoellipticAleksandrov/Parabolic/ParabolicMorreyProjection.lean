module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareMoments
public import HypoellipticAleksandrov.Parabolic.DensityToPoint

/-!
# Physical parabolic Morrey affine projection

This module transports the unit forward-box velocity-affine moment
projection to positive-radius forward parabolic boxes.  It proves only the
exact set image, affine covariance, and reproduction properties.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped BigOperators

/-- The canonical average transported from the unit forward parabolic box. -/
noncomputable def parabolicMorreyBoxAverage {d : Nat}
    (t₀ : Real) (v₀ : PDE.Vec d) (r : Real)
    (u : TimeVelocity d -> Real) : Real :=
  parabolicMorreyUnitAverage (pullbackScalar u t₀ v₀ r)

/-- The dimensional physical velocity slope of the transported moment projection. -/
noncomputable def parabolicMorreyBoxVelocitySlope {d : Nat}
    (t₀ : Real) (v₀ : PDE.Vec d) (r : Real)
    (u : TimeVelocity d -> Real) (i : Fin d) : Real :=
  r⁻¹ * parabolicMorreyUnitVelocityCoeff (pullbackScalar u t₀ v₀ r) i

/-- The canonical time-independent velocity-affine projection on a forward box. -/
noncomputable def parabolicMorreyBoxAffineProjection {d : Nat}
    (t₀ : Real) (v₀ : PDE.Vec d) (r : Real)
    (u : TimeVelocity d -> Real) : TimeVelocity d -> Real :=
  fun z => parabolicMorreyBoxAverage t₀ v₀ r u +
    ∑ i : Fin d, parabolicMorreyBoxVelocitySlope t₀ v₀ r u i *
      (z.2 i - v₀ i)

/-- A positive-radius affine scaling maps the unit forward box onto the
corresponding physical forward box. -/
theorem parabolicAffine_image_parabolicMorreyUnitBox
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r) :
    parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d =
      parabolicBox 1 r t₀ v₀ := by
  simpa only [parabolicMorreyUnitBox] using
    (parabolicAffine_image_parabolicBox (t₀ := t₀) (v₀ := v₀) (vartheta := 1) hr)

/-- The physical projection evaluated in affine coordinates is exactly the
unit-box projection of the scalar pullback. -/
@[simp] theorem parabolicMorreyBoxAffineProjection_parabolicAffine
    {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)
    (u : TimeVelocity d -> Real) (z : TimeVelocity d) :
    parabolicMorreyBoxAffineProjection t₀ v₀ r u
        (parabolicAffine t₀ v₀ r z) =
      parabolicMorreyUnitAffineProjection
        (pullbackScalar u t₀ v₀ r) z := by
  simp only [parabolicMorreyBoxAffineProjection, parabolicMorreyBoxAverage,
    parabolicMorreyBoxVelocitySlope, parabolicMorreyUnitAffineProjection,
    parabolicAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show v₀ i + r * z.2 i - v₀ i = r * z.2 i by ring]
  calc
    (r⁻¹ * parabolicMorreyUnitVelocityCoeff (pullbackScalar u t₀ v₀ r) i) *
        (r * z.2 i) =
        (r⁻¹ * r) * parabolicMorreyUnitVelocityCoeff (pullbackScalar u t₀ v₀ r) i *
          z.2 i := by ring
    _ = parabolicMorreyUnitVelocityCoeff (pullbackScalar u t₀ v₀ r) i * z.2 i := by
      rw [inv_mul_cancel₀ hr.ne', one_mul]

end HypoellipticAleksandrov.Parabolic
