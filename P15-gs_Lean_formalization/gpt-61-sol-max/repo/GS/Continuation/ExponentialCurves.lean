
import GS.Continuation.ExponentialBasics
import GS.Extensions.GeodesicNormal



/-!
# Concrete exponential curves for m=2

The matrix exponential curves satisfy their defining ODEs, preserve
orthogonality, and have normal acceleration under the stated hypotheses.

This is NOT an assertion that the singular general m=3 family has geodesics.
Nor is the explicit generator image defined to be a manifold tangent space.
The embedded-orbit theorem and the intrinsic/extrinsic geodesic bridge remain
separate obligations.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable (B₂ P B₁ C Ω : Mat n)


variable (t : ℝ)

def gsExpLeft  : Mat n := B₂ * expLine C t

def gsExpRight  : Mat n := expLine Ω t * B₁

def gsExpCurve  : Mat n :=
  product2 (gsExpLeft B₂ C t) P (gsExpRight B₁ Ω t)

def gsExpVelocity  : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t) (C + P * Ω * Pᵀ)

def gsExpAcceleration  : Mat n :=
  lift (gsExpLeft B₂ C t) (P * gsExpRight B₁ Ω t)
    (accelerationCore C (P * Ω * Pᵀ))















theorem gsExpLeft_hasDerivAt  :
    HasDerivAt (gsExpLeft B₂ C) (gsExpLeft B₂ C t * C) t := by
  unfold gsExpLeft
  simpa only [ Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    GS.MatrixBase.hasDerivAt_matrix_mul (hasDerivAt_const t B₂) (hasDerivAt_expLine C t)

theorem gsExpRight_hasDerivAt  :
    HasDerivAt (gsExpRight B₁ Ω) (Ω * gsExpRight B₁ Ω t) t := by
  unfold gsExpRight
  simpa only [ Matrix.mul_zero, add_zero, Matrix.mul_assoc] using
    GS.MatrixBase.hasDerivAt_matrix_mul (hasDerivAt_expLine_left Ω t) (hasDerivAt_const t B₁)

/-- The carrier P exp(t Omega) B1 has the constant left generator P Omega P^T. -/
theorem gsExpCarrier_hasDerivAt (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (fun s : ℝ => P * gsExpRight B₁ Ω s)
      ((P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t)) t := by
  have he : (P * Ω * Pᵀ) * (P * gsExpRight B₁ Ω t) =
      P * (Ω * gsExpRight B₁ Ω t) := by
    simp [Matrix.mul_assoc,← Matrix.mul_assoc Pᵀ P,hP.1]
  rw [he]
  simpa only [Matrix.zero_mul, zero_add] using
    GS.MatrixBase.hasDerivAt_matrix_mul (hasDerivAt_const t P) (gsExpRight_hasDerivAt B₁ Ω t)

theorem gsExpCurve_hasDerivAt (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpCurve B₂ P B₁ C Ω) (gsExpVelocity B₂ P B₁ C Ω t) t := by
  have h := GS.MatrixBase.hasDerivAt_matrix_mul
    (gsExpLeft_hasDerivAt B₂ C t) (gsExpCarrier_hasDerivAt P B₁ Ω hP t)
  unfold gsExpCurve
  simpa only [product2, gsExpVelocity, lift, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc, gsExpCurve] using h

theorem gsExpVelocity_hasDerivAt (hP : Orthogonal P) (t : ℝ) :
    HasDerivAt (gsExpVelocity B₂ P B₁ C Ω) (gsExpAcceleration B₂ P B₁ C Ω t) t := by
  have h := GS.MatrixBase.hasDerivAt_matrix_mul
    (GS.MatrixBase.hasDerivAt_matrix_mul (gsExpLeft_hasDerivAt B₂ C t)
      (hasDerivAt_const t (C+P*Ω*Pᵀ)))
    (gsExpCarrier_hasDerivAt P B₁ Ω hP t)
  change HasDerivAt (fun s => gsExpLeft B₂ C s * (C+P*Ω*Pᵀ) * (P*gsExpRight B₁ Ω s)) _ t
  convert h using 1 <;>
    simp only [gsExpAcceleration, lift, accelerationCore, two_smul, Matrix.mul_zero, add_zero] <;>
      noncomm_ring








end GS.Continuation
