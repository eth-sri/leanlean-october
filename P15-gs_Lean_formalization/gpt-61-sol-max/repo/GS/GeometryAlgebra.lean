
import GS.Projection
import Mathlib.Tactic.NoncommRing



/-!
# Algebra underlying tangent operations and transport

The Taylor identity is an exact polynomial identity. It is not asserted to be
a proof of existence of an embedded manifold, a quotient retraction, or of a
geodesic. These analytic obligations are separated in the coverage report.

-/

open Matrix
namespace GS


variable (B₂ P B₁ C Ω B : Mat n)

def tangentParam  : Mat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem conjugate_skew (C : Mat n) (hC : IsSkew C) : IsSkew (B*C*Bᵀ) := by
  simp_all [IsSkew, Matrix.mul_assoc]

theorem tangentParam_factored  (hP : Orthogonal P) :
    tangentParam B₂ P B₁ C Ω = B₂ * (C + P*Ω*Pᵀ) * (P*B₁) := by
  symm
  calc
    B₂ * (C + P*Ω*Pᵀ) * (P*B₁) =
        B₂*C*P*B₁ + B₂*P*Ω*(Pᵀ*P)*B₁ := by noncomm_ring
    _ = tangentParam B₂ P B₁ C Ω := by
      rw [hP.1]
      simp [tangentParam]

end GS
