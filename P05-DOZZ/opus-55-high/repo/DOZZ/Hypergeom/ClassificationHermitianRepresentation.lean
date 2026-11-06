/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianResidual

/-! Reality symmetrizes the constant tensor obtained from the Cramer coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A real Gauss solution is a Hermitian tensor in any global analytic Gauss fundamental pair on
the slit plane. The constant coefficient matrix from the Cramer expansion is symmetrized using
the pointwise reality of the solution. -/
theorem realGaussCramer_hermitian_representation
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∃ α δ : ℝ, ∃ β : ℂ, ∀ z ∈ gaussCutPlane,
      (T z : ℂ) =
        f z * star ((α : ℂ) * f z + β * g z) +
          g z * star (star β * f z + (δ : ℂ) * g z) := by
  obtain ⟨u, v, hcoords⟩ := realGaussCramer_conjugates_have_constant_basis_coordinates
    a b c T hT hf hg hODEf hODEg hW
  let m₁₁ := star u.1
  let m₁₂ := star u.2
  let m₂₁ := star v.1
  let m₂₂ := star v.2
  let α := m₁₁.re
  let δ := m₂₂.re
  let β := (m₂₁ + star m₁₂) / 2
  have hα : α = (m₁₁ + star m₁₁) / 2 := by
    dsimp [α]
    rw [Complex.add_conj]
    norm_num
  have hδ : δ = (m₂₂ + star m₂₂) / 2 := by
    dsimp [δ]
    rw [Complex.add_conj]
    norm_num
  have hβstar : star β = (m₁₂ + star m₂₁) / 2 := by
    simp [β, star_add]
    ring
  let Q : ℂ → ℂ → ℂ := fun x y =>
    m₁₁ * x * star x + m₁₂ * x * star y +
      m₂₁ * y * star x + m₂₂ * y * star y
  have hsymmetrize (x y : ℂ) :
      x * star (α * x + β * y) +
          y * star (star β * x + δ * y) =
        (Q x y + star (Q x y)) / 2 := by
    rw [hα, hδ, hβstar]
    simp [Q, β, star_add, star_mul]
    ring_nf
  refine ⟨α, δ, β, ?_⟩
  intro z hz
  have hC₁ : gaussCramerCoefficient₁ T f g z =
      m₁₁ * star (f z) + m₁₂ * star (g z) := by
    calc
      gaussCramerCoefficient₁ T f g z =
          star (star (gaussCramerCoefficient₁ T f g z)) := by simp
      _ = star (u.1 * f z + u.2 * g z) := by simp_all
      _ = m₁₁ * star (f z) + m₁₂ * star (g z) := by
        rw [star_add, star_mul, star_mul]
        ring
  have hC₂ : gaussCramerCoefficient₂ T f g z =
      m₂₁ * star (f z) + m₂₂ * star (g z) := by
    calc
      gaussCramerCoefficient₂ T f g z =
          star (star (gaussCramerCoefficient₂ T f g z)) := by simp
      _ = star (v.1 * f z + v.2 * g z) := by simp_all
      _ = m₂₁ * star (f z) + m₂₂ * star (g z) := by
        rw [star_add, star_mul, star_mul]
        ring
  have hTQ : (T z) = Q (f z) (g z) := by
    calc
      (T z) = gaussCramerCoefficient₁ T f g z * f z +
          gaussCramerCoefficient₂ T f g z * g z := ((realGaussCramer_reconstruct T (hW z hz)).1)
      _ = Q (f z) (g z) := by grind
  have hQreal : Q (f z) (g z) = star (Q (f z) (g z)) := by
    calc
      Q (f z) (g z) = (T z) := hTQ.symm
      _ = star (T z : ℂ) := by simp
      _ = star _ := by simp_all
  calc
    (T z) = Q (f z) (g z) := hTQ
    _ = (Q (f z) (g z) + star _) / 2 := by
      calc
        Q (f z) (g z) = (Q (f z) (g z) + Q (f z) (g z)) / 2 := by ring
        _ = (Q (f z) (g z) + star _) / 2 := by tauto
    _ = f z * star _ +
          g z * star _ :=
      (hsymmetrize (f z) (g z)).symm

end DOZZ.Proofs
