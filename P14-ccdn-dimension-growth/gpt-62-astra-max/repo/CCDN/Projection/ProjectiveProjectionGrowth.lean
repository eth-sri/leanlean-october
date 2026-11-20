/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveBox
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import CCDN.Projection.ProjectiveLinearCountTransfer

/-! The quantitative counting step for the constructed projection. The
height and finite-fiber losses remain polynomial in the original degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable (m k : ℕ)

/-- The exponent `18 + 3 * m + N + 2 * N * (m + 1)`, with `N = m + k + 2`, of the degree in the
point-count bound obtained by projecting an `(m + 1)`-dimensional variety in `ℙ^(m + k + 1)` to a
hypersurface in `ℙ^(m + 2)`. -/
def projectionDegreeExponent : ℕ :=
  18 + 3 * m + (m + k + 2) + 2 * (m + k + 2) * (m + 1)

/-- There is a constant `C` depending only on `m` and `k` with the following property. Let integer
forms `b`, with coefficients bounded by the birational projection height, satisfy an irreducible
homogeneous relation `f` of degree `d ≥ 5` modulo `I`, and let every affine fiber of the projection
of the zero locus of `I` have at most `d ^ (m + k + 2)` points. Then the zero locus of `I` in
`ℙ^(m + k + 1)` has at most `C * d ^ projectionDegreeExponent m k * B ^ (m + 1)` rational points of
height at most `B`. -/
theorem projective_projection_dimension_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (CoordinatePolynomial (m + k + 2))) (d : ℕ), 5 ≤ d →
      ∀ b : Fin (m + 3) → Fin (m + k + 2) → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + k + 2) d) →
      ∀ f : CoordinatePolynomial (m + 3),
      Irreducible f → f.IsHomogeneous d → f.totalDegree = d →
      aeval (fun i => integerLinearForm (b i)) f ∈ I →
      (∀ z : Fin (m + 3) → ℚ, ∀ s : Finset (Fin (m + k + 2) → ℚ),
        (∀ x ∈ s, x ∈ idealZeroLocus I) →
        (∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) →
        s.card ≤ d ^ (m + k + 2)) →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_hypersurface_dimension_growth m
  let N := m + k + 2
  let T : ℝ := N * birationalProjectionHeightConstant N
  have hT : 1 ≤ T := by
    have hpos := birationalProjectionHeightConstant_pos N
    bound
  refine ⟨C * T ^ (m + 1), by positivity, ?_⟩
  intro I d hd b hb f hf hfhom hfdeg hrel hfiber B hB
  let H : ℝ := birationalProjectionHeightConstant N * d ^ (2 * N)
  have hH : 1 ≤ H := by
    have hconst : (1 : ℝ) ≤ birationalProjectionHeightConstant N := by
      exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos N)
    bound
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight N d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le N d (by omega)
  have hbound := projective_integer_linear_count_transfer
    (n := m + k + 1) (m := m + 2) I b f (by grind)
    hrel (d ^ N) hfiber H B (by linarith) hbH
  have hheight : 1 ≤ (N : ℝ) * H * B := by
    bound
  have htarget := hcount f (by rwa [hfdeg]) hf (by omega) (N * H * B) hheight
  rw [hfdeg] at htarget
  have hnon : (0 : ℝ) ≤ (d : ℝ) ^ N := by positivity
  have hh := by
    apply (show (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      d ^ N * projectiveCount (projectiveZeroLocus f) (N * H * B) by
        exact_mod_cast hbound).trans
    exact mul_le_mul_of_nonneg_left htarget hnon
  convert hh using 1
  dsimp only [projectionDegreeExponent, H, T, N]
  ring

end
end CCDN
