/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.ProjectiveProjectionGrowth
import CCDN.Projection.BoundedDegreeNormalizationFiber

/-! Dimension growth for homogeneous prime ideals of positive
projective dimension. -/

namespace CCDN
section
open MvPolynomial

/-- The general projective-variety bound, with dimension and codimension
displayed separately. The hypotheses use the Hilbert polynomial of
the coordinate ring. -/
theorem projective_variety_dimension_growth (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I (m + 1) d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ)) (d : ℕ), 5 ≤ d →
      ∀ b : Fin (m + 3) → Fin (m + k + 2) → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + k + 2) d) →
      ∀ f : MvPolynomial (Fin (m + 3)) ℚ,
      Irreducible f → f.IsHomogeneous d → f.totalDegree = d →
      aeval (fun i => integerLinearForm (b i)) f ∈ I →
      (∀ z : Fin (m + 3) → ℚ, ∀ s : Finset (Fin (m + k + 2) → ℚ),
        (∀ x ∈ s, x ∈ idealZeroLocus I) →
        (∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) →
        s.card ≤ d ^ (m + k + 2)) →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * d ^ projectionDegreeExponent m k * B ^ (m + 1) := by
    obtain ⟨C, hC, hcount⟩ := projective_hypersurface_dimension_growth m
    let N := m + k + 2
    let T : ℝ := N * birationalProjectionHeightConstant N
    have hN : 1 ≤ N := by grind
    have hT : 1 ≤ T := by
      have hpos := birationalProjectionHeightConstant_pos N
      bound
    refine ⟨C * T ^ (m + 1), by positivity, ?_⟩
    intro I d hd b hb f hf hfhom hfdeg hrel hfiber B hB
    let H : ℝ := birationalProjectionHeightConstant N * d ^ (2 * N)
    have hd1 : (1 : ℝ) ≤ d := by bound
    have hH : 1 ≤ H := by
      have hconst : (1 : ℝ) ≤ birationalProjectionHeightConstant N := by
        exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos N)
      bound
    have hbH (i j) : |(b i j : ℝ)| ≤ H := by
      have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight N d := by
        exact_mod_cast hb i j
      apply hh.trans
      dsimp [H]
      exact_mod_cast integerBirationalProjectionHeight_le N d (by omega)
    have hbound := projective_integer_linear_count_transfer
      I b f (by grind)
      hrel (d ^ N) hfiber H B (by linarith) hbH
    have hheight : 1 ≤ N * H * B :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (mod_cast hN) hH) hB
    have htarget := hcount f (by grind) hf (by omega) (N * H * B) hheight
    rw [hfdeg] at htarget
    have hh : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        (d : ℝ) ^ N * (C * (d : ℝ) ^ (18 + 3 * m) *
          ((N : ℝ) * H * B) ^ (m + 1)) := by
      apply (show (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        (d : ℝ) ^ N * projectiveCount (projectiveZeroLocus f) ((N : ℝ) * H * B) by
          exact_mod_cast hbound).trans
      exact mul_le_mul_of_nonneg_left htarget (by positivity)
    convert hh using 1
    dsimp [projectionDegreeExponent, H, T, N]
    simp [pow_add, pow_mul, mul_pow]
    ring
  refine ⟨C, hC, ?_⟩
  intro I hprime hI d hd hdimdeg B hB
  have : I.IsPrime := hprime
  obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le (m + 1) (m + k + 2)
      (by omega) I hI d hdimdeg
  apply hcount I d hd b hb f hP.irreducible hfhom hfdeg ((hP.aeval_mem_iff _).mpr dvd_rfl) _ B hB
  intro z s hzero hproj
  exact (linear_normalization_fiber_card_le I
    (fun i => integerLinearForm (b i.succ))
    (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
    (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)).trans
    (Nat.le_self_pow (by omega) d)

