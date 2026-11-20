/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.HomogeneousProjectionEquation
import CCDN.Projection.ProjectiveLinearCountTransfer

/-! Transfer a hypersurface bound through the bounded integral projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The projection costs a factor of `d` for the fibers and the height loss raised to the
projective dimension. The same argument applies to the plane and higher-dimensional bounds. -/
theorem ProjectiveHypersurfaceGrowth.projected {m e : ℕ}
    (h : ProjectiveHypersurfaceGrowth m e) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime → IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I (m + 1) d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (e + 1 + 2 * (n + 1) * (m + 1)) * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := h
  let A : ℝ := birationalProjectionHeightConstant (n + 1)
  let T : ℝ := ((n + 1 : ℕ) : ℝ) * A
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos (n + 1))
  refine ⟨C * T ^ (m + 1), by dsimp [T]; positivity, ?_⟩
  intro I hprime hI d hd hdimdeg B hB
  obtain ⟨b, f, hb, hN, hP, rfl⟩ :=
    exists_bounded_birational_hypersurface_projection (m + 1) (n + 1)
      I d hdimdeg
  have hfhom := homogeneous_projection_equation I hI _ (fun _ => linearForm_isHomogeneous _)
    f hP.irreducible.ne_zero hP.ker_eq
  let H := A * (f.totalDegree : ℝ) ^ (2 * (n + 1))
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by exact_mod_cast hd.trans' (by decide : 1 ≤ 5)))
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh := (hb i j).trans (Int.ofNat_le.mpr
      (integerBirationalProjectionHeight_le (n + 1) f.totalDegree (by omega)))
    dsimp [H, A]
    exact_mod_cast hh
  have hfiber (z : Fin (m + 3) → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hs : ∀ x ∈ s, x ∈ idealZeroLocus I)
      (hz : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :=
    linear_normalization_fiber_card_le I
    (fun i => integerLinearForm (b i.succ)) (fun _ => linearForm_totalDegree_le _)
    hN.injective hN.filtered f.totalDegree hdimdeg (z ∘ Fin.succ) s hs
    (fun x hx i => hz x hx i.succ)
  have hbound := projective_integer_linear_count_transfer I b f hfhom hP.aeval_mem
    1 (isHomogeneous_one _ _) f.totalDegree f.totalDegree (hfiber 0)
    (fun z s hs _ hz => hfiber z s hs hz) H B (by linarith) hbH
  simp at hbound
  have hheight : 1 ≤ ((n + 1 : ℕ) : ℝ) * H * B := by
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ n + 1 by omega)) hH) hB
  calc
    _ ≤ (f.totalDegree : ℝ) * projectiveCount (projectiveZeroLocus f) ((n + 1 : ℕ) * H * B) := by
      exact_mod_cast hbound
    _ ≤ (f.totalDegree : ℝ) * (C * (f.totalDegree : ℝ) ^ e *
        (((n + 1 : ℕ) : ℝ) * H * B) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left (hcount f hfhom hP.irreducible hd _ hheight) (by positivity)
    _ = _ := by dsimp [T, H]; ring

end
end CCDN
