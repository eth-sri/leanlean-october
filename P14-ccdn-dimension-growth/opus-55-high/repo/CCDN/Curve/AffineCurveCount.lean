/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Statements
import CCDN.Plane.CurveCount
import CCDN.Projection.AffineProjectionCount
import CCDN.Projection.ScaleAbsorption

/-! The coefficient-uniform affine curve count of CCDN Theorem 3. A bounded integral projection
reduces a curve in `𝔸ⁿ` to an irreducible plane equation of the same degree, whose points the
plane bound `PlaneCurveBound` counts; exceptional fibres contribute at most `d(d − 1)` points and
the enlarged box costs a constant depending only on `n`. -/

namespace CCDN
section
open MvPolynomial

/-- The affine curve counting bound `AffineCurveBound` of CCDN Theorem 3: the plane bound, after
a degree-preserving bounded projection to the plane. -/
theorem affine_curve_count : AffineCurveBound := by
  obtain ⟨C, hC, hplane⟩ := planeCurveBound_of_residue_bound planeResidueConstant_pos.le planeResidueBound
  intro n _hn
  let K := Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)
  have hK : 0 < K := by
    have := projectionLogConstant_nonneg n
    positivity
  refine ⟨C * K + 1, by positivity, ?_⟩
  intro I hI d hd hdegree B hB
  obtain ⟨f, hf, hfd, hred⟩ : ∃ f : MvPolynomial (Fin 2) ℚ, Irreducible f ∧ f.totalDegree = d ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
    obtain ⟨k₀, k₁, f, hk₀, hk₁, hf, hfd, hker, hcount⟩ :=
      exists_bounded_projection_card_le I d hd hdegree
    refine ⟨f, hf, hfd, fun B hB => ?_⟩
    let S := integralPoints (idealZeroLocus I) B
    let R := S.image rationalPoint
    let π : RatPoint n → RatPoint 2 := fun z =>
      ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
    let P := S.image (degreeProjection n k₀ k₁)
    have hc := hcount R (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact (mem_integralPoints.mp hz).2)
    have hRcard := Finset.card_image_of_injective S (rationalPoint_injective n)
    have himg : R.image π = P.image rationalPoint := by
      simp [R, P, Finset.image_image]
      congr 1
      funext z
      exact (rationalPoint_degreeProjection z).symm
    rw [hRcard, himg, Finset.card_image_of_injective P (rationalPoint_injective 2)] at hc
    have hP : P ⊆ integralPoints (zeroLocus f) (projectionBoxFactor n d * B) := by
      rintro _ hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzbox := mem_integerBox.mpr (mem_integralPoints.mp hz).1
      apply mem_integralPoints.mpr
      refine ⟨mem_integerBox.mp (degreeProjection_box hk₀ hk₁ (by linarith) hzbox), ?_⟩
      change eval (rationalPoint (degreeProjection n k₀ k₁ z)) f = 0
      rw [rationalPoint_degreeProjection]
      have hfI := (hker f).mpr (dvd_refl f)
      have hh := (mem_integralPoints.mp hz).2 _ hfI
      rw [eval_polynomial_coordinate_map] at hh
      convert hh using 1
      congr 2
      funext j
      fin_cases j <;> rfl
    exact hc.trans (Nat.add_le_add_right (Finset.card_le_card hP) _)
  have hbox :=
    one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hp := hplane f hf (hfd.symm ▸ hd) _ hbox
  rw [hfd] at hp
  have hredR : (count (idealZeroLocus I) B : ℝ) ≤
      count (zeroLocus f) (projectionBoxFactor n d * B) + (d * (d - 1) : ℕ) := by
    exact_mod_cast hred B hB
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have herr : ((d * (d - 1) : ℕ) : ℝ) ≤ curveBound d B := by
    calc
      _ ≤ (d : ℝ) ^ 2 := by
        exact_mod_cast (show d * (d - 1) ≤ d ^ 2 by
          simpa [pow_two] using Nat.mul_le_mul_left d (Nat.sub_le d 1))
      _ ≤ d ^ 4 := by nlinarith [one_le_pow₀ hd1 (n := 2), sq_nonneg (d ^ 2 - 1)]
      _ ≤ _ := degree_four_le_curveBound hd hB
  calc
    _ ≤ (count (zeroLocus f) (projectionBoxFactor n d * B) : ℝ) + (d * (d - 1) : ℕ) := hredR
    _ ≤ C * curveBound d (projectionBoxFactor n d * B) + curveBound d B := add_le_add hp herr
    _ ≤ C * (K * curveBound d B) + curveBound d B :=
      add_le_add (mul_le_mul_of_nonneg_left (curveBound_scale_of_log_le hd (projectionBoxFactor_one_le n d) hB
    (projectionLogConstant_nonneg n) (projectionBoxFactor_log_le n hd)) hC.le)
        le_rfl
    _ = _ := by ring

