/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import CCDN.Surface.CurveComponents
public import CCDN.Surface.TopFormAuxiliary
import CCDN.Surface.NonlinearCount
import CCDN.Surface.TopFormSurfaceComponents

/-! For an auxiliary section of a surface of degree at least sixteen,
all nonlinear components together contribute O(d^18 B) bounded integer points.
The union of the degree-one components is not covered by this estimate. -/

public section
namespace CCDN
open MvPolynomial

/-- The nonlinear part of the corrected large-degree surface bound, using
constructed components and the curve counting theorem. The
constant precedes the surface equation, its coefficients, and the box radius. -/
theorem top_form_surface_nonlinear_count :
    ∃ A : ℝ, 0 < A ∧
      ∀ f : CCDN.IntegerPolynomial 3,
      HasAbsIrreducibleTopForm f →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      ∃ S : Finset (CCDN.CoordinateIdeal 3),
        ∃ δ : CCDN.CoordinateIdeal 3 → ℕ,
          (∀ P ∈ S, IsSurfaceCurve (CCDN.rationalPolynomial f) P (δ P) ∧ 0 < δ P) ∧
          ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤ topFormAuxiliaryConstant 1 *
            ↑f.totalDegree ^ (9 / 2 : ℝ) *
              B ^ (1 / (f.totalDegree : ℝ) ^ (1 / 2 : ℝ)) ∧
          (count (zeroLocus (CCDN.rationalPolynomial f) \
            (⋃ P ∈ S.filter (fun P => δ P = 1), idealZeroLocus P)) B : ℝ) ≤
              A * ↑f.totalDegree ^ 18 * B := by
  classical
  obtain ⟨K, hK, hcount⟩ := nonlinear_curve_union_bound
  let C := topFormAuxiliaryConstant 1
  have hC := topFormAuxiliaryConstant_pos 1
  let A := K * Real.exp 1 * (480 * C + 2 * C ^ 4)
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro f hir hd B hB
  obtain ⟨S, δ, hcomponents, hsum, hcover⟩ :=
    top_form_surface_curve_components f hir hB
  let T := S.filter (fun P => 2 ≤ δ P)
  let L := ⋃ P ∈ S.filter (fun P => δ P = 1), idealZeroLocus P
  have hcurves (P : CCDN.CoordinateIdeal 3) (hP : P ∈ T) :
      P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P) := by
    obtain ⟨hPS, hδ⟩ := Finset.mem_filter.mp hP
    exact ⟨(hcomponents P hPS).1.isPrime, hδ, (hcomponents P hPS).1.degree⟩
  have hsubsum : (∑ P ∈ T, δ P) ≤ ∑ P ∈ S, δ P :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
  have hTsum := by
    have hcast : ((∑ P ∈ T, δ P : ℕ) : ℝ) ≤ ((∑ P ∈ S, δ P : ℕ) : ℝ) := by
      exact_mod_cast hsubsum
    simpa only [Nat.cast_sum, ← Real.sqrt_eq_rpow] using hcast.trans hsum
  have hnonlinear :=
    hcount T δ f.totalDegree hd C B hC.le hB hcurves hTsum
  have houtside :
      count (zeroLocus (CCDN.rationalPolynomial f) \ L) B ≤
        count (⋃ P ∈ T, idealZeroLocus P) B := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hbox, hxf, hxL⟩ := mem_integralPoints.mp hx
    have hzero : eval x f = 0 := by simpa [zeroLocus] using hxf
    obtain ⟨P, hPS, hxP⟩ := hcover x hbox hzero
    have hpositive := (hcomponents P hPS).2
    have hnotone : δ P ≠ 1 := by
      intro hone
      apply hxL
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPS, hone⟩, hxP⟩⟩
    have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hPS, by omega⟩
    exact mem_integralPoints.mpr ⟨hbox,
      Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hPT, hxP⟩⟩⟩
  refine ⟨S, δ, hcomponents, hsum, ?_⟩
  have hh : (count (zeroLocus (CCDN.rationalPolynomial f) \ L) B : ℝ) ≤
        (count (⋃ P ∈ T, idealZeroLocus P) B : ℝ) := by exact_mod_cast houtside
  exact hh.trans hnonlinear

end CCDN
