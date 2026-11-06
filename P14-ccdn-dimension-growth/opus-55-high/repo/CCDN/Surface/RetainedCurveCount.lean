/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Surface.CurveComponents
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.SmallDegreeSurfaceCurveCount

/-! The retained part of the small-degree surface cover. Lines and
nonlinear prime curves are counted together, using their common degree
budget and the logarithmic cap on the retained degrees. -/

namespace CCDN
section
open MvPolynomial Finset

theorem surface_curve_number_weight {d : ℕ} (hd : 5 ≤ d) {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ≤
      (20 * Real.exp (1 / 20 : ℝ)) * B := by
  calc
    _ ≤ B ^ (1 / Real.sqrt d + 1 / 2) * (Real.log B + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      · linarith [Real.log_nonneg hB]
    _ ≤ _ := by
      have hh := surface_nonlinear_polylog_weight hd 1 hB
      simp_all

/-- There is an absolute constant `C` such that, for an integer surface equation `f` of degree
`d ≥ 5` with absolutely irreducible top-degree form and a finite family `S` of curves of
positive degree on the surface, each of degree at most `D (log B + 1)` and of total degree at
most `A B^(1/√d) (log B + 1)`, the union of the curves has at most
`C (d⁶ + A (D² (D + 1) + 1)) B` integral points of height at most `B`. -/
theorem retained_surface_curve_union_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (A D B : ℝ),
      0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ I ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ 0 < δ I) →
      (∀ I ∈ S, (δ I : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ I ∈ S, (δ I : ℝ)) ≤
        A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) →
      (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
        C * ((f.totalDegree : ℝ) ^ 6 + A * (D ^ 2 * (D + 1) + 1)) * B := by
  obtain ⟨Cline, hCline, hline⟩ := surface_degree_one_component_contribution
  obtain ⟨Ccurve, hCcurve, hcurve⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (d : ℕ), 5 ≤ d →
      ∀ A D B : ℝ, 0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ P ∈ S, P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∀ P ∈ S, (δ P : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ P ∈ S, (δ P : ℝ)) ≤
        A * B ^ (1 / Real.sqrt d) * (Real.log B + 1) ^ 1 →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C * A * D ^ 2 * (D + 1) * B := by
    obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
    let C₀ := ((1 + 3).factorial / (1 / 20 : ℝ) ^ (1 + 3) * Real.exp (1 / 20))
    refine ⟨K * C₀, mul_pos hK (by positivity), ?_⟩
    intro S δ d hd A D B hA hD hB hcurve hcap hbudget
    have hsum : ∑ P ∈ S, curveBound (δ P) B ≤ C₀ * A * D ^ 2 * (D + 1) * B := by
      have hB0 := zero_lt_one.trans_le hB
      have hlog := Real.log_nonneg hB
      have hsum : (∑ i ∈ S, curveBound (δ i) B) ≤
          (∑ i ∈ S, (δ i : ℝ)) * D ^ 2 * (D + 1) *
            B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
        calc
          _ ≤ ∑ i ∈ S, (δ i : ℝ) * D ^ 2 * (D + 1) *
              B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 :=
            Finset.sum_le_sum (fun i hi => curveBound_logarithmic_degree
              (hcurve i hi).2.1 hB hD (hcap i hi))
          _ = _ := by simp [Finset.sum_mul]
      calc
        _ ≤ _ := hsum
        _ ≤ (A * B ^ (1 / Real.sqrt d) * (Real.log B + 1) ^ 1) *
            D ^ 2 * (D + 1) *
            B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
          gcongr
        _ = (A * D ^ 2 * (D + 1)) *
            (B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ (1 + 3)) := by
          rw [Real.rpow_add hB0, pow_add]
          ring
        _ ≤ (A * D ^ 2 * (D + 1)) * (C₀ * B) :=
          mul_le_mul_of_nonneg_left (surface_nonlinear_polylog_weight hd (1 + 3) hB)
            (by positivity)
        _ = _ := by grind
    calc
      _ ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) := by
        exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
      _ ≤ ∑ P ∈ S, K * curveBound (δ P) B := by
        apply Finset.sum_le_sum
        grind
      _ = K * ∑ P ∈ S, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
      _ ≤ K * (C₀ * A * D ^ 2 * (D + 1) * B) :=
        mul_le_mul_of_nonneg_left hsum hK.le
      _ = _ := by ring
  let Ccard := 20 * Real.exp (1 / 20 : ℝ)
  have hCcard : 0 < Ccard := by dsimp [Ccard]; positivity
  let C := Cline + Ccurve + Ccard
  refine ⟨C, (by grind), ?_⟩
  intro f hir hd S δ A D B hA hD hB hS hcap hbudget
  let lines := S.filter (fun I => δ I = 1)
  let curves := S.filter (fun I => 2 ≤ δ I)
  have hlineCount := hline f hir (by omega) B (by linarith) lines
    (fun I hI => by
      obtain ⟨hIS, hδ⟩ := mem_filter.mp hI
      exact ⟨(hS I hIS).1.isPrime, (hS I hIS).1.height_eq, hδ ▸ (hS I hIS).1.degree⟩)
    (fun I hI => (hS I (mem_filter.mp hI).1).1.mem)
  have hcurveBudget : (∑ I ∈ curves, (δ I : ℝ)) ≤
      A * B ^ (1 / Real.sqrt f.totalDegree) * (Real.log B + 1) ^ 1 := by
    rw [pow_one]
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget
  have hcurveCount := hcurve curves δ f.totalDegree hd A D B hA hD hB
    (fun I hI => by
      obtain ⟨hIS, hδ⟩ := mem_filter.mp hI
      exact ⟨(hS I hIS).1.isPrime, hδ, (hS I hIS).1.degree⟩)
    (fun I hI => hcap I (mem_filter.mp hI).1) hcurveBudget
  have hcard : (lines.card : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) := by
    calc
      _ ≤ (S.card : ℝ) := mod_cast card_le_card (filter_subset (fun I => δ I = 1) S)
      _ = ∑ _I ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun I hI => mod_cast (hS I hI).2)
  have hcardBound : lines.card ≤ A * Ccard * B := by
    have hh := mul_le_mul_of_nonneg_left (surface_curve_number_weight hd hB) hA
    grind
  have hsub : (⋃ I ∈ S, idealZeroLocus I) ⊆
      (⋃ I ∈ lines, idealZeroLocus I) ∪ ⋃ I ∈ curves, idealZeroLocus I := by
    intro x hx
    obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
    by_cases hδ : δ I = 1
    · aesop
    · have hδ2 : 2 ≤ δ I := by have := (hS I hIS).2; omega
      exact Or.inr (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS, hδ2⟩, hxI⟩⟩)
  have hcount : (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
      (count (⋃ I ∈ lines, idealZeroLocus I) B : ℝ) +
        count (⋃ I ∈ curves, idealZeroLocus I) B := by
    exact_mod_cast (count_mono hsub (le_refl B)).trans
      (count_union_le (⋃ I ∈ lines, idealZeroLocus I) (⋃ I ∈ curves, idealZeroLocus I) B)
  have hCl : Cline ≤ C := by grind
  have hCc : Ccurve ≤ C := by grind
  have hCn : Ccard ≤ C := by grind
  have hB0 : 0 ≤ B := by linarith
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl
    (show 0 ≤ (f.totalDegree : ℝ) ^ 6 by positivity)) hB0
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCn hA) hB0
  have hc := mul_le_mul_of_nonneg_right hCc
    (show 0 ≤ A * D ^ 2 * (D + 1) * B by positivity)
  nlinarith

