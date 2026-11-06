module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Selected proof slices adapted from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Released under MIT-0; see third_party/twelfth/LICENSE-MIT-0.
Provenance: third_party/twelfth/ATKINSON_STATIONARY_DYADIC_MANIFEST.json.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationaryBlockBound
public import MathCollab.Density.Stronger.Atkinson.AtkinsonDampedDyadic
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set Filter
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

section
variable (T G L : ℝ) (N : ℕ)
include T G L N
theorem atkinsonStationaryLeadingFiniteSum_eq_dyadic :
    atkinsonStationaryLeadingFiniteSum T G L N =
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        atkinsonStationaryBlock T G L (2^j) (truncatedDyadicLength N j) :=
  sum_range_eq_truncatedDyadic (atkinsonStationaryLeadingTerm T G L)
    (atkinsonStationaryLeadingTerm_zero T G L) N

theorem norm_atkinsonStationaryLeadingFiniteSum_le_blocks :
    ‖atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        ‖atkinsonStationaryBlock T G L (2^j) (truncatedDyadicLength N j)‖ := by
  rw [atkinsonStationaryLeadingFiniteSum_eq_dyadic]
  exact norm_sum_le _ _
end

theorem exists_norm_atkinsonStationarySum_le_dyadic {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) := by
  pm_231 C hC A hA hblock exists_atkinsonSourceCutoff_block_bound hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  pm_1071 A B hA.trans
  intro T G hT hlower hupper
  pm_207 hAT A T le_max_left hT
  pm_207 hBT B T le_max_right hT
  have hT0 : 0 < T := by grind
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  rw [atkinsonStationaryLeadingSum_eq_finite hT0 hG hL hwidth]
  apply (norm_atkinsonStationaryLeadingFiniteSum_le_blocks T G (Real.log T) _).trans
  unfold atkinsonDyadicPhaseBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply (hblock T G hAT hlower hupper (2^j) _
    (pow_pos (by norm_num) _) (truncatedDyadic_endpoint_le (Finset.mem_range.mp hj))).trans_eq
  ring

section
variable {δ : ℝ} (hδ : 0 < δ)
include δ hδ
theorem exists_norm_atkinsonStationarySum_le_fullDyadic :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T)) := by pm_4397 A hA exists_norm_atkinsonStationarySum_le_dyadic hA.trans atkinsonDyadicPhaseBound_le_full T

/-- The complete literal stationary source is controlled by native undamped phase prefixes. -/
theorem exists_norm_atkinsonStationarySum_le_undamped :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G*T^(-(1/4:ℝ))*
          atkinsonUndampedDyadicPhaseBound T (atkinsonSourceCutoff T G (Real.log T)) := by pm_4397 T₀ hT₀ exists_norm_atkinsonStationarySum_le_fullDyadic hT₀.trans atkinsonFullDyadicPhaseBound_le_undamped hT0
end

end MathCollab.Density.Stronger.Atkinson
