module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm. See third_party/twelfth/ATKINSON_PACKET_MANIFEST.json and
third_party/twelfth/LICENSE-MIT-0.
Mathlib dependencies retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonGapBudget

@[expose] public section

open Complex Finset Set Filter
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard
open MathCollab.Density.Stronger.Fourth
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonArithmeticGapBudget (η : ℝ) (N : ℕ) (W : Finset ℝ) : ℝ :=
  (Nat.clog 2 N:ℝ)*∑ j ∈ Finset.range (Nat.clog 2 N),
    (((2^j:ℕ):ℝ)^(1/2+η))*∑ t ∈ W, ∑ u ∈ W,
      atkinsonPrefixGapMajorant (2^j) (2^j) t u

theorem atkinson_quarter_energy_power {x : ℝ} (hx : 0 < x) (η : ℝ) :
    (x^(-(1/4:ℝ)))^2*x^(1+η) = x^(1/2+η) := by
  rw [sq,← Real.rpow_add hx,← Real.rpow_add hx]
  congr 1
  ring

theorem exists_atkinsonGapBudget_le_arithmetic {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ W : Finset ℝ,
      (∀ j < Nat.clog 2 N, ∀ t ∈ W, ∀ u ∈ W,
        0 ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u) →
      atkinsonDyadicGapBudget N W ≤ C*atkinsonArithmeticGapBudget η N W := by
  obtain ⟨C,hC,henergy⟩ := exists_atkinsonBlockCoefficientEnergy_le hη
  refine ⟨C,hC,?_⟩
  intro N W hnonneg
  unfold atkinsonDyadicGapBudget atkinsonArithmeticGapBudget
  have hsum :
      (∑ j ∈ Finset.range (Nat.clog 2 N),
        (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*atkinsonBlockCoefficientEnergy (2^j) (2^j)*
          ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u) ≤
      ∑ j ∈ Finset.range (Nat.clog 2 N),
        C*((((2^j:ℕ):ℝ)^(1/2+η))*
          ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u) := by
    apply Finset.sum_le_sum
    intro j hj
    have hM : (0:ℝ) < ((2^j:ℕ):ℝ) := by positivity
    have hS : 0 ≤ ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u :=
      Finset.sum_nonneg (fun t ht => Finset.sum_nonneg
        (fun u hu => hnonneg j (Finset.mem_range.mp hj) t ht u hu))
    have he := henergy (2^j) (2^j) (pow_pos (by norm_num) _) le_rfl
    calc
      _ ≤ (((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*(C*((2^j:ℕ):ℝ)^(1+η))*
          ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (sq_nonneg _)) hS
      _ = C*((((2^j:ℕ):ℝ)^(-(1/4:ℝ)))^2*((2^j:ℕ):ℝ)^(1+η))*
          ∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGapMajorant (2^j) (2^j) t u := by ring
      _ = _ := by rw [atkinson_quarter_energy_power hM]; ring
  have hm := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Nat.clog 2 N) : (0:ℝ) ≤ _)
  rw [← Finset.mul_sum] at hm
  exact hm.trans_eq (by ring)

end MathCollab.Density.Stronger.Atkinson
