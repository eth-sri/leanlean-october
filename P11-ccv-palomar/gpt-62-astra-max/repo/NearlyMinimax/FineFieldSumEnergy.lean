module

public import NearlyMinimax.FineFieldSubsetL2


@[expose] public section

/-! Summation of actual time-integrated higher field moments over all
selected subsets, with a geometric count envelope. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def fineFieldSubsetEnergyBase (d : ℕ) : ℝ :=
  4 * 2 ^ d * hyperplaneSpatialMomentConstant d ^ 2

theorem hyperplaneSpatialMomentConstant_ge_one (d : ℕ) :
    1 ≤ hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have hc := spatialExponentialConstant_nonneg d
  bound

variable {d k : ℕ} [NeZero d] (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo)
include hd hlo

theorem finePairTimeSubsetMoment_uniform_square_integral_le {S : Finset (Fin k)} (hS : 4 ≤ S.card) :
    (∫ U, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      2 ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
        k ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  have hc : S.card ≤ k := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hv : 2 ^ (d * (k - S.card)) ≤ (2 : ℝ) ^ (d * k) :=
    pow_le_pow_right₀ (by norm_num) (by bound)
  have hconst  :=
    pow_le_pow_right₀ (hyperplaneSpatialMomentConstant_ge_one d) (Nat.mul_le_mul_left 2 hc)
  have hj : S.card ^ 8 ≤ (k : ℝ) ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hc) 8
  apply (finePairTimeSubsetMoment_square_integral_le hd (hi := hi) hlo hS).trans
  have hC := (hyperplaneSpatialMomentConstant_positive d).le
  have h2 := mul_le_mul hv hconst (pow_nonneg hC _) (by positivity)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul h2 hj (by positivity) (by positivity)) (sq_nonneg (lo ^ (2 - (d : ℝ))))
  convert hh using 1 <;> simp [mul_pow, ← pow_mul] <;> ring

/-- Any family of higher subsets has the same geometric count envelope;
the concrete even-subset field family is a particular case. -/
theorem finePairTimeSubsetMoment_sum_abs_square_integral_le {s : Finset (Finset (Fin k))}
    (hs : ∀ S ∈ s, 4 ≤ S.card) :
    (∫ U, (∑ S ∈ s, |finePairTimeSubsetMoment lo hi U S|) ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      fineFieldSubsetEnergyBase d ^ k * k ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2 := by
  classical
  let K  := 2 ^ (d * k) * hyperplaneSpatialMomentConstant d ^ (2 * k) *
    k ^ 8 * (lo ^ (2 - (d : ℝ))) ^ 2
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d k) s
    (fun S U => |finePairTimeSubsetMoment lo hi U S|) K
    (fun S _ => (finePairTimeSubsetMoment_measurable lo hi S).abs)
    (fun S hS => by simpa using finePairTimeSubsetMoment_square_integrable hd hlo (hs S hS))
    (fun S hS => by simpa using finePairTimeSubsetMoment_uniform_square_integral_le hd hlo (hs S hS))
  have hc : s.card ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by
      have hsub : s ⊆ Finset.univ.powerset := by simp
      simpa using Finset.card_le_card hsub)) 2
  apply (h.trans (mul_le_mul_of_nonneg_right hc (by
    positivity [(hyperplaneSpatialMomentConstant_positive d).le]))).trans_eq
  dsimp [K, fineFieldSubsetEnergyBase]
  simp [mul_pow, pow_mul]
  have hfour : 4 ^ k = (2 : ℝ) ^ (k * 2) := by
    rw [show 4 = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [hfour]
  ring

end NearlyMinimax
