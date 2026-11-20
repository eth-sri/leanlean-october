/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Finset.Max
public import Mathlib.LinearAlgebra.Matrix.Notation

/-! # Moment bounds for finite and countable sums -/

@[expose] public section
open scoped ENNReal
namespace DOZZ.Proofs

section
variable {ι : Type*}

/-- For a finite nonempty sum, compare with the largest summand before taking powers. -/
theorem ennreal_finset_sum_rpow_le_card_rpow_sum (S : Finset ι) (hne : S.Nonempty) (f : ι → ℝ≥0∞)
    (p : ℝ) (hp : 0 ≤ p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  have hsum : (∑ i ∈ S, f i) ≤ (S.card : ℝ≥0∞) * f i₀ := by
    calc
      _ ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp
  have h := ENNReal.rpow_le_rpow hsum hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
  exact h.trans (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i => (f i) ^ p) (fun _ _ => zero_le) hi₀))

theorem ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos (S : Finset ι) (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS, ENNReal.zero_rpow_of_pos hp]
  · exact ennreal_finset_sum_rpow_le_card_rpow_sum S hS f p hp.le

private theorem ennreal_rpow_finset_sum_le_sum_rpow (s : Finset ι) (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, a i) ^ p ≤ ∑ i ∈ s, (a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      exact ENNReal.rpow_add_le_add_rpow (a i) (∑ j ∈ s, a j) hp.le hp1 |>.trans
        (add_le_add_right ih _)

/-- Subadditivity for a concave power applies to countable sums. -/
theorem ennreal_rpow_tsum_le_tsum_rpow (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, a i) ^ p ≤ ∑' i, (a i) ^ p := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  have hmono : Monotone (fun x : ℝ≥0∞ => x ^ p) := fun _ _ h =>
    ENNReal.rpow_le_rpow h hp.le
  have hzero  := ENNReal.zero_rpow_of_pos hp
  have hcontinuous : Continuous (fun x : ℝ≥0∞ => x ^ p) :=
    ENNReal.continuous_rpow_const
  rw [hmono.map_iSup_of_continuousAt
    hcontinuous.continuousAt hzero]
  apply iSup_le
  intro s
  exact (ennreal_rpow_finset_sum_le_sum_rpow s a hp hp1).trans
    (le_iSup_of_le s le_rfl)

end

theorem ennreal_add3_rpow_le (a b c : ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) :
    (a + b + c) ^ q ≤ (3 : ℝ≥0∞) ^ q * (a ^ q + b ^ q + c ^ q) := by
  let f  := ![a, b, c]
  have h := ennreal_finset_sum_rpow_le_card_rpow_sum (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ 0⟩ f q hq
  simpa [f, Fin.sum_univ_succ, add_assoc] using h

theorem ennreal_rpow_le_max_one_rpow (x : ℝ≥0∞) {t tm : ℝ} (ht : 0 ≤ t) (htm : t ≤ tm) :
    x ^ t ≤ max 1 x ^ tm :=
  (ENNReal.rpow_le_rpow (le_max_right 1 x) ht).trans
    (ENNReal.rpow_le_rpow_of_exponent_le (le_max_left 1 x) htm)

/-- The positive-base power identity in function notation. -/
theorem ennreal_ofReal_rpow_of_pos {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) :=
  ENNReal.ofReal_rpow_of_pos hx

end DOZZ.Proofs
