module

public import Mathlib

/-!
# The threshold form (paper Proposition 8.8)

If `(Σ a_j v_j)_+² ≤ Σ D_j a_j² + d (Σ a_j)²` for all `a ≥ 0`, with every `D_j > 0` and `d > 0`,
then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ² / d`.

The helpers in `GradedNear.ThresholdAux` prove this direction, "quadratic ⇒ threshold".
The threshold is a zero of the continuous scalar function `t ↦ d Σ_j (v_j - t)_+ / D_j - t` on
`[0, b]`, found by the intermediate value theorem; the test vector
`a_j = (v_j - t)_+ / D_j` then turns the quadratic hypothesis into the threshold bound.
-/

@[expose] public section

namespace GradedNear

namespace ThresholdAux

open Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The positive part, with the order of arguments fixed for the formulas below. -/
def pos (x : ℝ) : ℝ := max x 0

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_right _ _

lemma pos_mono {x y : ℝ} (h : x ≤ y) : pos x ≤ pos y := max_le_max h le_rfl

lemma pos_mul (x : ℝ) : pos x * x = pos x ^ 2 := by
  rcases le_total x 0 with h | h <;> simp [pos, h, pow_two]

/-- The resource quadratic form in the scalar two-test inequality. -/
def resource (D : ι → ℝ) (d : ℝ) (a : ι → ℝ) : ℝ :=
  (∑ i, D i * a i ^ 2) + d * (∑ i, a i) ^ 2

lemma resource_nonneg (D : ι → ℝ) (d : ℝ) (a : ι → ℝ) (hD : ∀ i, 0 < D i) (hd : 0 < d) :
    0 ≤ resource D d a :=
  add_nonneg (sum_nonneg fun i _ => mul_nonneg (hD i).le (sq_nonneg _))
    (mul_nonneg hd.le (sq_nonneg _))

/-- The common-threshold scalar cost. -/
def thresholdCost (v D : ι → ℝ) (d t : ℝ) : ℝ :=
  t ^ 2 / d + ∑ i, pos (v i - t) ^ 2 / D i

/-- Existence of the common threshold, by a continuous scalar fixed-point equation. -/
theorem exists_common_threshold (v D : ι → ℝ) (d : ℝ) (hD : ∀ i, 0 < D i) (hd : 0 < d)
    (hquad : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → pos (∑ i, a i * v i) ^ 2 ≤ resource D d a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.sqrt d ∧ thresholdCost v D d t ≤ 1 := by
  let b := d * ∑ i, pos (v i) / D i
  let f : ℝ → ℝ := fun t => d * (∑ i, pos (v i - t) / D i) - t
  have hb : 0 ≤ b := mul_nonneg hd.le (sum_nonneg fun i _ => div_nonneg (pos_nonneg _) (hD i).le)
  have hf : Continuous f := by unfold f pos; fun_prop
  have hfb : f b ≤ 0 := by
    have hp : (∑ i, pos (v i - b) / D i) ≤ ∑ i, pos (v i) / D i :=
      sum_le_sum fun i _ => div_le_div_of_nonneg_right (pos_mono (by linarith)) (hD i).le
    simp only [f, b]
    nlinarith [mul_le_mul_of_nonneg_left hp hd.le]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hb hf.continuousOn ⟨hfb, by simpa [f] using hb⟩
  let a : ι → ℝ := fun i => pos (v i - t) / D i
  have ha : ∀ i, 0 ≤ a i := fun i => div_nonneg (pos_nonneg _) (hD i).le
  have htfix : t = d * ∑ i, a i := by simp only [f] at hft; linarith
  have hcoord : ∀ i, a i * v i = D i * a i ^ 2 + t * a i := by
    intro i
    have hi := ne_of_gt (hD i)
    have hp := pos_mul (v i - t)
    dsimp [a]
    field_simp
    nlinarith
  have hdot : (∑ i, a i * v i) = resource D d a := by
    simp_rw [hcoord, sum_add_distrib, ← mul_sum]
    unfold resource
    rw [htfix]
    ring
  have hres : 0 ≤ resource D d a := resource_nonneg D d a hD hd
  have hres₁ : resource D d a ≤ 1 := by
    have hq := hquad a ha
    rw [hdot, pos, max_eq_left hres] at hq
    nlinarith
  have hcost : thresholdCost v D d t = resource D d a := by
    unfold thresholdCost resource
    have he : ∀ i, pos (v i - t) ^ 2 / D i = D i * a i ^ 2 := by
      intro i
      simp only [a]
      field_simp
    simp_rw [he]
    rw [htfix]
    field_simp
    ring
  have ht₂ : t ^ 2 ≤ d := by
    rw [← hcost] at hres₁
    unfold thresholdCost at hres₁
    have hS : 0 ≤ ∑ i, pos (v i - t) ^ 2 / D i :=
      sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hD i).le
    exact (div_le_one hd).1 (by linarith)
  exact ⟨t, ht.1, Real.le_sqrt_of_sq_le ht₂, hcost ▸ hres₁⟩

end

end ThresholdAux

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] (v D : ι → ℝ) (d : ℝ)
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hq : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt d ∧
      ∑ j, (max 0 (v j - τ)) ^ 2 / D j ≤ 1 - τ ^ 2 / d := by
  have hquad : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      ThresholdAux.pos (∑ j, a j * v j) ^ 2 ≤ ThresholdAux.resource D d a := by
    intro a ha
    rw [ThresholdAux.pos, max_comm]
    exact hq a ha
  obtain ⟨τ, hτ0, hτd, hcost⟩ := ThresholdAux.exists_common_threshold v D d hD hd hquad
  refine ⟨τ, hτ0, hτd, ?_⟩
  simp only [ThresholdAux.pos, max_comm, ThresholdAux.thresholdCost] at hcost ⊢
  linarith

end GradedNear
