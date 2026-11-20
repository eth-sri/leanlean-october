/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestIntegrationByParts

/-! Exponential growth envelopes for smooth finite-chaos scores. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

section
variable {ι : Type*} [Fintype ι] (a v : ι → ℝ) (γ : ℝ)
include ι

/-- The finite-chaos mass is nonnegative when all coefficients are nonnegative. -/
lemma finiteChaosVectorMass_nonneg (ha : ∀ i, 0 ≤ a i) (x : ι → ℝ) :
    0 ≤ finiteChaosVectorMass a v γ x := by
  classical
  unfold finiteChaosVectorMass
  exact Finset.sum_nonneg fun i hi => mul_nonneg (ha i) (Real.exp_nonneg _)

/-- Every Wick weight in a finite family has a common absolute-exponential envelope. -/
theorem finiteChaosVectorWeight_absExp_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z i,
      ‖finiteChaosVectorWeight a v γ z i‖ ≤
        B * Real.exp (|γ| * ∑ j, |z j|) := by
  classical
  let b  := fun i => |a i| * Real.exp (|γ ^ 2 / 2 * v i|)
  let B  := 1 + ∑ i, b i
  have hb (i : ι) : 0 ≤ b i := by
    dsimp [b]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbi (i : ι) : b i ≤ B := by
    have hle : b i ≤ ∑ j, b j := by
      simpa using (Finset.single_le_sum (s := Finset.univ) (f := b)
        (fun j hj => hb j) (Finset.mem_univ i))
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro z i
  rw [finiteChaosVectorWeight, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have harg : γ * z i - γ ^ 2 / 2 * v i ≤
      |γ| * ∑ j, |z j| + |γ ^ 2 / 2 * v i| := by
    have hlin : γ * z i ≤ |γ| * |z i| := by
      calc
        γ * z i ≤ |γ * z i| := le_abs_self _
        _ = |γ| * |z i| := abs_mul _ _
    have hcoord : |z i| ≤ ∑ j, |z j| := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (f := fun j : ι => |z j|)
        (fun j hj => abs_nonneg (z j)) (Finset.mem_univ i))
    have hcoord'  :=
      mul_le_mul_of_nonneg_left hcoord (abs_nonneg γ)
    have hconst : -(γ ^ 2 / 2 * v i) ≤ |γ ^ 2 / 2 * v i| := neg_le_abs _
    linarith
  calc
    |a i| * Real.exp (γ * z i - γ ^ 2 / 2 * v i) ≤
        |a i| * Real.exp (|γ| * ∑ j, |z j| + |γ ^ 2 / 2 * v i|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (abs_nonneg _)
    _ = b i * Real.exp (|γ| * ∑ j, |z j|) := by
      dsimp [b]
      rw [Real.exp_add]
      ring
    _ ≤ B * Real.exp (|γ| * ∑ j, |z j|) :=
      mul_le_mul_of_nonneg_right (hbi i) (Real.exp_nonneg _)

end

/-- The two-weight part of the Hessian of a scalar test of a Wick sum. -/
noncomputable def finiteChaosVectorPairScore {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ : ℝ) (F'' : ℝ → ℝ) (z : ι → ℝ) (i j : ι) : ℝ :=
  finiteChaosVectorWeight a v γ z i * finiteChaosVectorWeight a v γ z j *
    F'' (finiteChaosVectorMass a v γ z)

/-- Bounded first and second derivatives give an exponential-linear envelope for the score used
in the Gaussian integration-by-parts formula. -/
theorem finiteChaosVectorTestScore_exp_growth_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (F' F'' : ℝ → ℝ)
    (hF' : ∀ x, 0 ≤ x → ‖F' x‖ ≤ B₁) (hF'' : ∀ x, 0 ≤ x → ‖F'' x‖ ≤ B₂) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z i j,
      ‖finiteChaosVectorTestScore a v γ F' z i‖ ≤
          M * Real.exp (2 * (|γ| * ∑ k, |z k|)) ∧
      ‖finiteChaosVectorTestScoreDerivative a v γ F' F'' z i j‖ ≤
          M * Real.exp (2 * (|γ| * ∑ k, |z k|)) ∧
      ‖finiteChaosVectorPairScore a v γ F'' z i j‖ ≤
          M * Real.exp (2 * (|γ| * ∑ k, |z k|)) := by
  obtain ⟨B, hB, hWeight⟩ := finiteChaosVectorWeight_absExp_bound a v γ
  let K := B * B₁
  let L := B ^ 2 * B₂
  refine ⟨K + L + |γ| * (K + L), by dsimp [K, L]; positivity, fun z i j => ?_⟩
  let u := |γ| * ∑ k, |z k|
  let e := Real.exp (2 * u)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have he : Real.exp u ≤ e := Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp u * Real.exp u = e := by rw [← Real.exp_add, ← two_mul]
  have hm := finiteChaosVectorMass_nonneg a v γ ha z
  have hf (i : ι) : ‖finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)‖ ≤ K * e := by
    rw [norm_mul]
    calc
      _ ≤ B * Real.exp u * B₁ := mul_le_mul (hWeight z i) (hF' _ hm) (norm_nonneg _) (by positivity)
      _ = K * Real.exp u := by dsimp [K]; ring
      _ ≤ K * e := mul_le_mul_of_nonneg_left he (by dsimp [K]; positivity)
  have hd : ‖if i = j then finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z) else 0‖
      ≤ K * e := by
    split_ifs <;> first | exact hf i | simp only [norm_zero]; dsimp [K, e]; positivity
  have hp : ‖finiteChaosVectorWeight a v γ z i * finiteChaosVectorWeight a v γ z j *
      F'' (finiteChaosVectorMass a v γ z)‖ ≤ L * e := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (B * Real.exp u) * (B * Real.exp u) * B₂ :=
        mul_le_mul (mul_le_mul (hWeight z i) (hWeight z j) (norm_nonneg _) (by positivity))
          (hF'' _ hm) (norm_nonneg _) (by positivity)
      _ = L * e := by rw [← hsq]; dsimp [L]; ring
  have hKL : 0 ≤ K ∧ 0 ≤ L := by dsimp [K, L]; constructor <;> positivity
  refine ⟨(hf i).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)), ?_,
    hp.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _))⟩
  · exact (le_add_of_nonneg_right hKL.2).trans (le_add_of_nonneg_right (by positivity))
  · unfold finiteChaosVectorTestScoreDerivative
    simp only [mul_assoc, ← mul_add, norm_mul, Real.norm_eq_abs γ]
    refine (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hd
      (by simpa only [mul_assoc] using hp))) (abs_nonneg γ)).trans ?_
    change |γ| * (K * e + L * e) ≤ (K + L + |γ| * (K + L)) * e
    rw [← add_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (add_nonneg hKL.1 hKL.2)) (Real.exp_nonneg _)
  · exact (le_add_of_nonneg_left hKL.1).trans (le_add_of_nonneg_right (by positivity))

end DOZZ.Proofs
