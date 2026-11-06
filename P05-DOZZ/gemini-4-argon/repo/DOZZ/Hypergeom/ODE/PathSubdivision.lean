/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.Complex.Basic

/-! A continuous path on a compact interval admits a finite equal subdivision with small image
increments. This is the compactness step for disk-chain continuation. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

theorem exists_path_subdivision {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      ∀ i : ℕ, i < N →
        dist (γ ((i : ℝ) / (N : ℝ)))
          (γ (((i + 1 : ℕ) : ℝ) / (N : ℝ))) < ε ∧
        ∀ t ∈ Icc ((i : ℝ) / (N : ℝ)) (((i + 1 : ℕ) : ℝ) / (N : ℝ)),
          dist (γ t) (γ ((i : ℝ) / (N : ℝ))) < ε := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hclose⟩ := hu ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N := n + 1
  have hNnat := Nat.succ_pos n
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hgap : 1 / (N : ℝ) < δ := by simpa [N] using hn
  refine ⟨N, hNnat, ?_⟩
  intro i hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) / (N : ℝ) := by positivity
  have hi1 : (i : ℝ) / (N : ℝ) ≤ 1 := by
    apply (div_le_one hN).2
    exact_mod_cast (Nat.le_of_lt hi)
  have hiNext0 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) / (N : ℝ) := by positivity
  have hiNext1 : ((i + 1 : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    apply (div_le_one hN).2
    exact_mod_cast (Nat.succ_le_iff.mpr hi)
  refine ⟨?_, ?_⟩
  · exact hclose _ ⟨hi0, hi1⟩ _ ⟨hiNext0, hiNext1⟩ (by rw [Real.dist_eq]; rw [show (i : ℝ) / (N : ℝ) - ((i + 1 : ℕ) : ℝ) / (N : ℝ) = -(1 / (N : ℝ)) by linarith [(show ((i + 1 : ℕ) : ℝ) / (N : ℝ) - (i : ℝ) / (N : ℝ) = 1 / (N : ℝ) by rw [Nat.cast_add, Nat.cast_one]; ring)], abs_neg, abs_of_pos (one_div_pos.mpr hN)]; exact hgap)
  · intro t ht
    have hinterval : dist t ((i : ℝ) / (N : ℝ)) ≤
        (((i + 1 : ℕ) : ℝ) / (N : ℝ)) - (i : ℝ) / (N : ℝ) := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    simpa [dist_comm] using
      hclose _ ⟨hi0, hi1⟩ t ⟨le_trans (⟨hi0, hi1⟩ : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1).1 ht.1, le_trans ht.2 (⟨hiNext0, hiNext1⟩ : ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1).2⟩ (by simpa [dist_comm] using (by rw [(show (((i + 1 : ℕ) : ℝ) / (N : ℝ)) - (i : ℝ) / (N : ℝ) = 1 / (N : ℝ) by rw [Nat.cast_add, Nat.cast_one]; ring)] at hinterval; exact hinterval.trans_lt hgap))

/-- Every parameter lies in a member of a fixed equal subdivision. The selected index is the
right-hand interval at an interior subdivision point, leaving only the terminal point in the
last interval's right boundary. -/
theorem exists_equal_subdivision_interval (N : ℕ) (hN : 0 < N)
    {t} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < N ∧
      (i : ℝ) / (N : ℝ) ≤ t ∧
      t ≤ ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∧
      (t < ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∨ t = 1) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let x : ℝ := (N : ℝ) * t
  have hxupper : x ≤ (N : ℝ) := by
    dsimp [x]
    nlinarith [ht.2]
  let q : ℕ := Nat.floor x
  have hqle : (q : ℝ) ≤ x := by
    dsimp [q]
    exact Nat.floor_le (by dsimp [x]; exact mul_nonneg (by positivity) ht.1)
  have : q ≤ N := by
    exact_mod_cast hqle.trans hxupper
  let i : ℕ := min q (N - 1)
  have hxupper' : x ≤ (i + 1 : ℕ) := by
    by_cases hqLt : q < N
    · have hiq : i = q := by
        dsimp [i]
        rw [Nat.min_eq_left]
        omega
      rw [hiq]
      exact (show x < (q + 1 : ℕ) by simpa [q] using Nat.lt_floor_add_one x).le
    · have hqEq : q = N := by omega
      have hiEq : i = N - 1 := by
        dsimp [i]
        rw [Nat.min_eq_right]
        omega
      rw [hiEq, (show N - 1 + 1 = N by omega)]
      exact_mod_cast hxupper
  refine ⟨i, (show i < N by dsimp [i]; omega), (by apply (div_le_iff₀ hNreal).2; simpa [x, mul_comm] using (show (i : ℝ) ≤ x by dsimp [i]; exact (Nat.cast_le.mpr (Nat.min_le_left q (N - 1))).trans hqle)), (by apply (le_div_iff₀ hNreal).2; simpa [x, mul_comm] using hxupper'), ?_⟩
  by_cases hqLt : q < N
  · have hiq : i = q := by
      dsimp [i]
      rw [Nat.min_eq_left]
      omega
    left
    simpa [hiq] using (by apply (lt_div_iff₀ hNreal).2; simpa [x, mul_comm] using (show x < (q + 1 : ℕ) by simpa [q] using Nat.lt_floor_add_one x))
  · have hqEq : q = N := by omega
    have hxEq : x = (N : ℝ) := le_antisymm hxupper (by
      simpa [q, hqEq] using hqle)
    exact Or.inr (by dsimp [x] at hxEq; nlinarith [hNreal])

end DOZZ.Proofs
