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

public section

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
  have hcompact : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hγ
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hclose⟩ := hu ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  let N := n + 1
  have hNnat  := Nat.succ_pos n
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
  have htime : dist ((i : ℝ) / (N : ℝ)) (((i + 1 : ℕ) : ℝ) / (N : ℝ)) < δ := by
    rw [Real.dist_eq]
    have hdiff :
        ((i + 1 : ℕ) : ℝ) / (N : ℝ) - (i : ℝ) / (N : ℝ) = 1 / (N : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [show (i : ℝ) / (N : ℝ) - ((i + 1 : ℕ) : ℝ) / (N : ℝ) = -(1 / (N : ℝ)) by linarith [hdiff], abs_neg,
      abs_of_pos (one_div_pos.mpr hN)]
    exact hgap
  refine ⟨?_, ?_⟩
  · grind
  · intro t ht
    have hleft : (i : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hi0, hi1⟩
    have hright : ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨hiNext0, hiNext1⟩
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hleft.1 ht.1, le_trans ht.2 hright.2⟩
    have hinterval : dist t ((i : ℝ) / (N : ℝ)) ≤
        (((i + 1 : ℕ) : ℝ) / (N : ℝ)) - (i : ℝ) / (N : ℝ) := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    grind

/-- Every parameter lies in a member of a fixed equal subdivision. The selected index is the
right-hand interval at an interior subdivision point, leaving only the terminal point in the
last interval's right boundary. -/
theorem exists_equal_subdivision_interval (N : ℕ) (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : ℕ, i < N ∧
      (i : ℝ) / (N : ℝ) ≤ t ∧
      t ≤ ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∧
      (t < ((i + 1 : ℕ) : ℝ) / (N : ℝ) ∨ t = 1) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let x : ℝ := (N : ℝ) * t
  have hxnonneg : 0 ≤ x := by
    continuity
  have hxupper : x ≤ (N : ℝ) := by
    dsimp [x]
    nlinarith [ht.2]
  let q : ℕ := Nat.floor x
  have hqle : (q : ℝ) ≤ x := by
    exact Nat.floor_le hxnonneg
  have hqN : q ≤ N := by
    exact_mod_cast hqle.trans hxupper
  let i : ℕ := min q (N - 1)
  have hiN : i < N := by
    dsimp [i]
    omega
  have hix : (i : ℝ) ≤ x := by
    dsimp [i]
    simp_all
  have hxupper' : x ≤ (i + 1 : ℕ) := by
    by_cases hqLt : q < N
    · have hiq : i = q := by
        omega
      rw [hiq]
      have hstrict : x < (q + 1 : ℕ) := by
        simpa [q] using Nat.lt_floor_add_one x
      exact hstrict.le
    · 
      have hiEq : i = N - 1 := by
        omega
      simp_all
  have hleft : (i : ℝ) / (N : ℝ) ≤ t := by
    field_simp <;> nlinarith
  have hright : t ≤ ((i + 1 : ℕ) : ℝ) / (N : ℝ) := by
    field_simp <;> nlinarith
  refine ⟨i, hiN, hleft, hright, ?_⟩
  by_cases hqLt : q < N
  · have hiq : i = q := by
      dsimp [i]
      rw [Nat.min_eq_left]
      omega
    have hstrict : x < (q + 1 : ℕ) := by
      simpa [q] using Nat.lt_floor_add_one x
    have hstrict' : t < ((q + 1 : ℕ) : ℝ) / (N : ℝ) := by
      apply (lt_div_iff₀ hNreal).2
      simpa [x, mul_comm] using hstrict
    left
    simpa [hiq] using hstrict'
  grind

end DOZZ.Proofs
