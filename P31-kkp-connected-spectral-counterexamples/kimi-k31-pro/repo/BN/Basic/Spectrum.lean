/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

module
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import BN.Basic.Inner
@[expose] public section

/-!
# Ordered spectrum of a Hermitian matrix

This file records the ordered real spectrum of a Hermitian matrix, matching the
conventions in `docs/sol.tex`. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
`F` is the sum of squares of the two largest positive eigenvalues, with missing
terms replaced by zero.
-/

namespace BN

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

/-- The eigenvalues of a Hermitian matrix in nonincreasing order. The value at
`i` is the paper's `λ_{i+1}`. -/
noncomputable def eigs₀ (hA : A.IsHermitian) : Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues₀

/-- The largest eigenvalue `λ₁(A)`. -/
noncomputable def lambdaMax (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  eigs₀ hA ⟨0, Fintype.card_pos⟩

/-- The second-largest eigenvalue `λ₂(A)`. -/
noncomputable def lambdaSecond (hA : A.IsHermitian) [Nontrivial n] : ℝ :=
  eigs₀ hA ⟨1, Fintype.one_lt_card⟩

/-- The sum of squares of the two largest positive eigenvalues of a Hermitian
matrix, with missing terms replaced by zero. -/
noncomputable def F (hA : A.IsHermitian) : ℝ :=
  if h0 : 0 < Fintype.card n then
    let t0 := (max (hA.eigenvalues₀ ⟨0, h0⟩) 0) ^ 2
    if h1 : 1 < Fintype.card n then
      t0 + (max (hA.eigenvalues₀ ⟨1, h1⟩) 0) ^ 2
    else t0
  else 0

lemma F_eq (hA : A.IsHermitian) [Nontrivial n] :
    F hA = (max (lambdaMax hA) 0) ^ 2 + (max (lambdaSecond hA) 0) ^ 2 := by
  have h1 : 1 < Fintype.card n := Fintype.one_lt_card
  have h0 : 0 < Fintype.card n := Nat.zero_lt_of_lt h1
  unfold F lambdaMax lambdaSecond eigs₀
  rw [dif_pos h0, dif_pos h1]

lemma F_nonneg (hA : A.IsHermitian) : 0 ≤ F hA := by
  dsimp [F]
  split_ifs <;> positivity

/-! ### N11 — Adjacency Frobenius mass -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option linter.unusedSectionVars false

end BN
