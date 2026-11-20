module

public import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting
public import Mathlib.Data.Nat.Find
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

public section

@[expose] section

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

theorem scale_exists (K : ℕ) : ∃ n : ℕ, K ≤ 2 ^ (n ^ 2) := by
  refine ⟨K + 1, ?_⟩
  have hK : K < 2 ^ K := Nat.lt_pow_self (by decide : 1 < 2)
  exact hK.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

noncomputable def gridScale (K : ℕ) : ℕ := Nat.find (scale_exists K)

def gridWidth (K : ℕ) : ℕ := 2 ^ (gridScale K + 2)

theorem gridWidth_ge_two (K : ℕ) : 2 ≤ gridWidth K := by
  simpa only [gridWidth, pow_one] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ gridScale K + 2))

end MatrixMultiplication.Foundation.Separation

end

end OAI
