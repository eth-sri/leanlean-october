/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters

/-!
# Corollaries 31 and 32: the parameters of the program, and where its costs are bounded

For real c > 10, 0 < θ < 0.9 and ε < R_c(γ) there are parameters G for the program text (rational c'
and θ', a threshold m₀) and a constant C such that on every instance with 1 ≤ D ≤ N^ε and with m ≥
m₀ the costs of Theorem 30 at these parameters are at most C times

    Tp = N² (log D + 1)²/D^γ     and     Tq = D^q (log D + 1),

γ and q being those of c and θ (`exists_ratParams`).

The rational parameters come from `exists_rat_params` and the costs at them from
`Corollary31.costs`. What is left is to compare the bounds: γ(c', θ') ≥ γ(c, θ) and q(θ') ≤ q(θ)
make the bounds at the rational parameters smaller (`le_preBound31`, `le_queryBound31`), and both
bounds are at least 1 (`one_le_preBound31`, `one_le_queryBound31`), so that additive constants can
be absorbed.
-/

@[expose] public section



namespace Light.Sec4



/-- The bound on the preprocessing, N² (log D + 1)²/D^γ. -/
noncomputable def preBound31 (γ : ℝ) (N D₀ : ℕ) :=
  (N : ℝ) ^ 2 * (Real.log D₀ + 1) ^ 2 / (D₀ : ℝ) ^ γ
/-- The bound on a query, D^q (log D + 1); the summand 1 makes it at least 1 at D = 1. -/
noncomputable def queryBound31 (q : ℝ) (D₀ : ℕ) := (D₀ : ℝ) ^ q * (Real.log D₀ + 1)

section

variable {N D₀ : ℕ}

end

end Light.Sec4
