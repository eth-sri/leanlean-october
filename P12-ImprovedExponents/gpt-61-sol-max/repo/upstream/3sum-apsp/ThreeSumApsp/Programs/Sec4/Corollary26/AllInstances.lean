/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.ParameterSteps
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters

/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4



/-! ## Time and need -/

/-! ## The test -/

/-! ## The limits -/

section

variable {lim : Limits} {N D₀ w U fr d : ℕ}

end

/-! ## The matrices of an instance -/

/-- The first matrix of an instance. -/
def thinMX (x : ThinInst) : ThreeSumApsp.IntMatrix x.N x.D := fun i j => x.X.getD (i * x.D + j) 0

/-- The second matrix of an instance. -/
def thinMY (x : ThinInst) : ThreeSumApsp.IntMatrix x.D x.N := fun i j => x.Y.getD (i * x.N + j) 0

theorem matAt_thinMX {x} {μ} {fr} (h : x.Pre μ fr) : MatAt μ x.x
    (thinMX x) := by
  intro i j

  rw [Nat.add_assoc, h.segX.getD (by
    rw [h.lenX]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.D)
    omega
  ) 0]
  rfl

theorem matAt_thinMY {x} {μ} {fr} (h : x.Pre μ fr) : MatAt μ x.y
    (thinMY x) := by
  intro i j

  rw [Nat.add_assoc, h.segY.getD (by
    rw [h.lenY]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.N)
    omega
  ) 0]
  rfl

/-- The entry of the product of the two matrices is the entry that the task asks for. -/
theorem entryN_thin x {I J} (hI : I < x.N) (hJ : J < x.N) :
    entryN (thinMX x) (thinMY x) I J = thinEntry x.N x.D x.X x.Y I J := by
  rw [entryN, dif_pos ⟨hI, hJ⟩, Matrix.mul_apply, thinEntry, List.sum_map_range, Finset.sum_range]
  rfl

/-! ## The routine -/

/-- The answers of the offline routine are those that the task asks for. -/
def map_entryN_thin {x : ThinInst} {μ} {fr} (h : x.Pre μ fr) :=
  List.map_congr_left fun _ hq =>
    entryN_thin x (h.ltWI _ (List.of_mem_zip hq).1) (h.ltWJ _ (List.of_mem_zip hq).2)

/-! ## The time in the regime -/

/-! ## The need is polynomial in the parameters -/

section

variable {N D U Q : ℕ}

end

end Light.Sec4
