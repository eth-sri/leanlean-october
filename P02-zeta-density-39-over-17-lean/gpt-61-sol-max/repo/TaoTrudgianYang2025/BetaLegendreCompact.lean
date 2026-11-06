module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaLegendreAllOrders

@[expose] public section

/-!
# Common compact slope domains and finite-order dual-phase uniformity

A fixed closed interval strictly inside (2^(-sigma),1) belongs to every
sufficiently accurate model phase's actual slope image. The final consumer
derives that inclusion and all requested derivative errors with one tolerance.
Canonical-domain extension and the transformed-sum theorem remain separate.
-/

noncomputable section

open Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025


def legendreFiniteInputOrder (Q : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (Q+1), (inversePhaseOrder (inversePhaseDerivativeExpression n)+1)

theorem legendreFiniteInputOrder_le {Q n : ℕ} (hn : n ≤ Q) :
    inversePhaseOrder (inversePhaseDerivativeExpression n)+1 ≤ legendreFiniteInputOrder Q := by
  unfold legendreFiniteInputOrder
  exact Finset.single_le_sum (fun k _ => Nat.zero_le
    (inversePhaseOrder (inversePhaseDerivativeExpression k)+1))
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))


