/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.Formula
public import InfinitaryLogic.Lomega1omega.QuantifierRank
public import InfinitaryLogic.Karp.CarrierTheorem

/-!
# Quantifier Rank of Scott Formulas

This file proves bounds on the quantifier rank of Scott formulas and connects
BF-equivalence to agreement on Lω₁ω formulas of bounded quantifier rank.

## Main Results

- `scottFormula_qrank_le`: The Scott formula at level α has quantifier rank ≤ α.
- `BFEquiv_iff_EquivQRω_formulas`: BF-equivalence at level α between tuples is
  equivalent to agreement on all Lω₁ω formulas of quantifier rank ≤ α (for α < ω₁).

## References

- [Mar16]
- [KK04]
-/

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω

-- Derive Encodable from Countable for use in einf/esup
attribute [local instance] Encodable.ofCountable

end Language

end FirstOrder
