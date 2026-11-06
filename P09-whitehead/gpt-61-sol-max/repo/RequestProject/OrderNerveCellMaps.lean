import Mathlib.Tactic

import RequestProject.OrderPosetCoverThree
import RequestProject.UnivCoverIncl
import RequestProject.OrderNerveDecoding

/-! Naturality of actual cellular order chains in the full nerve. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem ordNerveChain2_chain2 (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 (chain2 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain2 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [map_add]
  | single t n =>
      simp_all [ordNerveChain2, orderCxMap]

/-- The full cellular three-boundary is natural under actual monotone maps. -/
theorem chain2_ordBoundary3 (f : P → Q) (hf : Monotone f) (c : OrdTet P →₀ ℤ) :
    chain2 (orderCxMap f hf) (ordBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (ordTetMap f hf) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single t n =>
      classical simp_all [ordBoundary3, ordTetMap_boundary]

end FiniteChains.Comb
