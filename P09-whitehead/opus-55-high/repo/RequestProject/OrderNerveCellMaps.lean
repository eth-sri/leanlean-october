import RequestProject.OrderPosetCoverThree
import RequestProject.UnivCoverIncl
import RequestProject.OrderNerveDecoding
import RequestProject.Tac


/-! Naturality of actual cellular order chains in the full nerve. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem ordNerveChain2_chain2 (f : P → Q) hf (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 (chain2 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain2 c) := by
  lin_ind c with c d hc hd => simp_all [map_add, hc, hd]
  | t n =>
      simp [Finsupp.mapDomain_single, ordNerveChain2, Nerve.cmap_of, orderCxMap]

/-- The full cellular three-boundary is natural under actual monotone maps. -/
theorem chain2_ordBoundary3 (f : P → Q) hf c :
    chain2 (orderCxMap f hf) (ordBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (ordTetMap f hf) c) := by
  lin_ind c with c d hc hd => simp [map_add, hc, hd, Finsupp.mapDomain_add]
  | t n =>
      rw [ordBoundary3, Finsupp.linearCombination_single, map_smul,
        Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single]
      congr 1
      exact ordTetMap_boundary f hf t
