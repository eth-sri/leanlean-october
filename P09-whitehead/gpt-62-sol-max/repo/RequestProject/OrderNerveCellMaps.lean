module

public import RequestProject.FinsuppBasis
public import RequestProject.OrderPosetCoverThree
public import RequestProject.UnivCoverIncl
public import RequestProject.OrderNerveDecoding

@[expose] public section

/-! Naturality of actual cellular order chains in the full nerve. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem ordNerveChain2_chain2 (f : P → Q) (hf : Monotone f) (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 (chain2 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain2 c) := by
  finsupp_singles c
  intro t n
  simp [ordNerveChain2, Nerve.cmap_of, orderCxMap]

/-- The full cellular three-boundary is natural under actual monotone maps. -/
theorem chain2_ordBoundary3 (f : P → Q) (hf : Monotone f) (c : OrdTet P →₀ ℤ) :
    chain2 (orderCxMap f hf) (ordBoundary3 c) =
      ordBoundary3 (Finsupp.mapDomain (ordTetMap f hf) c) := by
  finsupp_basis c
  intro t
  simpa only [ordBoundary3, Finsupp.linearCombination_single, one_smul, chain2_apply,
    Finsupp.mapDomain_single] using ordTetMap_boundary f hf t

end FiniteChains.Comb
