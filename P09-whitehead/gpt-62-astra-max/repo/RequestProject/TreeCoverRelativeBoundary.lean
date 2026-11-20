module

public import RequestProject.TreeCoverAcyclic

@[expose] public section

/-! Prescribed nonzero boundaries survive the actual spanning-tree collapse. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K)
  (N : Subgroup (FreeGroup (NonTree T))) [N.Normal]
  (hN : ∀ f, treeRel T f ∈ N)

/-- Two lifted edge chains with equal vertex boundaries are equal as soon as
their non-tree coordinates agree. The difference is a cycle supported on trees. -/
theorem piE_injective_of_same_boundary (c d : (CovQ T N × K.E) →₀ ℤ)
    (hb : bdry1 (treeCover T N hN) c = bdry1 (treeCover T N hN) d)
    (he : piE T N c = piE T N d) : c = d := by
  classical
  apply sub_eq_zero.mp
  apply treeChain_eq_zero (hN := hN)
  · apply support_isTree_of_piE_eq_zero (N := N) <;> simp_all
  · simp_all

variable [DecidableEq (NonTree T)]

end FiniteChains.Comb.SpanningTree
