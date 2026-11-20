module

public import RequestProject.OrderNerveCellMaps
public import RequestProject.FinsuppBasis
public import RequestProject.CellularChainMapZero

@[expose] public section

/-! The degree-one dictionary for actual order chains and their finite prisms. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def ordNerveChain0 : (P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun p => FreeAbelianGroup.of [p])

theorem ordNerveChain0_bdry1 (c : OrdEdge P →₀ ℤ) :
    ordNerveChain0 (bdry1 (orderCx P) c) = Nerve.bdry (ordNerveChain1 c) := by
  finsupp_basis c
  intro e
  rw [bdry1_single]
  simp only [map_smul, map_sub]
  simp [ordNerveChain0, ordNerveChain1, orderCx, Nerve.bdryOn, Nerve.consMap_of, smul_sub, Finsupp.linearCombination_single]

theorem ordNerveChain1_mem_inc (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 c ∈ Nerve.Inc P := by
  apply Finsupp.linearCombination_mem (T := (Nerve.Inc P).toIntSubmodule) _ c
  intro e
  apply Nerve.of_mem_inc
  simpa [List.isChain_cons] using e.2

theorem ordNerveChain1_lengthProjection (c : OrdEdge P →₀ ℤ) :
    Nerve.lengthProjection 2 (ordNerveChain1 c) = ordNerveChain1 c := by
  classical
  finsupp_basis c
  intro e
  simp [ordNerveChain1]

theorem ordNerveChain1_chain1 (f : P → Q) (hf : Monotone f) (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 (chain1 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain1 c) := by
  finsupp_basis c
  intro e
  change ordNerveChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
    (Finsupp.single e 1)) = _
  rw [Finsupp.mapDomain_single]
  simp [ordNerveChain1, Nerve.cmap_of, orderCxMap]

end FiniteChains.Comb
