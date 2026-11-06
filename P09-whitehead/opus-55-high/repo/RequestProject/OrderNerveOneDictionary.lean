import RequestProject.OrderNerveCellMaps
import RequestProject.CellularChainMapZero
import RequestProject.Tac


/-! The degree-one dictionary for actual order chains and their finite prisms. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

noncomputable def ordNerveChain0 : (P →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun p => FreeAbelianGroup.of [p])

theorem ordNerveChain0_bdry1 (c : OrdEdge P →₀ ℤ) :
    ordNerveChain0 (bdry1 (orderCx P) c) = Nerve.bdry (ordNerveChain1 c) := by
  lin_ind c e n =>
    rw [bdry1_single]
    simp [map_smul, map_sub]
    simp [ordNerveChain0, ordNerveChain1, orderCx, Nerve.bdryOn,
      Nerve.consMap_of, smul_sub, map_sub, Finsupp.linearCombination_single]

theorem ordNerveChain1_mem_inc c :
    ordNerveChain1 c ∈ Nerve.Inc P := by
  lin_ind c e n using aesop =>
    simp [ordNerveChain1, Finsupp.linearCombination_single]
    apply AddSubgroup.zsmul_mem
    apply Nerve.of_mem_inc
    grind

theorem ordNerveChain1_lengthProjection (c : OrdEdge P →₀ ℤ) :
    Nerve.lengthProjection 2 (ordNerveChain1 c) = ordNerveChain1 c := by
  classical
  lin_ind c e n => simp [ordNerveChain1]

theorem ordNerveChain1_chain1 (f : P → Q) hf (c : OrdEdge P →₀ ℤ) :
    ordNerveChain1 (chain1 (orderCxMap f hf) c) = Nerve.cmap f (ordNerveChain1 c) := by
  lin_ind c e n =>
    change ordNerveChain1 (Finsupp.mapDomain (orderCxMap f hf).onE
      (Finsupp.single e n)) = _
    simp [ordNerveChain1, Nerve.cmap_of, orderCxMap]
