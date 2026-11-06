import RequestProject.OrderNerveCellularSingularChains
import RequestProject.OrderNerveSmallHomotopyZero
import RequestProject.OrderNerveSmallCellularChainMap
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision

noncomputable def orderCellSingularChain0 {P} [PartialOrder P] :
    (P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 0 :=
  Finsupp.lmapDomain ℤ ℤ (fun p => orderNerveSingularSimplex (ComposableArrows.mk₀ p))

theorem orderCellSingularChain0_single {P} [PartialOrder P] (p : P) r :
    orderCellSingularChain0 (Finsupp.single p r) =
      Finsupp.single (orderNerveSingularSimplex (ComposableArrows.mk₀ p)) r :=
  Finsupp.mapDomain_single

/-- The realized oriented edge has its target minus its source as boundary. -/
theorem orderCellSingularChain1_boundary {P} [PartialOrder P] c :
    boundary 0 (orderCellSingularChain1 c) = orderCellSingularChain0 (P := P) (bdry1 (orderCx P) c) := by
  lin_ind c e r =>
    have h0 : (nerve P).δ (0) (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.2 := by
      apply CategoryTheory.Functor.ext (by fin_cases ·; rfl)
    have h1 : (nerve P).δ (1) (ordEdgeNerveEquiv P e) =
        ComposableArrows.mk₀ e.val.1 := by
      apply CategoryTheory.Functor.ext (by fin_cases ·; rfl)
    rwd [orderCellSingularChain1_single, boundary_single, Fin.sum_univ_two]
    simp only [orderNerveSingularSimplex_face, h0, h1, Fin.val_zero, Fin.val_one,
      pow_zero, pow_one, one_smul, neg_smul]
    rwd [bdry1_single, map_smul, map_sub,
      orderCellSingularChain0_single, orderCellSingularChain0_single]
    simp [orderCx, sub_eq_add_neg]

theorem orderSmallSingularApproximation0_realization {P} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    orderCellSingularChain0 (orderSmallCellularApproximation0 c) =
      orderSmallSingularApproximation0 c := by
  have he : orderCellSingularChain0.comp orderSmallCellularApproximation0 =
      (orderSmallSingularApproximation0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] _) := by
    apply orderSmallSingle_spans
    intro σ
    simp [LinearMap.comp_apply, orderSmallCellularApproximation0_single,
      orderCellSingularChain0_single, orderSmallSingularApproximation0_single]
    rfl
  exact DFunLike.congr_fun he c
