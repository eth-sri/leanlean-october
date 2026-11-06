import RequestProject.OrderNerveSingularTwoCycles
import RequestProject.OrderNerveSingularHomologyComparison
import RequestProject.TopologicalSingular.HomologySurjectivity
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The actual realization unit is surjective on second singular homology. -/
theorem orderNerveExplicitSingularH2_epi P [PartialOrder P] :
    Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2) := by
  unfold HomologicalComplex.homologyMap HomologicalComplex.shortComplexFunctor
  apply shortComplex_homologyMap_epi_of_representatives
  intro c hc
  change ((complex (orderNerveRealization P)).d 2 _) c = 0 at hc
  rwd [ChainComplex.next_nat_succ, complex_d] at hc
  obtain ⟨z, hz, b, hb⟩ := orderNerveRealization_twoCycle_cellularRepresentative c hc
  refine ⟨Finsupp.mapDomain (ordTriNerveEquiv P) z, ?_, ?_⟩
  · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d 2
      ((ComplexShape.down ℕ).next 2) _ = 0
    rwd [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
    rwd [mathlibOrderNerve_d2, hz, Finsupp.mapDomain_zero]
  · rwd [ChainComplex.prev]
    tauto

theorem orderNerveSingularH2Comparison_factor P [PartialOrder P] :
    orderNerveSingularH2Comparison P =
      HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2 ≫
        (homologyMathlibIso (orderNerveRealization P) 2).hom := by
  have he : orderNerveExplicitSingularMap P ≫ (complexMathlibIso _).hom =
      orderNerveRealizationChainComparison P ≫
        (FiniteChains.freeSingularChainComplexIso _).hom := by
    simp [orderNerveExplicitSingularMap, complexMathlibIso, Category.assoc]
  change (HomologicalComplex.homologyFunctor _ _ 2).map
      (orderNerveRealizationChainComparison P) ≫
      (HomologicalComplex.homologyFunctor _ _ 2).map
        (FiniteChains.freeSingularChainComplexIso _).hom =
    (HomologicalComplex.homologyFunctor _ _ 2).map
      (orderNerveExplicitSingularMap P) ≫
      (HomologicalComplex.homologyFunctor _ _ 2).map
        (complexMathlibIso _).hom
  grind

theorem orderNerveSingularH2Comparison_epi P [PartialOrder P] :
    Epi (orderNerveSingularH2Comparison P) := by
  rwd [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularH2_epi P
  infer_instance

theorem orderCellSingularH2Map_surjective P [PartialOrder P] :
    Function.Surjective (orderCellSingularH2Map P) := by
  intro x
  cases' (ModuleCat.epi_iff_surjective _).mp (orderNerveSingularH2Comparison_epi P) x with y hy
  obtain ⟨z, rfl⟩ := (mathlibOrderNerveComplexH2Equiv P).surjective y
  tauto

/-- A zero cellular pushdown annihilates every actual singular second-homology
class, without any remaining comparison-image hypothesis. -/
theorem orderNerveSingularH2Map_zero_of_orderH2Map_zero {P Q}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) hf
    (hzero : orderNerveH2Map f hf = 0) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0 := by
  letI := orderNerveSingularH2Comparison_epi P
  apply (cancel_epi (orderNerveSingularH2Comparison P)).mp
  simp [orderNerveSingularH2Comparison_pushdown_zero f hf hzero, Limits.comp_zero]
