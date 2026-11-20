module

public import RequestProject.OrderNerveSingularAcyclicity
public import RequestProject.OrderNerveSingularHomologyComparison
public import RequestProject.TopologicalSingular.HomologySurjectivity

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

theorem orderNerveExplicitSingularHomology_epi (P : Type) [PartialOrder P] (n : ℕ) :
    Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  apply shortComplex_homologyMap_epi_of_representatives
  intro c hc
  change (complex (orderNerveRealization P)).d _
    _ c = 0 at hc
  erw [ChainComplex.next_nat_succ, complex_d] at hc
  obtain ⟨z, hz, _, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative n c hc
  refine ⟨orderNerveGradedDecode _ z, ?_, ?_⟩
  · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d _
      _ _ = 0
    erw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
    apply orderNerveGradedEncode_injective n
    erw [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hz,
      ← Nerve.lengthProjection_bdry, hz0, map_zero]
  · change ∃ a : (complex (orderNerveRealization P)).X _,
      (complex (orderNerveRealization P)).d _ _ a = _
    erw [ChainComplex.prev]
    refine ⟨b, ?_⟩
    erw [complex_d] <;> assumption

section

variable (P : Type) [PartialOrder P]

theorem orderNerveSingularH2Comparison_factor :
    orderNerveSingularH2Comparison P =
      HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) 2 ≫
        (homologyMathlibIso _ 2).hom := by
  have he : orderNerveExplicitSingularMap P ≫ (complexMathlibIso _).hom =
      orderNerveRealizationChainComparison P ≫
        (FiniteChains.freeSingularChainComplexIso _).hom := by
    simp [orderNerveExplicitSingularMap, complexMathlibIso, Category.assoc]
  change (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ 2).map
      (orderNerveRealizationChainComparison P) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ 2).map
        _ =
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ 2).map
      _ ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) _ 2).map
        _
  grind

theorem orderNerveSingularH2Comparison_epi :
    Epi (orderNerveSingularH2Comparison P) := by
  erw [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularHomology_epi P 1
  infer_instance

theorem orderCellSingularH2Map_surjective :
    Function.Surjective (orderCellSingularH2Map P) := by
  intro x
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp (orderNerveSingularH2Comparison_epi P) x
  obtain ⟨z, rfl⟩ := (mathlibOrderNerveComplexH2Equiv P).surjective y <;> aesop

end

/-- A zero cellular pushdown annihilates every actual singular second-homology
class, without any remaining comparison-image hypothesis. -/
theorem orderNerveSingularH2Map_zero_of_orderH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hzero : orderNerveH2Map f hf = 0) :
    (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0 := by
  letI := orderNerveSingularH2Comparison_epi P
  apply (cancel_epi (orderNerveSingularH2Comparison P)).mp
  simp_all [orderNerveSingularH2Comparison_pushdown_zero]

end FiniteChains.Comb
