import RequestProject.OrderNerveSingularBoundaryReflection
import RequestProject.OrderNerveSingularH2Surjective
import RequestProject.TopologicalSingular.HomologyInjectivity
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The canonical realization comparison is injective on every positive
singular homology group. -/
theorem orderNerveExplicitSingularHomology_mono P [PartialOrder P] n :
    Mono (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  apply shortComplex_homologyMap_mono_of_reflects_boundaries
  intro c hc hb
  change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d _
    _ c = 0 at hc
  rw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq] at hc
  change ∃ b : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
    (complex (orderNerveRealization P)).d _ _ b = _ at hb
  rw [ChainComplex.prev] at hb
  cases' hb with b hb
  rw [complex_d] at hb
  cases' orderNerveExplicitSingular_reflects_boundaries n c hc b hb with a ha
  change ∃ a : (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).X
    ((ComplexShape.down ℕ).prev (n + 1)),
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d
      _ _ a = c
  rw [ChainComplex.prev]
  refine ⟨a, ?_⟩
  rw [AlternatingFaceMapComplex.obj_d_eq]
  exact ha

theorem orderNerveSingularH2Comparison_mono P [PartialOrder P] :
    Mono (orderNerveSingularH2Comparison P) := by
  rw [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularHomology_mono P 1
  infer_instance

theorem orderCellSingularH2Map_injective P [PartialOrder P] :
    Function.Injective (orderCellSingularH2Map P) := by
  have h := (ModuleCat.mono_iff_injective _).mp (orderNerveSingularH2Comparison_mono P)
  exact h.comp (mathlibOrderNerveComplexH2Equiv P).injective

/-- An actual isomorphism, with the original natural comparison as forward map. -/
noncomputable def orderCellSingularH2Equiv P [PartialOrder P] :=
  LinearEquiv.ofBijective _
    ⟨orderCellSingularH2Map_injective P, orderCellSingularH2Map_surjective P⟩

theorem orderCellSingularH2Equiv_natural {P Q} [PartialOrder P] [PartialOrder Q]
    f hf z :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)).hom (orderCellSingularH2Equiv P z)) =
        orderCellSingularH2Equiv Q (orderNerveH2Map f hf z) :=
  orderCellSingularH2Map_natural f hf z
