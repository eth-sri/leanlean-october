module

public import RequestProject.OrderNerveSingularBoundaryReflection
public import RequestProject.OrderNerveSingularH2Surjective
public import RequestProject.TopologicalSingular.HomologyInjectivity

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

section

variable (P : Type) [PartialOrder P]

/-- The canonical realization comparison is injective on every positive
singular homology group. -/
theorem orderNerveExplicitSingularHomology_mono (n : ℕ) :
    Mono (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  apply shortComplex_homologyMap_mono_of_reflects_boundaries
  intro c hc hb
  change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d _
    _ c = 0 at hc
  rw [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq] at hc
  change ∃ b : (complex (orderNerveRealization P)).X _,
    (complex (orderNerveRealization P)).d _ _ b = _ at hb
  rw [ChainComplex.prev] at hb
  obtain ⟨b, hb⟩ := hb
  rw [complex_d] at hb
  obtain ⟨a, ha⟩ := orderNerveExplicitSingular_reflects_boundaries n c hc b hb
  change ∃ a : (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).X
    _,
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d
      _ _ a = c
  rw [ChainComplex.prev]
  refine ⟨a, ?_⟩
  rw [AlternatingFaceMapComplex.obj_d_eq]
  exact ha

theorem orderNerveSingularH2Comparison_mono :
    Mono (orderNerveSingularH2Comparison P) := by
  rw [orderNerveSingularH2Comparison_factor]
  letI := orderNerveExplicitSingularHomology_mono P 1
  infer_instance

theorem orderCellSingularH2Map_injective :
    Function.Injective (orderCellSingularH2Map P) := ((ModuleCat.mono_iff_injective _).mp (orderNerveSingularH2Comparison_mono P)).comp (mathlibOrderNerveComplexH2Equiv P).injective

/-- An actual isomorphism, with the original natural comparison as forward map. -/
noncomputable def orderCellSingularH2Equiv :=
  LinearEquiv.ofBijective _
    ⟨orderCellSingularH2Map_injective P, orderCellSingularH2Map_surjective P⟩

end

theorem orderCellSingularH2Equiv_natural {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P → Q) (hf : Monotone f) (z : OrderNerveH2 P) :
    ((((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj _).map
      (orderNerveRealizationMap f hf)).hom (orderCellSingularH2Equiv P z)) =
        orderCellSingularH2Equiv Q (orderNerveH2Map f hf z) :=
  by apply orderCellSingularH2Map_natural

end FiniteChains.Comb
