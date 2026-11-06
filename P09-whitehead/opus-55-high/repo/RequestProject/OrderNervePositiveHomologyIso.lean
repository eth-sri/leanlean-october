import RequestProject.OrderNerveSingularH2Iso
import RequestProject.OrderNerveSingularAcyclicity
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

theorem orderNerveExplicitSingularHomology_epi P [PartialOrder P] n :
    Epi (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  apply shortComplex_homologyMap_epi_of_representatives
  intro c hc
  change (complex (orderNerveRealization P)).d _
    _ c = 0 at hc
  rwd [ChainComplex.next_nat_succ, complex_d] at hc
  obtain ⟨z, hz, _, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative n c hc
  refine ⟨orderNerveGradedDecode _ z, ?_, ?_⟩
  · change (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1)) _ = 0
    rwd [ChainComplex.next_nat_succ, AlternatingFaceMapComplex.obj_d_eq]
    apply orderNerveGradedEncode_injective n
    rwd [orderNerveGradedEncode_boundary, orderNerveGradedEncode_decode _ hz,
      ← Nerve.lengthProjection_bdry, hz0, map_zero]
  · change ∃ a : (complex (orderNerveRealization P)).X ((ComplexShape.down ℕ).prev (n + 1)),
      (complex (orderNerveRealization P)).d _ _ a = _
    rwd [ChainComplex.prev]
    refine ⟨b, ?_⟩
    rwd [complex_d]
    exact hb

/-- The canonical realized-simplex map computes the actual positive integral
singular homology of every order-nerve realization, without finiteness assumptions. -/
theorem orderNerveExplicitSingularHomology_isIso P [PartialOrder P] n :
    IsIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  letI := orderNerveExplicitSingularHomology_mono P n
  letI := orderNerveExplicitSingularHomology_epi P n
  exact isIso_of_mono_of_epi _

noncomputable def orderNervePositiveSingularHomologyIso P [PartialOrder P] n :
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology (n + 1) ≅
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) := by
  letI := orderNerveExplicitSingularHomology_isIso P n
  exact asIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) _) ≪≫
    homologyMathlibIso _ _
