import RequestProject.OrderNerveTightChainMap
import RequestProject.TopologicalSingular.SmallRefinement
import RequestProject.OrderNerveGradedBoundary
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

def orderRefinementSmall P [PartialOrder P] n :
    Chain (orderNerveRealization P) n →ₗ[ℤ] smallChains (orderNerveRealizationOpenStar P) n :=
  (smallRefinement _ (orderNerveRealizationOpenStar_isOpen P)
    (orderNerveRealizationOpenStar_cover P) n).codRestrict _
      (smallRefinement_mem_small _ _ _ n)

theorem orderRefinementSmall_boundary n c :
    smallBoundary (orderNerveRealizationOpenStar P) n (orderRefinementSmall P (n + 1) c) =
      orderRefinementSmall P n (boundary n c) := by
  apply Subtype.ext
  exact smallRefinement_boundary _ _ _ n c

def orderSingularToNerve P [PartialOrder P] n :=
  (orderTightToNerve P n).comp (orderRefinementSmall P n)

theorem orderSingularToNerve_boundary n c :
    Nerve.bdry (orderSingularToNerve P (n + 1) c) =
      orderSingularToNerve P n (boundary n c) := by
  rwd [orderTightToNerve_boundary, orderRefinementSmall_boundary]
  rfl

theorem orderSingularToNerve_zero_boundary c :
    Nerve.bdry (orderSingularToNerve P 0 c) =
      augmentation c • FreeAbelianGroup.of ([] : List P) := by
  rwd [orderSmallToNerve0_boundary]
  rfl

theorem orderSingularToNerve_length n c :
    Nerve.lengthProjection (n + 1) (orderSingularToNerve P n c) = orderSingularToNerve P n c :=
  orderTightToNerve_length n _

theorem orderSingularToNerve_mem_inc n c :
    orderSingularToNerve P n c ∈ Nerve.Inc P := orderTightToNerve_mem_inc n _

theorem orderSingularToNerve_supported n A
    {c}
    (hc : c ∈ subChains (orderNerveRealizationSubcomplex P A) n) :
    orderSingularToNerve P n c ∈ Nerve.IncOn A :=
  orderTightToNerve_supported n A _ (smallRefinement_support _ _ _ n _ hc)

/-- The return map on the original simplicial chains. -/
def orderNerveRoundTrip (P : Type) [PartialOrder P] n :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderSingularToNerve P n).comp ((orderNerveExplicitSingularMap P).f n).hom

theorem orderNerveRoundTrip_boundary n c :
    Nerve.bdry (orderNerveRoundTrip P (n + 1) c) =
      orderNerveRoundTrip P n
        ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom c) := by
  have he := congrArg (· c) ((orderNerveExplicitSingularMap P).comm _ n)
  rwd [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  rwd [orderSingularToNerve_boundary]
  tauto

theorem orderNerveRoundTrip_supported n s :
    orderNerveRoundTrip P n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  apply orderSingularToNerve_supported
  rwd [orderNerveExplicitSingularMap_single]
  exact single_mem_subChains _ n _ 1 (orderNerveSingularSimplex_supported _ s (by simp))

theorem orderNerveRoundTrip_zero_boundary c :
    Nerve.bdry (orderNerveRoundTrip P 0 c) = Nerve.bdry (orderNerveGradedEncode 0 c) := by
  lin_ind c s r =>
    change Nerve.bdry (orderSingularToNerve P 0 ((orderNerveExplicitSingularMap P).f 0 _)) = _
    rwd [orderNerveExplicitSingularMap_single, orderSingularToNerve_zero_boundary,
      augmentation_single, orderNerveGradedEncode_single, map_zsmul, Nerve.bdry_of]
    rfl
