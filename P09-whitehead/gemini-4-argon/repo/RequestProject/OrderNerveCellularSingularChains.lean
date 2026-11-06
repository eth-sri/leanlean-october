module

public import RequestProject.OrderNerveExplicitSingularMap

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

noncomputable def orderCellSingularChain1 {P : Type} [PartialOrder P] :
    (OrdEdge P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 1 :=
  ((orderNerveExplicitSingularMap P).f 1).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordEdgeNerveEquiv P))

noncomputable def orderCellSingularChain2 {P : Type} [PartialOrder P] :
    (OrdTri P →₀ ℤ) →ₗ[ℤ] Chain (orderNerveRealization P) 2 :=
  ((orderNerveExplicitSingularMap P).f 2).hom.comp
    (Finsupp.lmapDomain ℤ ℤ (ordTriNerveEquiv P))

theorem orderCellSingularChain1_single {P : Type} [PartialOrder P] (e : OrdEdge P) (r : ℤ) :
    orderCellSingularChain1 (Finsupp.single e r) =
      Finsupp.single (orderNerveSingularSimplex (ordEdgeNerveEquiv P e)) r := by
  change (orderNerveExplicitSingularMap P).f 1
    (Finsupp.mapDomain (ordEdgeNerveEquiv P) (Finsupp.single e r)) = _
  erw [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

theorem orderCellSingularChain2_single {P : Type} [PartialOrder P] (t : OrdTri P) (r : ℤ) :
    orderCellSingularChain2 (Finsupp.single t r) =
      Finsupp.single (orderNerveSingularSimplex (ordTriNerveEquiv P t)) r := by
  change (orderNerveExplicitSingularMap P).f 2
    (Finsupp.mapDomain (ordTriNerveEquiv P) (Finsupp.single t r)) = _
  erw [Finsupp.mapDomain_single]
  exact orderNerveExplicitSingularMap_single _ _ _

/-- The canonical realized cellular two-chain has exactly its singular boundary. -/
theorem orderCellSingularChain2_boundary {P : Type} [PartialOrder P] (c : OrdTri P →₀ ℤ) :
    boundary 1 (orderCellSingularChain2 c) = orderCellSingularChain1 (bdry2 (orderCx P) c) := by
  have h := congrArg (fun f => f (Finsupp.mapDomain (ordTriNerveEquiv P) c))
    ((orderNerveExplicitSingularMap P).comm 2 1).symm
  erw [complex_d, AlternatingFaceMapComplex.obj_d_eq] at h
  change (orderNerveExplicitSingularMap P).f 1
      ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
        (Finsupp.mapDomain (ordTriNerveEquiv P) c)) =
    boundary 1 (orderCellSingularChain2 c) at h
  erw [mathlibOrderNerve_d2] at h
  exact h.symm
