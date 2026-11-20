module

public import RequestProject.MathlibOrderNerveCells
public import RequestProject.FinsuppBasis
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- Mathlib's free integral module simplicial object of the actual poset nerve. -/
noncomputable def mathlibOrderNerveModule : SimplicialObject (ModuleCat ℤ) :=
  nerve P ⋙ ModuleCat.free ℤ

/-- The actual Mathlib alternating-face differential on a triangle agrees with
its actual cellular second boundary in order coordinates. -/
theorem mathlibOrderNerve_d2_single (t : OrdTri P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.single (ordTriNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P)
          (bdry2 (orderCx P) (Finsupp.single t 1)) := by
  rw [ordTriangleBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- The actual Mathlib alternating-face differential on a tetrahedron agrees
with its genuine order-nerve third boundary. -/
theorem mathlibOrderNerve_d3_single (t : OrdTet P) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.single (ordTetNerveEquiv P t) 1) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordTetBoundary t) := by
  rw [ordTetBoundary_nerve_faces]
  simp [AlgebraicTopology.AlternatingFaceMapComplex.objD, mathlibOrderNerveModule,
    SimplicialObject.δ, Fin.sum_univ_succ, ModuleCat.free]
  abel

/-- Actual finite two-chains satisfy the Mathlib/cellular boundary comparison. -/
theorem mathlibOrderNerve_d2 (c : OrdTri P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
        Finsupp.mapDomain (ordEdgeNerveEquiv P) (bdry2 (orderCx P) c) := by
  finsupp_basis c
  intro t
  simpa only [Finsupp.mapDomain_single] using mathlibOrderNerve_d2_single P t

/-- Actual finite three-chains satisfy the Mathlib/order-nerve boundary comparison. -/
theorem mathlibOrderNerve_d3 (c : OrdTet P →₀ ℤ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
        Finsupp.mapDomain (ordTriNerveEquiv P) (ordBoundary3 c) := by
  finsupp_basis c
  intro t
  simpa only [Finsupp.mapDomain_single, ordBoundary3, Finsupp.linearCombination_single,
    one_smul] using mathlibOrderNerve_d3_single P t

end FiniteChains.Comb
