import Mathlib.CategoryTheory.Whiskering
import RequestProject.MathlibOrderNerveChainBoundary
import RequestProject.OrderNerveCellMaps
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial Opposite
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The triangle dictionary commutes with the actual Mathlib nerve map. -/
theorem ordTriNerveEquiv_map f hf (t : OrdTri P) :
    ordTriNerveEquiv Q ((orderCxMap f hf).onF t) =
      (nerveMap hf.functor).app (op ⦋2⦌) (ordTriNerveEquiv P t) := by
  apply CategoryTheory.Functor.ext (by fin_cases · <;> rfl)

/-- The tetrahedron dictionary commutes with the actual Mathlib nerve map. -/
theorem ordTetNerveEquiv_map f hf t :
    ordTetNerveEquiv Q (ordTetMap f hf t) =
      (nerveMap hf.functor).app (op ⦋3⦌) (ordTetNerveEquiv P t) := by
  apply CategoryTheory.Functor.ext (by fin_cases · <;> rfl)

/-- The actual Mathlib simplicial-module map induced by a monotone map. -/
def mathlibOrderNerveModuleMap (f : P → Q) (hf : Monotone f) :
    mathlibOrderNerveModule P ⟶ mathlibOrderNerveModule Q :=
  CategoryTheory.Functor.whiskerRight (nerveMap hf.functor) _

/-- The actual Mathlib chain map induced by a monotone map. -/
def mathlibOrderNerveChainMap (f : P → Q) (hf : Monotone f) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶
      AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule Q) :=
  AlgebraicTopology.AlternatingFaceMapComplex.map (mathlibOrderNerveModuleMap f hf)

/-- The actual cellular two-chain pushforward is the actual Mathlib chain map
under the proved order-simplex coordinates. -/
theorem mathlibOrderNerveChainMap_two f hf
    (c : OrdTri P →₀ ℤ) :
    ((mathlibOrderNerveChainMap f hf).f 2).hom
      (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
        Finsupp.mapDomain (ordTriNerveEquiv Q) (chain2 (orderCxMap f hf) c) := by
  change Finsupp.mapDomain ((nerveMap hf.functor).app (op ⦋2⦌))
    (Finsupp.mapDomain (ordTriNerveEquiv P) c) =
      Finsupp.mapDomain (ordTriNerveEquiv Q)
        (Finsupp.mapDomain (orderCxMap f hf).onF c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro t _
  exact (ordTriNerveEquiv_map f hf t).symm

/-- The actual three-chain dictionary also commutes with the actual Mathlib chain map. -/
theorem mathlibOrderNerveChainMap_three f hf
    (c : OrdTet P →₀ ℤ) :
    ((mathlibOrderNerveChainMap f hf).f 3).hom
      (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
        Finsupp.mapDomain (ordTetNerveEquiv Q)
          (Finsupp.mapDomain (ordTetMap f hf) c) := by
  change Finsupp.mapDomain ((nerveMap hf.functor).app (op ⦋3⦌))
    (Finsupp.mapDomain (ordTetNerveEquiv P) c) =
      Finsupp.mapDomain (ordTetNerveEquiv Q)
        (Finsupp.mapDomain (ordTetMap f hf) c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro t _
  exact (ordTetNerveEquiv_map f hf t).symm
