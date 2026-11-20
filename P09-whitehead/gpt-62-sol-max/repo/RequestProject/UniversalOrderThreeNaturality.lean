module

public import RequestProject.FinsuppBasis
public import RequestProject.OrderUniversalThree
public import RequestProject.CombPi2

@[expose] public section

/-! Naturality of genuine lifted tetrahedra, including the transported first face. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def uOrdTetMap (f : P → Q) (hf : Monotone f) (a : P) (t : UOrdTet P a) : UOrdTet Q (f a) :=
  ⟨(@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) t.1.1, ordTetMap f hf t.1.2), by
    rw [endV_univLiftV, t.2]
    rfl⟩

theorem uOrdTetMap_face0 (f : P → Q) (hf : Monotone f) (a : P) (t : UOrdTet P a) :
    univLiftF a (orderCxMap f hf) (uOrdTetFace t 0) = uOrdTetFace (uOrdTetMap f hf a t) 0 := by
  apply Subtype.ext
  apply Prod.ext
  · exact univLiftV_extend a (orderCxMap f hf) (eb := ordPos t.1.2.2.1)
      (c := t.1.1) t.2
  · rfl

theorem uOrdTetMap_boundary (f : P → Q) (hf : Monotone f) (a : P) (t : UOrdTet P a) :
    Finsupp.mapDomain (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      (uOrdTetBoundary t) = uOrdTetBoundary (uOrdTetMap f hf a t) := by
  let L  :=
    Finsupp.lmapDomain ℤ ℤ (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
  change L (uOrdTetBoundary t) = _
  simp only [uOrdTetBoundary, tetrahedronBoundary, map_sub, map_add]
  simp only [L, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [uOrdTetMap_face0]
  rfl

theorem univLift_uOrdBoundary3 (f : P → Q) (hf : Monotone f) (a : P)
    (y : UOrdTet P a →₀ ℤ) :
    chain2 (univLift (orderCx P) (orderCxMap f hf) a) (uOrdBoundary3 y) =
      uOrdBoundary3 (Finsupp.mapDomain (uOrdTetMap f hf a) y) := by
  finsupp_basis y
  intro t
  simpa only [uOrdBoundary3, Finsupp.linearCombination_single, one_smul, chain2_apply,
    Finsupp.mapDomain_single, univLift] using! uOrdTetMap_boundary f hf a t

end FiniteChains.Comb
