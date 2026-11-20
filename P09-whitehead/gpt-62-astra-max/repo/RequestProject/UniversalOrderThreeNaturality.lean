module

public import RequestProject.OrderUniversalThree


@[expose] public section

/-! Naturality of genuine lifted tetrahedra, including the transported first face. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

variable (f : P → Q) (hf : Monotone f) (a : P)

variable (t : UOrdTet P a)

def uOrdTetMap : UOrdTet Q (f a) :=
  ⟨(@univLiftV (orderCx P) _ a (orderCxMap f hf) t.1.1, ordTetMap f hf t.1.2), by
    rw [endV_univLiftV, t.2]
    rfl⟩

theorem uOrdTetMap_face0 :
    univLiftF a (orderCxMap f hf) (uOrdTetFace0 t) = uOrdTetFace0 (uOrdTetMap f hf a t) := by
  apply Subtype.ext
  apply Prod.ext
  · exact univLiftV_extend a _ (eb := ordPos _) t.2
  · rfl

theorem uOrdTetMap_boundary :
    Finsupp.mapDomain (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      (uOrdTetBoundary t) = uOrdTetBoundary (uOrdTetMap f hf a t) := by
  let L :=
    Finsupp.lmapDomain ℤ ℤ (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
  change L _ = _
  simp only [uOrdTetBoundary, map_sub, map_add]
  simp only [L, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [uOrdTetMap_face0]
  rfl

theorem univLift_uOrdBoundary3
    (y : UOrdTet P a →₀ ℤ) :
    chain2 (univLift (orderCx P) (orderCxMap f hf) a) (uOrdBoundary3 y) =
      uOrdBoundary3 (Finsupp.mapDomain (uOrdTetMap f hf a) y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [map_add, hc, hd, Finsupp.mapDomain_add]
  | single t n =>
    rw [uOrdBoundary3, Finsupp.linearCombination_single, map_smul]
    change n • Finsupp.mapDomain (@univLiftF (orderCx P) (orderCx Q) a (orderCxMap f hf))
      (uOrdTetBoundary t) = _
    rw [uOrdTetMap_boundary, Finsupp.mapDomain_single, uOrdBoundary3,
      Finsupp.linearCombination_single]

end FiniteChains.Comb
