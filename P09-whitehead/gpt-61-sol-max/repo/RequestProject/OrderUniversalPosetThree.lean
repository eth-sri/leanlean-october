import Mathlib.Tactic

import RequestProject.OrderUniversalPosetHom
import RequestProject.OrderUniversalThree

/-! The actual lifted three-boundary under the universal-cover order identification. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P] {a : P}

variable (t : OrdTet (UOrder P a))
def uOrderTet  : UOrdTet P a :=
  ⟨(t.1.1, ⟨(uOrderEnd t.1.1, uOrderEnd t.1.2.1,
    uOrderEnd t.1.2.2.1, uOrderEnd t.1.2.2.2),
    uOrderEnd_monotone t.2.1, uOrderEnd_monotone t.2.2.1,
    uOrderEnd_monotone t.2.2.2⟩), rfl⟩

/-- The four actual lifted faces have precisely the alternating nerve boundary. -/
theorem uOrderTet_boundary  :
    Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t) := by
  obtain ⟨⟨v, w, z, r⟩, hvw, hwz, hzr⟩ := t
  let t : OrdTet (UOrder P a) := ⟨(v, w, z, r), hvw, hwz, hzr⟩
  have h0 : uOrderFace ⟨(w, z, r), hwz, hzr⟩ = uOrdTetFace0 (uOrderTet t) := by
    apply Subtype.ext
    exact Prod.ext hvw.2.symm (Subtype.ext rfl)
  have h1 : uOrderFace ⟨(v, z, r), hvw.trans hwz, hzr⟩ =
      uOrdTetFace1 (uOrderTet t) := rfl
  have h2 : uOrderFace ⟨(v, w, r), hvw, hwz.trans hzr⟩ =
      uOrdTetFace2 (uOrderTet t) := rfl
  have h3 : uOrderFace ⟨(v, w, z), hvw, hwz⟩ = uOrdTetFace3 (uOrderTet t) := rfl
  have hsub (x y : OrdTri (UOrder P a) →₀ ℤ) :
      Finsupp.mapDomain uOrderFace (x - y) =
        Finsupp.mapDomain uOrderFace x - Finsupp.mapDomain uOrderFace y :=
    (Finsupp.lmapDomain ℤ ℤ uOrderFace).map_sub x y
  change Finsupp.mapDomain uOrderFace (ordTetBoundary t) = uOrdTetBoundary (uOrderTet t)
  simp only [ordTetBoundary, hsub, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
    uOrdTetBoundary]
  rw [h0, h1, h2, h3]

/-- The cellular comparison commutes with the full actual universal-cover three-boundary. -/
theorem uOrderHom_ordBoundary3 (c : OrdTet (UOrder P a) →₀ ℤ) :
    chain2 uOrderHom (ordBoundary3 c) = uOrdBoundary3 (Finsupp.mapDomain uOrderTet c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single t n =>
    rw [ordBoundary3, Finsupp.linearCombination_single, map_smul]
    change n • Finsupp.mapDomain uOrderFace (ordTetBoundary t) = _
    rw [uOrderTet_boundary, Finsupp.mapDomain_single, uOrdBoundary3,
      Finsupp.linearCombination_single]

end FiniteChains.Comb
