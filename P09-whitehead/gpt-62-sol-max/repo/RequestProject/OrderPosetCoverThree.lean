module

public import RequestProject.OrderPosetCovering
public import RequestProject.OrderNormalizationHomotopy

@[expose] public section

/-! Three-simplex maps and their unique lifts through actual poset coverings. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The three-cell map of the full nerve, without truncating at the two-skeleton. -/
def ordTetMap (f : P → Q) (hf : Monotone f) (t : OrdTet P) : OrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2.1, f t.1.2.2.2),
    hf t.2.1, hf t.2.2.1, hf t.2.2.2⟩

theorem ordTetMap_face (f : P → Q) (hf : Monotone f) (t : OrdTet P) (i : Fin 4) :
    (orderCxMap f hf).onF (ordTetFace t i) = ordTetFace (ordTetMap f hf t) i := by
  fin_cases i <;> rfl

/-- Lift a chain from a specified initial vertex by successive upward steps. -/
def liftOrdTet {f : P → Q} (hf : Monotone f)
    (up : ∀ a b, f a ≤ b → {p // a ≤ p ∧ f p = b})
    (s : OrdTet Q) (a : P) (ha : f a = s.1.1) :
    {t : OrdTet P // t.1.1 = a ∧ ordTetMap f hf t = s} :=
  let b := up a s.1.2.1 (ha.symm ▸ s.2.1)
  let c := up b.1 s.1.2.2.1 (b.2.2.symm ▸ s.2.2.1)
  let d := up c.1 s.1.2.2.2 (c.2.2.symm ▸ s.2.2.2)
  ⟨⟨(a, b.1, c.1, d.1), b.2.1, c.2.1, d.2.1⟩, rfl,
    Subtype.ext (Prod.ext ha (Prod.ext b.2.2 (Prod.ext c.2.2 d.2.2)))⟩

theorem IsPosetCover.tet_ext {f : P → Q} (hf : IsPosetCover f) {t s : OrdTet P}
    (h : t.1.1 = s.1.1) (hm : ordTetMap f hf.mono t = ordTetMap f hf.mono s) : t = s := by
  have h₁ := hf.up_inj t.2.1 (h ▸ s.2.1) (congrArg (·.1.2.1) hm)
  have h₂ := hf.up_inj t.2.2.1 (h₁ ▸ s.2.2.1) (congrArg (·.1.2.2.1) hm)
  have h₃ := hf.up_inj t.2.2.2 (h₂ ▸ s.2.2.2) (congrArg (·.1.2.2.2) hm)
  exact Subtype.ext (Prod.ext h (Prod.ext h₁ (Prod.ext h₂ h₃)))

/-- The full-nerve three-cell map commutes with the actual cellular three-boundary. -/
theorem ordTetMap_boundary (f : P → Q) (hf : Monotone f) (t : OrdTet P) :
    Finsupp.mapDomain (orderCxMap f hf).onF (ordTetBoundary t) =
      ordTetBoundary (ordTetMap f hf t) := by
  rw [ordTetBoundary, ordTetBoundary, mapDomain_tetrahedronBoundary]
  exact congrArg tetrahedronBoundary (funext (ordTetMap_face f hf t))

end FiniteChains.Comb
