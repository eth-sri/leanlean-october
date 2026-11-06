import RequestProject.OrderPosetCovering
import RequestProject.OrderNormalizationHomotopy
import RequestProject.Tac


/-! Three-simplex maps and their unique lifts through actual poset coverings. -/

bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The three-cell map of the full nerve, without truncating at the two-skeleton. -/
def ordTetMap (f : P → Q) (hf : Monotone f) (t : OrdTet P) : OrdTet Q :=
  ⟨(f t.1.1, f t.1.2.1, f t.1.2.2.1, f t.1.2.2.2),
    hf t.2.1, hf t.2.2.1, hf t.2.2.2⟩

namespace IsPosetCover
variable {f : P → Q} (hf : IsPosetCover f)

/-- Every full-nerve three-cell lifts uniquely from a specified lift of its first vertex. -/
theorem existsUnique_tetLift s a (ha : f a = s.1.1) :
    ∃! t, t.1.1 = a ∧ ordTetMap f hf.mono t = s := by
  obtain ⟨b, ⟨hab, hfb⟩, -⟩ := hf.up a s.1.2.1 (by grind)
  obtain ⟨c, ⟨hbc, hfc⟩, -⟩ := hf.up b s.1.2.2.1 (by grind)
  obtain ⟨d, ⟨hcd, hfd⟩, -⟩ := hf.up c s.1.2.2.2 (by grind)
  refine ⟨⟨(a, b, c, d), hab, hbc, hcd⟩, ⟨rfl, ?_⟩, ?_⟩
  · exact Subtype.ext (by aesop)
  · intro t ht
    have hb : t.1.2.1 = b := hf.up_inj (by grind) hab
      (by aesop)
    have hc : t.1.2.2.1 = c := hf.up_inj
      (by grind) (hab.trans hbc)
      (by aesop)
    have hd : t.1.2.2.2 = d := hf.up_inj
      (by grind)
      ((hab.trans hbc).trans hcd)
      (by aesop)
    aesop

end IsPosetCover

/-- The full-nerve three-cell map commutes with the actual cellular three-boundary. -/
theorem ordTetMap_boundary (f : P → Q) hf t :
    Finsupp.mapDomain (orderCxMap f hf).onF (ordTetBoundary t) =
      ordTetBoundary (ordTetMap f hf t) := by
  have hsub (x y : OrdTri P →₀ ℤ) :
      Finsupp.mapDomain (orderCxMap f hf).onF (x - y) =
        Finsupp.mapDomain (orderCxMap f hf).onF x -
          Finsupp.mapDomain (orderCxMap f hf).onF y :=
    (Finsupp.lmapDomain ℤ ℤ (orderCxMap f hf).onF).map_sub x y
  simp [ordTetBoundary, hsub, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single]
  rfl
