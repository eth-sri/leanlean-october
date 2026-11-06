module

public import RequestProject.Oriented
public import RequestProject.GenusApply
public import RequestProject.ChamberQuotientFinite

@[expose] public section

backwardOptions



/-!
Finite marking of the genus block. The canonical loops are indexed by `Fin q × Bool`,
so there is one marking for each of the paper's `2q` distinguished generators.
This proves the filling and group injectivity for these actual loops; it does not assert
(B2), (B3), or a comparison with topological second homotopy groups.
-/


namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (a b : ℕ → α)
  (q : ℕ) [NeZero q]

abbrev finiteSig (x : Fin q × Bool) := gSig q (x.1.val, x.2)

def finitePairs (q : ℕ) : List ((Fin q × Bool) × (Fin q × Bool)) :=
  (List.finRange q).map fun h => ((h, false), (h, true))

omit [NeZero q] in
/-- Reindexing the surface word by the finite set of its handles. -/
theorem commWord_finitePairs {G : Type} [Group G] (f : ℕ × Bool → G) :
    commWord (fun x : Fin q × Bool => f (x.1.val, x.2)) (finitePairs q) =
      commWord f (genPairs q) := by
  simp only [finitePairs, genPairs, commWord, List.map_map]
  have h := List.map_coe_finRange_eq_range (n := q)
  rw [← h, List.map_map]
  rfl

local instance genusPi1Group : Group
    (Pi1 (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)) :=
  @Pi1.instGroup (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)

/-- The finite list of marked loops bounds the canonical surface polygon. -/
theorem finite_hfilling :
    commWord (fun x : Fin q × Bool =>
      Pi1.mk (⟨finiteSig q x, isPath_gSig q (x.1.val, x.2)⟩ :
        Loop (orderCx (NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))))) (gBase q)))
      (finitePairs q) = 1 := (commWord_finitePairs q _).trans (genus_hfilling q)

abbrev finiteLw (_ : PUnit.{1}) (x : Fin q × Bool) : FiniteChains.Comb.Oriented α :=
  genusLw a b q (PUnit.unit.{1} : PUnit.{1}) (x.1.val, x.2)

/-- The internal generators are finite, since the quotient has finitely many edges. -/
instance finite_spineGens
    (T : SpanningTree (orderCx (QOld (cmpRel (SCell (gvc q) (gec q) (gc q)))))) :
    Finite (spineGens T) := inferInstanceAs (Finite {e : _ // ¬ T.isTree e})

/-- The block has finitely many cell and marking relators. -/
instance finite_spineRels :
    Finite (spineRels (A := cmpRel (SCell (gvc q) (gec q) (gc q))) (Fin q × Bool)) :=
  inferInstanceAs (Finite (_ ⊕ (Fin q × Bool)))

end FiniteChains.Davis.Genus
