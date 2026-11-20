module

public import RequestProject.GenusOrdinaryLiftedTopHomology
public import RequestProject.GenusFreeFaceCoverHomology



@[expose] public section

/-! Full ordinary recorded collapse pairs preserve H2 in arbitrary covering spaces. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

/-- Delete every lift of both cells of an actual recorded ordinary pair.
This is a genuine comparison between consecutive chosen collapse stages;
neither finite sheet number nor relative homology vanishing is an input. -/
theorem genus_ordinary_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (s t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) 3 := by
  have g := recordedGeometry (s := Sum.inl s) (t := t) hsplit
  apply g.cover_homology hf
  exact genus_ordinary_lifted_link_fillings q hf left right s t g.face_dim g.top_dim
    (recorded_old_sign q left right s t hsplit) hsplit

end FiniteChains.Davis.Genus
