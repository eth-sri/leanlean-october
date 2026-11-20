module

public import RequestProject.GenusCutLiftedLinkFillings
public import RequestProject.GenusFreeFaceCoverHomology



@[expose] public section

/-! Both cells of a recorded cut pair may be deleted in every covering sheet. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

variable (hf : IsPosetCover f) (left right : List (GenusCollapsePair q))
include hf

/-- Positivity and dimensions follow from the chosen collapse certificate. -/
theorem genus_recorded_cut_pair_cover_homology
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 := by
  obtain ⟨hs, hp⟩ := recorded_cut_data q left right σ t hsplit
  have hne := hs.symm ▸ σ.2.1
  have hσ : σ = fullCutCell t hne := Subtype.ext hs.symm
  subst σ
  have g := recordedGeometry (s := Sum.inr (fullCutCell t hne)) hsplit
  apply g.cover_homology hf
  intro v hv
  have h := genus_cut_lifted_link_fillings q hf left right t hne g.top_dim hp hsplit v hv
  exact ⟨h 2, h 3⟩

end FiniteChains.Davis.Genus
