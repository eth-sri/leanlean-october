module

public import RequestProject.PosetCoverFreeFaceHomology
public import RequestProject.GenusCollapseStages
public import RequestProject.NerveMaximalFamilyDeletion
public import RequestProject.NerveGenerationComposition

@[expose] public section

/-! The recorded genus-collapse pairs supply actual covered free-face retractions. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

variable {q} {left : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
  {t : QOld (cmpRel (GenusVertex q))}

/-- Delete the inverse images of both cells. Only the two link fillings
needed for the maximal cell can differ between ordinary and cut pairs. -/
theorem PairGeometry.cover_homology (g : PairGeometry (genusCollapseStage q left) s t) (hf : IsPosetCover f)
    (hlink : ∀ v, f v = Sum.inl t →
      let B := fun p => (genusCollapseStage q left (f p) ∧ f p ≠ s) ∧ p < v
      FillsDegreeIn B 2 ∧ FillsDegreeIn B 3) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [cellPair s t]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [cellPair s t]) (f p)) 3 := by
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ s
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := by
    intro p hp
    change f p = Sum.inl t at hp
    simpa [C, hp] using And.intro g.top_mem g.distinct
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    exact (hf.up_inj le_rfl hpx (hp.trans (genus_top_cell_maximal q t g.top_dim (f x) (by rw [← hp]; exact hf.mono hpx)).symm)).symm
  have htop := maximalFamily_homology hTC hmax (fun v h => (hlink v h).1) (fun v h => (hlink v h).2)
  have hface := cover_freeFace_homology hf g.top_mem (truncatedCell_le_of_inc s t g.incident) g.distinct g.unique
  rw [genusCollapseStage_step]
  exact ⟨generatesDegreeIn_trans (fun _ h => h.1) (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ h => h.1) (hface.2 3) htop.2⟩

end FiniteChains.Davis.Genus
