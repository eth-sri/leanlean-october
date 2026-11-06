import Mathlib.Tactic

import RequestProject.GenusOrdinaryLiftedTopHomology
import RequestProject.GenusFreeFaceCoverHomology
import RequestProject.NerveMaximalFamilyDeletion
import RequestProject.NerveGenerationComposition

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
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))
  have hp : pair ∈ genusChainCollapse q := by
    aesop
  obtain ⟨hs, ht, hordinary⟩ := genus_recorded_old_pair_data q s t hp
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by simp [pair]
  have hcert := genusCollapseStage_suffix_certificate q left (pair :: right) hsplit
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (pair :: right) hsplit
      (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inl s
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := by
    aesop
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    have hx  := genus_top_cell_maximal q t ht (f x)
      (by rw [← hp]; exact hf.mono hpx)
    exact (hf.up_inj (le_refl p) hpx (hp.trans hx.symm)).symm
  have hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 2 := by
    intro v hv
    exact (genus_ordinary_lifted_link_fillings q hf left right s t hs ht hordinary hsplit v hv).1
  have hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 3 := by
    intro v hv
    exact (genus_ordinary_lifted_link_fillings q hf left right s t hs ht hordinary hsplit v hv).2
  have htop := maximalFamily_homology hTC hmax hlink₁ hlink₂
  have hface := genus_recorded_free_face_cover_homology q hf left right (Sum.inl s) t hsplit
  have he : (fun p => genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1))]) (f p)) =
      (fun p => C p ∧ ¬ T p) := by
    funext p
    exact propext (genusCollapseStage_ordinary_step_iff q left s t (f p))
  rw [he]
  exact ⟨generatesDegreeIn_trans (fun _ h => h.1)
      (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ h => h.1) (hface.2 3) htop.2⟩

end FiniteChains.Davis.Genus
