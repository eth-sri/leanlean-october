import RequestProject.GenusCutLiftedLinkFillings
import RequestProject.GenusFreeFaceCoverHomology
import RequestProject.NerveMaximalFamilyDeletion
import RequestProject.NerveGenerationComposition


/-! Both cells of a recorded cut pair may be deleted in every covering sheet. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Nerve
variable (q : ℕ) [NeZero q]
  {P : Type} [PartialOrder P] {f : P → GenusTruncatedCell q}

theorem genus_cut_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hne : t.1.spx.Nonempty)
    (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) 3 := by
  let pair : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (pair :: right).map Prod.fst := by tauto
  have hcert := genusCollapseStage_suffix_certificate q left _ hsplit
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left _ hsplit
      _ t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hcert.1).2⟩
  let C := fun p => genusCollapseStage q left (f p) ∧ f p ≠ Sum.inr (fullCutCell t hne)
  let T := fun p => f p = Sum.inl t
  have hTC : ∀ p, T p → C p := by
    grind
  have hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p := by
    intro p hp x _ hpx
    have hx := genus_top_cell_maximal q t ht (f x)
      (by rw [← hp]; exact hf.mono hpx)
    exact (hf.up_inj (le_refl p) hpx (hp.trans hx.symm)).symm
  have hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 2 := by
    intro v hv
    exact genus_cut_lifted_link_fillings q hf left right t hne ht hpositive hsplit v hv 2
  have hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) 3 := by
    intro v hv
    exact genus_cut_lifted_link_fillings q hf left right t hne ht hpositive hsplit v hv 3
  have htop := maximalFamily_homology hTC hmax hlink₁ hlink₂
  have hface := genus_recorded_free_face_cover_homology q hf left right
    (Sum.inr (fullCutCell t hne)) t hsplit
  have he : (fun p => genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) (f p)) =
      (fun p => C p ∧ ¬ T p) := by
    funext p
    exact propext (genusCollapseStage_cut_step_iff q left t hne _)
  rw [he]
  exact ⟨generatesDegreeIn_trans (by simp_all)
      (generatesDegreeIn_of_acyclicRelIn hface.1) htop.1,
    reflectsBoundsIn_trans (fun _ h => h.1) (hface.2 3) htop.2⟩

/-- Positivity and dimensions follow from the chosen collapse certificate. -/
theorem genus_recorded_cut_pair_cover_homology (hf : IsPosetCover f)
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    GeneratesDegreeIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 ∧
    ReflectsBoundsIn (fun p => genusCollapseStage q left (f p))
      (fun p => genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) (f p)) 3 := by
  classical
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    simp_all
  have ht := (genus_oldCell_removed_iff_dimension_three q t).mp
    (by simp_all)
  have hc := genusCollapseStage_suffix_certificate q left
    _ hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex _)
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex _)
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex _)) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    simp_all
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    grind [spineInc]
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1
    · simpa [posCube, hv] using hh.symm
    · simpa [posCube, hv] using hh.symm
  have hne := hs.symm ▸ σ.2.1
  have hstep := genus_cut_pair_cover_homology q hf left right t hne ht hpositive
    (by simp_all)
  simp_all
