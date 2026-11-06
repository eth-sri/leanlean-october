import RequestProject.GenusFreeFaceRetraction


/-! Actual intermediate cell sets of the chosen genus-block geometric collapse. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev GenusCollapsePair := Cube (GenusVertex q) ×
  (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))

def genusCollapseStage (left : List (GenusCollapsePair q)) (c : GenusTruncatedCell q) :=
  truncatedFaceIndex c ∉ left.map Prod.snd ∧
    match c with
    | .inl d => qCubeToCoordinate d.1 ∉ left.map Prod.fst
    | .inr _ => True

theorem genusCollapseStage_nil c : genusCollapseStage q [] c := by
  grind [genusCollapseStage]

theorem genusCollapseStage_final_iff c :
    genusCollapseStage q (genusChainCollapse q) c ↔ c ∈ genusSpineCellSet q :=
  (genusSpineCellSet_iff_survives q c).symm

theorem genusCollapseStage_active_top left
    t (hc : genusCollapseStage q left (Sum.inl t))
    (ht : t.1.spx.card = 3) :
    qCubeToCoordinate t.1 ∈ Collapse.remainingTops
      (topCubes (ASC.orderComplex (GenusVertex q))) left := by
  apply (Collapse.mem_remainingTops _ _ _).mpr
  refine ⟨mem_topCubes.mpr ⟨?_, by simpa using ht⟩, hc.2⟩
  rw [freeSet_qCubeToCoordinate]
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb

/-- Every strict boundary cell of a remaining top cube is still present at that stage. -/
theorem genusCollapseStage_boundary_mem (left right : List (GenusCollapsePair q))
    (hl : genusChainCollapse q = left ++ right)
    t
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (c : GenusTruncatedCell q) (hct : c < Sum.inl t) : genusCollapseStage q left c := by
  refine ⟨genus_later_top_boundary_avoids_prefix_faces q left right hl c t ht hct.le, ?_⟩
  cases c with
  | inr σ => trivial
  | inl d =>
    intro hm
    have hfull : qCubeToCoordinate d.1 ∈ (genusChainCollapse q).map Prod.fst := by
      simp_all
    have hd := (genus_oldCell_removed_iff_dimension_three q d).mp hfull
    have hlt := truncatedCellDimension_strictMono hct
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl t)
    omega

theorem genusCollapseStage_suffix_certificate (left right : List (GenusCollapsePair q))
    (hl : genusChainCollapse q = left ++ right) :
    Collapse.IsPairCollapse (spineInc (ASC.orderComplex (GenusVertex q))) right
      (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left) := by
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  exact hc.suffix

theorem genusCollapseStage_ordinary_step_iff left
    f t c :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) c ↔
      (genusCollapseStage q left c ∧ c ≠ Sum.inl f) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective
      (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) := by
    intro d e h
    exact Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c with
  | inl d =>
    simp [genusCollapseStage, truncatedFaceIndex, List.map_append, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      ne_eq, Sum.inl.injEq, hinj.eq_iff]
    tauto
  | inr σ => simp [genusCollapseStage, truncatedFaceIndex]
