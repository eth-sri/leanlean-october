import Mathlib.Tactic

import RequestProject.GenusFreeFaceRetraction

/-! Actual intermediate cell sets of the chosen genus-block geometric collapse. -/
namespace FiniteChains.Davis.Genus

variable (q : ℕ) [NeZero q]

abbrev GenusCollapsePair := Cube (GenusVertex q) ×
  (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))

variable (left : List (GenusCollapsePair q))
variable (c : GenusTruncatedCell q)
def genusCollapseStage    :=
  truncatedFaceIndex c ∉ left.map Prod.snd ∧
    match c with
    | .inl d => qCubeToCoordinate d.1 ∉ left.map Prod.fst
    | .inr _ => True

theorem genusCollapseStage_nil  : genusCollapseStage q [] c := by
  cases c <;> simp [genusCollapseStage]

theorem genusCollapseStage_final_iff  :
    genusCollapseStage q (genusChainCollapse q) c ↔ c ∈ genusSpineCellSet q :=
  (genusSpineCellSet_iff_survives q c).symm

theorem genusCollapseStage_active_top 
    (t : QOld (cmpRel (GenusVertex q))) (hc : genusCollapseStage q left (Sum.inl t))
    (ht : t.1.spx.card = 3) :
    qCubeToCoordinate t.1 ∈ Collapse.remainingTops
      (topCubes (ASC.orderComplex (GenusVertex q))) left := by
  apply (Collapse.mem_remainingTops _ _ _).mpr
  refine ⟨mem_topCubes.mpr ⟨?_, by simpa using ht⟩, hc.2⟩
  rw [freeSet_qCubeToCoordinate]
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb

variable (left right : List (GenusCollapsePair q))
/-- Every strict boundary cell of a remaining top cube is still present at that stage. -/
theorem genusCollapseStage_boundary_mem 
    (hl : genusChainCollapse q = left ++ right)
    (t : QOld (cmpRel (GenusVertex q)))
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (c : GenusTruncatedCell q) (hct : c < Sum.inl t) : genusCollapseStage q left c := by
  refine ⟨genus_later_top_boundary_avoids_prefix_faces q left right hl c t ht hct.le, ?_⟩
  cases c with
  | inr σ => trivial
  | inl d =>
    intro hm
    have hfull : qCubeToCoordinate d.1 ∈ (genusChainCollapse q).map Prod.fst := by
      grind
    have hd := (genus_oldCell_removed_iff_dimension_three q d).mp hfull
    have hlt := truncatedCellDimension_strictMono hct
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl t)
    omega

theorem genusCollapseStage_suffix_certificate 
    (hl : genusChainCollapse q = left ++ right) :
    Collapse.IsPairCollapse (spineInc (ASC.orderComplex (GenusVertex q))) right
      (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left) := by
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  exact hc.suffix

theorem genusCollapseStage_ordinary_step_iff 
    (f t : QOld (cmpRel (GenusVertex q))) (c : GenusTruncatedCell q) :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) c ↔
      (genusCollapseStage q left c ∧ c ≠ Sum.inl f) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective
      (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) := by
    intro d e h
    exact Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c with
  | inl d =>
    simp only [genusCollapseStage, truncatedFaceIndex, List.map_append, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      ne_eq, Sum.inl.injEq, hinj.eq_iff]
    tauto
  | inr σ => simp [genusCollapseStage, truncatedFaceIndex]

/-- Dimensions and the nonpositive corner of any recorded ordinary pair. -/
theorem genus_recorded_old_pair_data
    (s t : QOld (cmpRel (GenusVertex q)))
    (hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate s.1)) ∈ genusChainCollapse q) :
    s.1.spx.card = 2 ∧ t.1.spx.card = 3 ∧ t.1.sgn ≠ 0 := by
  refine ⟨genus_removedFace_dimension q (Sum.inl s)
      (List.mem_map.mpr ⟨_, hp, rfl⟩),
    (genus_oldCell_removed_iff_dimension_three q t).mp
      (List.mem_map.mpr ⟨_, hp, rfl⟩), ?_⟩
  intro hs
  apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
    (qCubeToCoordinate s.1) hp
  simpa only [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 hs

/-- Every recorded cut pair consists of its positive top cube and full cut face. -/
theorem genus_recorded_cut_pair_data
    
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    t.1.spx.card = 3 ∧ t.1.spx = σ.1 ∧ t.1.sgn = 0 := by
  classical
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by simp [hsplit]
  have ht := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨(qCubeToCoordinate t.1, Sum.inr σ.1), hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left
    ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right) hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
      (Sum.inr σ.1) := by
    have hm : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q))
        (Sum.inr σ.1) ∩
        Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left := by
      rw [hc.2.1]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp hm).1
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    aesop (add simp [spineInc])
  refine ⟨ht, ?_, ?_⟩
  · have hh := congrArg freeSet he
    simpa using hh
  · funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1 <;> simpa [posCube, hv] using hh.symm

end FiniteChains.Davis.Genus
