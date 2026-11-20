module

public import RequestProject.GenusFreeFaceRetraction

@[expose] public section

/-! Actual intermediate cell sets of the chosen genus-block geometric collapse. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev GenusCollapsePair := Cube (GenusVertex q) ×
  (Cube (GenusVertex q) ⊕ Finset (GenusVertex q))

def genusCollapseStage (left : List (GenusCollapsePair q)) (c : GenusTruncatedCell q) : Prop :=
  truncatedFaceIndex c ∉ left.map Prod.snd ∧
    match c with
    | .inl d => qCubeToCoordinate d.1 ∉ left.map Prod.fst
    | .inr _ => True

theorem genusCollapseStage_nil (c : GenusTruncatedCell q) : genusCollapseStage q [] c := by
  cases c <;> simp [genusCollapseStage]

theorem genusCollapseStage_final_iff (c : GenusTruncatedCell q) :
    genusCollapseStage q (genusChainCollapse q) c ↔ c ∈ genusSpineCellSet q :=
  (genusSpineCellSet_iff_survives q c).symm

theorem genusCollapseStage_active_top (left : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hc : genusCollapseStage q left (Sum.inl t))
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
    (t : QOld (cmpRel (GenusVertex q)))
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (c : GenusTruncatedCell q) (hct : c < Sum.inl t) : genusCollapseStage q left c := by
  refine ⟨genus_later_top_boundary_avoids_prefix_faces q left right hl c t ht hct.le, ?_⟩
  cases c with
  | inr σ => trivial
  | inl d =>
    intro hm
    have hfull : qCubeToCoordinate d.1 ∈ (genusChainCollapse q).map Prod.fst := by
      rw [hl, List.map_append]
      exact List.mem_append.mpr (Or.inl hm)
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

theorem genusCollapseStage_step_iff (left : List (GenusCollapsePair q))
    (s : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q))) (c : GenusTruncatedCell q) :
    genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)]) c ↔
      (genusCollapseStage q left c ∧ c ≠ s) ∧ c ≠ Sum.inl t := by
  have hinj : Function.Injective (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) :=
    fun _ _ h => Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  cases c <;>
    simp only [genusCollapseStage, List.map_append, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or,
      truncatedFaceIndex_injective.eq_iff, hinj.eq_iff, ne_eq, Sum.inl.injEq, Sum.inr_ne_inl] <;> tauto


/-- The location of an actual free face and its top cube in the collapse. -/
structure GenusPairData (left : List (GenusCollapsePair q)) (s : GenusTruncatedCell q)
    (t : QOld (cmpRel (GenusVertex q))) : Prop where
  dim_face : truncatedCellDimension s = 2
  dim_top : t.1.spx.card = 3
  incident : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex s)
  face_lt : s < Sum.inl t
  top_mem : genusCollapseStage q left (Sum.inl t)
  boundary_mem : ∀ x : GenusTruncatedCell q, x < Sum.inl t → genusCollapseStage q left x
  unique_coface : ∀ x : GenusTruncatedCell q, genusCollapseStage q left x → s ≤ x → x ≠ s → x = Sum.inl t

theorem genus_pair_data {left right : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
    {t : QOld (cmpRel (GenusVertex q))}
    (h : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right) :
    GenusPairData q left s t := by
  let p  := (qCubeToCoordinate t.1, truncatedFaceIndex s)
  have hp  := h ▸ List.mem_append_right _ List.mem_cons_self
  have hd := genus_removedFace_dimension q s (List.mem_map_of_mem (f := Prod.snd) hp)
  have ht := (genus_oldCell_removed_iff_dimension_three q t).mp (List.mem_map_of_mem (f := Prod.fst) hp)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) h
  have hi := (Finset.mem_inter.mp (hc.2.1.symm ▸ Finset.mem_singleton_self (qCubeToCoordinate t.1))).1
  refine ⟨hd, ht, hi, lt_of_le_of_ne (truncatedCell_le_of_inc s t hi) ?_,
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) h _ t htail le_rfl,
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩,
    (genusCollapseStage_boundary_mem q left (p :: right) h t htail), ?_⟩
  · intro he
    rw [he, ht] at hd
    omega
  · intro x hx hsx hxs
    have hdim : truncatedCellDimension x = 3 := by
      have := truncatedCellDimension_strictMono (lt_of_le_of_ne hsx hxs.symm)
      have := genusTruncatedCell_dimension_le_three q x
      omega
    cases x with
    | inr d => have := genus_cutCell_dimension_le_two q d; omega
    | inl d =>
      have hi' := truncatedCell_inc_of_le s d hsx hd hdim (genus_simplex_mem_faces q d.1.isSimplex)
      have he := Finset.mem_singleton.mp (hc.2.1 ▸
        Finset.mem_inter.mpr ⟨hi', genusCollapseStage_active_top q left d hx hdim⟩)
      exact congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext he)))

theorem GenusPairData.link_iff {left : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
    {t : QOld (cmpRel (GenusVertex q))} (h : GenusPairData q left s t) (x : GenusTruncatedCell q) :
    (x ≠ s ∧ x < Sum.inl t) ↔ (genusCollapseStage q left x ∧ x ≠ s) ∧ x < Sum.inl t :=
  ⟨fun hx => ⟨⟨h.boundary_mem x hx.2, hx.1⟩, hx.2⟩, fun hx => ⟨hx.1.2, hx.2⟩⟩

end FiniteChains.Davis.Genus
