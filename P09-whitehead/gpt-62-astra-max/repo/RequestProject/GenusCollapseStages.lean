module

public import RequestProject.GenusFreeFaceRetraction

@[expose] public section

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

variable (c : GenusTruncatedCell q)

theorem genusCollapseStage_nil : genusCollapseStage q [] c := by
  cases c <;> simp [genusCollapseStage]

theorem genusCollapseStage_final_iff :
    genusCollapseStage q (genusChainCollapse q) c ↔ c ∈ genusSpineCellSet q :=
  (genusSpineCellSet_iff_survives q c).symm

theorem genusCollapseStage_active_top (left : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q))) (hc : genusCollapseStage q left (Sum.inl t))
    (ht : t.1.spx.card = 3) :
    qCubeToCoordinate t.1 ∈ Collapse.remainingTops
      (topCubes (ASC.orderComplex (GenusVertex q))) left := by
  apply (Collapse.mem_remainingTops _ _ _).mpr
  refine ⟨mem_topCubes.mpr ⟨?_, by simp_all⟩, hc.2⟩
  rw [freeSet_qCubeToCoordinate]
  intro a ha b hb _
  exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb

section

variable (left right : List (GenusCollapsePair q)) (hl : genusChainCollapse q = left ++ right)
include hl

/-- Every strict boundary cell of a remaining top cube is still present at that stage. -/
theorem genusCollapseStage_boundary_mem
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
      grind
    have hd := (genus_oldCell_removed_iff_dimension_three q d).mp hfull
    have hlt := truncatedCellDimension_strictMono hct
    have hmax := genusTruncatedCell_dimension_le_three q (Sum.inl t)
    omega

theorem genusCollapseStage_suffix_certificate :
    Collapse.IsPairCollapse (spineInc (ASC.orderComplex (GenusVertex q))) right
      (Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left) := by
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  exact hc.suffix

end

variable {q} {left right : List (GenusCollapsePair q)}
  {s : GenusTruncatedCell q} {t : QOld (cmpRel (GenusVertex q))}

abbrev cellPair (s : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q))) : GenusCollapsePair q :=
  (qCubeToCoordinate t.1, truncatedFaceIndex s)

theorem genusCollapseStage_step :
    genusCollapseStage q (left ++ [cellPair s t]) =
      fun x => (genusCollapseStage q left x ∧ x ≠ s) ∧ x ≠ Sum.inl t := by
  have hinj : Function.Injective (fun d : QOld (cmpRel (GenusVertex q)) => qCubeToCoordinate d.1) :=
    fun _ _ h => Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext h))
  funext x
  cases x <;> simp [cellPair, genusCollapseStage, truncatedFaceIndex_injective.eq_iff, hinj.eq_iff] <;> tauto

/-- Geometry of a *recorded* collapse: its free face, unique coface and intact
lower boundary in the current stage. The same certificate serves the loop and
cover homology comparisons. -/
structure PairGeometry (C : GenusTruncatedCell q → Prop) (s : GenusTruncatedCell q)
    (t : QOld (cmpRel (GenusVertex q))) : Prop where
  face_dim : truncatedCellDimension s = 2
  top_dim : t.1.spx.card = 3
  incident : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex s)
  top_mem : C (Sum.inl t)
  distinct : Sum.inl t ≠ s
  unique : ∀ x, C x → s ≤ x → x ≠ s → x = Sum.inl t
  boundary : ∀ x, x < Sum.inl t → C x

theorem recordedGeometry (split : genusChainCollapse q = left ++ cellPair s t :: right) :
    PairGeometry (genusCollapseStage q left) s t := by
  let p := cellPair s t
  have hp : p ∈ genusChainCollapse q := by simp [split, p]
  have hs := genus_removedFace_dimension q s (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p, cellPair]
  have hc := genusCollapseStage_suffix_certificate q left _ split
  refine ⟨hs, ht, (genusChainCollapse_isPairCollapse q).pair_inc hp,
    ⟨genus_later_top_boundary_avoids_prefix_faces q left _ split _ t htail le_rfl,
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩, ?_, ?_,
    genusCollapseStage_boundary_mem q left _ split t htail⟩
  · intro h
    have he := congrArg truncatedCellDimension h
    change t.1.spx.card = truncatedCellDimension s at he
    omega
  · intro x hx hsx hxs
    have hd := truncatedCellDimension_strictMono (lt_of_le_of_ne hsx hxs.symm)
    have hm := genusTruncatedCell_dimension_le_three q x
    have he : truncatedCellDimension x = 3 := by omega
    cases x with
    | inr σ => have := genus_cutCell_dimension_le_two q σ; omega
    | inl d =>
      have hi := truncatedCell_inc_of_le s d hsx hs he (genus_simplex_mem_faces q d.1.isSimplex)
      have hm := Finset.mem_inter.mpr ⟨hi, genusCollapseStage_active_top q left d hx he⟩
      rw [hc.2.1] at hm
      exact congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext (Finset.mem_singleton.mp hm))))

theorem PairGeometry.comparison (g : PairGeometry (genusCollapseStage q left) s t)
    (hc : ConnectedIn (fun x => x ≠ s ∧ x < Sum.inl t))
    (hs : SimplyConnectedIn (fun x => x ≠ s ∧ x < Sum.inl t)) :
    LoopComparison (genusCollapseStage q left) (genusCollapseStage q (left ++ [cellPair s t])) := by
  have he : (fun x => x ≠ s ∧ x < Sum.inl t) =
      (fun x => (genusCollapseStage q left x ∧ x ≠ s) ∧ x < Sum.inl t) :=
    funext fun x => propext ⟨fun h => ⟨⟨g.boundary x h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  rw [he] at hc hs
  rw [genusCollapseStage_step]
  have hface := loopComparison_delete_free_face g.top_mem (truncatedCell_le_of_inc s t g.incident) g.distinct g.unique
  apply hface.trans (loopComparison_delete_maximal (fun x _ => genus_top_cell_maximal q t g.top_dim x) _ hc hs) (fun _ h => h.1)
  obtain ⟨x, hxs, hxt⟩ := genus_top_boundary_nonempty q s g.face_dim t g.top_dim
  exact ⟨x, ⟨g.boundary x hxt, hxs⟩, hxt⟩

end FiniteChains.Davis.Genus
