module

public import RequestProject.GenusCutPairCollapse
public import RequestProject.GenusSpineTruncation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

private theorem simplex_of_face {σ : Finset (GenusVertex q)}
    (h : σ ∈ (ASC.orderComplex (GenusVertex q)).faces) :
    IsSimplex (cmpRel (GenusVertex q)) σ := by
  apply isSimplex_cmpRel_iff.mpr
  intro a ha b hb
  by_cases hab : a = b
  · exact Or.inl (hab ▸ le_rfl)
  · exact h ha hb hab

/-- Every admissible coordinate cube of positive dimension is an actual retained cell. -/
theorem exists_oldCell_of_coordinate (c : Cube (GenusVertex q))
    (hc : freeSet c ∈ (ASC.orderComplex (GenusVertex q)).faces)
    (hne : (freeSet c).Nonempty) :
    ∃ d : QOld (cmpRel (GenusVertex q)), qCubeToCoordinate d.1 = c := by
  let d := coordinateToQCube ⟨c, simplex_of_face q hc⟩
  have hd : qCubeToCoordinate d = c := coordinateToQCube_toCoordinate _
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨he, _⟩
    exact Finset.nonempty_iff_ne_empty.mp hne he
  exact ⟨⟨d, hold⟩, hd⟩

/-- Every coordinate pair in the certificate decodes to a genuine top and facet. -/
private theorem genus_pair_cells (p : GenusCollapsePair q)
    (hp : p ∈ genusChainCollapse q) :
    ∃ (t : QOld (cmpRel (GenusVertex q))) (f : GenusTruncatedCell q),
      p = (qCubeToCoordinate t.1, truncatedFaceIndex f) := by
  classical
  have hc := genusChainCollapse_isPairCollapse q
  have ht := mem_topCubes.mp (hc.top_mem hp)
  obtain ⟨t, htc⟩ := exists_oldCell_of_coordinate q p.1 ht.1
    (Finset.card_pos.mp (by have hh := ht.2; omega))
  have hi := hc.pair_inc hp
  cases hf : p.2 with
  | inl g =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hg =>
      obtain ⟨j, _, hjL, _⟩ := mem_cofaces.mp hi
      have hgL : freeSet g ∈ (ASC.orderComplex (GenusVertex q)).faces := by
        intro a ha b hb hab
        exact hjL (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
      obtain ⟨f, hfc⟩ := exists_oldCell_of_coordinate q g hgL
        (Finset.card_pos.mp (by omega))
      exact ⟨t, Sum.inl f, Prod.ext htc.symm (by simp only [truncatedFaceIndex, hfc, hf])⟩
    next => simp at hi
  | inr σ =>
    rw [hf] at hi
    simp only [spineInc] at hi
    split at hi
    next hσ =>
      let f : CutCell (cmpRel (GenusVertex q)) :=
        ⟨σ, Finset.card_pos.mp (by have hh := hσ.2; omega), simplex_of_face q hσ.1⟩
      exact ⟨t, Sum.inr f, Prod.ext htc.symm hf⟩
    next => simp at hi

/-- The lower link left by deleting a paired face is connected and simply connected. -/
theorem genus_pair_link_connectivity {left right : List (GenusCollapsePair q)}
    {s : GenusTruncatedCell q} {t : QOld (cmpRel (GenusVertex q))}
    (h : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right) :
    ConnectedIn (fun x : GenusTruncatedCell q => x ≠ s ∧ x < Sum.inl t) ∧
    SimplyConnectedIn (fun x : GenusTruncatedCell q => x ≠ s ∧ x < Sum.inl t) := by
  cases s with
  | inl f =>
    have ho := (genus_old_pair_data q left right f t h).2.2
    have hi := (genus_pair_data q h).incident
    exact ⟨ordinaryTruncatedBoundary_connectedIn ho hi, ordinaryTruncatedBoundary_simplyConnectedIn ho hi⟩
  | inr σ =>
    obtain ⟨hs, hne, ht, hp⟩ := genus_cut_pair_data q left right σ t h
    have he : fullCutCell t hne = σ := Subtype.ext hs
    rw [← he]
    exact ⟨positiveCutPuncturedBoundary_connectedIn t hne hp ht,
      positiveCutPuncturedBoundary_simplyConnectedIn t hne hp ht⟩

/-- Each recorded pair reflects null homotopies at its stage. -/
private theorem genus_recorded_pair_injIn {left right : List (GenusCollapsePair q)}
    {s : GenusTruncatedCell q} {t : QOld (cmpRel (GenusVertex q))}
    (hsplit : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right) :
    InjIn (genusCollapseStage q left)
      (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)])) := by
  have h := genus_pair_data q hsplit
  have hface := injIn_delete_free_face h.top_mem h.face_lt.le h.face_lt.ne.symm h.unique_coface
  have hJ := h.link_iff
  obtain ⟨hconn, hsc⟩ := genus_pair_link_connectivity q hsplit
  have hn : ∃ x, (genusCollapseStage q left x ∧ x ≠ s) ∧ x < Sum.inl t := by
    obtain ⟨x, hx⟩ := genus_top_boundary_nonempty q s h.dim_face t h.dim_top
    exact ⟨x, (hJ x).mp hx⟩
  have htop := injIn_delete_maximal (fun x _ hx => genus_top_cell_maximal q t h.dim_top x hx)
    hn (connectedIn_congr hJ hconn) (fun v l hv hp hl =>
      (hsc v l ((hJ v).mpr hv) hp (pathIn_mono (fun x => (hJ x).mpr) hl)).mono
        (fun x => (hJ x).mp))
  have H := injIn_trans (fun _ hz => hz.1) hface htop
  have hEq := funext fun x => propext (genusCollapseStage_step_iff q left s t x)
  rwa [hEq]

theorem genusCollapseStage_append_subset (left right : List (GenusCollapsePair q))
    (c : GenusTruncatedCell q) (hc : genusCollapseStage q (left ++ right) c) :
    genusCollapseStage q left c := by
  constructor
  · intro hm
    exact hc.1 (by simpa only [List.map_append, List.mem_append] using Or.inl hm)
  · cases c with
    | inl d =>
      intro hm
      exact hc.2 (by simpa only [List.map_append, List.mem_append] using Or.inl hm)
    | inr σ => trivial

/-- Iterate a comparison along the collapse, decoding the recorded cells at each step. -/
theorem genus_collapse_suffix
    {R : List (GenusCollapsePair q) → List (GenusCollapsePair q) → Prop}
    (hrefl : ∀ l, R l l)
    (hstep : ∀ {l r : List (GenusCollapsePair q)} {s : GenusTruncatedCell q}
        {t : QOld (cmpRel (GenusVertex q))},
      genusChainCollapse q = l ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: r →
      R l (l ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)]))
    (htrans : ∀ l p r, R l (l ++ [p]) → R (l ++ [p]) ((l ++ [p]) ++ r) →
      R l ((l ++ [p]) ++ r))
    {l r : List (GenusCollapsePair q)} (h : genusChainCollapse q = l ++ r) : R l (l ++ r) := by
  induction r generalizing l with
  | nil => simpa using hrefl l
  | cons p r ih =>
    obtain ⟨t, s, rfl⟩ := genus_pair_cells q p (by simp [h])
    have hr := ih (l := l ++ [_]) (by simpa only [List.append_assoc, List.singleton_append] using h)
    simpa only [List.append_assoc, List.singleton_append] using htrans l _ r (hstep h) hr

theorem genusCollapseStage_nil_eq : genusCollapseStage q [] = fun _ => True :=
  funext fun x => propext (iff_true_intro (genusCollapseStage_nil q x))

theorem genusCollapseStage_full_eq :
    genusCollapseStage q (genusChainCollapse q) = fun c => c ∈ genusSpineCellSet q :=
  funext fun c => propext (genusCollapseStage_final_iff q c)

/-- The actual surviving spine reflects all based null homotopies of the truncated block. -/
theorem genusSpine_injIn :
    InjIn (fun _ : GenusTruncatedCell q => True)
      (fun c => c ∈ genusSpineCellSet q) := by
  simpa only [List.nil_append, genusCollapseStage_nil_eq, genusCollapseStage_full_eq] using
    genus_collapse_suffix q (R := fun l r => InjIn (genusCollapseStage q l) (genusCollapseStage q r))
      (fun _ => injIn_self _) (genus_recorded_pair_injIn q)
      (fun l p r => injIn_trans (genusCollapseStage_append_subset q (l ++ [p]) r))
      (l := []) (r := genusChainCollapse q) rfl

theorem genusSpineToTruncated_pi1_injective :
    Function.Injective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  have hincl : Function.Injective
      (pi1Map (orderCxMap (fun c : GenusSpineCell q => c.1) monotone_subtypeVal)
        (spineBase q)) :=
    pi1Map_injective_of_injIn (genusSpine_injIn q) monotone_subtypeVal
      (·.2) monotone_id (fun _ => rfl) (spineBase q)
  intro z w he
  apply (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).injective
  apply hincl
  rwa [← genusSpineToTruncated_pi1_factor, ← genusSpineToTruncated_pi1_factor]

theorem genusSpineToOld_pi1_injective :
    Function.Injective (pi1Map (genusSpineToOld q) (spineBase q)) :=
  (genusSpine_pi1_injective_iff q).mpr (genusSpineToTruncated_pi1_injective q)

end FiniteChains.Davis.Genus
