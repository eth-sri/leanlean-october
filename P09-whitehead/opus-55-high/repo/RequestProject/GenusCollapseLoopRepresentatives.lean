import RequestProject.GenusCollapseIteration
import RequestProject.OrderComplexMaximalPath
import RequestProject.Tac


bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_free_face_loop_representative
    C S
    (f : GenusTruncatedCell q) t
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (htC : C (Sum.inl t))
    (hactive : ∀ d, C (Sum.inl d) →
      d.1.spx.card = 3 → qCubeToCoordinate d.1 ∈ S)
    (hfree : Collapse.IsFree (spineInc (ASC.orderComplex (GenusVertex q))) S
      (truncatedFaceIndex f) (qCubeToCoordinate t.1))
    a p
    (ha : C a ∧ a ≠ f)
    (hp : IsPathX (orderCx (GenusTruncatedCell q)) p a a)
    (hC : PathIn C p) :
    ∃ l, IsPathX (orderCx (GenusTruncatedCell q)) l a a ∧
      PathIn (fun x => C x ∧ x ≠ f) l ∧ Htpy (orderCx (GenusTruncatedCell q)) a a p l := by
  have hinc : qCubeToCoordinate t.1 ∈
      spineInc (ASC.orderComplex _) (truncatedFaceIndex f) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex _) (truncatedFaceIndex f) ∩ S := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    simp_all
  have hft := truncatedCell_le_of_inc f t hinc
  have hne : (Sum.inl t) ≠ f := by
    intro he
    have hh := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension f at hh
    omega
  apply loop_representative_delete_free_face htC hft hne ?_ ha hp hC
  intro x hx hfx hxf
  have hdim : truncatedCellDimension x = 3 := by
    have hlt := truncatedCellDimension_strictMono (lt_of_le_of_ne hfx hxf.symm)
    have hmax := genusTruncatedCell_dimension_le_three q x
    omega
  cases x with
  | inr σ =>
    have hh := genus_cutCell_dimension_le_two q σ
    omega
  | inl d =>
    have hd := hdim
    have hL : d.1.spx ∈ (ASC.orderComplex _).faces := by
      intro a ha b hb _
      exact (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb
    have hi := truncatedCell_inc_of_le f d hfx hf hd hL
    have hm := Finset.mem_inter.mpr ⟨hi, hactive d hx hd⟩
    rw [hfree] at hm
    have he :=
      Finset.mem_singleton.mp hm
    have hc := qCubeCoordinateEquiv.injective (Subtype.ext he)
    exact congrArg Sum.inl (Subtype.ext hc)

theorem genus_ordinary_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hf : f.1.spx.card = 2) (ht : t.1.spx.card = 3) (hordinary : t.1.sgn ≠ 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right))
    a loop
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by tauto
  have hc := genusCollapseStage_suffix_certificate q left _ hsplit
  have hfree := hc.2.1
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex _)
      (Sum.inl (qCubeToCoordinate f.1)) := by
    have hm : qCubeToCoordinate t.1 ∈
        spineInc (ASC.orderComplex _) (Sum.inl (qCubeToCoordinate f.1)) ∩
          Collapse.remainingTops (topCubes (ASC.orderComplex _)) left := by
      rw [hfree]
      exact Finset.mem_singleton_self _
    simp_all
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left _ hsplit
        _ t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have ha' := (genusCollapseStage_ordinary_step_iff q left f t a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q _
    _
    (Sum.inl f) t hf ht htC
    (genusCollapseStage_active_top q left) hfree a loop ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inl f ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inl f) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left _ hsplit t htail x hlt, hne⟩, hlt⟩
    simp_all
  have hconn := connectedIn_congr hJ (ordinaryTruncatedBoundary_connectedIn hordinary hi)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inl f)
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_ordinary_step_iff q left f t x).mpr hx) hrB,
    hhl.trans hhr⟩

theorem genus_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (t : QOld (cmpRel (GenusVertex q)))
    (hne : t.1.spx.Nonempty) (ht : t.1.spx.card = 3) (hpositive : t.1.sgn = 0)
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr t.1.spx) :: right))
    a loop
    (ha : genusCollapseStage q
      (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inr t.1.spx)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, Sum.inr t.1.spx)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by tauto
  have hc := genusCollapseStage_suffix_certificate q left _ hsplit
  have hfree := hc.2.1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left _ hsplit
        _ t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hf : truncatedCellDimension (Sum.inr (fullCutCell t hne)) = 2 := by
    change t.1.spx.card - 1 = 2
    omega
  have ha' := (genusCollapseStage_cut_step_iff q left t hne a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := genus_free_face_loop_representative q _
    _
    _ t hf ht htC
    (genusCollapseStage_active_top q left) hfree a loop ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t ↔
        (genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne)) ∧ x < Sum.inl t := by
    constructor
    · rintro ⟨hne, hlt⟩
      exact ⟨⟨genusCollapseStage_boundary_mem q left _ hsplit t htail x hlt, hne⟩, hlt⟩
    simp_all
  have hconn := connectedIn_congr hJ (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht)
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ Sum.inr (fullCutCell t hne))
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    hconn l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono
    (fun x hx => (genusCollapseStage_cut_step_iff q left t hne x).mpr hx) hrB,
    hhl.trans hhr⟩

theorem genus_old_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right))
    a loop
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  have hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) ∈ genusChainCollapse q := by
    simp_all
  have hf := genus_removedFace_dimension q (Sum.inl f)
    (by aesop)
  have ht := (genus_oldCell_removed_iff_dimension_three q t).mp
    (by simp_all)
  have hordinary : t.1.sgn ≠ 0 := by
    intro hs
    apply genusChainCollapse_old_face_nonpositive q _
      _ hp
    simpa [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 hs
  exact genus_ordinary_pair_loop_representative q left right f t hf ht hordinary hsplit a loop ha hpath hC

theorem genus_recorded_cut_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right))
    a loop
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  classical
  have hp : (qCubeToCoordinate t.1, Sum.inr σ.1) ∈ genusChainCollapse q := by
    simp_all
  have ht : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
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
  have hstep := genus_cut_pair_loop_representative q left right t hne ht hpositive
    (by simp_all) a loop
    (by simp_all) hpath hC
  simp_all

theorem genus_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    p
    (hsplit : genusChainCollapse q = left ++ (p :: right))
    a loop
    (ha : genusCollapseStage q (left ++ [p]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ [p])) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  have hp : p ∈ genusChainCollapse q := by
    simp_all
  obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
  have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) := Prod.ext ht.symm hf.symm
  rw [he] at hsplit ha ⊢
  cases f with
  | inl f => exact genus_old_pair_loop_representative q left right f t hsplit a loop ha hpath hC
  | inr σ => exact genus_recorded_cut_pair_loop_representative q left right σ t hsplit a loop ha hpath hC

/-- Construct a loop in the terminal stage of any actual suffix of the chosen collapse. -/
theorem genus_collapse_suffix_loop_representative
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right)
    a loop
    (ha : genusCollapseStage q (left ++ right) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (genusCollapseStage q (left ++ right)) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  induction right generalizing left loop with
  | nil => exact ⟨loop, hpath, by simpa using hC, Htpy.refl _⟩
  | cons p right ih =>
    have haTail : genusCollapseStage q ((left ++ [p]) ++ right) a := by
      simp_all
    have haFirst := genusCollapseStage_append_subset q _ right a haTail
    obtain ⟨l, hl, hlC, hhl⟩ := genus_pair_loop_representative q left right p hsplit
      a loop haFirst hpath hC
    obtain ⟨r, hr, hrC, hhr⟩ := ih _
      (by simp_all)
      l haTail hl hlC
    exact ⟨r, hr, by simp_all,
      hhl.trans hhr⟩

/-- Every loop of the truncated block based in its surviving spine is represented in that spine. -/
theorem genusSpine_loop_representative a
    loop
    (ha : a ∈ genusSpineCellSet q)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a) :
    ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt l a a ∧
      PathIn (· ∈ genusSpineCellSet q) l ∧
      Htpy (orderCx (GenusTruncatedCell q)) a a loop l := by
  obtain ⟨l, hl, hC, hh⟩ := genus_collapse_suffix_loop_representative q
    (genusChainCollapse q) [] (by simp) a loop
    ((genusCollapseStage_final_iff q a).mpr ha) hpath
    (fun e _ => ⟨genusCollapseStage_nil q e.1.1.1, genusCollapseStage_nil q e.1.1.2⟩)
  exact ⟨l, hl, pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc) hC, hh⟩

theorem genusSpineToTruncated_pi1_factor_weak
    z :
    pi1Map (genusSpineToTruncated q) (spineBase q) z =
      pi1Map (orderCxMap (·.1) monotone_subtypeVal)
        (spineBase q) (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    apply congrArg Pi1.mk
    apply Subtype.ext
    simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]

theorem genusSpineToTruncated_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  rintro ⟨p⟩
  obtain ⟨r, hr, hrB, hh⟩ := genusSpine_loop_representative q
    _ p.1 (spineBase q).2 p.2
  let lifted : Loop (orderCx (GenusSpineCell q)) (spineBase q) :=
    ⟨liftPathIn r hrB, isPath_liftPathIn r hrB _ _ hr⟩
  refine ⟨(strictOrderPi1Equiv (P := GenusSpineCell q) _).symm (Pi1.mk lifted), ?_⟩
  rw [genusSpineToTruncated_pi1_factor_weak, MulEquiv.apply_symm_apply]
  apply Quotient.sound
  change Htpy _ (spineBase q).1 (spineBase q).1
    (mapPath (subposetHom _) (liftPathIn r hrB)) p.1
  rw [mapPath_liftPathIn]
  exact hh.symm

theorem genusSpineToOld_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToOld q) (spineBase q)) := by
  intro z
  obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
    ((genusSpineToTruncated q).onV (spineBase q)) z
  cases' genusSpineToTruncated_pi1_surjective q v with w hw
  exact ⟨w, by simp_all [genusSpine_pi1_factor, hw]⟩

noncomputable def genusSpineToOldPi1Equiv :=
  MulEquiv.ofBijective _
    ⟨genusSpineToOld_pi1_injective q, genusSpineToOld_pi1_surjective q⟩
