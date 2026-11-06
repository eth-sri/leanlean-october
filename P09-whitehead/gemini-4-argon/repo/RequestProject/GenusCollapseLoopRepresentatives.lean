module

public import RequestProject.GenusCollapseIteration
public import RequestProject.OrderComplexMaximalPath

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

abbrev LoopRep (C : GenusTruncatedCell q → Prop) (a : GenusTruncatedCell q)
    (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool)) : Prop :=
  ∃ l, IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt l a a ∧
    PathIn C l ∧ Htpy (orderCx (GenusTruncatedCell q)) a a loop l

theorem genus_step_loop_representative
    (left right : List (GenusCollapsePair q))
    (f : GenusTruncatedCell q) (t : QOld (cmpRel (GenusVertex q)))
    (hf : truncatedCellDimension f = 2) (ht : t.1.spx.card = 3)
    (hsplit : genusChainCollapse q = left ++ ((qCubeToCoordinate t.1, truncatedFaceIndex f) :: right))
    (hstep_iff : ∀ x, genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex f)]) x ↔
      (genusCollapseStage q left x ∧ x ≠ f) ∧ x ≠ Sum.inl t)
    (hconn : ConnectedIn (fun x => x ≠ f ∧ x < Sum.inl t))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex f)]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    LoopRep q (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex f)])) a loop := by
  let p : GenusCollapsePair q := (qCubeToCoordinate t.1, truncatedFaceIndex f)
  have htail : qCubeToCoordinate t.1 ∈ (p :: right).map Prod.fst := by simp [p]
  have hc := genusCollapseStage_suffix_certificate q left (p :: right) hsplit
  have hfree := hc.2.1
  have hinc : qCubeToCoordinate t.1 ∈
      spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) :=
    (Finset.mem_inter.mp (hfree ▸ Finset.mem_singleton_self _)).1
  have htC : genusCollapseStage q left (Sum.inl t) :=
    ⟨genus_later_top_boundary_avoids_prefix_faces q left (p :: right) hsplit
        (Sum.inl t) t htail (le_refl _),
      ((Collapse.mem_remainingTops _ _ _).mp hc.1).2⟩
  have hne : (Sum.inl t : GenusTruncatedCell q) ≠ f := fun he => by
    have hh := congrArg truncatedCellDimension he
    change t.1.spx.card = truncatedCellDimension f at hh; omega
  have ha' := (hstep_iff a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := loop_representative_delete_free_face htC
    (truncatedCell_le_of_inc f t hinc) hne
    (fun x hx hfx hxf => by
      have hdim : truncatedCellDimension x = 3 := by
        have := truncatedCellDimension_strictMono (lt_of_le_of_ne hfx hxf.symm)
        have := genusTruncatedCell_dimension_le_three q x; omega
      cases x with
      | inr σ => have := genus_cutCell_dimension_le_two q σ; omega
      | inl d =>
        have hd : d.1.spx.card = 3 := hdim
        have hi := truncatedCell_inc_of_le (L := ASC.orderComplex (GenusVertex q)) f d hfx hf hd
          fun a ha b hb _ => (isSimplex_cmpRel_iff.mp d.1.isSimplex) a ha b hb
        have hm : qCubeToCoordinate d.1 ∈
            spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) ∩
              Collapse.remainingTops (topCubes (ASC.orderComplex (GenusVertex q))) left :=
          Finset.mem_inter.mpr ⟨hi, genusCollapseStage_active_top q left d hx hd⟩
        rw [hfree] at hm
        exact congrArg Sum.inl (Subtype.ext
          (qCubeCoordinateEquiv.injective (Subtype.ext (Finset.mem_singleton.mp hm)))))
    ha'.1 hpath hC
  have hJ (x : GenusTruncatedCell q) :
      x ≠ f ∧ x < Sum.inl t ↔ (genusCollapseStage q left x ∧ x ≠ f) ∧ x < Sum.inl t :=
    ⟨fun ⟨hne, hlt⟩ =>
      ⟨⟨genusCollapseStage_boundary_mem q left (p :: right) hsplit t htail x hlt, hne⟩, hlt⟩,
     fun h => ⟨h.1.2, h.2⟩⟩
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (C := fun x => genusCollapseStage q left x ∧ x ≠ f)
    (t := Sum.inl t) (fun x _ htx => genus_top_cell_maximal q t ht x htx)
    (connectedIn_congr hJ hconn) l ha' ha' hl hlf
  exact ⟨r, hr, pathIn_mono (fun x hx => (hstep_iff x).mpr hx) hrB, hhl.trans hhr⟩

theorem genus_pair_loop_representative
    (left right : List (GenusCollapsePair q))
    (p : GenusCollapsePair q)
    (hsplit : genusChainCollapse q = left ++ (p :: right))
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ [p]) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    LoopRep q (genusCollapseStage q (left ++ [p])) a loop := by
  classical
  have hp : p ∈ genusChainCollapse q :=
    hsplit ▸ List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨t, f, ht, hf⟩ := genus_pair_cells q p hp
  have he : p = (qCubeToCoordinate t.1, truncatedFaceIndex f) := Prod.ext ht.symm hf.symm
  rw [he] at hsplit ha hp ⊢
  have ht3 : t.1.spx.card = 3 := (genus_oldCell_removed_iff_dimension_three q t).mp
    (List.mem_map.mpr ⟨_, hp, rfl⟩)
  have hc := genusCollapseStage_suffix_certificate q left _ hsplit
  have hi : qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q)) (truncatedFaceIndex f) :=
    (Finset.mem_inter.mp (hc.2.1 ▸ Finset.mem_singleton_self _)).1
  cases f with
  | inl f =>
    have hf2 : f.1.spx.card = 2 := genus_removedFace_dimension q (Sum.inl f)
      (List.mem_map.mpr ⟨_, hp, rfl⟩)
    have hordinary : t.1.sgn ≠ 0 := fun hs =>
      genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1) (qCubeToCoordinate f.1) hp
        (by simpa only [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 hs)
    exact genus_step_loop_representative q left right (Sum.inl f) t hf2 ht3 hsplit
      (genusCollapseStage_ordinary_step_iff q left f t)
      (ordinaryTruncatedBoundary_connectedIn hordinary hi) a loop ha hpath hC
  | inr σ =>
    have heq : qCubeToCoordinate t.1 = posCube σ.1 := by
      simp only [truncatedFaceIndex, spineInc] at hi
      split at hi
      · exact Finset.mem_singleton.mp hi
      · simp at hi
    have hs : t.1.spx = σ.1 := by simpa using congrArg freeSet heq
    have hpositive : t.1.sgn = 0 := funext fun v => by
      have hh := qCubeToCoordinate_parity t.1 v; rw [heq] at hh
      by_cases hv : v ∈ σ.1 <;> simpa [posCube, hv] using hh.symm
    have hne : t.1.spx.Nonempty := hs.symm ▸ σ.2.1
    have hstep := genus_step_loop_representative q left right (Sum.inr (fullCutCell t hne)) t
      (by change t.1.spx.card - 1 = 2; omega) ht3
      (by simpa only [truncatedFaceIndex, fullCutCell, hs] using hsplit)
      (genusCollapseStage_cut_step_iff q left t hne)
      (positiveCutPuncturedBoundary_connectedIn t hne hpositive ht3)
      a loop (by simpa only [truncatedFaceIndex, fullCutCell, hs] using ha) hpath hC
    simpa only [truncatedFaceIndex, fullCutCell, hs] using hstep

theorem genus_collapse_suffix_loop_representative
    (right left : List (GenusCollapsePair q))
    (hsplit : genusChainCollapse q = left ++ right)
    (a : GenusTruncatedCell q) (loop : List ((orderCx (GenusTruncatedCell q)).E × Bool))
    (ha : genusCollapseStage q (left ++ right) a)
    (hpath : IsPath (orderCx (GenusTruncatedCell q)).src
      (orderCx (GenusTruncatedCell q)).tgt loop a a)
    (hC : PathIn (genusCollapseStage q left) loop) :
    LoopRep q (genusCollapseStage q (left ++ right)) a loop := by
  induction right generalizing left loop with
  | nil => exact ⟨loop, hpath, by simpa using hC, Htpy.refl _⟩
  | cons p right ih =>
    have haTail : genusCollapseStage q ((left ++ [p]) ++ right) a := by simpa using ha
    obtain ⟨l, hl, hlC, hhl⟩ := genus_pair_loop_representative q left right p hsplit
      a loop (genusCollapseStage_append_subset q (left ++ [p]) right a haTail) hpath hC
    obtain ⟨r, hr, hrC, hhr⟩ := ih (left ++ [p]) (by simpa using hsplit) l haTail hl hlC
    exact ⟨r, hr, by simpa using hrC, hhl.trans hhr⟩

noncomputable def genusSpineToOldPi1Equiv :
    Pi1 (genusSpineCx q) (spineBase q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) ((genusSpineToOld q).onV (spineBase q)) := by
  refine MulEquiv.ofBijective (pi1Map (genusSpineToOld q) (spineBase q))
    ⟨genusSpineToOld_pi1_injective q, fun z => ?_⟩
  obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
    ((genusSpineToTruncated q).onV (spineBase q)) z
  rcases v with ⟨p⟩
  obtain ⟨l, hl, hC, hh⟩ := genus_collapse_suffix_loop_representative q
    (genusChainCollapse q) [] (by simp) (spineBase q).1 p.1
    ((genusCollapseStage_final_iff q _).mpr (spineBase q).2) p.2
    (fun e _ => ⟨genusCollapseStage_nil q e.1.1.1, genusCollapseStage_nil q e.1.1.2⟩)
  have hrB := pathIn_mono (fun c hc => (genusCollapseStage_final_iff q c).mp hc) hC
  let lifted : Loop (orderCx (GenusSpineCell q)) (spineBase q) :=
    ⟨liftPathIn l hrB, isPath_liftPathIn l hrB (spineBase q).2 (spineBase q).2 hl⟩
  let w := (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).symm (Pi1.mk lifted)
  refine ⟨w, ?_⟩
  have hfactor : ∀ x, pi1Map (genusSpineToTruncated q) (spineBase q) x =
      pi1Map (orderCxMap Subtype.val monotone_subtypeVal) (spineBase q)
        (strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q) x) := fun x =>
    Quotient.inductionOn x fun _ => congrArg Pi1.mk (Subtype.ext
      (by simp [genusSpineToTruncated, mapPath, Hom.comp, List.map_map, Function.comp_def]))
  have hw : pi1Map (genusSpineToTruncated q) (spineBase q) w = Pi1.mk p := by
    rw [hfactor, MulEquiv.apply_symm_apply]
    apply Quotient.sound
    change Htpy (orderCx (GenusTruncatedCell q)) (spineBase q).1 (spineBase q).1
      (mapPath (subposetHom (fun c => c ∈ genusSpineCellSet q)) (liftPathIn l hrB)) p.1
    rw [mapPath_liftPathIn]; exact hh.symm
  rw [genusSpine_pi1_factor, hw]; exact hv
