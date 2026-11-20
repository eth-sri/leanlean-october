module

public import RequestProject.GenusCollapseIteration
public import RequestProject.OrderComplexMaximalPath

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

private def LoopRepresentatives (U B : GenusTruncatedCell q → Prop) (a : GenusTruncatedCell q) : Prop :=
  ∀ (l : Loop (orderCx (GenusTruncatedCell q)) a), B a → PathIn U l.1 →
    ∃ r : Loop (orderCx (GenusTruncatedCell q)) a, PathIn B r.1 ∧ Htpy (orderCx _) a a l.1 r.1

private theorem genus_recorded_pair_loop_representative {left right : List (GenusCollapsePair q)}
    {s : GenusTruncatedCell q} {t : QOld (cmpRel (GenusVertex q))}
    (hsplit : genusChainCollapse q = left ++ (qCubeToCoordinate t.1, truncatedFaceIndex s) :: right)
    (a : GenusTruncatedCell q) :
    LoopRepresentatives q (genusCollapseStage q left)
      (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, truncatedFaceIndex s)])) a := by
  intro loop ha hC
  have h := genus_pair_data q hsplit
  have ha' := (genusCollapseStage_step_iff q left s t a).mp ha
  obtain ⟨l, hl, hlf, hhl⟩ := loop_representative_delete_free_face h.top_mem h.face_lt.le
    h.face_lt.ne.symm h.unique_coface ha'.1 loop.2 hC
  have hconn := connectedIn_congr h.link_iff (genus_pair_link_connectivity q hsplit).1
  obtain ⟨r, hr, hrB, hhr⟩ := maximal_path_representative
    (fun x _ hx => genus_top_cell_maximal q t h.dim_top x hx) hconn l ha' ha' hl hlf
  exact ⟨⟨r, hr⟩, pathIn_mono (fun x => (genusCollapseStage_step_iff q left s t x).mpr) hrB,
    hhl.trans hhr⟩

/-- Every loop of the truncated block based in its surviving spine is represented in that spine. -/
private theorem genusSpine_loop_representative (a : GenusTruncatedCell q) :
    LoopRepresentatives q (fun _ => True) (fun c => c ∈ genusSpineCellSet q) a := by
  have h := genus_collapse_suffix q
    (R := fun l r => LoopRepresentatives q (genusCollapseStage q l) (genusCollapseStage q r) a)
    (fun _ loop _ hl => ⟨loop, hl, Htpy.refl _⟩)
    (fun h => genus_recorded_pair_loop_representative q h a) ?_ (l := []) (r := genusChainCollapse q) rfl
  · simpa only [List.nil_append, genusCollapseStage_nil_eq, genusCollapseStage_full_eq] using h
  · intro l p r hf ht loop ha hl
    obtain ⟨m, hm, hh⟩ := hf loop (genusCollapseStage_append_subset q _ _ a ha) hl
    obtain ⟨n, hn, hh'⟩ := ht m ha hm
    exact ⟨n, hn, hh.trans hh'⟩

theorem genusSpineToTruncated_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToTruncated q) (spineBase q)) := by
  rintro ⟨p⟩
  obtain ⟨r, hrB, hh⟩ := genusSpine_loop_representative q (spineBase q).1 p (spineBase q).2
    (fun _ _ => ⟨trivial, trivial⟩)
  let lifted : Loop (orderCx (GenusSpineCell q)) (spineBase q) :=
    ⟨liftPathIn r.1 hrB, isPath_liftPathIn r.1 hrB (spineBase q).2 (spineBase q).2 r.2⟩
  refine ⟨(strictOrderPi1Equiv (P := GenusSpineCell q) (spineBase q)).symm (Pi1.mk lifted), ?_⟩
  rw [genusSpineToTruncated_pi1_factor, MulEquiv.apply_symm_apply]
  apply Quotient.sound
  change Htpy (orderCx (GenusTruncatedCell q)) (spineBase q).1 (spineBase q).1
    (mapPath (subposetHom (fun c => c ∈ genusSpineCellSet q)) (liftPathIn r.1 hrB)) p.1
  rw [mapPath_liftPathIn]
  exact hh.symm

theorem genusSpineToOld_pi1_surjective :
    Function.Surjective (pi1Map (genusSpineToOld q) (spineBase q)) := by
  intro z
  obtain ⟨v, hv⟩ := truncatedRetraction_pi1_surjective_at
    ((genusSpineToTruncated q).onV (spineBase q)) z
  obtain ⟨w, hw⟩ := genusSpineToTruncated_pi1_surjective q v
  exact ⟨w, by rw [genusSpine_pi1_factor, hw]; exact hv⟩

noncomputable def genusSpineToOldPi1Equiv :
    Pi1 (genusSpineCx q) (spineBase q) ≃*
      Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) ((genusSpineToOld q).onV (spineBase q)) :=
  MulEquiv.ofBijective (pi1Map (genusSpineToOld q) (spineBase q))
    ⟨genusSpineToOld_pi1_injective q, genusSpineToOld_pi1_surjective q⟩

end FiniteChains.Davis.Genus
