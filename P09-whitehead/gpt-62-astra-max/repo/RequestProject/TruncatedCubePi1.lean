module

public import RequestProject.TruncatedCubePoset
public import RequestProject.StrictOrderComplex

@[expose] public section

/-! Based path comparison for the actual truncated face poset, before collapse. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

noncomputable def truncatedRetractionHom :
    Hom (orderCx (TruncatedCell A)) (orderCx (QOld A)) :=
  orderCxMap truncatedCellRetraction truncatedCellRetraction_monotone

noncomputable def truncatedSectionHom :
    Hom (orderCx (QOld A)) (orderCx (TruncatedCell A)) :=
  orderCxMap oldCellIncl oldCellIncl_monotone

variable (a : TruncatedCell A)

/-- The retraction also reflects null homotopies at a new cut-cell basepoint. -/
theorem truncatedRetraction_pi1_injective_at :
    Function.Injective (pi1Map truncatedRetractionHom a) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨p⟩ hp
  let g : TruncatedCell A → TruncatedCell A := fun c =>
    oldCellIncl (truncatedCellRetraction c)
  have hg : Monotone g := oldCellIncl_monotone.comp truncatedCellRetraction_monotone
  have hnat := htpy_loop_mapPath_le monotone_id hg
    truncatedCell_le_retraction p.2
  have hsec := mapPath_htpy truncatedSectionHom (Quotient.exact hp)
  have hgnil : Htpy _ (g a) (g a)
      (mapPath (orderCxMap g hg) p.1) [] := by
    simpa [g, truncatedSectionHom, truncatedRetractionHom, mapPath, orderCxMap,
      List.map_map, Function.comp_def] using hsec
  have hconj : Htpy _ (g a) (g a)
      ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
        [ordPos (truncatedCell_le_retraction a)]) [] := by
    simpa [mapPath, orderCxMap] using hnat.symm.trans hgnil
  have hstep := hconj.congr_append (isPath_ordPos (truncatedCell_le_retraction a))
    (isPath_ordNeg (truncatedCell_le_retraction a))
  have hc := htpy_ordPos_ordNeg (truncatedCell_le_retraction a)
  have hA := hc.congr_append (isPath_nil' a)
    (p.2.append (show IsPath (orderCx (TruncatedCell A)).src
      (orderCx (TruncatedCell A)).tgt
      [ordPos (truncatedCell_le_retraction a), ordNeg (truncatedCell_le_retraction a)]
      a a from ⟨rfl, rfl, rfl⟩))
  have hB := hc.congr_append p.2 (isPath_nil' a)
  have hstrip : Htpy _ a a
      ([ordPos (truncatedCell_le_retraction a)] ++
        ([ordNeg (truncatedCell_le_retraction a)] ++ p.1 ++
          [ordPos (truncatedCell_le_retraction a)]) ++
        [ordNeg (truncatedCell_le_retraction a)]) p.1 := by
    simpa [List.append_assoc] using hA.trans (by simp_all)
  exact Quotient.sound (hstrip.symm.trans (hstep.trans (by assumption)))

theorem truncatedRetraction_pi1_surjective_at :
    Function.Surjective (pi1Map truncatedRetractionHom a) := by
  rintro ⟨p⟩
  let e := truncatedCell_le_retraction a
  let lp : Loop (orderCx (TruncatedCell A)) a :=
    ⟨[ordPos e] ++ mapPath truncatedSectionHom p.1 ++ [ordNeg e],
      ((isPath_ordPos e).append (isPath_mapPath truncatedSectionHom p.2)).append
        (isPath_ordNeg e)⟩
  refine ⟨Pi1.mk lp, Quotient.sound ?_⟩
  change Htpy _ _ _
    _ p.val
  have hs := htpy_ordSelf_nil (truncatedCellRetraction a)
  have hA := hs.congr_append (isPath_nil' (truncatedCellRetraction a))
    (p.2.append (isPath_ordNeg (le_refl (truncatedCellRetraction a))))
  have hB := (htpy_revPath (isPath_ordPos (le_refl (truncatedCellRetraction a))) hs).congr_append p.2 (isPath_nil' (truncatedCellRetraction a))
  simp only [List.nil_append, List.append_nil, revPath_nil] at hA hB
  simpa [loopSetoid, ordPos, ordNeg, lp, e, truncatedRetractionHom, truncatedSectionHom, mapPath, orderCxMap,
    List.map_map, Function.comp_def, revPath, revGerm] using (hA.trans hB)

end FiniteChains.Davis
