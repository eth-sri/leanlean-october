module

public import Chazelle.Core.FactsInterior

/-!
# WP-B: the cut structure of the good models

`cutStructure : CutStructureSpec` — the combinatorial Lemmas 2.1–2.2 for every good model
(chain models of chains of simple polygons, interior models of simple polygons) and every finite
admissible family: a non-cut position inside a walk edge faces exactly one region, every region is
faced, and two **non-cut** positions face the same region iff no chord separates their keys.

`CutStructureSpec` is this corrected statement (review finding B1).
-/

namespace Chazelle.Core

@[expose] public section

/-- **WP-B: the cut structure** (corrected statement, non-cut positions in part 3). -/
theorem cutStructure : CutStructureSpec := by
  intro M Q F hM hF
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  refine ⟨fun p t hp ht0 ht1 hcut => hW.faces_existsUnique hAdm hfin hp ⟨ht0, ht1⟩ hcut,
    fun U hU => hW.exists_faces hAdm hfin hU, ?_⟩
  intro p p' t t' U U' hU hU' hp hp' ht0 ht1 ht0' ht1' hcut hcut' hf hf'
  exact hW.eq_iff_not_separates hAdm hfin hU hU' hp hp' ⟨ht0, ht1⟩ ⟨ht0', ht1'⟩ hcut hcut' hf hf'

end

end Chazelle.Core
