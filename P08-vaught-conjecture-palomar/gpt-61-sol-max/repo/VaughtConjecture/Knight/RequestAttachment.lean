/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ReducedProjectionRequest
import VaughtConjecture.AmalgamationPlan.PlanAttachment
import VaughtConjecture.Knight.Domain

/-! # The common plan of the actual context and one requested one-point extension

`IsPlan.attach_one_over_face` (`AmalgamationPlan/PlanAttachment.lean`) attaches a prescribed
one-point plan over a visible face of a plan, retaining both plans literally.  This module
instantiates it on the actual model-produced reference context `C` and a requested reduced
one-point type `P` over the root:

* the **context plan** is embedded on the old coordinates (`Fin.castSuccEmb`);
* the **request plan** is embedded on the root coordinates plus the fresh point
  (`onePointProj C.proj`), its domain being the root face plus `last`
  (`univ_image_onePointProj`);
* their **agreement on the shared root face** is derived from the request's root compatibility
  (`typeMap castSucc P = some (reduce p)`) and the context's exact consistency
  (`typeMap C.proj C.p₀ = some p`): both restrict to the root's own plan, pushed
  (`plan_of_typeMap_eq_some`, `restrictPlan_image`);
* the result (`exists_common_plan`) is a support plan on all `C.m + 1` points in which the old
  face and the request face are visible and carry the context's and the request's plans
  **exactly** (`restrictPlan` equalities); in the form the explicit one-point extension of cell
  schemes consumes, `common_plan_hface`.

The pivot lemma (`exists_pivot_outside_root`) remains a necessary-condition check on any such
plan; it is not a hypothesis here — the attachment theorem supplies the geometry from the two
plans and their agreement.  For a whole finite candidate envelope rather than one fresh point,
`IsPlan.amalgamate` (#344) attaches two support plans agreeing on a common visible overlap on
their literal union; the one-point form is what one requested projection needs.

**The cell inventory** (`requestInventory`, over the common plan, by the explicit one-point
extension `CellScheme.extendOneWith`): the old cells, the request's **fresh cells** (those
containing the fresh point, pushed along `onePointProj e`), and one cell per **remaining graded
index** — in the plan, containing the fresh point, not inside the request face.  It is complete
(`requestInventory_complete`, from the context's and the request's completeness), its old face
is literally the context's domain (`requestInventory_old_face`), its request face is visible
and carries the request's plan (`requestInventory_request_face`), each fresh request cell sits
at its pushed graded index (`cell_freshCell`, injectively), and every cell is an old cell, a
fresh request cell, or a remaining-index cell (`requestInventory_cases`); the fresh request
cells are visible on the request face, the remaining-index cells are not, and an old cell is
visible on the request face exactly when it is visible on the root face of the context
(`scope_castAdd_subset_iff`).  Over the actual context and request:
`ReferenceContext.exists_requestInventory`, and the **shared root with rows**
(`ReferenceContext.shared_root`): the context's domain restricted to the root face and the
request's domain restricted to its initial face are both the root's domain, rows included, so
the rows the two faces prescribe agree on the shared root.

## Where this stops: the first genuinely new mixed-semantic obligation

The rows of the old cells and of the request's fresh cells are prescribed by the two faces (the
old face literally; the request face through the fresh-cell embedding and the shared root), and
they agree where both apply.  Not prescribed by anything are the rows of the **remaining-index
cells**: the full-scope controllers `(univ, k)` and every new mixed proper scope containing the
fresh point outside the request face.  Their rows must be consistent with the context's rows
and with the request's rows at once (mixed locality across the two faces), correct for the
reference data (equality on the exact requests, inequality on the lower-bound requests), and
bountiful for **every** permitted labelling of the two faces.  Two qualifications are part of
the obligation, not resolved by the inventory: one cell per remaining index is index
completeness, not semantic adequacy — owned witnesses or availability may require several cells
at one index — and the mixed proper scopes need the same work as the full-scope controllers.
`ReducedDeterminingProbe` (#343) is a template for a small determining set of probes; its proof
uses the fixed repaired scheme and does not transfer to this inventory.  No supply record is
added; nothing replaces the context by the fixed coupled example.

Construction-private (not root-exported). -/

namespace VaughtConjecture.Knight

open    AmalgamationPlan  


/-! ## Plans of faces -/

section

/-- Restriction commutes with the image along an injection. -/
theorem restrictPlan_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (g : ι ↪ κ)
    (S : VaughtConjecture.AmalgamationPlan.SupportFamily ι) (T : Finset ι) :
    Plan.restrictPlan (S.image (Finset.image g)) (T.image g) =
      (Plan.restrictPlan S T).image (Finset.image g) := by
  ext U
  simp  [Plan.restrictPlan,   ]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hsub⟩
    exact ⟨V, ⟨hV, (Finset.image_subset_image_iff g.injective).mp hsub⟩, rfl⟩
  · grind

variable {k m : ℕ}

/-- The image of a restricted scheme's plan is the restriction of the plan to the face. -/
theorem image_restrictFace_plan (D : CellScheme (ι := Fin m) Finset.univ) (f : Fin k ↪ Fin m)
    (hr : Finset.univ.image f ∈ D.plan) :
    (D.restrictFace f hr).plan.image (Finset.image f) =
      Plan.restrictPlan D.plan (Finset.univ.image f) := by
  ext S
  simp  [ CellScheme.mem_restrictFace_plan D f hr, Plan.restrictPlan,
     ]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT, Finset.image_subset_image (Finset.subset_univ T)⟩
  · rintro ⟨hS, hsub⟩
    obtain ⟨T, -, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨T, hS, rfl⟩

theorem univ_image_onePointProj e :
    (Finset.univ : Finset (Fin (k + 1))).image (onePointProj e) =
      Finset.univ.image (e.trans Fin.castSuccEmb) ∪ {Fin.last m} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (onePointProj_last e)
    | cast i => simp_all
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc i, onePointProj_castSucc e i⟩
    · grind [onePointProj_last]

theorem image_castSuccEmb_union_last :
    (Finset.univ : FiniteScope m).image Fin.castSuccEmb ∪ {Fin.last m} = Finset.univ := by simp_all


/-! ## The common plan over the actual context -/


/-! ## The cell inventory: old cells, the request's fresh cells, one cell per remaining index

`requestInventory` is the explicit one-point extension (`CellScheme.extendOneWith`) of the
context scheme `X` along the common plan, with two kinds of new cells: the request's **fresh
cells** (those containing the fresh point, pushed along `onePointProj e`) and one cell per
remaining graded index of the plan that contains the fresh point but is **not** inside the
request face (`OutsideIndex`).  Index completeness is by construction; the old face is literal;
the request face carries the request's plan and each fresh request cell sits at its pushed
graded index.  What this does **not** decide is semantic adequacy at the outside indices:
whether one cell per index suffices, and which rows those cells carry. -/


/-! ## Over the actual context -/


