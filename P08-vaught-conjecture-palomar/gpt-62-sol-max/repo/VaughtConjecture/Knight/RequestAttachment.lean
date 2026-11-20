/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReducedProjectionRequest
public import VaughtConjecture.AmalgamationPlan.PlanAttachment
public import VaughtConjecture.Knight.ExtendOneWith

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

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd

universe w

/-! ## Plans of faces -/

section PlanImage

/-- Restriction commutes with the image along an injection. -/
theorem restrictPlan_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (g : ι ↪ κ)
    (S : Finset (Finset ι)) (T : Finset ι) :
    Plan.restrictPlan (S.image (Finset.image g)) (T.image g) =
      (Plan.restrictPlan S T).image (Finset.image g) := by
  ext U
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hsub⟩
    exact ⟨V, ⟨hV, (Finset.image_subset_image_iff g.injective).mp hsub⟩, rfl⟩
  · rintro ⟨V, ⟨hV, hVT⟩, rfl⟩
    exact ⟨⟨V, hV, rfl⟩, Finset.image_subset_image hVT⟩

variable {k m : ℕ}

/-- The image of a restricted scheme's plan is the restriction of the plan to the face. -/
theorem image_restrictFace_plan (D : CellScheme (ι := Fin m) Finset.univ) (f : Fin k ↪ Fin m)
    (hr : Finset.univ.image f ∈ D.plan) :
    (D.restrictFace f hr).plan.image (Finset.image f) =
      Plan.restrictPlan D.plan (Finset.univ.image f) := by
  ext S
  simp only [Finset.mem_image, CellScheme.mem_restrictFace_plan D f hr, Plan.restrictPlan,
    Finset.mem_inter, Finset.mem_powerset]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact ⟨hT, Finset.image_subset_image (Finset.subset_univ T)⟩
  · rintro ⟨hS, hsub⟩
    obtain ⟨T, -, rfl⟩ := Finset.subset_image_iff.mp hsub
    exact ⟨T, hS, rfl⟩

theorem univ_image_onePointProj (e : Fin k ↪ Fin m) :
    (Finset.univ : Finset (Fin (k + 1))).image (onePointProj e) =
      Finset.univ.image (e.trans Fin.castSuccEmb) ∪ {Fin.last m} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (onePointProj_last e)
    | cast i => exact Or.inl ⟨i, (onePointProj_castSucc e i).symm⟩
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc i, onePointProj_castSucc e i⟩
    · exact ⟨Fin.last k, onePointProj_last e⟩

theorem image_castSuccEmb_union_last :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb ∪ {Fin.last m} = Finset.univ := by
  rw [image_castSuccEmb_univ, Finset.union_comm, ← Finset.insert_eq,
    Finset.insert_erase (Finset.mem_univ _)]

end PlanImage

/-! ## The common plan over the actual context -/

section Attach

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

/-- The retained old face, in the form the explicit one-point extension of cell schemes
consumes: a face of the context's points is visible in the common plan exactly when it is
visible in the context's plan. -/
theorem common_plan_hface {m : ℕ} {Rp : Finset (Finset (Fin (m + 1)))}
    {P₀ : Finset (Finset (Fin m))}
    (hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
      P₀.image (Finset.image Fin.castSuccEmb)) :
    ∀ B : Finset (Fin m), B.image Fin.castSuccEmb ∈ Rp ↔ B ∈ P₀ := by
  intro B
  have hsub : B.image Fin.castSuccEmb ⊆ Finset.univ.image Fin.castSuccEmb :=
    Finset.image_subset_image (Finset.subset_univ B)
  constructor
  · intro h
    have : B.image Fin.castSuccEmb ∈ Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) :=
      Finset.mem_inter.mpr ⟨h, Finset.mem_powerset.mpr hsub⟩
    rw [hRA, Finset.mem_image] at this
    obtain ⟨B', hB', e⟩ := this
    rwa [(Finset.image_injective Fin.castSuccEmb.injective) e] at hB'
  · intro h
    have : B.image Fin.castSuccEmb ∈ Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) := by
      rw [hRA]; exact Finset.mem_image_of_mem _ h
    exact (Finset.mem_inter.mp this).1

end Attach

/-! ## The cell inventory: old cells, the request's fresh cells, one cell per remaining index

`requestInventory` is the explicit one-point extension (`CellScheme.extendOneWith`) of the
context scheme `X` along the common plan, with two kinds of new cells: the request's **fresh
cells** (those containing the fresh point, pushed along `onePointProj e`) and one cell per
remaining graded index of the plan that contains the fresh point but is **not** inside the
request face (`OutsideIndex`).  Index completeness is by construction; the old face is literal;
the request face carries the request's plan and each fresh request cell sits at its pushed
graded index.  What this does **not** decide is semantic adequacy at the outside indices:
whether one cell per index suffices, and which rows those cells carry. -/

section Inventory

open CellScheme
open CellScheme.restrictFace (pushGraded)

variable {m n : ℕ} (X : CellScheme (ι := Fin m) Finset.univ)
  (Y : CellScheme (ι := Fin (n + 1)) Finset.univ) (e : Fin n ↪ Fin m)
  (Rp : Finset (Finset (Fin (m + 1)))) (hR : Plan.IsPlan Finset.univ Rp)
  (hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb))
  (hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e)))

/-- The request's fresh cells: those whose scope contains the fresh point. -/
abbrev FreshReq : Type := {c : Cell Y // Fin.last n ∈ Y.scope c}

/-- The remaining graded indices: in the common plan, containing the fresh point, not inside the
request face. -/
abbrev OutsideIndex : Type :=
  {BJ : Finset (Fin (m + 1)) × ℕ // BJ ∈ (Plan.gradedPlan Rp).filter
    (fun BJ => Fin.last m ∈ BJ.1 ∧ ¬ BJ.1 ⊆ Finset.univ.image (onePointProj e))}

/-- The new cells' graded indices. -/
def newIndex : FreshReq Y ⊕ OutsideIndex e Rp → Finset (Fin (m + 1)) × ℕ
  | Sum.inl c => pushGraded (onePointProj e) (Y.cell c.1)
  | Sum.inr BJ => BJ.1

include hRB in
theorem newIndex_mem (x : FreshReq Y ⊕ OutsideIndex e Rp) :
    newIndex Y e Rp x ∈ Plan.gradedPlan Rp := by
  classical
  rcases x with c | BJ
  · have hmem : (Y.scope c.1).image (onePointProj e) ∈ Rp := by
      have : (Y.scope c.1).image (onePointProj e) ∈
          Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) := by
        rw [hRB]; exact Finset.mem_image_of_mem _ (Y.scope_mem_plan c.1)
      exact (Finset.mem_inter.mp this).1
    have h := Plan.mem_gradedPlan.mp (Y.cell_mem c.1)
    refine Plan.mem_gradedPlan.mpr ⟨hmem, h.2.1, ?_⟩
    change (Y.cell c.1).2 ≤ ((Y.cell c.1).1.image (onePointProj e)).card
    rw [Finset.card_image_of_injective _ (onePointProj e).injective]
    exact h.2.2
  · exact (Finset.mem_filter.mp BJ.2).1

/-- **The cell inventory** over the common plan. -/
noncomputable def requestInventory : CellScheme (ι := Fin (m + 1)) Finset.univ :=
  extendOneWith X Rp hR (common_plan_hface hRA) (newIndex Y e Rp) (newIndex_mem Y e Rp hRB)

variable {X Y e Rp hR hRA hRB}

end Inventory

/-! ## Over the actual context -/

section Actual

open CellScheme
open CellScheme.restrictFace (pushGraded)

variable {M : Type w} {α β : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} (C : ReferenceContext R t reqs) (hβ : β ≤ α)

end Actual

end VaughtConjecture.Knight
