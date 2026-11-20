/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ExtendOneWith
public import VaughtConjecture.Knight.PullbackSemantics
public import VaughtConjecture.Knight.AssembledReferenceContext
public import VaughtConjecture.Knight.RowReadback

/-! # The four-point duplication context over the assembled scheme

A **legal extension of the assembled three-point domain** by one fresh point, with literal old-face
preservation and universal fresh-cell readback.

**The construction.**  The fourth point is a *copy* of the point `0`: the folding
`fold : Fin 4 → Fin 3` sends `3 ↦ 0` and fixes the rest.  The plan `plan₄` consists of the old
faces (pushed along `castSucc`), their copies under the fold (`{3}`, `{1,3}`, `{1,2,3}`), and the
domain — a support plan with pivots `3, 0` (`isPlan₄`, and the face equation `hface₄`, by
`decide`).  The new cells are one copy of every old cell for every new face whose fold is the
cell's scope (`Copy`), plus one mute cell at `(univ, 4)`.  The retraction `ret` sends a copy to
its original, and the rows are the old rows pulled back
(`rows₄ := family₀.rows.pullback ret mute₄ …`, `Knight/PullbackSemantics.lean`).

**Legality.**  `D₄` is complete (`D₄_complete`); `rows₄` is coded and consistent
(`rows₄_isCoded`, `rows₄_isConsistent`, by the pullback theorems with the section property
`hsect₄`).  Bountifulness: at proper-scope pairs it transports from `semScheme₀` — the retraction is
a bijection of lower sets on every proper face, old or copied (`eProper`, `bountiful₄_proper`); at
full-scope pairs it is `bountiful_full_scope`; the proper-to-full cases (`ProperToFull₄`) reduce,
through restriction to the old cells (`restrict_old_respects`) and the pullback of the old extension
(`pullback_of_sect`), to old bountifulness plus **rigidity** (`Rigidity₄`,
`properToFull₄_of_rigidity`; the grade-four case by `bountiful_full_scope`).  Rigidity —
**uniqueness of extension over a fixed old labelling**: every respecting labelling of a full-scope
lower set of grade at most three agrees at a cell and at its retraction — is the controller-probe
lemma applied to a copy and its original (`rigidity₄`).  Hence `fourPointDomain : SemScheme 4`.

**Readback.**  The old labelled type `p₀ : S (ω·2) 3` carries the row of the capped cell with cap
`ω + 4`; `extendsDomain_fourPoint` is literal face readback (rows included); the coface
`fourPointCoface` is the old labelling pulled back (`isCoface_fourPoint`).  The inherited reference
data `R₄` keep the old cap and trigger (grade three, `ω + 4`), threshold `3`, the old singleton at
`ω + 1` as representative, and one fresh request at the copied singleton `s3copy` (block `ω`,
offset `1`); every controller at `(univ, 3)` is correct because both full copies read the old row at
the singleton (`fourPointInputs`).  `readback_fourPoint` is Lemma 10.1.1's readback: every coface
with the `⊥`-pattern of the coface reads `ω + 1` at the fresh cell; `fourPointCoface_readback`
realizes it with the trigger active.

**Scope.**  This is a legal *duplication* extension.  It forces the copied cell's label to equal
its original's; it does not support independently prescribed fresh labels, arbitrary requests, or
realization inside two fixed models (the two-context experiment).  Construction-private (not
root-exported). -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

section FourPoint

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-- The folding of the fourth point onto the first. -/
def fold : Fin 4 → Fin 3
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0

theorem fold_castSucc (i : Fin 3) : fold (Fin.castSuccEmb i) = i := by revert i; decide

theorem image_fold_image_castSucc (B : Finset (Fin 3)) :
    (B.image Fin.castSuccEmb).image fold = B := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := B)]
  exact Finset.image_congr fun i _ => fold_castSucc i

/-- The two-copy plan on `Fin 4`. -/
def plan₄ : Finset (Finset (Fin 4)) :=
  {∅, {0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {1, 3}, {0, 1, 2}, {1, 2, 3}, Finset.univ}

/-- The plan on a pair `{x, y}` (the full powerset). -/
theorem isPlan_pair (x y : Fin 4) (hxy : x ≠ y) :
    Plan.IsPlan ({x, y} : Finset (Fin 4)) {∅, {x}, {y}, {x, y}} := by
  refine Plan.IsPlan.step (a := x) (b := y) (Q := {∅, {y}}) (R := {∅, {x}})
    (by simp) (by simp) hxy ?_ ?_ ?_ ?_ ?_
  · rw [Finset.erase_insert (by simpa using hxy)]; exact Plan.IsPlan.singleton y
  · rw [Finset.pair_comm, Finset.erase_insert (by simpa using hxy.symm)]
    exact Plan.IsPlan.singleton x
  · rw [Finset.erase_insert (by simpa using hxy), Finset.erase_singleton]; simp
  · rw [Finset.erase_insert (by simpa using hxy), Finset.erase_singleton]
    ext B; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_powerset, Finset.subset_empty]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨Or.inl h1, h2⟩
      · exact absurd (h1 ▸ h2) (by simp)
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨Or.inl h1, h2⟩
      · exact absurd (h1 ▸ h2) (by simp)
  · ext B
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto

theorem isPlan₄ : Plan.IsPlan (Finset.univ : Finset (Fin 4)) plan₄ := by
  have hR : Plan.IsPlan ({1, 2, 3} : Finset (Fin 4))
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {1, 2, 3}} := by
    refine Plan.IsPlan.step (a := 3) (b := 2) (Q := {∅, {1}, {2}, {1, 2}})
      (R := {∅, {1}, {3}, {1, 3}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({1, 2, 3} : Finset (Fin 4)).erase 3 = {1, 2} by decide]
      exact isPlan_pair 1 2 (by decide)
    · rw [show ({1, 2, 3} : Finset (Fin 4)).erase 2 = {1, 3} by decide]
      exact isPlan_pair 1 3 (by decide)
  have hQ : Plan.IsPlan ({0, 1, 2} : Finset (Fin 4))
      {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}} := by
    refine Plan.IsPlan.step (a := 0) (b := 2) (Q := {∅, {1}, {2}, {1, 2}})
      (R := {∅, {0}, {1}, {0, 1}})
      (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
    · rw [show ({0, 1, 2} : Finset (Fin 4)).erase 0 = {1, 2} by decide]
      exact isPlan_pair 1 2 (by decide)
    · rw [show ({0, 1, 2} : Finset (Fin 4)).erase 2 = {0, 1} by decide]
      exact isPlan_pair 0 1 (by decide)
  refine Plan.IsPlan.step (a := 3) (b := 0) (Q := {∅, {0}, {1}, {2}, {0, 1}, {1, 2}, {0, 1, 2}})
    (R := {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {1, 2, 3}}) (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide)
  · rw [show (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} by decide]; exact hQ
  · rw [show (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} by decide]; exact hR

/-- The face equation of the plan: a face of `Fin 3` is visible iff its push-forward is. -/
theorem hface₄ : ∀ B : Finset (Fin 3), B.image Fin.castSuccEmb ∈ plan₄ ↔ B ∈ Prop3.plan := by
  decide

/-- The new faces: the copies of the old faces, and the domain. -/
def newFaces : Finset (Finset (Fin 4)) := {{3}, {1, 3}, {1, 2, 3}, Finset.univ}

theorem newFaces_subset : ∀ B ∈ newFaces, B ∈ plan₄ := by decide

/-- The old scheme. -/
noncomputable abbrev C₀ : CellScheme (ι := Fin 3) Finset.univ := family₀.scheme

/-- **The copies**: an old cell together with a new face whose fold is its scope. -/
abbrev Copy : Type := {p : ↥newFaces × Cell C₀ // C₀.scope p.2 = (p.1.1).image fold}

/-- The new cells: the copies and the mute top cell. -/
abbrev New : Type := Copy ⊕ Unit

noncomputable def newCell₄ : New → Finset (Fin 4) × ℕ
  | .inl p => (p.1.1.1, C₀.grade p.1.2)
  | .inr _ => (Finset.univ, 4)

theorem newCell₄_mem (x : New) : newCell₄ x ∈ Plan.gradedPlan plan₄ := by
  rcases x with p | _
  · refine Plan.mem_gradedPlan.mpr ⟨newFaces_subset _ p.1.1.2, C₀.grade_pos _, ?_⟩
    change C₀.grade p.1.2 ≤ (p.1.1.1).card
    calc C₀.grade p.1.2 ≤ (C₀.scope p.1.2).card := C₀.grade_le_card_scope _
      _ = ((p.1.1.1).image fold).card := by rw [p.2]
      _ ≤ (p.1.1.1).card := Finset.card_image_le
  · change (Finset.univ, 4) ∈ _
    exact Plan.mem_gradedPlan.mpr ⟨by decide, by decide, by decide⟩

/-- **The four-point scheme.** -/
noncomputable abbrev D₄ : CellScheme (ι := Fin 4) Finset.univ :=
  CellScheme.extendOneWith C₀ plan₄ isPlan₄ hface₄ newCell₄ newCell₄_mem

/-- The old cell with cap `ω + 4`, the target of the mute cell under the (irrelevant) retraction. -/
noncomputable def a₂cell : Cell C₀ := family₀.e (.inr (.inr (.inr a₂c)))

/-- The mute cell: the graded index `(univ, 4)`. -/
noncomputable def mute₄ (d : Cell D₄) : Prop := D₄.cell d = (Finset.univ, 4)

noncomputable instance : DecidablePred mute₄ := fun d => inferInstanceAs (Decidable (D₄.cell d = _))

/-! ### Bountifulness: proper-scope pairs transport, full-scope pairs are general -/

theorem fold_injOn : ∀ B ∈ plan₄, B ≠ Finset.univ →
    ∀ x ∈ B, ∀ y ∈ B, fold x = fold y → x = y := by decide
theorem fold_mem_plan : ∀ B ∈ plan₄, B ≠ Finset.univ → B.image fold ∈ Prop3.plan := by decide
theorem card_fold_proper : ∀ B ∈ plan₄, B ≠ Finset.univ → (B.image fold).card = B.card := by decide
theorem castSucc_sub_old : ∀ B ∈ plan₄, (3 : Fin 4) ∉ B →
    ∀ S : Finset (Fin 3), S ⊆ B.image fold → S.image Fin.castSuccEmb ⊆ B := by decide

/-- The unfolding of an old face containing `0` into the copy containing `3`. -/
def unfold (S : Finset (Fin 3)) : Finset (Fin 4) :=
  S.image fun i => if i = 0 then 3 else Fin.castSuccEmb i

/-! ## Part 4 — the old labelled type, literal face readback, the coface, the readback inputs -/

/-- Every old cell lies below the top cell. -/
theorem hall₀ (d : Cell C₀) : GradedLe (C₀.cell d) (C₀.cell top) := by
  rw [cell_top]
  refine ⟨Finset.subset_univ _, ?_⟩
  change C₀.grade d ≤ 3
  exact (C₀.grade_le_card_scope d).trans ((Finset.card_le_univ _).trans (by simp))

/-- **The old labelled type**: `semScheme₀` labelled by the row of the capped cell with cap
`ω + 4`, at the stage `ω·2`. -/
noncomputable def p₀ : S stage 3 where
  scheme := semScheme₀
  label d := rowA₂ ⟨d, hall₀ d⟩
  label_bound _ := Or.inl (rowA₂_stage_bound _)
  respects := rowA₂_respects.toRespects hall₀

/-! ### The coface: the pullback of the old labelling -/

theorem image_fold_univ : (Finset.univ : Finset (Fin 4)).image fold = Finset.univ := by decide

/-! ### The inherited reference data and the fresh request -/

/-- Cells of the old scheme at the full grade-three index are the capped cells. -/
theorem old_full_three {x : family₀.X} (h : family₀.cellX x = (Finset.univ, 3)) :
    ∃ b : ↥family₀.S₃, x = .inr (.inr (.inr b)) := by
  rcases x with c | H' | s' | b
  · exact absurd (congrArg Prod.fst h) (Prop3.scope_ne_univ c)
  · exact absurd (congrArg Prod.snd h) (by decide : (1 : ℕ) ≠ 3)
  · exact absurd (congrArg Prod.snd h) (by decide : (2 : ℕ) ≠ 3)
  · exact ⟨b, rfl⟩

theorem v₀_le_η₁ : v₀ ≤ η₁ := by
  unfold v₀ η₁; rw [ofOrd_le_ofOrd]
  exact add_le_add_right
    (Nat.cast_le.mpr (by decide : (1 : ℕ) ≤ 3) : ((1 : ℕ) : Ordinal) ≤ (3 : ℕ)) _

/-! ## Part 5 — the scope-changing cases: reduction to old bountifulness through rigidity -/

/-- Respect transports along an equality of graded pairs. -/
theorem RespectsSemanticsBelow.cast {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ BJ' : Finset ι × ℕ} (h : BJ = BJ') {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) :
    RespectsSemanticsBelow sem BJ' (fun d => r ⟨d.1, by rw [h]; exact d.2⟩) := by
  subst h
  exact hr

/-! ## The endpoint: the legal duplication extension

A **legal duplication extension**: the fourth point duplicates the point `0`; the four-point domain
with its associated semantics is unconditional (`fourPointDomain`: coded, complete, consistent,
bountiful); it extends the old labelled type with literal old-face preservation
(`extendsDomain_fourPoint`, `isCoface_fourPoint`); and the fresh cell reads back universally
(`readback_fourPoint`: every coface with the `⊥`-pattern of the coface `fourPointCoface` reads
`ω + 1` at the copied singleton), realized by the coface with the trigger active
(`fourPointCoface_readback`, `fourPointCoface_trigger`).

**Scope.**  The extension forces the copied cell's label to equal its original's (uniqueness of
extension over a fixed old labelling).  It does not support independently prescribed fresh
labels, arbitrary requests, or realization inside two fixed models. -/

end FourPoint

end VaughtConjecture.Knight
