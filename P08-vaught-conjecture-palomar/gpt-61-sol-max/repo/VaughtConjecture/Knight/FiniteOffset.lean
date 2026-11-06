import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.Terminal

/-! # The finite-offset kernel: `mapCell` calculus and the row invariant (#51 (2/3))

The **unconditional kernel** of the master-spine experiment (#51; guide §5.1–5.3), split out
of `Knight/Spine.lean` so that the finished mathematics is exported from the root while the
not-yet-inhabited spine skeleton stays outside the import cone.  Everything here is a
theorem about *given* stage types under exact restriction — no spine, no scheduler, no
model-existence input.

## Contents

* **Transport of `TransformsTo` across a bijection of cells** (`TransformsTo.of_equiv`):
  Def. 2.3.9 mentions its cells only through the grade function and the two labellings, so
  the relation transports along any bijection commuting with the three.
* **The `mapCell` functor calculus**: identity and composition laws (`mapCell_refl`,
  `mapCell_trans`), injectivity, the scope equation, the lower-set bijection below an
  old-face cell (`belowCellEquiv`) and the row-reading equation (`rows_E_mapCell`) — the
  laws of `Knight/Terminal.lean`'s `mapCell` needed by any coherence bookkeeping over the
  labelled-cover order.
* **The finite offset assignment** (`FiniteOffset`, guide §5.1): a *partial* map `η` on the
  source-`⊤` cells of a stage type, sending an assigned occurrence class to the target
  value `α + (i+1)` and keeping an unassigned class **genuinely `⊤`** (`offsetLabel`,
  `offsetLabel_eq_top_iff`); the target labelling is strictly bounded at the next block
  `α + ω` (`offsetLabel_lt_or_top`), while the source type keeps its structural source-stage
  bound.  Coherent restriction (`comap`, functorial by the `mapCell` laws) and extension
  (`extend`, `extendFresh` — newly seen classes unassigned, the selected controller
  assigned) with their `comap`/`extend` compatibility laws.
* **The finite-offset row invariant** (`RowLaw`): the locality clause of Def. 2.5.4 at the
  target labelling, demanded at every source-`⊤` controller.  Proper controllers are free
  (`RowObligation.of_ne_top`); **case 1 of the three source-row cases** (old-face
  inheritance) is an *equivalence* (`rowObligation_comap_iff`); `RowLaw.of_extension`
  reduces any install to its newborn obligations.
* **The band condition and the exact residue** (`Banded`, `offsetLabel_orderly`,
  `RowLaw.rowObligation_all`): with the row law and the band condition the target labelling
  satisfies orderliness and locality — `RespectsSemantics` **minus availability**
  (Def. 2.5.4(2)), which is therefore the single missing property for `offsetLabel` to be a
  genuine stage-`(α + ω)` labelling; that availability residue is the provisional-band /
  companion mathematics of #51's remaining boundaries.  No `SelectiveRowSupply` or
  unrestricted-semantics premise appears anywhere: the source rows are fields of
  `SemScheme`, consumed through `p.respects` alone.

The consumer experiment — spine states, the two install constructors, the preservation
lemmas along the idle/install trace, and the open producer obligations — is
`Knight/Spine.lean` (not root-exported; see its docstring for the honest status). -/

namespace VaughtConjecture.Knight


open CellScheme.restrictFace (toCell belowMap toCell_strictMono toCell_injective
  exists_toCell_eq scope_toCell_subset image_scope_restrictFace gradedLe_restrictFace_iff
  toCell_cast_eq_of_emb)

universe w

/-! ### Transport of `TransformsTo` across a bijection of cells

The transformation relation of Def. 2.3.9 mentions its family of cells only through the grade
function and the two labellings, so it transports across any bijection commuting with the
three.  This is the reindexing engine of the row-invariant transports below (the `reindex` of
`Knight/Transform.lean` is the one-sided pullback special case). -/

namespace Transform

theorem TransformsTo.of_equiv {D D' : Type*} {grade : D → ℕ} {grade' : D' → ℕ}
    {p q : D → ExtOrd} {p' q' : D' → ExtOrd} (e : D' ≃ D)
    (hg : ∀ d, grade (e d) = grade' d) (hp : ∀ d, p (e d) = p' d)
    (hq : ∀ d, q (e d) = q' d) (h : TransformsTo grade' p' q') : TransformsTo grade p q := by
  obtain ⟨g, σ, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨g, σ, h1, h2, h3, h4, h5, fun d => ?_⟩
  have h6' := h6 (e.symm d)
  rw [← hq (e.symm d), ← hp (e.symm d), ← hg (e.symm d), e.apply_symm_apply] at h6'
  exact h6'

end Transform

/-! ### The `mapCell` calculus

`Knight/Terminal.lean` introduces `mapCell h : Cell p → Cell q` for an exact restriction
`h : typeMap f q = some p` (with `label_mapCell`, `grade_mapCell`).  The spine's coherence
bookkeeping needs its functor laws (`mapCell_refl`, `mapCell_trans`), its injectivity, its
scope equation, and the induced bijection of the lower sets below a cell together with the
row-reading equation — all proved by the substitution pattern of `label_mapCell` (replace `p`
by the literal face restriction; `mapCell` is then definitionally `toCell`). -/

namespace StageType

variable {α : Ordinal₀} {k m n : ℕ}

/-- **Composition law**: the cell map of a composite restriction is the composite of the cell
maps (the two strictly monotone enumerations of the `f.trans g`-visible cells agree). -/
theorem mapCell_trans {z : S α n} {y : S α m} {x : S α k} {g : Fin m ↪ Fin n}
    {f : Fin k ↪ Fin m} (hzy : typeMap g z = some y) (hyx : typeMap f y = some x)
    (hzx : typeMap (f.trans g) z = some x) d :
    mapCell hzx d = mapCell hzy (mapCell hyx d) := by
  obtain ⟨hg, rfl⟩ : ∃ hr, z.restrictFace g hr = y :=
    ⟨visible_of_typeMap_eq_some hzy, restrictFace_eq_of_typeMap_eq_some hzy⟩
  obtain ⟨hf, rfl⟩ : ∃ hr, (z.restrictFace g hg).restrictFace f hr = x :=
    ⟨visible_of_typeMap_eq_some hyx, restrictFace_eq_of_typeMap_eq_some hyx⟩
  set D := z.scheme.scheme with hD
  have hvis  := visible_of_typeMap_eq_some hzx
  set e : Fin ((D.restrictFace g hg).restrictFace f hf).card → Cell D :=
    fun c => toCell D g hg (toCell (D.restrictFace g hg) f hf c) with he_def
  have he  :=
    (toCell_strictMono D g hg).comp (toCell_strictMono (D.restrictFace g hg) f hf)
  have hvis_e : ∀ c, D.scope (e c) ⊆ Finset.univ.image (f.trans g) := by
    intro c
    have h1 : ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        = D.scope (e c) :=
      image_scope_restrictFace D g hg _
    rw [← h1]
    have h2 : (D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c) ⊆
        Finset.univ.image f :=
      scope_toCell_subset (D.restrictFace g hg) f hf _
    calc ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        ⊆ (Finset.univ.image f).image g := Finset.image_subset_image h2
      _ = Finset.univ.image (f.trans g) := by
          rw [Finset.image_image]; rfl
  have hcard  :=
    congrArg (fun w => w.scheme.scheme.card) (restrictFace_eq_of_typeMap_eq_some hzx)
  have key := toCell_cast_eq_of_emb D (f.trans g) hvis he hvis_e hcard d
  calc mapCell hzx d
      = toCell D (f.trans g) hvis (Fin.cast hcard.symm d) := by
        
        congr 1
    _ = e d := key
    _ = mapCell hzy (mapCell hyx d) := rfl

end StageType

/-! ### The finite offset assignment `η` (guide §5.1)

One block step over a source type `p ∈ S^α_n` retains a **partial** offset assignment on the
source-`⊤` cells: `η(c) = i` means the occurrence class of `c` is to receive the proper value
`α + (i+1)` at the next block, while an **undefined** `η(c)` means the class remains genuinely
`⊤` — the distinction between "undefined" and "offset `0`" is essential (`α + 1` versus `⊤`).
Proper source values are never touched.  The induced **target labelling** is `offsetLabel`;
its stage bound at `α + ω` is `offsetLabel_lt_or_top`.

The assignment is spine-private data: the public projections read only the induced labelling
and the row facts, never `η` itself. -/

open StageType

variable {α : Ordinal₀} {k m n : ℕ}


/-! ### The finite-offset row invariant (guide §5.2–5.3; the spine's private invariant)

The **row obligation** at a controlling cell `Ξ` is the locality clause of Def. 2.5.4 read at
the *target* labelling: the source semantic row of `Ξ` transforms (Def. 2.3.9) to the target
labelling of the cells below `Ξ`, capped at the target value of `Ξ`.  The **row law** demands
it at every source-`⊤` controller.  Proper-valued controllers are easier and are discharged
unconditionally (`RowObligation.of_ne_top`): a proper cap does not see the new band, so their
source locality witnesses are inherited verbatim — hence the row law at source-`⊤`
controllers is exactly the locality clause of "`offsetLabel` respects the source rows".

Three transports drive the bounded row induction:

* `RowObligation.of_ne_top` — proper controllers, free;
* `rowObligation_comap_iff` — **case 1 of the three source-row cases** (old-face
  inheritance): below an old-face cell the extension and the face have the *same* cells,
  rows, and target values (`belowCellEquiv`, `rows_E_mapCell`, `offsetLabel_comap`), so the
  obligation transports both ways;
* `RowLaw.of_extension` — the install-step engine: to extend the row law across an exact
  extension only the **newborn** obligations are owed; old-face controllers inherit theirs.

What is **not** proved here — deliberately: the newborn obligations themselves.  For a fresh
install they are the selected/companion witnesses (cases 2 and 3 of the three source-row
cases), consumed as data of the install; for a source-cover install they are the
Lemma-5.3.7-shaped facts about provisional values on larger covers (#51's remaining
boundaries).  `RowObligation.of_unassigned` discharges them in the offset-free situation
(newly absorbed source regions with no assigned class in sight), which is also the base of
the induction (`rowLaw_empty`) and the post-limit restart. -/


