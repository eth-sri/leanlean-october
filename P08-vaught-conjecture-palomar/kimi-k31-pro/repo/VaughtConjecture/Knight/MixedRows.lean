/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.MixedOwnValues
public import VaughtConjecture.Knight.CrossGradeRecoding
public import VaughtConjecture.Knight.PartialSections
public import VaughtConjecture.Knight.MixedIndexConstraints

/-! # The mixed rows over the actual context: consistency from the recodings

The reviewer's assignment (2026-09-15, V-C item 2): use the cross-grade recoding to assemble
the actual mixed rows and prove consistency, with one common inventory of values including the
newly assigned own values, no independently chosen codebook, and the threshold `N` arbitrary.

**The rows.**  On the cell inventory over the actual context, the rows are those prescribed by
both faces (`prescribedRows`: the context's rows on old cells, the request's rows on fresh
cells) with, at every remaining-index cell of grade `j`, **the recoding at grade `j` of the
full labelling** on its lower set (`recode j S ∘ fullLabel`; `mixedRows`).  The value set `S`
is the set of all label values of both faces; the own values introduce nothing new
(`fullLabel_eq_or`), so every label is keyed and one codebook serves all rows.

**Proved.**  The rows are coded (`mixedRows_isCoded`) and **consistent** (`mixedRows_isConsistent`,
Def. 2.5.12): the old rows and the fresh rows respect their lower sets by transport of the
context's and the request's consistency along the lower-set equivalences; a recoded row is
orderly, respects locality at every cell below it — at an old cell by the inherited locality
through the recoding (`coded_locality_recode`, the fixed-key coded locality and the Cap Lemma,
as in `Knight/ContextSourceRowRespect.lean`), at a fresh cell likewise from the request's
locality, at a lower remaining-index cell by the **cross-grade recoding transformation**
(`crossGrade_transformsTo_capped`) — and satisfies availability by the own values
(`fullLabel_availability`) and the monotonicity of the recoding on keyed labels.  The full
labelling **respects the rows** (`fullLabel_respects`): it keeps the context's and the
request's labels literally, decodes each recoded row (`recode_transformsTo`), and is available.

**Not proved.**  Bountifulness (Def. 2.5.14) of these rows — the field that would make them a
`SemScheme` — is not attempted here; it is the reviewer's item 3.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

/-! ## The recoding at a grade, generically -/


/-! ## The inventory over the actual context -/

section Inventory

variable {m n : ℕ} {X : CellScheme (ι := Fin m) Finset.univ}
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ} {e : Fin n ↪ Fin m}
  {Rp : Finset (Finset (Fin (m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    X.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj e)) =
    Y.plan.image (Finset.image (onePointProj e))}
  (hvX : Finset.univ.image e ∈ X.plan) (hvY : Finset.univ.image Fin.castSuccEmb ∈ Y.plan)
  (hroot : X.restrictFace e hvX = Y.restrictFace Fin.castSuccEmb hvY)
  (rowsX : Semantics X) (rowsY : Semantics Y) (labX : Cell X → ExtOrd) (labY : Cell Y → ExtOrd)

/-! ### The rows -/

variable (hX : ∀ d, SelfVis (X.grade d) (labX d)) (hY : ∀ c, SelfVis (Y.grade c) (labY c))

/-! ### Every cell is old, an identified request cell, or a remaining-index cell -/

variable (hfresh : ∀ c : Cell Y, Fin.last n ∈ Y.scope c)

/-! ### Consistency on a face, transported -/

/-! ### Consistency at the old and the request cells -/

variable (hXres : RespectsSemantics rowsX labX) (hYres : RespectsSemantics rowsY labY)
  (hXcons : rowsX.IsConsistent) (hYcons : rowsY.IsConsistent)

/-! ### Consistency at the remaining-index cells -/

variable (hn : ∀ i : Cell X, ¬ X.scope i ⊆ Finset.univ.image e)

/-! ### The assembled properties -/

/-! ### The first bountifulness obligation: what the recoded rows force -/

/-- The constantly-`⊥` labelling respects every semantics on every lower set. -/
theorem respectsBelow_bot {ι₀ : Type*} [DecidableEq ι₀] {A₀ : Finset ι₀} {D₀ : CellScheme A₀}
    (sem : Semantics D₀) (BJ : Finset ι₀ × ℕ) :
    RespectsSemanticsBelow sem BJ (fun _ => (⊥ : ExtOrd)) :=
  RespectsSemanticsBelow.bot sem BJ


