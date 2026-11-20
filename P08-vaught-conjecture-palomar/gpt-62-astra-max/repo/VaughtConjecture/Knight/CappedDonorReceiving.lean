/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSelector

/-! # The gated receiving-input family and both original-state fibres (notes32 §§4–6)

The reviewer's notes32 §§4–6 (audit5 §§3–5) on the coherent capped-donor selector of
`Knight/CappedDonorSelector.lean`: a **constructed family of receiving inputs** — states of the
request scheme `P` and the private scheme `C` at every numerical cutoff `j`, with a free
grade-one gate and numerical persistent shadow fields — and **both original-state fibres**,
proved from the unchanged old bountifulness of `P` and `C` alone.  This is the receiving-input
side only; the physical (legal-probe) realization of notes32 §7 is not here.

**Effective grades.**  At cutoff `j` the present fields of `P` are its lower set
`effP nP j = (univ, min j (nP + 1))` and those of `C` (arity `J ≥ N`) are
`effC J j = (univ, min j J)`; the cap (grade `N`) is present exactly when `N ≤ j`, and then the
cap's lower domain `Low` — the acquisition face's cells of grade at most `N` — is present
(`capLe`); the private cells above grade `N` are present only from their own grade on.  A
section at such a cutoff restricts to the cap's lower domain (`lowC`), which is all the selector
reads.  Caps are
permissible at a scheme's *own* effective grade: an `N`-visible cut is permissible for `P`
because every grade of `P` is below `N` (`selfVis_effP_of_N`); the external cap `γ` is
`j`-visible, hence visible at every present grade, including those above `N`.

**States** (`State j`): lawful current numerical sections `u` of `effP nP j` and `v` of
`effC J j`, the grade-one gate, and **numerical persistent shadows** `shadowP`, `shadowC` —
`1`-visible values for *every* field, present or future (**future-field visibility**).

**The filtered literal face** (newapproach2 §3.1).  The common face `(A, KA)` is the literal
root, of any arity `KA ≥ 0`; at cutoff `j` its **present portion** is the grade-`≤ j` part, and
admissibility demands the two numerical sections to agree on it **at every cutoff**
(`Admissible.face`, through `reqFace`/`privFace`) — not only once the whole face is present.
For `KA > K` this is what lets the low-reference repairs (`CappedDonorRetarget`,
`CappedDonorRelease`) control the already-present high-grade root values.  Installing a face
prescription (`exists_installP`, `exists_installC`) is old bountifulness on the present lower set
`(A, min KA j)` (`faceSec`, `faceCSec`), through the equal-index form
`Semantics.IsBountiful.extend`; an empty present portion (empty root, or `j = 0`) needs no
extension call.
**Admissibility** (`Admissible`): both sections lawful; the whole common face literal whenever
it is present; gate and shadows `1`-visible; each present field's shadow has the field's
numerical support; the finite support guard (11) — a positive gate and cap shadow force positive
reference shadows and the donor's support on the request fields; and the numerical relation
(10), **only when the cap is present**, the gate is positive and the cap is positive:

    u ∧ cut v = sel v        on every request cell.

A positive future cap shadow never forces a positive numerical cap before grade `N`.

**The fibres.**  Both retain the entire common face, every original cap coordinate, and the
**cap receipts** of the gate and of every shadow (`CapReceipts`: agreement below the comparison
cap); at a positive cap the gate and every shadow are retained literally:

* `exists_private_lift` (§5): for an independently lawful private prescription `v₁` agreeing
  with `v` below a permissible `γ`, there is an admissible state with `v₁` literally and `u`
  retained below `γ`.  Two cases when active: `cut v₁ ≤ γ` uses old `P`-bountifulness at `γ`
  from the old ambient `u`; `γ < cut v₁` uses old `P`-bountifulness at `cut v₁` from the lawful
  ambient `sel v₁` with the exact face prescription, whose compatibility hypothesis is the
  capped-donor boundary (7).
* `exists_request_lift` (§6): for a lawful request prescription `u₁` agreeing with `u` below
  `γ`, old `C`-bountifulness installs the face and **clipping every private coordinate of grade
  at least `N` at `γ`** (`clip`, lawful by grade-sensitive capping) restores the relation
  through the clip identities of the selector.
* **Bottom cap** (`offState`): at `γ = ⊥` the gate is switched off and the shadows of the
  present fields recomputed as the `1`-visible roundings of the new values (the future shadows
  are retained); the relation and the guard are then vacuous.  At a positive cap an already
  positive gate is never switched off (the persistence lemma `admissible_persist`).

The **empty block list** needs no representative: the selector is then identically bottom and
the relation is vacuous (`Ref.sel_of_isEmpty`).  The actual pair with the gate on is admissible
at every cutoff (`actual_admissible`), by `sel vact = p ∧ cut vact`.  All old extension calls
are inside the unchanged `P` and `C`; no new-domain bountifulness is an input. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

/-! ## Bountifulness with equal indices -/

/-- Bountifulness with the source index allowed to equal the target index. -/
theorem Semantics.IsBountiful.extend {ι : Type*} [DecidableEq ι] {A}
    {D : CellScheme A} {sem} (hb : sem.IsBountiful) {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan) (h : GradedLe CI BJ)
    {p} {q} {γ}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hcompat : CappedEq (q ∘ CellScheme.below.mono h) p γ) :
    ∃ q', RespectsSemanticsBelow sem BJ q' ∧
      CappedEq q' q γ ∧
      ∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d := by
  by_cases heq : CI = BJ
  · subst heq
    exact ⟨p, hp, fun d => (hcompat d).symm, fun _ => rfl⟩
  exact hb CI BJ hCI hBJ h heq p q γ hp hq hγ hcompat

namespace CappedDonor

/-! ## Effective cutoffs -/

/-- The present request fields at cutoff `j`. -/
def effP (nP j : ℕ) : Finset (Fin (nP + 1)) × ℕ := (Finset.univ, min j (nP + 1))

/-- The present private fields at cutoff `j`. -/
def effC (J j : ℕ) : Finset (Fin J) × ℕ := (Finset.univ, min j J)

/-- Native occurrences, clipping the requested grade to the carrier arity. -/
abbrev _root_.VaughtConjecture.Knight.SemScheme.ClippedCells {n : ℕ} (S : SemScheme n) (j : ℕ) :=
  S.scheme.below (effC n j)

section Cutoffs

variable {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

theorem effP_mem {j} (hj : 0 < j) : effP nP j ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨P.scheme.isPlan.domain_mem, lt_min hj (Nat.succ_pos _), by
    change min j (nP + 1) ≤ Finset.univ.card
    simp⟩

theorem gradeC_le d : C.scheme.grade d ≤ J :=
  (C.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (C.scheme.scope d))

theorem effC_mem {j} (hj : 0 < j) (hJ : 0 < J) : effC J j ∈ Plan.gradedPlan C.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨C.scheme.isPlan.domain_mem, lt_min hj hJ, by
    change min j J ≤ Finset.univ.card
    simp⟩

end Cutoffs

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## Effective grades relative to the reference data -/

include R in
/-- An `N`-visible cut is permissible at the request scheme's own effective grade. -/
theorem selfVis_effP_of_N j {β} (hβ : SelfVis N β) : SelfVis (effP nP j).2 β :=
  hβ.mono ((min_le_right _ _).trans R.arity_lt.le)

/-! ## The present portion of the face -/

/-- A face cell present at cutoff `j` as a present request field. -/
def reqFace {j} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (effP nP j) :=
  ⟨a.1, ⟨Finset.subset_univ _, le_min h (gradeP_le a.1)⟩⟩

/-- The private copy of a face cell present at cutoff `j` as a present private field. -/
def privFace {j} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    C.scheme.below (effC J j) :=
  ⟨(R.face a).1, ⟨Finset.subset_univ _, le_min ((R.face_grade a).trans_le h) (gradeC_le _)⟩⟩

theorem face_le_effC {j} : GradedLe (R.A', min R.KA j) (effC J j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (R.KA_lt_N.le.trans R.N_le))⟩

/-! ## States and admissibility -/

/-! ## Cap receipts, persistence at a positive cap, and the bottom-cap state -/

/-! ## Installing a face prescription by old bountifulness -/

/-- Old `P`-bountifulness installs a lawful private face prescription into a request section at
a permissible cap, on the present portion of the face; nothing is done when that portion is
empty. -/
theorem exists_installP {j} {u}
    (hu : P.rows.Lawful u)
    {v₁} (hv₁ : C.rows.Lawful v₁)
    {γ} (hγ : SelfVis (effP nP j).2 γ)
    (hcompat : ∀ a (h : P.scheme.grade a.1 ≤ j),
      min (u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ) :
    ∃ u₁, P.rows.Lawful u₁ ∧
      CappedEq u₁ u γ ∧
      ∀ a (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v₁ (R.privFace a h) := by
  by_cases hk : 0 < min R.KA j
  · obtain ⟨u₁, hu₁, hcap, hface⟩ := P.bountiful.extend (Plan.mem_gradedPlan.mpr ⟨R.A_mem, hk, (min_le_left _ _).trans R.KA_le_card⟩)
      (effP_mem (hk.trans_le (min_le_right _ _))) ⟨Finset.subset_univ (R.A, min R.KA j).1, le_min (min_le_right R.KA j) (LE.le.trans (min_le_left R.KA j) (KA_le R))⟩ ((R.faceAt_respects (min_le_left _ _) _).mp (hv₁.mono R.face_le_effC)) hu hγ
      (fun a => hcompat (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))
    exact ⟨u₁, hu₁, hcap, fun a h => hface ⟨a.1, ⟨a.2.1, le_min a.2.2 h⟩⟩⟩
  · exact ⟨u, hu, fun _ => rfl, fun a h => (hk (lt_min ((P.scheme.grade_pos a.1).trans_le a.2.2) ((P.scheme.grade_pos a.1).trans_le h))).elim⟩

/-! ## Clipping the coordinates of grade at least `N` -/

/-! ## The private-context-prescribed fibre (notes32 §5) -/

/-! ## The request-prescribed fibre (notes32 §6) -/

/-! ## The actual state -/

end Ref

end CappedDonor

end VaughtConjecture.Knight
