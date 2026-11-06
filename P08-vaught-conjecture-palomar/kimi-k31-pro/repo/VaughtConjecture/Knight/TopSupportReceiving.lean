/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopSupport
public import VaughtConjecture.Knight.FiniteCutReceiving
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.PositiveNormalization

/-! # Receiving corollaries of the top-support criterion, conditional on finite-cut receiving

The reviewer's notes20 §3 / plan34 §3 (2026-09-19).  **Finite-cut receiving** (`FiniteCutReceiving`,
FC) is the hypothesis, stated small and consumer-facing: over every realized root, every legal
one-point candidate over it, and every proper cutoff below the stage, some actual coface on the
candidate's exact scheme agrees with the candidate below the cutoff.  Nothing here produces FC,
and no supply record or reference-context construction is presumed.

Two corollaries, both needing FC and exact parent consistency of the realization (so that the
returned coface retains the root's tops):

* **Unique admissible support ⇒ exact readback** (`exact_of_unique_topSupport`): if the whole
  top set is the only admissible support containing the root's tops, the candidate itself is
  realized.  The Notes19 candidate passes this test (`TopSupportRegression`).
* **Minimal admissible support ⇒ exact occurrence of its lowering**
  (`exact_of_minimal_topSupport`): for an inclusion-minimal admissible support `H` containing the
  root's tops, the uniform lowering `lowerType P H β` is realized exactly.

Neither realizes a desired nonminimal top pattern; that is the remaining difficulty
(plan34 §4), not addressed here.

**Quantifiers.**  FC is a single-stage, one-model statement with an arbitrary proper cutoff.
`OneBlockReadback` (the consumer banked in `OneBlockReadback`) is a two-model statement at block
stages with an exact upper-stage root and the fixed cutoff of the lower block.  FC for every model
at the upper block stage would give OBR, by taking the lower block stage as the cutoff and the
donor's actual coface as the candidate over the identical root; the converse is not established.
The two are documented as different quantifiers, not as logically independent.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Transform TopSupport

universe w

variable {α : LimitStage} {M : Type w} {m n : ℕ}

/-! ## The hypothesis -/

/-! ## Transport along equal domains -/

theorem SemScheme.castCell_castCell_symm {X Y : SemScheme n} (h : X = Y) (d : Cell Y.scheme) :
    SemScheme.castCell h (SemScheme.castCell h.symm d) = d := by
  subst h; rfl

/-- Respect transports along an equality of domains. -/
theorem respects_castCell {X Y : SemScheme n} (h : X = Y) {l : Cell X.scheme → ExtOrd}
    (hl : RespectsSemantics X.rows l) :
    RespectsSemantics Y.rows (fun d => l (SemScheme.castCell h.symm d)) := by
  subst h; exact hl

/-- Stage types with equal domains and labels are equal. -/
theorem StageType.eq_of_label {q P : S α.1 m} (h : q.scheme = P.scheme)
    (hl : ∀ d, q.label (SemScheme.castCell h.symm d) = P.label d) : q = P := by
  obtain ⟨sq, lq, bq, rq⟩ := q
  obtain ⟨sP, lP, bP, rP⟩ := P
  cases h
  have : lq = lP := funext hl
  subst this
  rfl

/-! ## Reading the FC output -/

theorem read_of_min_eq_of_lt {x y δ : ExtOrd} (h : min x δ = y) (hy : y < δ) : x = y := by
  by_cases hx : x ≤ δ
  · rwa [min_eq_left hx] at h
  · rw [min_eq_right (not_le.mp hx).le] at h
    exact absurd (h ▸ hy) (lt_irrefl _)

/-- A label below the cutoff is read back literally from agreement below the cutoff. -/
theorem label_eq_of_agree {q P : S α.1 m} (h : q.scheme = P.scheme) {δ : ExtOrd}
    (hagree : ∀ d, min (q.label d) δ = min (P.label (SemScheme.castCell h d)) δ)
    (d : Cell P.scheme.scheme) (hd : P.label d < δ) :
    q.label (SemScheme.castCell h.symm d) = P.label d := by
  obtain ⟨sq, lq, bq, rq⟩ := q
  obtain ⟨sP, lP, bP, rP⟩ := P
  cases h
  have := hagree d
  change min (lq d) δ = min (lP d) δ at this
  rw [min_eq_left hd.le] at this
  exact read_of_min_eq_of_lt this hd

/-- Every cell of a stage type on `n + 1` points has grade at most `n + 1`. -/
theorem grade_le_succ (P : S α.1 (n + 1)) (d : Cell P.scheme.scheme) :
    P.scheme.scheme.grade d ≤ n + 1 :=
  (CellScheme.grade_le_card_scope _ d).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _))

/-- The retained root tops of a coface: the root cells whose label is `⊤`. -/
def rootTops {p : S α.1 n} {P : S α.1 (n + 1)} (hP : IsCoface p P) : Set (Cell P.scheme.scheme) :=
  {c | ∃ d, c = hP.extendsDomain.cellOf d ∧ P.label c = ⊤}

/-! ## A proper cutoff above the proper labels always exists -/

theorem ordOf_bot : ordOf (⊥ : ExtOrd) = 0 := by grind [ordOf, ofOrd_ne_bot]

theorem ordOf_top : ordOf (⊤ : ExtOrd) = 0 := by grind [ordOf, ofOrd_ne_top]

/-- A proper cutoff below the stage and strictly above every proper label of a stage type. -/
theorem exists_proper_cutoff (P : S α.1 m) :
    ∃ δ : ExtOrd, ⊥ < δ ∧ δ < ofOrd α.1 ∧ ∀ d, P.label d ≠ ⊤ → P.label d < δ := by

  have h0 : (0 : Ordinal.{0}) < α.1 := by
    rw [← Ordinal.bot_eq_zero]; exact bot_lt_iff_ne_bot.mpr α.2.ne_bot
  let a : Ordinal.{0} := Finset.univ.sup fun d : Cell P.scheme.scheme => ordOf (P.label d)
  have ha : a < α.1 := by
    rw [Finset.sup_lt_iff h0]
    intro d _
    rcases ExtOrd.cases (P.label d) with h | h | ⟨s, h⟩
    · rw [h, ordOf_bot]; exact h0
    · rcases P.label_bound d with hd | hd
      · rw [h] at hd; exact absurd hd not_top_lt
      · rw [h, ordOf_top]; exact h0
    · rw [h, ordOf_ofOrd]
      rcases P.label_bound d with hd | hd
      · rwa [h, ofOrd_lt_ofOrd] at hd
      · rw [h] at hd; exact absurd hd (ofOrd_ne_top s)
  refine ⟨ofOrd (a + 1), bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _), ?_, ?_⟩
  · rw [ofOrd_lt_ofOrd, ← Order.succ_eq_add_one]; exact α.2.succ_lt ha
  · intro d hd
    rcases ExtOrd.cases (P.label d) with h | h | ⟨s, h⟩
    · rw [h]; exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
    · exact absurd h hd
    · rw [h, ofOrd_lt_ofOrd, ← Order.succ_eq_add_one, Order.lt_succ_iff]
      have := Finset.le_sup (f := fun d => ordOf (P.label d)) (Finset.mem_univ d)
      rwa [h, ordOf_ofOrd] at this

/-! ## The uniform lowering as a stage type -/

/-- The uniform lowering of a stage type, for `b < α` with `ofOrd b` visible at the point count
and above every proper label, and an admissible support. -/
noncomputable def lowerType (P : S α.1 (n + 1)) (H : Set (Cell P.scheme.scheme))
    {b : Ordinal.{0}} (hb : b < α.1) (hβ : SelfVis (n + 1) (ofOrd b))
    (hβgt : ∀ d, P.label d ≠ ⊤ → P.label d < ofOrd b)
    (hH : Admissible P.scheme.rows P.label H) : S α.1 (n + 1) where
  scheme := P.scheme
  label := lower P.label H (ofOrd b)
  label_bound d := by
    by_cases hd : P.label d = ⊤
    · by_cases hdH : d ∈ H
      · right; exact lower_of_mem hd hdH
      · left; rw [lower_of_not_mem hd hdH, ofOrd_lt_ofOrd]; exact hb
    · rw [lower_of_ne_top hd]; exact P.label_bound d
  respects := respects_lower P.respects (grade_le_succ P) hβ (ofOrd_ne_bot b) hβgt hH

/-- The lowering is a coface of the root when the root's tops are retained. -/
theorem isCoface_lowerType {p : S α.1 n} {P : S α.1 (n + 1)} (hP : IsCoface p P)
    {H : Set (Cell P.scheme.scheme)} {b : Ordinal.{0}} (hb : b < α.1)
    (hβ : SelfVis (n + 1) (ofOrd b)) (hβgt : ∀ d, P.label d ≠ ⊤ → P.label d < ofOrd b)
    (hH : Admissible P.scheme.rows P.label H) (hroot : rootTops hP ⊆ H) :
    IsCoface p (lowerType P H hb hβ hβgt hH) := by
  have hvis := hP.extendsDomain.visible
  have hp : P.restrictFace Fin.castSuccEmb hvis = p :=
    Option.some.inj ((typeMap_eq_some _ P hvis).symm.trans hP)
  unfold IsCoface
  rw [typeMap_eq_some Fin.castSuccEmb (lowerType P H hb hβ hβgt hH) hvis, ← hp]
  congr 1
  refine StageType.ext rfl (heq_of_eq (funext fun i => ?_))
  set c := CellScheme.restrictFace.toCell P.scheme.scheme Fin.castSuccEmb hvis i with hc
  change lower P.label H (ofOrd b) c = P.label c
  by_cases hi : P.label c = ⊤
  · rw [hi]
    apply lower_of_mem hi
    apply hroot
    exact ⟨SemScheme.castCell hP.extendsDomain.restrict i, rfl, hi⟩
  · exact lower_of_ne_top hi

/-! ## The two receiving corollaries -/

