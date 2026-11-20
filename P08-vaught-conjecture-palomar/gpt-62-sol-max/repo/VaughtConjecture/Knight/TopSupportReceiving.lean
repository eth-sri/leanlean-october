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

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd Transform TopSupport

universe w

variable {α : LimitStage} {m n : ℕ}

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
  aesop

theorem read_of_min_eq_of_lt {x y δ : ExtOrd} (h : min x δ = y) (hy : y < δ) : x = y := by grind

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

theorem ordOf_bot : ordOf (⊥ : ExtOrd) = 0 := by
  unfold ordOf
  rw [dite_eq_right]
  tauto

theorem ordOf_top : ordOf (⊤ : ExtOrd) = 0 := by
  unfold ordOf
  rw [dite_eq_right]
  rintro ⟨s, hs⟩
  exact ofOrd_ne_top s hs.symm

/-- A proper cutoff below the stage and strictly above every proper label of a stage type. -/
theorem exists_proper_cutoff (P : S α.1 m) :
    ∃ δ : ExtOrd, ⊥ < δ ∧ δ < ofOrd α.1 ∧ ∀ d, P.label d ≠ ⊤ → P.label d < δ := by
  classical
  have h0 : (0 : Ordinal.{0}) < α.1 := by
    rw [← Ordinal.bot_eq_zero]; exact bot_lt_iff_ne_bot.mpr α.2.ne_bot
  let a : Ordinal.{0} := Finset.univ.sup fun d : Cell P.scheme.scheme => ordOf (P.label d)
  have ha : a < α.1 := by
    rw [Finset.sup_lt_iff h0]
    intro d _
    rcases ExtOrd.cases (P.label d) with h | h | ⟨s, h⟩
    · rw [h, ordOf_bot]; exact h0
    · rcases P.label_bound d with hd | hd
      · simp_all
      · rw [h, ordOf_top]; exact h0
    · rw [h, ordOf_ofOrd]
      rcases P.label_bound d with hd | hd
      · simp_all
      · rw [h] at hd; simp_all
  refine ⟨ofOrd (a + 1), bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _), ?_, ?_⟩
  · rw [ofOrd_lt_ofOrd, ← Order.succ_eq_add_one]; exact α.2.succ_lt ha
  · intro d hd
    rcases ExtOrd.cases (P.label d) with h | h | ⟨s, h⟩
    · simp_all
    · exact absurd h hd
    · rw [h, ofOrd_lt_ofOrd, ← Order.succ_eq_add_one, Order.lt_succ_iff]
      have := Finset.le_sup (f := fun d => ordOf (P.label d)) (Finset.mem_univ d)
      rwa [h, ordOf_ofOrd] at this

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

end VaughtConjecture.Knight
