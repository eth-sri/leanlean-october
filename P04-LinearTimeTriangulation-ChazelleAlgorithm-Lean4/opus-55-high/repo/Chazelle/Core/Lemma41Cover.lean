module

public import Chazelle.MacT
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Infix
public import Mathlib.Order.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Field.GeomSum
public import Chazelle.Spec
public import Std.Data.HashMap
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.LocallyConvex.Separation

namespace Chazelle.Core.L41
@[expose] public section
def GradeOK (b x g : ℕ) : Prop := 2 ^ g ∣ x ∧ x + 2 ^ g ≤ b
instance (b x g : ℕ) : Decidable (GradeOK b x g) := by unfold GradeOK; infer_instance

/-- **The greedy grade**: the largest `g ≤ λ - 1` with `2^g ∣ x` and `x + 2^g ≤ b`. -/
def nextG (lam b x : ℕ) : ℕ := Nat.findGreatest (GradeOK b x) ztma
theorem gradeOK_zero {b x : ℕ} (h : x < b) : GradeOK b x 0 := ⟨by_simp, by_omega⟩
theorem gradeOK_mono {b x g g' : ℕ} (h : GradeOK b x g) (hg : g' ≤ g) : GradeOK b x g' :=
  ⟨(Nat.pow_dvd_pow 2 hg).trans h.1, by
    have := Nat.pow_le_pow_right ztciz hg; have := h.2; omega⟩
variable {lam b x : ℕ}
theorem nextG_spec (h : x < b) : GradeOK b x (nextG lam b x) :=
  Nat.findGreatest_spec (P := GradeOK b x) ztbg (gradeOK_zero h)
theorem nextG_le (lam b x : ℕ) : nextG lam b x ≤ lam - 1 := Nat.findGreatest_le _
theorem le_nextG {lam b x g : ℕ} (hg : g ≤ lam - 1) (h : GradeOK b x g) : g ≤ nextG lam b x :=
  Nat.le_findGreatest hg h

/-- The greedy grade is maximal. -/
theorem not_gradeOK_succ (hl : nextG lam b x + 1 ≤ lam - 1) :
    ¬ GradeOK b x (nextG lam b x + 1) := fun h => by
  have := le_nextG hl h; omega

/-- **The greedy cover** of `[x, b]` (pieces `(grade, start)`). -/
def cover (lam b x : ℕ) : List ztw :=
  if h : x < b then ztfie :: cover lam b zteay else []
termination_by b - x
decreasing_by have := Nat.one_le_two_pow (n := nextG lam b x); omega
theorem cover_of_lt (h : x < b) :
    cover lam b x = ztfie :: cover lam b zteay := by
  rw [cover, dite_eq_left h]
theorem cover_of_ge (h : b ≤ x) : cover lam b x = [] := by
  rw [cover, dite_eq_right by_omega]

/-- Induction along the cover (on `b - x`). -/
theorem cover_ind {b : ℕ} {Pr : ℕ → Prop}
    (h : ∀ x, (∀ y, b - y < b - x → Pr y) → Pr x) (x : ℕ) : Pr x := by
  suffices H : ∀ d x, b - x = d → Pr x from H _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih => intro x hx; exact h x (fun y hy => ih (b - y) by_omega y rfl)
theorem step_lt (h : x < b) : b - zteay < b - x := by
  grind

/-- **The pieces are aligned full chains** inside `[x, b]`. -/
theorem mem_cover {lam b : ℕ} (x : ℕ) : ∀ q ∈ cover lam b x,
    q.1 ≤ lam - 1 ∧ 2 ^ q.1 ∣ q.2 ∧ x ≤ q.2 ∧ q.2 + 2 ^ q.1 ≤ b := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    zuco
    zubfn
    · rw [cover_of_lt hx] at hq
      zujcq
      · have := nextG_spec (lam := lam) hx
        exact ⟨nextG_le _ _ _, this.1, le_rfl, this.2⟩
      grind
    · rw [cover_of_ge by_omega] at hq; simp_all

/-- **The pieces tile `[x, b]`.** -/
theorem cover_sum {lam b : ℕ} (x : ℕ) :
    ((cover lam b x).map fun q => 2 ^ q.1).sum = b - x := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    zubfn
    · rw [cover_of_lt hx, List.map_cons, List.sum_cons, ih _ ztqxa]
      have := (nextG_spec (lam := lam) hx).2; grind
    · rw [cover_of_ge by_omega]; simp_all

/-- The descending phase: from a position aligned to `2^h` with less than `2^h` to go, at most
`h` pieces. -/
theorem cover_length_desc {lam b : ℕ} (h : ℕ) : ∀ x, h ≤ lam → 2 ^ h ∣ x → b - x < 2 ^ h →
    (cover lam b x).length ≤ h := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    zulnn
    zubfn
    · zujhq
      zufi

      have hgh : g < h := by
        zukr
        have := Nat.pow_le_pow_right ztciz ztwap
        have := hs.2; omega
      have hrest : ztxfg := by
        zukr
        have hgh1 : ztsim := by
          by_contra hc2
          have := Nat.pow_le_pow_right ztciz ztwaq
          omega
        have hok : ztbabv := by
          refine ztlux
          omega
        have := le_nextG (lam := lam) by_omega hok
        omega
      have := ih g hgh ztqo by_omega zttat hrest
      omega
    · zuczq

/-- The ascending phase. -/
theorem cover_length_asc {lam b : ℕ} (hl : 1 ≤ lam) (x : ℕ) : ∀ h, h < lam → 2 ^ h ∣ x →
    b - x ≤ 2 ^ lam → (cover lam b x).length ≤ 2 * lam - h := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    zulmq
    zubfn
    · zujhq
      zufi

      zudhp
      zuhyk
      zugjf
      · zukfd
        have := cover_length_desc (lam := lam) (b := b) g ztqo by_omega hd' hr
        omega
      · zubhq
        zugjg
        · have hnd : ztzjn := fun hc => not_gradeOK_succ (lam := lam) (b := b)
            (x := x) hB ztuhh
          have hhg : h ≤ g := by
            zukr
            exact hnd ztmye
          zuicx
          have hodd : ztsjx := by
            zukr
            zudmb

          have hd2 : ztyld := by
            zuekl

          zufgr

          have := ih ztqo ztqxa ztbs hglt hd2 hb'
          omega
        · zukcg
          have e2 : ztmsq := by
            grind
          zudve

          · grind
          · zucda

            have hng : ztzjm := by
              zucvp

            zujjp
            grind
    · zuczq

/-- **At most `2λ` pieces.** -/
theorem cover_length_le (hl : 1 ≤ lam) (hb : b - x ≤ 2 ^ lam) :
    (cover lam b x).length ≤ 2 * lam := by
  have := cover_length_asc (b := b) hl x 0 by_omega by_simp hb
  omega
open Finset
variable {lam b : ℕ} (f : ℕ → ℕ)
/-- The descending phase. -/
theorem cover_weight_desc (h : ℕ) : ∀ x, h ≤ lam → 2 ^ h ∣ x →
    b - x < 2 ^ h → ((cover lam b x).map fun q => f q.1).sum ≤ ∑ g ∈ range h, f g := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    zulnn
    zubfn
    · zuhkv
      zufi

      have hgh : g < h := by
        zukr
        have := Nat.pow_le_pow_right ztciz ztwap
        have := hs.2; omega
      have hrest : ztxfg := by
        zukr
        have hgh1 : ztsim := by
          by_contra hc2
          have := Nat.pow_le_pow_right ztciz ztwaq
          omega
        have hok : ztbabv := by
          refine ztlux
          omega
        have := le_nextG (lam := lam) by_omega hok
        omega
      have := ih g hgh ztqo by_omega zttat hrest
      have hsub : ∑ k ∈ range ztbs, f k ≤ ∑ k ∈ range h, f k :=
        Finset.sum_le_sum_of_subset ztmbc
      rw [Finset.sum_range_succ] at hsub
      grind
    · zuczq

/-- The ascending phase. -/
theorem cover_weight_asc (hl : 1 ≤ lam) (x : ℕ) : ∀ h, h < lam →
    2 ^ h ∣ x → b - x ≤ 2 ^ lam → ((cover lam b x).map fun q => f q.1).sum ≤
      ∑ g ∈ Ico h lam, f g + ∑ g ∈ range lam, f g := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    zulmq
    zubfn
    · zuhkv
      zufi

      zudhp
      zuhyk
      have hle : ∑ k ∈ range ztbs, f k ≤ ∑ k ∈ range lam, f k :=
        Finset.sum_le_sum_of_subset ztmbc
      rw [Finset.sum_range_succ] at hle
      zubvt
      zugjf
      · zukfd
        have := cover_weight_desc (lam := lam) (b := b) f g ztqo by_omega hd' hr
        omega
      · zubhq
        zugjg
        · have hnd : ztzjn := fun hc => not_gradeOK_succ (lam := lam) (b := b)
            (x := x) hB ztuhh
          have hhg : h ≤ g := by
            zukr
            exact hnd ztmye
          zuicx
          have hodd : ztsjx := by
            zukr
            zudmb

          have hd2 : ztyld := by
            zuekl

          zufgr

          have := ih ztqo ztqxa ztbs hglt hd2 hb'
          have hI : ∑ k ∈ Ico g lam, f k = f g + ∑ k ∈ Ico ztbs lam, f k :=
            Finset.sum_eq_sum_Ico_succ_bot by_omega _
          have hI2 : ∑ k ∈ Ico g lam, f k ≤ ∑ k ∈ Ico h lam, f k :=
            Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_left hhg)
          omega
        · zukcg
          have e2 : ztmsq := by
            grind
          zudve

          · grind
          · zucda

            have hng : ztzjm := by
              zucvp

            zujjp
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
            have hI : f g ≤ ∑ k ∈ Ico h lam, f k := by
              have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
                (show g ∈ Ico h lam by simp only [Finset.mem_Ico]; omega)
              omega
            omega
    · zuczq

/-- **At most two pieces per grade.** -/
theorem cover_weight_le {lam b x : ℕ} (f : ℕ → ℕ) (hl : 1 ≤ lam) (hb : b - x ≤ 2 ^ lam) :
    ((cover lam b x).map fun q => f q.1).sum ≤ 2 * ∑ g ∈ range lam, f g := by
  have := cover_weight_asc (b := b) f hl x 0 by_omega by_simp hb
  have hI : ∑ g ∈ Ico 0 lam, f g = ∑ g ∈ range lam, f g := by_simp
  omega
theorem clog_le_of_le_two_mul {j lam : ℕ} (hj : j ≤ 2 * lam) :
    Nat.clog 2 j ≤ Nat.clog 2 lam + 1 := by
  zudwq
  have := Nat.le_pow_clog (b := 2) by_norm_num lam
  omega
end
end Chazelle.Core.L41
namespace Chazelle.Core.BuildStack
@[expose] public section
open List

/-- One step of the stack pass: pop if `x` is on top, push otherwise. -/
def step (st : List ℕ) (x : ℕ) : List ℕ := if st.head? = some x then st.tail else x :: st

/-- The stack after reading `u`. -/
def run (u : List ℕ) : List ℕ := u.foldl step []

/-- The chords open after `u` (exactly one occurrence in `u`), the latest opened first. -/
def openList (u : List ℕ) : List ℕ := u.reverse.filter (fun x => decide (u.count x = 1))

/-- Every letter of `w` occurs exactly twice. -/
def Twice (w : List ℕ) : Prop := ∀ x ∈ w, w.count x = 2

/-- **A parenthesis word**: no pattern `i … j … i … j` with `i ≠ j`. -/
def NoCross (w : List ℕ) : Prop := ∀ i j, i ≠ j → ¬ [i, j, i, j] <+ w

/-- The label of the gap after the first `m` letters: the innermost open chord (`none`: the root
region). -/
def label (w : List ℕ) (m : ℕ) : Option ℕ := (run ztibp).head?
theorem run_snoc (u : List ℕ) (x : ℕ) : run ztpen = step (run u) x := by
  simp [run, List.foldl_append]
variable {u : List ℕ} {x : ℕ} {w : List ℕ}
theorem mem_openList : x ∈ openList u ↔ u.count x = 1 := by
  zumtt
  grind

/-- **An opening event pushes.** -/
theorem openList_snoc_open (hx : u.count x = 0) :
    openList (u ++ [x]) = x :: openList u := by
  zumtt
  rw [reverse_append, reverse_singleton, singleton_append, filter_cons,
    ite_eq_left by_simp_all]
  zucr
  zuldd
  grind

/-- **A closing event pops**: if `x` occurs once in `u` and is the latest open chord, reading it
again removes it. -/
theorem openList_snoc_close {rest : List ℕ} (hx : u.count x = 1)
    (hlist : openList u = x :: rest) : openList ztpen = rest := by
  have hxu : x ∈ u.reverse := by_grind
  obtain ⟨a, b, hab⟩ := List.append_of_mem hxu
  have hcnt : u.reverse.count x = 1 := by_grind
  rw [hab, count_append, count_cons_self] at hcnt
  have hxa : x ∉ a := by_grind
  have hxb : x ∉ b := by_grind
  unfold openList at hlist ⊢
  rw [hab, filter_append, filter_cons, ite_eq_left by_simp_all] at hlist
  -- the part before `x` contributes nothing
  have ha : a.filter ztkwh = [] := by
    rcases hfa : a.filter ztqok with _ | ⟨z, zs⟩
    · rfl
    · exfalso
      rw [hfa, cons_append, cons.injEq] at hlist
      have hz : z ∈ a := mem_of_mem_filter (by rw [hfa]; simp)
      simp_all
  rw [ha, nil_append, cons.injEq] at hlist
  rw [reverse_append, reverse_singleton, singleton_append, filter_cons,
    ite_eq_right by_grind, hab, filter_append, filter_cons,
    ite_eq_right by_grind, ← hlist.2]
  have hcongr : ∀ l : List ℕ, x ∉ l →
      l.filter (fun y => decide ((u ++ [x]).count y = 1)) =
        l.filter ztkwh := by
    intro l hl
    zuldd
    grind
  simp_all

/-- The latest open chord of a prefix, when the next letter closes a chord: in a parenthesis
word, it is that chord. -/
theorem head_openList {w u v : List ℕ} (htw : Twice w) (hnc : NoCross w) {x : ℕ}
    (hw : w = u ++ [x] ++ v) (hx : u.count x = 1) : ∃ rest, openList u = x :: rest := by
  have hxo := mem_openList.2 hx
  rcases hlist : openList u with _ | ⟨y, rest⟩
  · simp_all
  · refine ⟨rest, ?_⟩
    zuct
    have hyx : y ≠ x := by_simp_all
    have hxr : x ∈ rest := by
      grind
    have hy1 : u.count y = 1 := mem_openList.1 by_simp_all
    -- `x` then `y` in `u`
    have h1 : [y, x] <+ u.reverse := by
      have : [y, x] <+ openList u := by
        simp_all
      exact this.trans filter_sublist
    have h1' : [x, y] <+ u := by simpa using h1.reverse
    -- `y` occurs again after the current `x`
    have hyw := htw y by_grind
    have hyv : y ∈ v := by
      grind
    have h2 : [x, y] <+ [x] ++ v := by_simp_all
    exact hnc x y (Ne.symm hyx) (by zuolq; exact h1'.append h2)

/-- **The stack is the list of open chords** on every prefix of a parenthesis word. -/
theorem run_eq_openList (htw : Twice w) (hnc : NoCross w) :
    ∀ {u : List ℕ}, u <+: w → run u = openList u := by
  zulnl
  induction u using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton u x ih =>
    intro hu
    obtain ⟨v, hv⟩ := hu
    have ih' := ih by_grind
    rw [run_snoc, ih']
    have hxw : w.count x = 2 := htw x by_grind
    have hcx : u.count x ≤ 1 := by
      grind
    rcases Nat.lt_or_ge (u.count x) 1 with h0 | h1
    · have h0' : u.count x = 0 := by_omega
      rw [openList_snoc_open h0']
      unfold step
      zucjw
      zuq
      have := mem_openList.1 (mem_of_mem_head? h)
      omega
    · have h1' : u.count x = 1 := by_omega
      obtain ⟨rest, hrest⟩ := head_openList htw hnc (hv.symm.trans by_rfl) h1'
      rw [openList_snoc_close h1' hrest, hrest]
      unfold step
      simp

/-- **The stack is empty at the end** of a parenthesis word. -/
theorem run_eq_nil (htw : Twice w) (hnc : NoCross w) : run w = [] := by
  rw [run_eq_openList htw hnc (prefix_refl w)]
  zumtt
  zummi
  zuh
  rw [mem_reverse] at hx
  simp [htw x hx]

/-- The label of a gap is the head of the open list. -/
theorem label_eq (htw : Twice w) (hnc : NoCross w) (m : ℕ) :
    label w m = (openList ztibp).head? := by
  unfold label
  rw [run_eq_openList htw hnc by_grind]

/-- Equal open sets give equal open lists (for two prefixes of one word). -/
theorem openList_eq_of_prefix {u u' : List ℕ} (h : u <+: u')
    (hiff : ∀ i, (u.count i = 1 ↔ u'.count i = 1)) : openList u = openList u' := by
  obtain ⟨v, rfl⟩ := h
  zumtt
  rw [reverse_append, filter_append]
  have hv : v.reverse.filter (fun x => decide ((u ++ v).count x = 1)) = [] := by
    zummi
    grind
  simp_all

/-- If `j` is open after `u` and below the latest open chord `i`, then `j` occurs before `i` in
`u`. -/
theorem sublist_of_openList {i j : ℕ} {rest : List ℕ} (h : openList u = i :: rest)
    (hj : j ∈ rest) : [j, i] <+ u := by
  have : [i, j] <+ u.reverse := by
    have : [i, j] <+ openList u := by_simp_all
    exact this.trans filter_sublist
  grind

/-- One direction of `label_eq_iff`, for a chord open at `m` but not at `m'`. -/
theorem label_ne_aux (htw : Twice w) (hnc : NoCross w) {m m' : ℕ} {j : ℕ}
    (hj : (w.take m).count j = 1) (hj' : (w.take m').count j ≠ 1) :
    (openList ztibp).head? ≠ (openList ztwhr).head? := by
  zudii
  have hjo : j ∈ openList _ := mem_openList.2 hj
  rcases hl : openList ztibp with _ | ⟨i, rest⟩
  · simp_all
  zvnen at heq
  rcases hl' : openList ztwhr with _ | ⟨i', rest'⟩
  · simp_all
  rw [hl', head?_cons, head?_cons, Option.some.injEq] at heq
  zufpx
  have hi' : ztoqg := mem_openList.1 by_simp_all
  have hji : j ≠ i := by_grind
  have hjr : j ∈ rest := by
    simp_all
  have hsub := sublist_of_openList hl hjr
  have hi1 : (w.take m).count i = 1 := mem_openList.1 by_simp_all
  rcases le_total m' m with hle | hle
  · -- `m' ≤ m`: `j` does not occur before `m'`, but `i` does, and `j` precedes `i`
    obtain ⟨z, hz⟩ : ztlcf :=
      ⟨(w.drop m').take _, by zunca⟩
    have hj0 : (w.take m').count j = 0 := by
      grind
    rw [hz, count_append, hi'] at hi1
    zvncr at hsub
    obtain ⟨l1, l2, heq, h1, h2⟩ := List.sublist_append_iff.1 hsub
    rcases l1 with _ | ⟨a, l1⟩
    · grind
    grind
  · -- `m ≤ m'`: `j` closes between `m` and `m'`, `i` after `m'`: a crossing
    obtain ⟨z, hz⟩ : ztlcg :=
      ⟨(w.drop m).take _, by zunca⟩
    have hiz : z.count i = 0 := by_simp_all
    have hjz : j ∈ z := by
      grind
    have hiw := htw i by_grind
    have hw : w = w.take m ++ z ++ w.drop m' := by rw [← hz, take_append_drop]
    have hiy : i ∈ w.drop m' := by
      grind
    have h2 :=
      (singleton_sublist.2 hjz).append (singleton_sublist.2 hiy)
    exact hnc j i hji (by zuolq; exact hsub.append h2)

/-- **Two gaps get the same label iff no chord separates them** (every chord is open at both or
at neither). -/
theorem label_eq_iff (htw : Twice w) (hnc : NoCross w) (m m' : ℕ) :
    label w m = label w m' ↔ ∀ i, ((w.take m).count i = 1 ↔ (w.take m').count i = 1) := by
  rw [label_eq htw hnc, label_eq htw hnc]
  constructor
  · intro h i
    zuct
    by_cases hA : (w.take m).count i = 1
    · have hB : (w.take m').count i ≠ 1 := by_omega
      exact label_ne_aux htw hnc hA hB h
    · have hB : ztoqg := by
        omega
      exact label_ne_aux htw hnc hB hA h.symm
  · zuq
    zuiel
    · obtain ⟨z, hz⟩ : ztlcg :=
        ⟨(w.drop m).take _, by zunca⟩
      rw [openList_eq_of_prefix by_simp_all h]
    · obtain ⟨z, hz⟩ : ztlcf :=
        ⟨(w.drop m').take _, by zunca⟩
      rw [openList_eq_of_prefix by_simp_all (fun i => (h i).symm)]
end
end Chazelle.Core.BuildStack
namespace Chazelle.Core
@[expose] public section
namespace ShootCut
theorem pow_succ' (g : ℕ) : 2 ^ ztbs = 2 * 2 ^ g := by_omega

/-! ## Downward -/

/-! ## Blocks of a tiling lie in the interval -/
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core.SortL
@[expose] public section
def seg (m : ℕ → ℕ) (a n : ℕ) : List ℕ := (List.range n).map fun i => m zteon
variable {m m' : ℕ → ℕ} {a n : ℕ}

/-- A segment has the requested length. -/
@[simp] theorem seg_length : (seg m a n).length = n := by simp [seg]

/-- The empty segment. -/
@[simp] theorem seg_zero : seg m a 0 = [] := rfl

/-- Reading a segment from its first word. -/
theorem seg_succ : seg m a ztkk = m a :: seg m ztdf n := by
  zuhav
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  zucr
  zucfh
  grind

/-- A segment splits at any point. -/
theorem seg_add (n₁ n₂ : ℕ) : seg m a (n₁ + n₂) = seg m a n₁ ++ seg m (a + n₁) n₂ := by
  induction n₁ generalizing a with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + n₂ = (k + n₂) + 1 by omega, seg_succ, ih, seg_succ,
      show a + 1 + k = a + zts by omega]
    simp only [List.cons_append]

/-- Reading a segment from its last word. -/
theorem seg_snoc : seg m a ztkk = seg m a n ++ [m ztteh] := by
  rw [seg_add n 1, seg_succ]
  simp

/-- Segments agree when the memories agree on them. -/
theorem seg_congr (h : ∀ i, i < n → m zteon = m' zteon) : seg m a n = seg m' a n := by
  zuhav
  simp_all

/-- Dropping the first words of a segment. -/
theorem seg_drop (d : ℕ) : (seg m a n).drop d = seg m (a + d) ztttv := by
  induction d generalizing a n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [seg_succ, List.drop_succ_cons, ih]
      zucr
      · omega
      · omega

/-- Taking the first words of a segment. -/
theorem seg_take (d : ℕ) : (seg m a n).take d = seg m a (min d n) := by
  induction d generalizing a n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [seg_succ, List.take_succ_cons, ih, show min zts ztkk = min k n + 1 by omega,
        seg_succ]

/-- The words of a segment. -/
theorem seg_getD (i : ℕ) (hi : i < n) : (seg m a n).getD i 0 = m zteon := by
  simp [seg, hi]

/-- A segment written one word past its end. -/
theorem seg_upd_end (v : ℕ) (f : ℕ → ℕ)
    (hf : ∀ x, f x = if x = a + n then v else m x) :
    seg f a ztkk = seg m a n ++ [v] := by
  rw [seg_snoc, hf ztteh, ite_eq_left rfl]
  zucr
  apply seg_congr
  grind

/-! ## One pass of the bottom-up merge sort -/
variable {α : Type} (le : α → α → Bool)

/-- **One merge pass** with run width `w`: merge the blocks `[2tw, 2tw + w)` and
`[2tw + w, 2tw + 2w)`, for `t = 0, 1, …`. -/
def mpass (w : ℕ) (l : List α) : List α :=
  if _h : w = 0 ∨ l = [] then l
  else List.merge ztjzx ztfef le ++ mpass w ztzgi
termination_by l.length
decreasing_by
  simp only [not_or] at _h
  have h1 : l.length ≠ 0 := by_simp_all
  simp only [List.length_drop]
  omega
variable {le}

/-- A pass of width `0` does nothing. -/
theorem mpass_zero (l : List α) : mpass le 0 l = l := by
  zukxt

/-- A pass of the empty list. -/
theorem mpass_nil (w : ℕ) : mpass le w ([] : List α) = [] := by
  zukxt
variable {w : ℕ} {l : List α}
/-- The defining equation of a pass on a nonempty list. -/
theorem mpass_eq (hw : 0 < w) (hl : l ≠ []) :
    mpass le w l = List.merge ztjzx ztfef le ++ mpass le w ztzgi := by
  rw [mpass, dite_eq_right_iff.mpr]
  grind

/-- A list is its first block, its second block and the rest. -/
theorem take_append_take_drop (w : ℕ) (l : List α) :
    l.take w ++ (l.drop w).take w ++ l.drop ztyx = l := by
  rw [List.append_assoc, show 2 * w = w + w by omega, ← List.drop_drop, List.take_append_drop,
    List.take_append_drop]

/-- **A pass is a permutation.** -/
theorem mpass_perm (w : ℕ) (l : List α) : (mpass le w l).Perm l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [mpass_zero]
    by_cases hl : l = []
    · subst hl; rw [mpass_nil]
    rw [mpass_eq hw hl]
    have hlen : (l.drop ztyx).length < n := by
      have : l.length ≠ 0 := by_grind
      grind
    have h1 := (List.merge_perm_append le (xs := l.take w) (ys := (l.drop w).take w)).append
      (ih _ hlen ztzgi rfl)
    exact h1.trans (by rw [take_append_take_drop])

/-- The first block of a pass has length `min (2 w) |l|`. -/
theorem merge_block_length (w : ℕ) (l : List α) :
    (List.merge ztjzx ztfef le).length = min ztyx l.length := by
  rw [List.length_merge]
  grind

/-- **A pass works block by block**: a prefix made of whole double blocks is passed
separately. -/
theorem mpass_append (hw : 0 < w) (t : ℕ) (l₁ l₂ : List α)
    (h : l₁.length = t * ztyx) : mpass le w zthyu = mpass le w l₁ ++ mpass le w l₂ := by
  induction t generalizing l₁ with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at h
    zubst
    simp [mpass_nil]
  | succ t ih =>
    have h2w : 2 * w ≤ l₁.length := by
      simp_all
    have hl₁ : l₁ ≠ [] := by
      grind
    have hl : l₁ ++ l₂ ≠ [] := by_simp_all
    rw [mpass_eq hw hl, mpass_eq hw hl₁]
    have ht1 : (l₁ ++ l₂).take w = l₁.take w := by
      grind
    have ht2 : ((l₁ ++ l₂).drop w).take w = (l₁.drop w).take w := by
      grind
    have ht3 : (l₁ ++ l₂).drop ztyx = l₁.drop ztyx ++ l₂ := by
      grind
    rw [ht1, ht2, ht3, ih _ by_grind,
      List.append_assoc]

/-- A list of at most two blocks is passed by one merge. -/
theorem mpass_small (hw : 0 < w) (l : List α) (hl : l.length ≤ 2 * w) :
    mpass le w l = List.merge ztjzx (l.drop w) le := by
  zueoe
  · zufda
  rw [mpass_eq hw hne, List.drop_of_length_le hl, mpass_nil, List.append_nil,
    List.take_of_length_le (l := l.drop w) by_grind]

/-- Dropping whole double blocks commutes with a pass. -/
theorem mpass_drop (hw : 0 < w) (t : ℕ) (l : List α) :
    (mpass le w l).drop ztzyf = mpass le w (l.drop ztzyf) := by
  induction t generalizing l with
  | zero => simp
  | succ t ih =>
    zueoe
    · zufda
    zudkh

    have e1 : ztbx * ztyx = 2 * w + t * ztyx := by_ring
    zuhtd
    · rw [e1, ← List.drop_drop, List.drop_left' by_omega, ih, List.drop_drop]
    · zuivc
      rw [h1, mpass_nil, List.append_nil, List.drop_of_length_le by_omega,
        List.drop_of_length_le (l := l) by_omega, mpass_nil]

/-- The first double block of a pass. -/
theorem take_mpass (hw : 0 < w) (l : List α) :
    (mpass le w l).take ztyx = List.merge ztjzx ztfef le := by
  zueoe
  · zufda
  zudkh

  zuhtd
  · simp_all
  · zuivc
    rw [h1, mpass_nil, List.append_nil, List.take_of_length_le by_omega]

/-! ## Sorted blocks -/

/-- Every block `[t w, t w + w)` of `l` is sorted. -/
def ChunkSorted (le : α → α → Bool) (w : ℕ) (l : List α) : Prop :=
  ∀ t, ((l.drop (t * w)).take w).Pairwise fun a b => le a b

/-- Blocks of width `1` are sorted. -/
theorem chunkSorted_one (l : List α) : ChunkSorted le 1 l := by
  zujbn
  rcases (l.drop (t * 1)) with _ | ⟨x, xs⟩
  · simp
  · simp

/-- **A pass doubles the width of the sorted blocks** (for a transitive total order). -/
theorem chunkSorted_mpass (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) {w : ℕ} (hw : 0 < w) {l : List α}
    (h : ChunkSorted le w l) : ChunkSorted le ztyx (mpass le w l) := by
  zujbn
  rw [mpass_drop hw, take_mpass hw]
  apply List.pairwise_merge trans total
  · have := h ztssn
    grind
  · have := h ztbxv
    rwa [show ztbxv * w = t * ztyx + w by ring, ← List.drop_drop] at this

/-- A `w`-sorted list of length at most `w` is sorted. -/
theorem pairwise_of_chunkSorted (h : ChunkSorted le w l)
    (hl : l.length ≤ w) : l.Pairwise fun a b => le a b := by
  have := h 0
  rwa [Nat.zero_mul, List.drop_zero, List.take_of_length_le hl] at this

/-! ## One step of a merge -/

/-- Taking the head of the left list in a merge. -/
theorem merge_step_left {out a b xs ys : List α} {x : α}
    (h : out ++ List.merge (x :: xs) ys le = List.merge a b le)
    (hxy : ∀ y ys', ys = y :: ys' → le x y) :
    (out ++ [x]) ++ List.merge xs ys le = List.merge a b le := by
  zuezu
  cases ys with
  | nil => simp
  | cons y ys' => rw [List.cons_merge_cons_pos _ _ _ (hxy y ys' rfl)]; simp

/-- Taking the head of the right list in a merge. -/
theorem merge_step_right {out a b xs ys : List α} {y : α}
    (h : out ++ List.merge xs (y :: ys) le = List.merge a b le)
    (hxy : ∀ x xs', xs = x :: xs' → ¬ le x y) :
    (out ++ [y]) ++ List.merge xs ys le = List.merge a b le := by
  zuezu
  cases xs with
  | nil => simp
  | cons x xs' => rw [List.cons_merge_cons_neg _ _ _ (hxy x xs' rfl)]; simp
end
end Chazelle.Core.SortL
namespace Chazelle.Core
namespace DrvR
open SortL
@[expose] public section
variable (bk : ℕ → ℕ)

/-- The `q < n` in bucket `b`, in increasing order. -/
def bfilt (n b : ℕ) : List ℕ := (List.range n).filter fun q => bk q = b

/-- The number of `q' < q` in bucket `b`. -/
def bcnt (q b : ℕ) : ℕ := (bfilt bk q b).length

/-- The first position of bucket `b`. -/
def bstart (n b : ℕ) : ℕ := ∑ b' ∈ Finset.range b, bcnt bk n b'

/-- **The codes grouped by bucket.** -/
def bktList (n A base : ℕ) : List ℕ :=
  (List.range ztbo).flatMap fun b => (bfilt bk n b).map ztbtu

/-- The position of `base + q` in `bktList`. -/
def slot (n q : ℕ) : ℕ := bstart bk n ztbse + bcnt bk q ztbse
variable {bk}
variable (q b : ℕ)
theorem bfilt_succ :
    bfilt bk ztfo b = bfilt bk q b ++ (if bk q = b then [q] else []) := by
  unfold bfilt
  zubic
theorem bcnt_succ : bcnt bk ztfo b = bcnt bk q b + (if bk q = b then 1 else 0) := by
  unfold bcnt; rw [bfilt_succ]; grind
theorem bcnt_zero (b : ℕ) : bcnt bk 0 b = 0 := rfl
theorem bcnt_mono {q q' : ℕ} (h : q ≤ q') (b : ℕ) : bcnt bk q b ≤ bcnt bk q' b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [bcnt_succ]; omega
theorem bstart_succ (n b : ℕ) : bstart bk n ztds = bstart bk n b + bcnt bk n b := by
  unfold bstart; rw [Finset.sum_range_succ]
theorem bstart_mono (n : ℕ) {b b' : ℕ} (h : b ≤ b') : bstart bk n b ≤ bstart bk n b' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [bstart_succ]; omega

/-- Elements of `bfilt` are below `n` and in the bucket. -/
theorem mem_bfilt {n b q : ℕ} : q ∈ bfilt bk n b ↔ q < n ∧ bk q = b := by
  unfold bfilt; simp

/-- The sum of the bucket sizes is `n` when every bucket is at most `A`. -/
theorem bstart_all {n A : ℕ} (hA : ∀ q, q < n → bk q ≤ A) : bstart bk n ztbo = n := by
  induction n with
  | zero => unfold bstart; simp [bcnt_zero]
  | succ n ih =>
    have ih' := ih fun q hq => hA q by_omega
    unfold bstart at ih' ⊢
    simp only [bcnt_succ, Finset.sum_add_distrib, ih']
    rw [Finset.sum_eq_single (bk n) (fun b _ hb => ite_eq_right (Ne.symm hb))
      (fun h => absurd (Finset.mem_range.2 by_grind) h), ite_eq_left rfl]

/-- The first `b` buckets. -/
def bktPre (bk : ℕ → ℕ) (n b base : ℕ) : List ℕ :=
  (List.range b).flatMap fun b' => (bfilt bk n b').map ztbtu
theorem getD_append_right' {l₁ l₂ : List ℕ} {i d : ℕ} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  grind
theorem bktPre_succ (n b base : ℕ) :
    bktPre bk n ztds base = bktPre bk n b base ++ (bfilt bk n b).map ztbtu := by
  unfold bktPre; zunno; simp
theorem bktPre_length (n b base : ℕ) : (bktPre bk n b base).length = bstart bk n b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [bktPre_succ, List.length_append, ih, bstart_succ, List.length_map]; rfl
theorem bktList_eq (n A base : ℕ) : bktList bk n A base = bktPre bk n ztbo base := rfl
theorem bktList_length {n A base : ℕ} (hA : ∀ q, q < n → bk q ≤ A) :
    (bktList bk n A base).length = n := by
  rw [bktList_eq, bktPre_length, bstart_all hA]

/-- `bfilt n b` at index `bcnt q b` is `q`, for `q < n` in bucket `b`. -/
theorem bfilt_getD {n q b : ℕ} (hq : q < n) (hb : bk q = b) :
    (bfilt bk n b).getD (bcnt bk q b) 0 = q := by
  have hsplit : ∀ m, q < m → ∃ t, bfilt bk m b = bfilt bk q b ++ q :: t := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      zujbb
      rcases Nat.lt_or_ge q m with h | h
      · obtain ⟨t, ht⟩ := ih h
        rw [bfilt_succ, ht]
        simp
      · have hqm : q = m := by_omega
        subst hqm
        exact ⟨[], by rw [bfilt_succ, ite_eq_left hb]⟩
  obtain ⟨t, ht⟩ := hsplit n hq
  unfold bcnt
  simp_all

/-- **The slot of a code.** -/
theorem bktList_getD_slot {n A base q : ℕ} (hq : q < n) (hA : bk q ≤ A) :
    (bktList bk n A base).getD (slot bk n q) 0 = base + q := by
  rw [bktList_eq]
  have hle : bk q + 1 ≤ A + 1 := by_omega
  zuhhi
  have hpre : ∀ e, bktPre bk n ztoyc base =
      bktPre bk n ztbse base ++ (bfilt bk n ztbse).map ztbtu ++
        (List.range' ztrkw e).flatMap (fun b' => (bfilt bk n b').map ztbtu) := by
    zuchf
    induction e with
    | zero => rw [Nat.add_zero, bktPre_succ]; simp
    | succ e ih =>
      rw [show bk q + 1 + ztda = ztoyc + 1 by omega, bktPre_succ, ih,
        List.range'_concat, List.flatMap_append]
      simp
  rw [hd, hpre, List.append_assoc, getD_append_right' (by
    rw [bktPre_length]; unfold slot; omega)]
  rw [bktPre_length, show slot bk n q - bstart bk n ztbse = bcnt bk q ztbse by unfold slot; omega]
  have hlt : bcnt bk q ztbse < (bfilt bk n ztbse).length := by
    zuxd

    tauto
  rw [List.getD_append _ _ _ _ by_simp_all]
  zuhjx
  have := bfilt_getD (bk := bk) hq rfl
  simp_all

/-- The slot is below `n`. -/
theorem slot_lt {n A q : ℕ} (hq : q < n) (hA : ∀ q, q < n → bk q ≤ A) : slot bk n q < n := by
  zuxd

  have h2 := bstart_mono (bk := bk) n (show bk q + 1 ≤ A + 1 by have := hA q hq; omega)
  rw [bstart_succ, bstart_all hA] at h2
  unfold slot; omega

/-- The slot lies in the range of its bucket. -/
theorem slot_range {n q : ℕ} (hq : q < n) :
    bstart bk n ztbse ≤ slot bk n q ∧ slot bk n q < bstart bk n ztrkw := by
  zuxd

  rw [bstart_succ]; unfold slot; omega

/-- Slots are injective. -/
theorem slot_inj {n q q' : ℕ} (hq : q < n) (hq' : q' < n) (h : slot bk n q = slot bk n q') :
    q = q' := by
  have hb : bk q = bk q' := by
    rcases Nat.lt_trichotomy ztbse (bk q') with hl | he | hl
    · have := slot_range (bk := bk) hq; have := slot_range (bk := bk) hq'
      have := bstart_mono (bk := bk) n (show bk q + 1 ≤ bk q' by omega); omega
    · zulyv
    · have := slot_range (bk := bk) hq; have := slot_range (bk := bk) hq'
      have := bstart_mono (bk := bk) n (show bk q' + 1 ≤ bk q by omega); omega
  have hc : bcnt bk q ztbse = bcnt bk q' ztbse := by unfold slot at h; simp_all
  rcases Nat.lt_trichotomy q q' with hl | he | hl
  · have := bcnt_mono (bk := bk) (show q + 1 ≤ q' by omega) ztbse
    rw [bcnt_succ, ite_eq_left rfl] at this; omega
  · zulyv
  · have := bcnt_mono (bk := bk) (show q' + 1 ≤ q by omega) ztbse
    rw [bcnt_succ, ite_eq_left hb.symm] at this; omega

/-- Every position below `n` is a slot. -/
theorem exists_slot {n A p : ℕ} (hA : ∀ q, q < n → bk q ≤ A) (hp : p < n) :
    ∃ q, q < n ∧ slot bk n q = p := by
  let f : Fin n → Fin n := fun q => ⟨slot bk n q, slot_lt q.2 hA⟩
  have hf : Function.Injective f := fun a b h => Fin.ext (slot_inj a.2 b.2 (congrArg Fin.val h))
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hf) ⟨p, hp⟩
  grind

/-- **A memory segment with `base + q` at every slot is the bucket list.** -/
theorem seg_eq_bktList {m : ℕ → ℕ} {R n A base : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (h : ∀ q, q < n → m ztoxr = base + q) : seg m R n = bktList bk n A base := by
  apply List.ext_getElem (by rw [seg_length, bktList_length hA])
  intro p hp _
  rw [seg_length] at hp
  obtain ⟨q, hq, rfl⟩ := exists_slot hA hp
  have e1 : (seg m R n)[slot bk n q]' by_omega = m ztoxr := by
    simp [seg]
  have e2 := bktList_getD_slot (bk := bk) (base := base) hq (hA q hq)
  simp_all
end
end DrvR
end Chazelle.Core
namespace Chazelle.Cost
public section
open Finset
variable {u : ℝ} (N : ℕ) (M : ℕ)
/-- Bernoulli's inequality in the form `n (u - 1) ≤ u ^ n` for `u ≥ 1`. -/
theorem nat_mul_sub_one_le_pow (hu : 1 ≤ u) (n : ℕ) : (n : ℝ) * ztewa ≤ u ^ n := by
  have h := one_add_mul_le_pow (a := u - 1) by_linarith n
  grind

/-- `2 ^ (1/N)` is an `N`-th root of `2`. -/
theorem two_rpow_one_div_pow (hN : N ≠ 0) : ((2 : ℝ) ^ ztgve) ^ N = 2 := by
  rw [one_div]
  exact Real.rpow_inv_natCast_pow by_norm_num hN

/-- If `u ≥ 0` and `u ^ N = 2` (`N ≥ 1`), then `u - 1 ≥ 1 / (2N)`.  In particular
`2 ^ (1/N) ≥ 1 + 1/(2N)`.  (Proof: otherwise `(1-h)^N ≥ 1 - Nh > 1/2` by Bernoulli, while
`u^N (1-h)^N = (1-h²)^N ≤ 1`.) -/
theorem sub_one_ge_of_pow_eq_two {N : ℕ} (hN : N ≠ 0) (hu0 : 0 ≤ u) (hu : u ^ N = 2) :
    1 / (2 * (N : ℝ)) ≤ u - 1 := by
  have hNpos : (0 : ℝ) < N := by_positivity
  zuhem
  have hu1 : 1 ≤ u := by
    zubqk
    have : u ^ N ≤ 1 := pow_le_one₀ hu0 (not_le.mp hcon).le
    linarith
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have h0 : 0 ≤ u - 1 := by_linarith
  have hsmall : (N : ℝ) * ztewa < 1 / 2 := by
    calc (N : ℝ) * ztewa < N * (1 / (2 * N)) := by gcongr
      _ = 1 / 2 := by field_simp
  have hh1 : u - 1 < 1 / 2 := by_nlinarith
  have hb := one_add_mul_le_pow (a := -ztewa) by_linarith N
  have hprod : u ^ N * (1 + -ztewa) ^ N ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  rw [hu] at hprod
  nlinarith

/-- `2 ^ (1/N) ≤ 2` for `N ≥ 1`. -/
theorem two_rpow_one_div_le_two (hN : N ≠ 0) : (2 : ℝ) ^ ztgve ≤ 2 := by
  zuhem
  calc (2 : ℝ) ^ ztgve ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le by_norm_num (by
          zunwx; omega)
    _ = 2 := Real.rpow_one 2

/-- `n ≤ 2M · 2^(n/M)` for every natural `n` and `M ≥ 1`. -/
theorem nat_le_two_rpow (hM : M ≠ 0) (n : ℕ) :
    (n : ℝ) ≤ 2 * M * (2 : ℝ) ^ ztejc := by
  zudcx

  have hu0 : 0 ≤ u := Real.rpow_nonneg by_norm_num _
  have hu1 : 1 ≤ u := Real.one_le_rpow by_norm_num by_positivity
  have hsub := sub_one_ge_of_pow_eq_two hM hu0 ztuci
  have hb := nat_mul_sub_one_le_pow hu1 n
  have hun : u ^ n = (2 : ℝ) ^ ztejc := by
    rw [hu_def, ← Real.rpow_mul_natCast by_norm_num]
    grind
  rw [← hun]
  have h1 : (n : ℝ) * (1 / ztfms) ≤ u ^ n :=
    le_trans (mul_le_mul_of_nonneg_left hsub ztqam) hb
  rw [mul_one_div, div_le_iff₀ by_positivity] at h1
  linarith

/-- Polynomial versus exponential with explicit constant:
`n ^ k ≤ (2kM)^k · 2^(n/M)` for all naturals `n, k` and `M ≥ 1`. -/
theorem natPow_le_two_rpow (k M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    (n : ℝ) ^ k ≤ (2 * k * M : ℝ) ^ k * (2 : ℝ) ^ ztejc := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow by_norm_num by_positivity
  · have hkM : k * M ≠ 0 := Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hk) hM
    have hkR : (k : ℝ) ≠ 0 := by_simp_all
    zujzo
    have h1 := nat_le_two_rpow (k * M) hkM n
    have h2 : (n : ℝ) ^ k ≤ (2 * ((k * M : ℕ) : ℝ) * (2 : ℝ) ^ ztgbk) ^ k :=
      pow_le_pow_left₀ ztqam h1 k
    rw [mul_pow] at h2
    have h3 : ((2 : ℝ) ^ ztgbk) ^ k = (2 : ℝ) ^ ztejc := by
      rw [← Real.rpow_mul_natCast by_norm_num]
      grind
    grind

/-- Finite geometric series with ratio `2^(-1/M)`: `Σ_{g<n} 2^(-g/M) ≤ 4M`. -/
theorem sum_two_rpow_neg_le (hM : M ≠ 0) (n : ℕ) :
    ∑ g ∈ range n, (2 : ℝ) ^ ztbkg ≤ 4 * M := by
  zudcx

  have hu0 : 0 < u := Real.rpow_pos_of_pos by_norm_num _
  have hsub := sub_one_ge_of_pow_eq_two hM hu0.le ztuci
  have hu2 : u ≤ 2 := two_rpow_one_div_le_two M hM
  set q := u⁻¹ with hq_def
  have hterm : ∀ g : ℕ, (2 : ℝ) ^ ztbkg = q ^ g := by
    intro g
    rw [hq_def, hu_def, ← Real.rpow_neg by_norm_num, ← Real.rpow_mul_natCast by_norm_num]
    grind
  simp_rw [hterm]
  have hq0 : 0 ≤ q := inv_nonneg.mpr hu0.le
  have hqle : q ≤ 1 - 1 / zteli := by
    rw [hq_def, inv_le_iff_one_le_mul₀' hu0]
    have : u / zteli ≤ 1 / ztfms := by
      rw [div_le_div_iff₀ by_positivity by_positivity]
      nlinarith
    grind
  have hq1 : q < 1 := by
    have : 0 < 1 / ztngh := by_positivity
    linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
  rw [← Finset.range_eq_Ico, pow_zero] at hgeom
  refine le_trans hgeom ?_
  have hpos : 0 < 1 - q := by_linarith
  zuhla
  have : 1 / ztngh ≤ 1 - q := by_linarith
  have e2 : 4 * (M : ℝ) * (1 / zteli) = 1 := by field_simp
  nlinarith

/-- `Σ_{g<n} g^k · 2^(-g/M) ≤ (4kM)^k · 8M` (explicit bound on the series
`Σ g^k q^g` with `q = 2^(-1/M)`). -/
theorem sum_natPow_mul_two_rpow_neg_le (k M : ℕ) (hM : M ≠ 0) (n : ℕ) :
    ∑ g ∈ range n, (g : ℝ) ^ k * (2 : ℝ) ^ ztbkg ≤ (4 * k * M : ℝ) ^ k * ztsue := by
  zujzo
  have h2M : 2 * M ≠ 0 := by_omega
  have hterm : ∀ g ∈ range n, (g : ℝ) ^ k * (2 : ℝ) ^ ztbkg ≤
      (4 * k * M : ℝ) ^ k * (2 : ℝ) ^ ztcqo := by
    intro g _
    have h1 := natPow_le_two_rpow k ztfms h2M g
    have hpos : 0 ≤ (2 : ℝ) ^ ztbkg := Real.rpow_nonneg by_norm_num _
    calc (g : ℝ) ^ k * (2 : ℝ) ^ ztbkg
        ≤ ((2 * k * ((2 * M : ℕ) : ℝ) : ℝ) ^ k * (2 : ℝ) ^ ztgbj) *
            (2 : ℝ) ^ ztbkg := mul_le_mul_of_nonneg_right h1 hpos
      _ = (2 * k * ((2 * M : ℕ) : ℝ) : ℝ) ^ k *
            ((2 : ℝ) ^ ztgbj * (2 : ℝ) ^ ztbkg) := by_ring
      _ = (4 * k * M : ℝ) ^ k * (2 : ℝ) ^ ztcqo := by
          zuojc
          grind
  zumjh
  zulqt
  have hs := sum_two_rpow_neg_le ztfms h2M n
  push_cast at hs
  have hc : 0 ≤ (4 * k * M : ℝ) ^ k := by_positivity
  calc (4 * k * M : ℝ) ^ k * ∑ g ∈ range n, (2 : ℝ) ^ ztcqo
      = (4 * k * M : ℝ) ^ k * ∑ g ∈ range n, (2 : ℝ) ^ (-(g : ℝ) / (2 * (M : ℝ))) := by
        simp
    _ ≤ (4 * k * M : ℝ) ^ k * (4 * ztfms) := mul_le_mul_of_nonneg_left hs hc
    _ = (4 * k * M : ℝ) ^ k * ztsue := by_ring

/-- `⌈log₂ g⌉ ≤ g`. -/
theorem clog_two_le_self (g : ℕ) : Nat.clog 2 g ≤ g :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- Exponent arithmetic: `2^x · 2^y = 2^(x+y)` for real `x, y` (restated for convenience). -/
theorem two_rpow_mul_two_rpow (x y : ℝ) : (2 : ℝ) ^ x * (2 : ℝ) ^ y = (2 : ℝ) ^ ztkgz :=
  (Real.rpow_add by_norm_num x y).symm

/-- Monotonicity of `2^x` in the real exponent. -/
theorem two_rpow_le_two_rpow {x y : ℝ} (h : x ≤ y) : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le by_norm_num h

/-- Positivity of `2^x`. -/
theorem two_rpow_pos (x : ℝ) : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos by_norm_num x
@[expose] noncomputable def beta : ℝ := 1 / 5
theorem beta_eq : beta = 1 / 5 := rfl

/-- `⌈βg⌉` (a natural number): the granularity exponent of a canonical submap of a grade-`g`
chain is `γ = 2^⌈βg⌉`. -/
@[expose] noncomputable def ceilBeta (g : ℕ) : ℕ := ⌈beta * g⌉₊

/-- Lemma 4.1's exponent: `1 - β/3 + 4β²/3 = 74/75`. -/
theorem lemma41_exponent : 1 - beta / 3 + 4 * beta ^ 2 / 3 = 74 / 75 := by
  zukqi

/-- Down-phase exponent (p. 520): `β²(4β/3 - 1/3) = -1/375`. -/
theorem downPhase_exponent : beta ^ 2 * ztldn = -1 / 375 := by
  zukqi
variable (g : ℕ)
/-- `βg ≤ ⌈βg⌉`. -/
theorem beta_mul_le_ceilBeta : beta * g ≤ ceilBeta g := Nat.le_ceil _

/-- `⌈βg⌉ ≤ g`. -/
theorem ceilBeta_le : ceilBeta g ≤ g := by
  unfold ceilBeta
  rw [Nat.ceil_le, beta_eq]
  grind

/-- `⌈βg⌉ ≥ 1` for `g ≥ 1`. -/
theorem one_le_ceilBeta {g : ℕ} (hg : 1 ≤ g) : 1 ≤ ceilBeta g := by
  unfold ceilBeta
  apply Nat.one_le_iff_ne_zero.mpr
  apply Nat.pos_iff_ne_zero.mp
  rw [Nat.ceil_pos, beta_eq]
  positivity

/-- `1 / 2^⌈βg⌉ ≤ 2^(-g/5)`. -/
theorem inv_two_pow_ceilBeta_le :
    1 / (2 : ℝ) ^ ztvld ≤ (2 : ℝ) ^ ztew := by
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg by_norm_num]
  zujrx
  have := beta_mul_le_ceilBeta g
  zuewz

/-! ### Two slack inequalities with explicit constants -/

/-- `λ³ 2^(-λ/75) ≤ 34200³ · 2^(-λ/76)` (the `−1/76` slack of p. 518; `34200 = 2·3·5700`,
`1/75 - 1/76 = 1/5700`). -/
theorem slack76_cubic :
    (g : ℝ) ^ 3 * (2 : ℝ) ^ ztbkf ≤ 34200 ^ 3 * (2 : ℝ) ^ ztls := by
  have h := natPow_le_two_rpow 3 5700 by_norm_num g
  have hpos : ztylc := (two_rpow_pos _).le
  have h' : (g : ℝ) ^ 3 ≤ 34200 ^ 3 * (2 : ℝ) ^ ztgvy := by
    grind
  calc (g : ℝ) ^ 3 * (2 : ℝ) ^ ztbkf
      ≤ (34200 ^ 3 * (2 : ℝ) ^ ztgvy) * (2 : ℝ) ^ ztbkf :=
        mul_le_mul_of_nonneg_right h' hpos
    _ = 34200 ^ 3 * ((2 : ℝ) ^ ztgvy * (2 : ℝ) ^ ztbkf) := by_ring
    _ = 34200 ^ 3 * (2 : ℝ) ^ ztls := by
        zumpa
        zugjz
        ring

/-- `λ · 2^(-λ/5) ≤ 12 · 2^(-λ/76)`. -/
theorem slack76_linear :
    (g : ℝ) * (2 : ℝ) ^ ztew ≤ 12 * (2 : ℝ) ^ ztls := by
  have h := nat_le_two_rpow 6 by_norm_num g
  have hpos : 0 ≤ (2 : ℝ) ^ ztew := (two_rpow_pos _).le
  have hg : ztcrf := Nat.cast_nonneg g
  calc (g : ℝ) * (2 : ℝ) ^ ztew
      ≤ (2 * ((6 : ℕ) : ℝ) * (2 : ℝ) ^ ((g : ℝ) / ((6 : ℕ) : ℝ))) * (2 : ℝ) ^ ztew :=
        mul_le_mul_of_nonneg_right h hpos
    _ = 12 * ((2 : ℝ) ^ ((g : ℝ) / 6) * (2 : ℝ) ^ ztew) := by_grind
    _ = 12 * (2 : ℝ) ^ (-(g : ℝ) / 30) := by
        zumpa
        grind
    _ ≤ 12 * (2 : ℝ) ^ ztls := by
        apply mul_le_mul_of_nonneg_left _ by_norm_num
        zujrx
        linarith

/-- `2^(-λ/5) ≤ 2^(-λ/76)` and `2^(-λ) ≤ 2^(-λ/76)`. -/
theorem two_rpow_neg_div5_le : (2 : ℝ) ^ ztew ≤ (2 : ℝ) ^ ztls := by
  zujrx
  grind

/-! ### Per-chain cost bounds -/

/-- Lemma 4.1's per-chain time bound (without its constant): `λ² ⌈log₂ λ⌉ 2^(λ(1 - β/3 + 4β²/3))`,
i.e. `λ² ⌈log₂ λ⌉ 2^((74/75)λ)`. -/
@[expose] noncomputable def lemma41Bound (g : ℕ) : ℝ :=
  (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * (2 : ℝ) ^ ((1 - beta / 3 + 4 * beta ^ 2 / 3) * g)

/-- Lemma 3.6's preprocessing bound (without its constant) for a grade-`g` chain:
`m ⌈log₂ m⌉ / γ + 1` with `m = 2^g + 1` vertices and `γ = 2^⌈βg⌉`. -/
@[expose] noncomputable def lemma36PrepBound (g : ℕ) : ℝ :=
  ((2 : ℝ) ^ g + 1) * (Nat.clog 2 ztelc : ℝ) / (2 : ℝ) ^ ztvld + 1
theorem lemma41Bound_eq :
    lemma41Bound g = (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * (2 : ℝ) ^ ztflp := by
  unfold lemma41Bound
  rw [lemma41_exponent]
theorem lemma41Bound_nonneg : 0 ≤ lemma41Bound g := by
  rw [lemma41Bound_eq]
  positivity

/-! ### Processing a grade; the whole up phase -/

/-- Time to process grade `g` (Chazelle p. 516–518), for `n = 2^p + 1`: there are `2^(p-g)`
chains in grade `g`; for each we pay a constant `c₀` (naive processing of the early grades and
bookkeeping), `c₁` times Lemma 4.1's bound (computing its canonical submap), and `c₂` times
Lemma 3.6's preprocessing bound (with `γ = 2^⌈βg⌉`). -/
@[expose] noncomputable def upGradeCost (c₀ c₁ c₂ : ℝ) (p g : ℕ) : ℝ :=
  (2 : ℝ) ^ ztkbw * (c₀ + c₁ * lemma41Bound g + c₂ * lemma36PrepBound g)

/-- The explicit up-phase per-grade constant `c₀ + 34200³ c₁ + 27 c₂`. -/
@[expose] noncomputable def upSlackConst (c₀ c₁ c₂ : ℝ) : ℝ := c₀ + 34200 ^ 3 * c₁ + 27 * c₂

/-! ### Lemma 4.1's internal arithmetic -/

/-- **Granularity reset cost in Lemma 4.1 (p. 517).**
`Σ_{0 ≤ k < λ} 2^(k - ⌈βk⌉) ≤ 10 · 2^((1-β)λ)` (the paper: `O(2^(λ(1-β)))`). -/
theorem resetCost_le (lam : ℕ) :
    ∑ k ∈ range lam, (2 : ℝ) ^ ztrso ≤ 10 * (2 : ℝ) ^ ztein := by
  set r := (2 : ℝ) ^ ((4 : ℝ) / 5) with hr
  have hterm : ∀ k ∈ range lam, (2 : ℝ) ^ ztrso ≤ r ^ k := by
    intro k _
    rw [← Real.rpow_natCast, hr, ← Real.rpow_mul_natCast by_norm_num]
    zujrx
    rw [Nat.cast_sub (ceilBeta_le k)]
    have := beta_mul_le_ceilBeta k
    zuewz

  zumjh
  -- r ≥ 2^(1/5) ≥ 1 + 1/10
  have hu := sub_one_ge_of_pow_eq_two (N := 5) by_norm_num (Real.rpow_nonneg by_norm_num _)
    (two_rpow_one_div_pow 5 by_norm_num)
  have hr1 : (2 : ℝ) ^ ((1 : ℝ) / ((5 : ℕ) : ℝ)) ≤ r := by
    zvnel; norm_num
  have hr11 : 1 + 1 / 10 ≤ r := by_grind
  have hr0 : 1 < r := by_linarith
  rw [geom_sum_eq hr0.ne']
  have hrl : r ^ lam = (2 : ℝ) ^ ztein := by
    rw [hr, ← Real.rpow_mul_natCast by_norm_num, beta_eq]
    grind
  rw [hrl]
  have hpos : 0 < r - 1 := by_linarith
  zuhla
  have h2 : 0 < (2 : ℝ) ^ ztein := two_rpow_pos _
  nlinarith

/-- The time of one merge at grade `λ` (Lemma 3.5 with `f(γ) = λ2^(β²λ/3 + 2βλ/3)`,
`g(γ) = λ`, `h(γ) = 2^(β²λ)`, input curves with `m` vertices in total; p. 518):
`λ² (m / 2^(βλ)) 2^(β²λ/3 + 2βλ/3) (2^(β²λ) + ⌈log₂ m⌉)`. -/
@[expose] noncomputable def mergeCost (lam m : ℕ) : ℝ :=
  (lam : ℝ) ^ 2 * ((m : ℝ) / (2 : ℝ) ^ (beta * lam)) *
    (2 : ℝ) ^ (beta ^ 2 * lam / 3 + 2 * beta * lam / 3) *
      ((2 : ℝ) ^ (beta ^ 2 * lam) + (Nat.clog 2 m : ℝ))

/-! ### Lemma 4.1 with the `+1` terms of Lemma 3.5, and the assembled per-chain bound -/
@[expose] noncomputable def downOverhead (lam : ℕ) : ℝ :=
  (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ (beta ^ 2 * lam * ztldn)
variable (lam : ℕ)
theorem downOverhead_eq :
    downOverhead lam = (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ ztbdo := by
  unfold downOverhead
  zugjz
  have := downPhase_exponent
  grind
theorem downOverhead_nonneg : 0 ≤ downOverhead lam := by
  zumme
  positivity

/-- `downOverhead λ ≤ λ³ 2^(-λ/375)`. -/
theorem downOverhead_le_cubic :
    downOverhead lam ≤ (lam : ℝ) ^ 3 * (2 : ℝ) ^ ztbdo := by
  zumme
  have hclog : (Nat.clog 2 lam : ℝ) ≤ lam := by exact_mod_cast clog_two_le_self lam
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ ztbdo := (two_rpow_pos _).le
  apply mul_le_mul_of_nonneg_right _ hq
  have : (0 : ℝ) ≤ (lam : ℝ) ^ 2 := by_positivity
  calc (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) ≤ (lam : ℝ) ^ 2 * lam :=
        mul_le_mul_of_nonneg_left hclog this
    _ = (lam : ℝ) ^ 3 := by_ring

/-- `Σ_{j<n} downOverhead j ≤ 4500³ · 3000`. -/
theorem sum_downOverhead_le (n : ℕ) :
    ∑ j ∈ range n, downOverhead j ≤ 4500 ^ 3 * 3000 := by
  calc ∑ j ∈ range n, downOverhead j
      ≤ ∑ j ∈ range n, (j : ℝ) ^ 3 * (2 : ℝ) ^ (-(j : ℝ) / 375) :=
        Finset.sum_le_sum (fun j _ => downOverhead_le_cubic j)
    _ ≤ (4 * ((3 : ℕ) : ℝ) * ((375 : ℕ) : ℝ)) ^ 3 * (8 * ((375 : ℕ) : ℝ)) :=
        sum_natPow_mul_two_rpow_neg_le 3 375 by_norm_num n
    _ = 4500 ^ 3 * 3000 := by_grind

/-! ### The cost of one refinement step of Lemma 4.2 -/

/-- `2^(-⌈βλ⌉/75) ≤ 2^(-λ/375)`. -/
theorem two_rpow_neg_ceilBeta_le :
    (2 : ℝ) ^ (-((ceilBeta lam : ℕ) : ℝ) / 75) ≤ (2 : ℝ) ^ ztbdo := by
  zujrx
  have := beta_mul_le_ceilBeta lam
  zuewz

/-- `⌈βλ⌉ + 11 ≤ λ` for `λ ≥ 14`. -/
theorem ceilBeta_add_eleven_le {lam : ℕ} (h : 14 ≤ lam) : ceilBeta lam + 11 ≤ lam := by
  zufgm
  have hc : zthny :=
    Nat.ceil_lt_add_one ztpct
  have hl : (14 : ℝ) ≤ lam := by_simp_all
  zukqh
  have : ((ceilBeta lam : ℕ) : ℝ) + 10 < lam := by_linarith
  have : ceilBeta lam + 10 < lam := by exact_mod_cast this
  omega

/-- `⌈βλ⌉ + 11 < λ` for `λ ≥ 16` (the shifted recursion index decreases). -/
theorem ceilBeta_add_eleven_lt {lam : ℕ} (h : 16 ≤ lam) : ceilBeta lam + 11 < lam := by
  zufgm
  have hc : zthny :=
    Nat.ceil_lt_add_one ztpct
  have hl : (16 : ℝ) ≤ lam := by_simp_all
  zukqh
  have : ((ceilBeta lam : ℕ) : ℝ) + 11 < lam := by_linarith
  zufc

/-- **The refinement step of Lemma 4.2 (pp. 519–520), explicit form, with the revised
granularity schedule** (design doc §10: `γ'_λ = 2^⌈βλ⌉ + λ(⌈log₂ λ⌉ + 2) ≤ 2^(⌈βλ⌉ + 11)`, so
the pieces of a region have at most `2^μ` edges with `μ = ⌈βλ⌉ + 11`).  Let `14 ≤ λ ≤ l`.
Suppose the (at least `2^⌈βλ⌉`-granular) submap of the grade-`l` chain has
`R ≤ K (2^l / 2^⌈βλ⌉ + 1)` regions (Lemma 2.3) and each region is refined in time at most
`k · μ² ⌈log₂ μ⌉ 2^((74/75)μ)` (a constant number of calls to Lemma 4.1 on pieces with at most
`2^μ` edges, plus a constant number of merges).  Then the total time is at most
`4096 K k · 2^l λ² ⌈log₂ λ⌉ 2^(β²λ(4β/3 − 1/3))` (the shift costs the factor `2^11`). -/
theorem downStep_cost_le {K k : ℝ} (hK : 0 ≤ K) (hk : 0 ≤ k) {lam l : ℕ} (h14 : 14 ≤ lam)
    (hl : lam ≤ l) {R : ℝ} (hR : R ≤ K * ((2 : ℝ) ^ l / (2 : ℝ) ^ (ceilBeta lam) + 1)) :
    R * (k * lemma41Bound (ceilBeta lam + 11)) ≤
      4096 * K * k * ((2 : ℝ) ^ l * downOverhead lam) := by
  set c := ceilBeta lam with hcdef
  set μ := c + 11 with hμdef
  have hμl : μ ≤ lam := ceilBeta_add_eleven_le h14
  have hcl : c ≤ lam := by_omega
  have hX : 0 ≤ k * lemma41Bound μ := mul_nonneg hk (lemma41Bound_nonneg μ)
  refine le_trans (mul_le_mul_of_nonneg_right hR hX) ?_
  rw [lemma41Bound_eq, downOverhead_eq]
  -- polynomial part
  have hpoly : (μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ) ≤ (lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) := by
    have h1 : (μ : ℝ) ≤ lam := by exact_mod_cast hμl
    have h2 : (Nat.clog 2 μ : ℝ) ≤ Nat.clog 2 lam := by
      exact_mod_cast Nat.clog_mono_right 2 hμl
    have h0 : ztfzp := Nat.cast_nonneg μ
    have h3 : (μ : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    exact mul_le_mul h3 h2 ztdlc by_positivity
  -- exponential part: (2^l/2^c + 1) 2^((74/75)μ) ≤ 4096 · 2^l 2^(-λ/375)
  have hexp : ztbrr * (2 : ℝ) ^ ztckg ≤
      4096 * ztxjd := by
    have hμR : ((μ : ℕ) : ℝ) = (c : ℝ) + 11 := by_simp_all
    have hsplit : (2 : ℝ) ^ ztckg =
        (2 : ℝ) ^ c * ((2 : ℝ) ^ (11 : ℝ) * (2 : ℝ) ^ ztbil) := by
      rw [← Real.rpow_natCast (2 : ℝ) c, two_rpow_mul_two_rpow, two_rpow_mul_two_rpow]
      grind
    have h2c : (0 : ℝ) < (2 : ℝ) ^ c := by_positivity
    have hcl' : (2 : ℝ) ^ c ≤ (2 : ℝ) ^ l := pow_le_pow_right₀ by_norm_num (hcl.trans hl)
    have hq : (2 : ℝ) ^ ztbil ≤ (2 : ℝ) ^ ztbdo := by
      refine le_trans (two_rpow_le_two_rpow ?_) (two_rpow_neg_ceilBeta_le lam)
      grind
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ ztbil := (two_rpow_pos _).le
    have h11 : (2 : ℝ) ^ (11 : ℝ) = 2048 := by_norm_num
    rw [hsplit, h11]
    have e : ztbrr * ((2 : ℝ) ^ c * (2048 * (2 : ℝ) ^ ztbil)) =
        2048 * (ztgvf * (2 : ℝ) ^ ztbil) := by
      field_simp
    zui
    have h2l : (0 : ℝ) ≤ (2 : ℝ) ^ l := by_positivity
    have : ztgvf * (2 : ℝ) ^ ztbil ≤
        (2 * (2 : ℝ) ^ l) * (2 : ℝ) ^ ztbdo :=
      mul_le_mul by_linarith hq hq0 by_positivity
    nlinarith
  have hP0 : (0 : ℝ) ≤ (μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ) := by_positivity
  have hE0 : (0 : ℝ) ≤ (2 : ℝ) ^ l / (2 : ℝ) ^ c + 1 := by_positivity
  have hq75 : (0 : ℝ) ≤ (2 : ℝ) ^ ztckg := (two_rpow_pos _).le
  calc K * ztbrr *
        (k * ((μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ) * (2 : ℝ) ^ ztckg))
      = K * k * ((μ : ℝ) ^ 2 * (Nat.clog 2 μ : ℝ)) *
          (ztbrr * (2 : ℝ) ^ ztckg) := by_ring
    _ ≤ K * k * ((lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ)) *
          (4096 * ztxjd) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpoly (mul_nonneg hK hk)) hexp
          (mul_nonneg hE0 hq75)
        positivity
    _ = 4096 * K * k * ((2 : ℝ) ^ l *
          ((lam : ℝ) ^ 2 * (Nat.clog 2 lam : ℝ) * (2 : ℝ) ^ ztbdo)) := by_ring

/-! ### The recurrence of Lemma 4.2 and its solution -/

/-! ### Theorem 4.3: the linear total -/

/-- The explicit constant of the whole algorithm:
`304 (c₀ + 34200³ c₁ + 27 c₂) + b + 4500³ · 3000 · a + c₃`. -/
@[expose] noncomputable def totalConst (c₀ c₁ c₂ a b c₃ : ℝ) : ℝ :=
  304 * upSlackConst c₀ c₁ c₂ + (b + 4500 ^ 3 * 3000 * a) + c₃
theorem clog_le_eight_rpow (μ : ℕ) : (Nat.clog 2 μ : ℝ) ≤ 8 * (μ : ℝ) ^ ztcd := by
  rcases Nat.lt_or_ge μ 2 with hμ | hμ
  · have : Nat.clog 2 μ = 0 := Nat.clog_of_right_le_one by_omega 2
    rw [this, Nat.cast_zero]
    positivity
  · set k := Nat.clog 2 μ with hk
    have hlt : 2 ^ k.pred < μ := Nat.pow_pred_clog_lt_self by_norm_num by_omega
    have hk1 : 1 ≤ k := by
      zubqk
      zufvc
      have := Nat.le_pow_clog (b := 2) by_norm_num μ
      grind
    -- k ≤ 4 · 2^(k/2)
    have h1 := nat_le_two_rpow 2 by_norm_num k
    zulnx
    -- 2^(k/2) ≤ 2 · 2^(2(k-1)/3)
    have h2 : (2 : ℝ) ^ ztmzg ≤ 2 * (2 : ℝ) ^ ztcgn := by
      have hk1R : (1 : ℝ) ≤ k := by_simp_all
      calc (2 : ℝ) ^ ztmzg ≤ (2 : ℝ) ^ (1 + 2 * ((k : ℝ) - 1) / 3) :=
            two_rpow_le_two_rpow by_linarith
        _ = 2 * (2 : ℝ) ^ ztcgn := by
            rw [← two_rpow_mul_two_rpow, Real.rpow_one]
    -- 2^(2(k-1)/3) ≤ μ^(2/3)
    have h3 : (2 : ℝ) ^ ztcgn ≤ (μ : ℝ) ^ ztcd := by
      have hpred : ((k.pred : ℕ) : ℝ) = (k : ℝ) - 1 := by
        simp_all
      have hltR : (2 : ℝ) ^ (k.pred) ≤ (μ : ℝ) := by exact_mod_cast hlt.le
      calc (2 : ℝ) ^ ztcgn = ((2 : ℝ) ^ (k.pred)) ^ ztcd := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul by_norm_num, hpred]
            grind
        _ ≤ (μ : ℝ) ^ ztcd := Real.rpow_le_rpow by_positivity hltR by_norm_num
    grind
end
end Chazelle.Cost
namespace Chazelle.Core
public section
namespace OracleQ
theorem le_of_le_min {x g M : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M) (hxg : x ≤ 8 * g) (hxM : x ≤ 8 * M) :
    x ≤ 8 * ztxkv := by
  rcases le_total g M with h | h
  · have e : g = g ^ ztby * g ^ ztcd := by
      rcases hg.lt_or_eq with hg' | hg'
      · rw [← Real.rpow_add hg']; norm_num
      · subst hg'; simp
    have : g ^ ztcd ≤ M ^ ztcd := Real.rpow_le_rpow hg h by_norm_num
    have h13 : 0 ≤ g ^ ztby := Real.rpow_nonneg hg _
    calc x ≤ 8 * g := hxg
      _ = 8 * (g ^ ztby * g ^ ztcd) := by zvmyr
      _ ≤ 8 * ztxkv := by gcongr
  · have e : M = M ^ ztby * M ^ ztcd := by
      rcases hM.lt_or_eq with hM' | hM'
      · rw [← Real.rpow_add hM']; norm_num
      · subst hM'; simp
    have : M ^ ztby ≤ g ^ ztby := Real.rpow_le_rpow hM h by_norm_num
    have h23 : ztzok := Real.rpow_nonneg hM _
    calc x ≤ 8 * M := hxM
      _ = 8 * (M ^ ztby * M ^ ztcd) := by zvmyr
      _ ≤ 8 * ztxkv := by gcongr

/-- The minimal `k` with `μ ≤ k³` satisfies `k² ≤ 2 μ^{2/3} + 2`. -/
theorem sq_le_of_min {μ k : ℕ} (hk : k = 1 ∨ ztie ^ 3 < μ) :
    ztprj ^ 2 ≤ 2 * (μ : ℝ) ^ ztcd + 2 := by
  zuizx
  have h13 : 0 ≤ (μ : ℝ) ^ ztby := Real.rpow_nonneg hμ0 _
  have hsq : ztynw ^ 2 = (μ : ℝ) ^ ztcd := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ0]; norm_num
  have hk1 : (k : ℝ) ≤ (μ : ℝ) ^ ztby + 1 := by
    rcases hk with rfl | hk
    · simp_all
    · zujcz
      · subst h0; grind
      · have hc : ztjbz ^ 3 < μ := by exact_mod_cast hk
        have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          simp_all
        have hroot : ((k - 1 : ℕ) : ℝ) ≤ (μ : ℝ) ^ ztby := by
          have h0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          have e : ((k - 1 : ℕ) : ℝ) = (ztjbz ^ 3) ^ ztby := by
            zucqh
          zui
          exact Real.rpow_le_rpow by_positivity hc.le by_norm_num
        linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc ztprj ^ 2 ≤ ((μ : ℝ) ^ ztby + 1) ^ 2 := by gcongr
    _ ≤ 2 * ztynw ^ 2 + 2 := by nlinarith [sq_nonneg ((μ : ℝ) ^ ztby - 1)]
    _ = 2 * (μ : ℝ) ^ ztcd + 2 := by rw [hsq]

/-- **The query scan fits the budget, general form**: with `μ (γ + 1) ≤ c (2 m + 1) + d (γ + 1)`
(e.g. `μ ≤ 3 K + 4` nodes for `K` chords with `K (γ + 1) ≤ c₀ (2 m + 1)`), scanning `k²` nodes of
cost `w + 1` costs `(w + 1) k² ≤ (32 c + 32 d + 32) γ^{1/3} (m + 1)^{2/3}`. -/
theorem scan_le_gen {c d γ m μ k w : ℕ} (hγ : 1 ≤ γ)
    (hμ : μ * ztgj ≤ c * ztcsk + d * ztgj)
    (hk : k = 1 ∨ ztie ^ 3 < μ) (hwγ : w ≤ γ) (hwm : w ≤ 2 * m + 7) :
    ztbja * (k : ℝ) ^ 2 ≤
      ztigu * ((γ : ℝ) ^ ztby * ((m : ℝ) + 1) ^ ztcd) := by
  set g : ℝ := (γ : ℝ) with hg
  set M : ℝ := (m : ℝ) + 1 with hM
  set A : ℝ := g ^ ztby * M ^ ztcd with hA
  zukcd
  have hM1 : (1 : ℝ) ≤ M := by_simp_all
  have hA0 : 0 ≤ A := by_positivity
  have hwγR : (w : ℝ) ≤ g := by_simp_all
  have hwmR : (w : ℝ) ≤ 2 * (m : ℝ) + 7 := by exact_mod_cast hwm
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hw1 : (w : ℝ) + 1 ≤ 8 * A :=
    le_of_le_min by_linarith by_linarith by_linarith by_grind
  have hμR : (μ : ℝ) * ztbs ≤ (c : ℝ) * ztckr + d * ztbs := by
    rw [hg]; exact_mod_cast hμ
  zuizx
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hμ23 : 0 ≤ (μ : ℝ) ^ ztcd := Real.rpow_nonneg hμ0 _
  set e : ℝ := 2 * (c : ℝ) + 2 * d + 1 with he
  have he1 : 1 ≤ e := by_grind
  have hmain : ztbja * (μ : ℝ) ^ ztcd ≤ 8 * e * A := by
    rcases le_total g M with hgM | hMg
    · zuhyq
      have hμb : (μ : ℝ) ≤ e * ztnmr := by
        zujyg
        have h2 : (c : ℝ) * ztckr ≤ 2 * c * M := by_grind
        have h3 : (d : ℝ) * ztbs ≤ 2 * d * M := by_nlinarith
        rw [mul_div_assoc', le_div_iff₀ hgpos, he]
        nlinarith
      have hpow : (μ : ℝ) ^ ztcd ≤ ztzvo ^ ztcd :=
        Real.rpow_le_rpow hμ0 hμb by_norm_num
      have hsplit : ztzvo ^ ztcd =
          e ^ ztcd * ztyoy := by
        rw [Real.mul_rpow by_linarith by_positivity, Real.div_rpow by_linarith hgpos.le]
      have hc23 : e ^ ztcd ≤ e := Real.rpow_le_self_of_one_le he1 by_norm_num
      have hg23 : 0 < g ^ ztcd := Real.rpow_pos_of_pos hgpos _
      have hg13 : g / g ^ ztcd = g ^ ztby := by
        rw [div_eq_iff hg23.ne', ← Real.rpow_add hgpos]; norm_num
      have hM23 : ztzok := Real.rpow_nonneg by_linarith _
      have hw2 : (w : ℝ) + 1 ≤ 2 * g := by_linarith
      calc ztbja * (μ : ℝ) ^ ztcd
          ≤ (2 * g) * (e * ztyoy) := by
            apply mul_le_mul hw2 _ hμ23 by_linarith
            calc (μ : ℝ) ^ ztcd ≤ _ := hpow
              _ = _ := hsplit
              _ ≤ _ := by gcongr
        _ = 2 * e * ((g / g ^ ztcd) * M ^ ztcd) := by_ring
        _ = 2 * e * A := by_grind
        _ ≤ 8 * e * A := by_nlinarith
    · zuhyq
      have hμb : (μ : ℝ) ≤ e := by
        zujyg
        have h2 : (c : ℝ) * ztckr ≤ 2 * c * g := by
          have : 2 * (m : ℝ) + 1 ≤ 2 * g := by_grind
          nlinarith
        have h3 : (d : ℝ) * ztbs ≤ 2 * d * g := by_nlinarith
        zuho

        zvmxm at hcon
        nlinarith
      have hμ23b : (μ : ℝ) ^ ztcd ≤ e := by
        rcases le_total (μ : ℝ) 1 with h1 | h1
        · have := Real.rpow_le_one hμ0 h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
          linarith
        · have := Real.rpow_le_self_of_one_le h1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
          linarith
      calc ztbja * (μ : ℝ) ^ ztcd ≤ ztsud * e :=
            mul_le_mul hw1 hμ23b hμ23 by_positivity
        _ = 8 * e * A := by_ring
  have hk2 := sq_le_of_min hk
  calc ztbja * (k : ℝ) ^ 2 ≤ ztbja * (2 * (μ : ℝ) ^ ztcd + 2) :=
        mul_le_mul_of_nonneg_left hk2 by_linarith
    _ = 2 * (ztbja * (μ : ℝ) ^ ztcd) + 2 * ztbja := by_ring
    _ ≤ 2 * (8 * e * A) + 2 * ztsud := by gcongr
    _ = ztigu * A := by_grind
end OracleQ
end
end Chazelle.Core
namespace Chazelle
namespace Exec
open Std
@[expose] public section
abbrev QPolygon : Type := List (ℚ × ℚ)

/-- A machine configuration over `ℚ`.  Register files and memories are hash maps; an absent key
denotes the value `0`, exactly like the all-zero initial configuration of the specification. -/
structure QConfig where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers (absent = `0`). -/
  nreg : HashMap ℕ ℕ
  /-- Rational registers (absent = `0`). -/
  rreg : HashMap ℕ ℚ
  /-- Natural memory (absent = `0`). -/
  nmem : HashMap ℕ ℕ
  /-- Rational memory (absent = `0`). -/
  rmem : HashMap ℕ ℚ
  /-- The triangles emitted so far, in order. -/
  output : List Polygon.Triangle
namespace QConfig

/-- Read natural register `r`. -/
def nr (c : QConfig) (r : ℕ) : ℕ := c.nreg.getD r 0

/-- Read rational register `r`. -/
def rr (c : QConfig) (r : ℕ) : ℚ := c.rreg.getD r 0

/-- Read natural memory cell `a`. -/
def nm (c : QConfig) (a : ℕ) : ℕ := c.nmem.getD a 0

/-- Read rational memory cell `a`. -/
def rm (c : QConfig) (a : ℕ) : ℚ := c.rmem.getD a 0
end QConfig

/-- Vertex lookup for a list-shaped rational polygon (as in `Polygon.vtx`). -/
def listVtx (Pq : QPolygon) : ℕ → ℚ × ℚ := fun i => Pq.getD i ztdr

/-! ## Basic facts -/
end
end Exec
namespace Geometry
@[expose] public section
variable (a b : Point) (t : ℝ) {s : Set Point} {S : Set Point}
@[simp] theorem add_fst : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem add_snd : (a + b).2 = a.2 + b.2 := rfl
@[simp] theorem sub_fst : (a - b).1 = a.1 - b.1 := rfl
@[simp] theorem sub_snd : (a - b).2 = a.2 - b.2 := rfl
@[simp] theorem smul_fst (a : Point) : (t • a).1 = t * a.1 := rfl
@[simp] theorem smul_snd (a : Point) : (t • a).2 = t * a.2 := rfl

/-- Two points are equal iff both coordinates agree. -/
theorem point_ext_iff {a b : Point} : a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := Prod.ext_iff

/-- Two points are equal if both coordinates agree. -/
theorem point_ext {a b : Point} (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := Prod.ext h1 h2

/-! ### The affine parametrisation `lerp` -/

/-- The point at parameter `t` on the line through `a` and `b`
(`t = 0` gives `a`, `t = 1` gives `b`). -/
def lerp (a b : Point) (t : ℝ) : Point := ztxwa
@[simp] theorem lerp_fst : (lerp a b t).1 = a.1 + t * (b.1 - a.1) := rfl
@[simp] theorem lerp_snd : (lerp a b t).2 = a.2 + t * (b.2 - a.2) := rfl

/-- `lerp a b t = a + t • (b - a)` as vectors. -/
theorem lerp_eq_add_smul : lerp a b t = a + t • zthu := by
  rfl

/-- `lerp a b t = (1 - t) • a + t • b` as vectors. -/
theorem lerp_eq_smul_add_smul : lerp a b t = ztca • a + t • b := by
  zuhun
@[simp] theorem lerp_zero : lerp a b 0 = a := by ext <;> simp [lerp]
@[simp] theorem lerp_one : lerp a b 1 = b := by ext <;> simp [lerp]

/-- Reversing the segment: `lerp b a t = lerp a b (1 - t)`. -/
theorem lerp_symm : lerp b a t = lerp a b ztca := by
  zuhun

/-- `lerp a b` is continuous in the parameter. -/
theorem continuous_lerp : Continuous zttsa := by
  zumti

/-- `lerp a b t` is injective in `t` when `a ≠ b`. -/
theorem lerp_injective {a b : Point} (hab : a ≠ b) : Function.Injective zttsa := by
  intro s t hst
  rw [point_ext_iff] at hst
  simp only [lerp_fst, lerp_snd] at hst
  grind

/-! ### The specification's segment is Mathlib's segment -/

/-- Membership in `Chazelle.segment` via `lerp`. -/
theorem mem_segment_iff_lerp {a b p : Point} :
    p ∈ Chazelle.segment a b ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = lerp a b t :=
  Iff.rfl

/-- `lerp a b t` lies on the segment for `0 ≤ t ≤ 1`. -/
theorem lerp_mem_segment {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp a b t ∈ Chazelle.segment a b :=
  ⟨t, h0, h1, rfl⟩

/-- The specification's closed segment is Mathlib's `segment ℝ a b`. -/
theorem segment_eq : Chazelle.segment a b = _root_.segment ℝ a b := by
  zufj
  rw [segment_eq_image']
  constructor
  · zuly
    exact ⟨t, ztcoy, (lerp_eq_add_smul a b t).symm⟩
  · zubcy
    exact ⟨t, ht0, ht1, lerp_eq_add_smul a b t⟩

/-- Membership in the segment via Mathlib's two-weight description. -/
theorem mem_segment_iff_weights {a b p : Point} :
    p ∈ Chazelle.segment a b ↔
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t = 1 ∧ s • a + t • b = p := by
  zunum; rfl

/-- The segment is symmetric. -/
theorem segment_comm : Chazelle.segment a b = Chazelle.segment b a := by
  rw [segment_eq, segment_eq, segment_symm]

/-- The left endpoint lies on the segment. -/
theorem left_mem_segment : a ∈ Chazelle.segment a b := by
  zunum; exact _root_.left_mem_segment ℝ a b

/-- The right endpoint lies on the segment. -/
theorem right_mem_segment : b ∈ Chazelle.segment a b := by
  zunum; exact _root_.right_mem_segment ℝ a b

/-- The segment is the convex hull of its endpoints. -/
theorem segment_eq_convexHull_pair :
    Chazelle.segment a b = convexHull ℝ {a, b} := by
  rw [segment_eq, convexHull_pair]

/-- A segment is convex. -/
theorem segment_convex : Convex ℝ ztemf := by
  rw [segment_eq]; exact convex_segment a b

/-- A segment with both endpoints in `s` lies in the convex hull of `s`. -/
theorem segment_subset_convexHull {a b : Point} (ha : a ∈ s) (hb : b ∈ s) :
    Chazelle.segment a b ⊆ convexHull ℝ s := by
  rw [segment_eq]; exact _root_.segment_subset_convexHull ha hb

/-- A segment with both endpoints in a convex set lies in it. -/
theorem segment_subset_of_convex (hs : Convex ℝ s) {a b : Point}
    (ha : a ∈ s) (hb : b ∈ s) : Chazelle.segment a b ⊆ s := by
  zunum; exact hs.segment_subset ha hb

/-- The convex hull of a finite set of points is compact. -/
theorem isCompact_convexHull_of_finite (hs : s.Finite) :
    IsCompact (convexHull ℝ s) :=
  hs.isCompact_convexHull ℝ

/-- A segment is compact. -/
theorem isCompact_segment : IsCompact ztemf := by
  rw [segment_eq_convexHull_pair]
  exact isCompact_convexHull_of_finite ((Set.finite_singleton b).insert a)

/-- A segment is closed. -/
theorem isClosed_segment : IsClosed ztemf :=
  (isCompact_segment a b).isClosed

/-- A segment is the continuous image of `[0,1]` under `lerp a b`. -/
theorem segment_eq_image_lerp :
    Chazelle.segment a b = lerp a b '' Set.Icc (0 : ℝ) 1 := by
  zufj
  constructor
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩

/-! ### Bounded sets -/

/-- The specification's boundedness is Mathlib's `Bornology.IsBounded` (sup norm). -/
theorem isBoundedSet_iff : IsBoundedSet S ↔ Bornology.IsBounded S := by
  constructor
  · zudtb
    refine isBounded_iff_forall_norm_le.2 ztexn
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    grind
  · zuq
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 h
    refine ⟨C, fun p hp => ?_⟩
    have h1 := (norm_fst_le p).trans zttma
    have h2 := (norm_snd_le p).trans zttma
    simp_all

/-- A subset of a bounded set is bounded. -/
theorem isBoundedSet_of_subset {S T : Set Point} (hT : IsBoundedSet T) (h : S ⊆ T) :
    IsBoundedSet S := by
  rw [isBoundedSet_iff] at hT ⊢
  exact hT.subset h

/-- A compact set is bounded. -/
theorem isBoundedSet_of_isCompact (hS : IsCompact S) : IsBoundedSet S := by
  rw [isBoundedSet_iff]; grind
end
public section
variable (a b c : Point)
/-- Swapping the first two arguments negates the determinant. -/
theorem det_swap12 : det b a c = - det a b c := by
  zucaf

/-- Swapping the last two arguments negates the determinant. -/
theorem det_swap23 : det a c b = - det a b c := by
  zucaf

/-- Swapping the outer arguments negates the determinant. -/
theorem det_swap13 : det c b a = - det a b c := by
  zucaf

/-- The determinant is invariant under cyclic rotation. -/
theorem det_cyclic : det b c a = det a b c := by
  zucaf

/-- The determinant is invariant under the other cyclic rotation. -/
theorem det_cyclic_right : det c a b = det a b c := by
  zucaf
@[simp] theorem det_self_left (a c : Point) : det a a c = 0 := by
  zucaf
@[simp] theorem det_self_right (a b : Point) : det a b b = 0 := by
  zucaf
@[simp] theorem det_self_outer (a b : Point) : det a b a = 0 := by
  zucaf

/-- A nonzero determinant forces the three points to be pairwise distinct. -/
theorem ne_of_det_ne_zero {a b c : Point} (h : det a b c ≠ 0) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  zusk
  · zujgh
  · zujgh
  · zujgh

/-! ### Affinity along segments -/

/-- The determinant is affine in its last argument along `lerp`. -/
theorem det_lerp (a b p q : Point) (t : ℝ) :
    det a b ztefl = ztca * det a b p + t * det a b q := by
  zuhqr

/-- The determinant is affine in its middle argument along `lerp`. -/
theorem det_lerp_mid (a c p q : Point) (t : ℝ) :
    det a ztefl c = ztca * det a p c + t * det a q c := by
  zuhqr

/-- The determinant is affine in its first argument along `lerp`. -/
theorem det_lerp_left (b c p q : Point) (t : ℝ) :
    det ztefl b c = ztca * det p b c + t * det q b c := by
  zuhqr

/-- The determinant is affine in its last argument along `x + t • v`. -/
theorem det_add_smul (a b x v : Point) (t : ℝ) :
    det a b (x + t • v) = det a b x + t * det a b (a + v) := by
  unfold det; zvneh; ring

/-- The determinant vanishes on the segment: `c ∈ segment a b → det a b c = 0`. -/
theorem det_eq_zero_of_mem_segment {a b c : Point} (h : c ∈ Chazelle.segment a b) :
    det a b c = 0 := by
  obtain ⟨t, -, -, rfl⟩ := mem_segment_iff_lerp.1 h
  zukqo

/-- The determinant vanishes on the line through `a` and `b`. -/
theorem det_lerp_self (a b : Point) (t : ℝ) : det a b ztrtg = 0 := by
  zukqo

/-- Converse: if `det a b c = 0` and `a ≠ b`, then `c` lies on the line through `a` and `b`. -/
theorem exists_lerp_of_det_eq_zero {a b c : Point} (hab : a ≠ b) (h : det a b c = 0) :
    ∃ t : ℝ, c = lerp a b t := by
  zumsh
  by_cases h1 : b.1 - a.1 = 0
  · have h2 : ztmuc := by
      grind
    refine ⟨ztnwh / ztti, point_ext ?_ ?_⟩
    · simp only [lerp_fst]
      grind
    simp_all
  · refine ⟨ztnwg / ztbco, point_ext ?_ ?_⟩
    · simp_all
    · zujop

/-! ### Continuity -/

/-- `x ↦ det a b x` is continuous. -/
theorem continuous_det_right (a b : Point) : Continuous (fun x : Point => det a b x) := by
  zujqk

/-- `x ↦ det a x c` is continuous. -/
theorem continuous_det_mid (a c : Point) : Continuous (fun x : Point => det a x c) := by
  zujqk

/-- `x ↦ det x b c` is continuous. -/
theorem continuous_det_left (b c : Point) : Continuous (fun x : Point => det x b c) := by
  zujqk

/-! ### The barycentric identities -/

/-- The three sub-determinants of `x` in the triangle `a b c` sum to `det a b c`. -/
theorem det_bary_sum (a b c x : Point) : det x b c + det a x c + det a b x = det a b c := by
  zucaf

/-- The barycentric reconstruction identity (in vector form). -/
theorem det_smul_eq_bary_combination (a b c x : Point) :
    det a b c • x = det x b c • a + det a x c • b + det a b x • c := by
  unfold det; ext <;> zvneh <;> ring

/-- Multilinearity: `det` of a convex combination in the last slot. -/
theorem det_smul_add_smul_add_smul (a b p q r : Point) (u v w : ℝ) (huvw : u + v + w = 1) :
    det a b (u • p + v • q + w • r) = u * det a b p + v * det a b q + w * det a b r := by
  zulbn
  zvneh
  grind
end
open Topology
@[expose] public section
variable (a b c : Point)
/-- The vertices lie in the triangle. -/
theorem vertex_mem_triangle_left : a ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ by_simp
theorem vertex_mem_triangle_mid : b ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ by_simp
theorem vertex_mem_triangle_right : c ∈ convexHull ℝ ({a, b, c} : Set Point) :=
  subset_convexHull ℝ _ by_simp

/-- A point of `convexHull ℝ {a, b, c}` is a convex combination of `a`, `b`, `c`
(no nondegeneracy needed). -/
theorem mem_convexHull_triple {a b c x : Point} :
    x ∈ convexHull ℝ ({a, b, c} : Set Point) ↔
      ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 ≤ w₃ ∧ w₁ + w₂ + w₃ = 1 ∧
        x = w₁ • a + w₂ • b + w₃ • c := by
  constructor
  · zuetb
    -- the set of convex combinations is convex and contains the three points
    suffices hS : convexHull ℝ ({a, b, c} : Set Point) ⊆
        {y : Point | ∃ w₁ w₂ w₃ : ℝ, 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ 0 ≤ w₃ ∧ w₁ + w₂ + w₃ = 1 ∧
          y = w₁ • a + w₂ • b + w₃ • c} from hS hx
    zumjb
    · zusy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, zero_le_one, le_rfl, le_rfl, by_norm_num, by_simp⟩
      · exact ⟨0, 1, 0, le_rfl, zero_le_one, le_rfl, by_norm_num, by_simp⟩
      · exact ⟨0, 0, 1, le_rfl, le_rfl, zero_le_one, by_norm_num, by_simp⟩
    · rintro y ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hu, rfl⟩ z ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, hv, rfl⟩
        s t hs ht hst
      refine ⟨s * u₁ + t * v₁, s * u₂ + t * v₂, s * u₃ + t * v₃, by_positivity, by_positivity,
        by positivity, by_grind, ?_⟩
      ext <;> zvneh <;> ring
  · zudfm
    have h := (convex_convexHull ℝ ({a, b, c} : Set Point)).sum_mem (t := Finset.univ)
      (w := ![w₁, w₂, w₃]) (z := ![a, b, c]) ?_ ?_ ?_
    · simpa [Fin.sum_univ_three] using h
    · zuhgt
      fin_cases i <;> simp [hw₁, hw₂, hw₃]
    · simp [Fin.sum_univ_three, hw]
    · zuhgt
      fin_cases i <;> simp [vertex_mem_triangle_left, vertex_mem_triangle_mid,
        vertex_mem_triangle_right]

/-! ### Barycentric coordinates -/

/-- First barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₁ (a b c x : Point) : ℝ := det x b c / det a b c

/-- Second barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₂ (a b c x : Point) : ℝ := det a x c / det a b c

/-- Third barycentric coordinate of `x` with respect to the triangle `a b c`. -/
noncomputable def bary₃ (a b c x : Point) : ℝ := det a b x / det a b c

/-- The barycentric coordinates sum to `1`. -/
theorem bary_sum {a b c : Point} (h : det a b c ≠ 0) (x : Point) :
    bary₁ a b c x + bary₂ a b c x + bary₃ a b c x = 1 := by
  zumrr
  rw [← add_div, ← add_div, det_bary_sum, div_self h]

/-- The barycentric reconstruction: `x = bary₁ • a + bary₂ • b + bary₃ • c`. -/
theorem bary_reconstruct {a b c : Point} (h : det a b c ≠ 0) (x : Point) :
    x = bary₁ a b c x • a + bary₂ a b c x • b + bary₃ a b c x • c := by
  have hid := det_smul_eq_bary_combination a b c x
  rw [point_ext_iff] at hid ⊢
  zvneh at hid ⊢
  zumrr
  grind

/-- Uniqueness of barycentric coordinates: the third coordinate of
`w₁ • a + w₂ • b + w₃ • c` (weights summing to `1`) is `w₃`. -/
theorem bary₃_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₃ a b c ztewj = w₃ := by
  unfold bary₃
  rw [det_smul_add_smul_add_smul a b a b c w₁ w₂ w₃ hw]
  simp_all

/-- The first barycentric coordinate of `w₁ • a + w₂ • b + w₃ • c` is `w₁`. -/
theorem bary₁_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₁ a b c ztewj = w₁ := by
  unfold bary₁
  rw [← det_cyclic, det_smul_add_smul_add_smul b c a b c w₁ w₂ w₃ hw]
  simp only [det_self_outer, det_self_right, mul_zero, add_zero, det_cyclic]
  simp_all

/-- The second barycentric coordinate of `w₁ • a + w₂ • b + w₃ • c` is `w₂`. -/
theorem bary₂_combination {a b c : Point} (h : det a b c ≠ 0) {w₁ w₂ w₃ : ℝ}
    (hw : w₁ + w₂ + w₃ = 1) : bary₂ a b c ztewj = w₂ := by
  unfold bary₂
  rw [← det_cyclic_right, det_smul_add_smul_add_smul c a a b c w₁ w₂ w₃ hw]
  simp only [det_self_right, det_self_outer, mul_zero, zero_add, add_zero, det_cyclic_right]
  simp_all
@[simp] theorem bary₁_vertex_left {a b c : Point} (h : det a b c ≠ 0) : bary₁ a b c a = 1 := by
  unfold bary₁; simp_all
@[simp] theorem bary₂_vertex_left : bary₂ a b c a = 0 := by
  zumrt
@[simp] theorem bary₃_vertex_left : bary₃ a b c a = 0 := by
  zumru
@[simp] theorem bary₁_vertex_mid : bary₁ a b c b = 0 := by
  zumrs
@[simp] theorem bary₂_vertex_mid {a b c : Point} (h : det a b c ≠ 0) : bary₂ a b c b = 1 := by
  unfold bary₂; simp_all
@[simp] theorem bary₃_vertex_mid : bary₃ a b c b = 0 := by
  zumru
@[simp] theorem bary₁_vertex_right : bary₁ a b c c = 0 := by
  zumrs
@[simp] theorem bary₂_vertex_right : bary₂ a b c c = 0 := by
  zumrt
@[simp] theorem bary₃_vertex_right {a b c : Point} (h : det a b c ≠ 0) : bary₃ a b c c = 1 := by
  zumrv

/-- `bary₁` is continuous in the point. -/
theorem continuous_bary₁ : Continuous (bary₁ a b c) :=
  (continuous_det_left b c).div_const _

/-- `bary₂` is continuous in the point. -/
theorem continuous_bary₂ : Continuous (bary₂ a b c) :=
  (continuous_det_mid a c).div_const _

/-- `bary₃` is continuous in the point. -/
theorem continuous_bary₃ : Continuous (bary₃ a b c) :=
  (continuous_det_right a b).div_const _

/-- `bary₁` is affine along segments. -/
theorem bary₁_lerp (a b c p q : Point) (t : ℝ) :
    bary₁ a b c ztefl = ztca * bary₁ a b c p + t * bary₁ a b c q := by
  unfold bary₁; rw [det_lerp_left]; ring

/-- `bary₂` is affine along segments. -/
theorem bary₂_lerp (a b c p q : Point) (t : ℝ) :
    bary₂ a b c ztefl = ztca * bary₂ a b c p + t * bary₂ a b c q := by
  unfold bary₂; rw [det_lerp_mid]; ring

/-- `bary₃` is affine along segments. -/
theorem bary₃_lerp (a b c p q : Point) (t : ℝ) :
    bary₃ a b c ztefl = ztca * bary₃ a b c p + t * bary₃ a b c q := by
  unfold bary₃; zuoha; ring

/-- Membership in a nondegenerate triangle: all barycentric coordinates are nonnegative. -/
theorem mem_triangle_iff_bary {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ convexHull ℝ ({a, b, c} : Set Point) ↔
      0 ≤ bary₁ a b c x ∧ 0 ≤ bary₂ a b c x ∧ 0 ≤ bary₃ a b c x := by
  rw [mem_convexHull_triple]
  constructor
  · zudfm
    zuelh
    simp_all
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨_, _, _, h₁, h₂, h₃, bary_sum h x, bary_reconstruct h x⟩

/-! ### Topology of a triangle -/

/-- A triangle is convex. -/
theorem convex_triangle : Convex ℝ ztlk :=
  convex_convexHull ℝ _

/-- A triangle is compact. -/
theorem isCompact_triangle :
    IsCompact ztlk :=
  isCompact_convexHull_of_finite by_simp_all

/-- A triangle is closed. -/
theorem isClosed_triangle : IsClosed ztlk :=
  (isCompact_triangle a b c).isClosed

/-- A triangle is bounded. -/
theorem triangle_bounded :
    IsBoundedSet ztlk :=
  isBoundedSet_of_isCompact (isCompact_triangle a b c)

/-- The open set `{0 < bary₁} ∩ {0 < bary₂} ∩ {0 < bary₃}`. -/
theorem isOpen_bary_pos :
    IsOpen {x : Point | 0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x} := by
  have h₁ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₁ a b c)
  have h₂ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₂ a b c)
  have h₃ := isOpen_lt (continuous_const (y := (0 : ℝ))) (continuous_bary₃ a b c)
  exact h₁.inter (h₂.inter h₃)

/-- Auxiliary: if `f` is affine along `lerp v x`, nonnegative on `T`, `f v = 1` and
`f x = 0`, then `x` is not an interior point of `T`. -/
theorem not_mem_interior_of_affine_zero {T : Set Point} {v x : Point} {f : Point → ℝ}
    (hT : ∀ y ∈ T, 0 ≤ f y) (hf : ∀ s : ℝ, f (lerp v x s) = zteb * f v + s * f x)
    (hv : f v = 1) (hx : f x = 0) : x ∉ interior T := by
  intro hint
  rw [mem_interior_iff_mem_nhds] at hint
  have hc : ContinuousAt (lerp v x) 1 := (continuous_lerp v x).continuousAt
  have hpre : ∀ᶠ s in 𝓝 (1 : ℝ), lerp v x s ∈ T := by
    have := hc.preimage_mem_nhds (by rwa [lerp_one])
    tauto
  have h1 : ∀ᶠ s in 𝓝[>] (1 : ℝ), lerp v x s ∈ T := hpre.filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs, hs1⟩ := (h1.and self_mem_nhdsWithin).exists
  have := hT _ hs
  rw [hf, hv, hx] at this
  grind

/-- The interior of a nondegenerate triangle: all barycentric coordinates positive. -/
theorem interior_triangle {a b c : Point} (h : det a b c ≠ 0) :
    interior ztlk =
      {x | 0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x} := by
  zuldc
  · zuh
    have hxT := interior_subset hx
    rw [mem_triangle_iff_bary h] at hxT
    obtain ⟨h₁, h₂, h₃⟩ := hxT
    refine ⟨lt_of_le_of_ne h₁ ?_, lt_of_le_of_ne h₂ ?_, lt_of_le_of_ne h₃ ?_⟩
    · zubww
      refine not_mem_interior_of_affine_zero ?_
        (bary₁_lerp a b c a x) (bary₁_vertex_left h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).1
    · zubww
      refine not_mem_interior_of_affine_zero ?_
        (bary₂_lerp a b c b x) (bary₂_vertex_mid h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).2.1
    · zubww
      refine not_mem_interior_of_affine_zero ?_
        (bary₃_lerp a b c c x) (bary₃_vertex_right h) h0.symm hx
      intro y hy; exact ((mem_triangle_iff_bary h).1 hy).2.2
  · apply interior_maximal _ (isOpen_bary_pos a b c)
    rintro x ⟨h₁, h₂, h₃⟩
    exact (mem_triangle_iff_bary h).2 by_grind

/-- Membership in the interior of a nondegenerate triangle. -/
theorem mem_interior_triangle_iff {a b c : Point} (h : det a b c ≠ 0) {x : Point} :
    x ∈ interior ztlk ↔
      0 < bary₁ a b c x ∧ 0 < bary₂ a b c x ∧ 0 < bary₃ a b c x := by
  rw [interior_triangle h]; rfl

/-- The centroid of a triangle. -/
noncomputable def centroid (a b c : Point) : Point :=
  (1 / 3 : ℝ) • a + (1 / 3 : ℝ) • b + (1 / 3 : ℝ) • c

/-- The centroid is an interior point of a nondegenerate triangle. -/
theorem centroid_mem_interior {a b c : Point} (h : det a b c ≠ 0) :
    centroid a b c ∈ interior ztlk := by
  rw [mem_interior_triangle_iff h]
  have hw : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1 := by_norm_num
  unfold centroid
  zuelh
  norm_num

/-- A nondegenerate triangle has nonempty interior. -/
theorem interior_triangle_nonempty {a b c : Point} (h : det a b c ≠ 0) :
    (interior ztlk).Nonempty :=
  ⟨_, centroid_mem_interior h⟩

/-- The closure of the interior of a nondegenerate triangle is the triangle. -/
theorem closure_interior_triangle {a b c : Point} (h : det a b c ≠ 0) :
    closure ztbahy =
      convexHull ℝ ({a, b, c} : Set Point) := by
  rw [(convex_triangle a b c).closure_interior_eq_closure_of_nonempty_interior
    (interior_triangle_nonempty h)]
  exact (isClosed_triangle a b c).closure_eq

/-! ### Faces -/

/-- The edge `a b` lies in the triangle. -/
theorem segment_subset_triangle_left :
    Chazelle.segment a b ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull by_simp by_simp

/-- The edge `b c` lies in the triangle. -/
theorem segment_subset_triangle_mid :
    Chazelle.segment b c ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull by_simp by_simp

/-- The edge `a c` lies in the triangle. -/
theorem segment_subset_triangle_right :
    Chazelle.segment a c ⊆ convexHull ℝ ({a, b, c} : Set Point) :=
  segment_subset_convexHull by_simp by_simp

/-- On the edge `a b`, the third barycentric coordinate vanishes (no nondegeneracy needed). -/
theorem bary₃_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ Chazelle.segment a b) :
    bary₃ a b c x = 0 := by
  unfold bary₃; rw [det_eq_zero_of_mem_segment hx, zero_div]

/-- On the edge `b c`, the first barycentric coordinate vanishes. -/
theorem bary₁_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ Chazelle.segment b c) :
    bary₁ a b c x = 0 := by
  unfold bary₁; rw [← det_cyclic, det_eq_zero_of_mem_segment hx, zero_div]

/-- On the edge `a c`, the second barycentric coordinate vanishes. -/
theorem bary₂_eq_zero_of_mem_segment {a b c x : Point} (hx : x ∈ Chazelle.segment a c) :
    bary₂ a b c x = 0 := by
  unfold bary₂; rw [det_swap23, det_eq_zero_of_mem_segment hx, neg_zero, zero_div]

/-- A point of a nondegenerate triangle with `bary₃ = 0` lies on the edge `a b`. -/
theorem mem_segment_of_bary₃_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h3 : bary₃ a b c x = 0) :
    x ∈ Chazelle.segment a b := by
  obtain ⟨h₁, h₂, -⟩ := (mem_triangle_iff_bary h).1 hx
  zucde

  rw [h3, zero_smul, add_zero] at hr
  rw [h3, add_zero] at hs
  zulfq

/-- A point of a nondegenerate triangle with `bary₁ = 0` lies on the edge `b c`. -/
theorem mem_segment_of_bary₁_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h1 : bary₁ a b c x = 0) :
    x ∈ Chazelle.segment b c := by
  obtain ⟨-, h₂, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  zucde

  rw [h1, zero_smul, zero_add] at hr
  rw [h1, zero_add] at hs
  zulfq

/-- A point of a nondegenerate triangle with `bary₂ = 0` lies on the edge `a c`. -/
theorem mem_segment_of_bary₂_eq_zero {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point)) (h2 : bary₂ a b c x = 0) :
    x ∈ Chazelle.segment a c := by
  obtain ⟨h₁, -, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  zucde

  rw [h2, zero_smul, add_zero] at hr
  rw [h2, add_zero] at hs
  zulfq

/-- A point of a nondegenerate triangle that is not interior lies on one of the three edges. -/
theorem mem_edge_of_not_mem_interior {a b c : Point} (h : det a b c ≠ 0) {x : Point}
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set Point))
    (hint : x ∉ interior ztlk) :
    x ∈ Chazelle.segment a b ∨ x ∈ Chazelle.segment b c ∨ x ∈ Chazelle.segment a c := by
  obtain ⟨h₁, h₂, h₃⟩ := (mem_triangle_iff_bary h).1 hx
  rw [mem_interior_triangle_iff h] at hint
  by_cases e₁ : bary₁ a b c x = 0
  · exact Or.inr (Or.inl (mem_segment_of_bary₁_eq_zero h hx e₁))
  by_cases e₂ : bary₂ a b c x = 0
  · exact Or.inr (Or.inr (mem_segment_of_bary₂_eq_zero h hx e₂))
  by_cases e₃ : bary₃ a b c x = 0
  · exact Or.inl (mem_segment_of_bary₃_eq_zero h hx e₃)
  grind

/-! ### The specification's triangles -/

/-- A valid triangle has nonzero determinant. -/
theorem det_ne_zero_of_validTriangle {P : Polygon} {t : Polygon.Triangle}
    (h : P.validTriangle t) : det (P.vtx t.1) (P.vtx t.2.1) (P.vtx t.2.2) ≠ 0 :=
  h.2.2.2
def lin (α β : ℝ) : Point →ₗ[ℝ] ℝ where
  toFun p := α * p.1 + β * p.2
  map_add' := by intro p q; simp only [add_fst, add_snd]; ring
  map_smul' := by intro t p; simp only [smul_fst, smul_snd, smul_eq_mul, RingHom.id_apply]; ring
@[simp] theorem lin_apply (α β : ℝ) (p : Point) : lin α β p = α * p.1 + β * p.2 := rfl
variable (φ : Point →ₗ[ℝ] ℝ) (s : Finset Point) (a b c : Point) {A : Set ℝ}
/-- Every linear functional on the plane is `lin α β` with `α = φ (1,0)`, `β = φ (0,1)`. -/
theorem linearMap_apply_eq (p : Point) :
    φ p = φ ztcei * p.1 + φ ztjeb * p.2 := by
  have hp : p = p.1 • (ztcei : Point) + p.2 • (ztjeb : Point) := by
    simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- A level set `{φ = u}` of a linear functional is convex. -/
theorem convex_level (u : ℝ) : Convex ℝ {x : Point | φ x = u} :=
  (convex_singleton u).linear_preimage φ

/-- For a nonzero linear functional `φ` there is a linear functional injective on every level
set of `φ`. -/
theorem exists_injOn_level {φ : Point →ₗ[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ∃ ψ : Point →ₗ[ℝ] ℝ, Set.InjOn ψ {x : Point | φ x = u} := by
  set α := φ ztcei with hα
  set β := φ ztjeb with hβ
  have hne : ¬ (α = 0 ∧ β = 0) := by
    zubf
    apply hφ
    apply LinearMap.ext
    zukjq
    rw [linearMap_apply_eq φ p, ← hα, ← hβ, h1, h2]
    simp
  have hαβ : α ^ 2 + β ^ 2 ≠ 0 := by
    zubww
    zufqo
    constructor <;> nlinarith [sq_nonneg α, sq_nonneg β]
  refine ⟨lin (-β) α, ?_⟩
  zuvc
  simp only [Set.mem_ofPred_eq] at hx hy
  rw [linearMap_apply_eq φ x, ← hα, ← hβ] at hx
  rw [linearMap_apply_eq φ y, ← hα, ← hβ] at hy
  simp only [lin_apply] at hxy
  grind

/-! ### Faces: a hull in a half-plane meets the boundary line in a face -/

/-- If a finite set `s` lies in the half-plane `{φ ≤ u}`, then the part of its convex hull
on the line `{φ = u}` is the convex hull of the points of `s` on that line. -/
theorem convexHull_inter_level_le (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (hs : ∀ y ∈ s, φ y ≤ u) :
    convexHull ℝ (s : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ztgwg := by
  classical
  zuldc
  · rintro x ⟨hx, hxu⟩
    simp only [Set.mem_ofPred_eq] at hxu
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hx
    -- all weight sits on vertices with `φ y = u`
    have hsum : ∑ y ∈ s, w y * ztrxr = 0 := by
      have hφx : φ x = ∑ y ∈ s, w y * φ y := by
        rw [← hwx, map_sum]
        simp
      have : ∑ y ∈ s, w y * ztrxr = u * ∑ y ∈ s, w y - ∑ y ∈ s, w y * φ y := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        grind
      simp_all
    have hzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y hy => mul_nonneg by_simp_all by_simp_all)).1 hsum
    have hw' : ∀ y ∈ s, w y ≠ 0 → φ y = u := by
      grind
    have hcoe : ((s.filter (fun y => φ y = u) : Finset Point) : Set Point) =
        (s : Set Point) ∩ {x | φ x = u} := by
      grind
    rw [← hcoe, Finset.mem_convexHull']
    refine ⟨w, by_simp_all, ?_, ?_⟩
    · rw [Finset.sum_filter_of_ne by_omega, hw1]
    · rw [Finset.sum_filter_of_ne, hwx]
      simp_all
  · apply Set.subset_inter
    · exact convexHull_mono Set.inter_subset_left
    · exact convexHull_min Set.inter_subset_right (convex_level φ u)

/-- The half-plane `{φ ≥ u}` version of `convexHull_inter_level_le`. -/
theorem convexHull_inter_level_ge (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (hs : ∀ y ∈ s, u ≤ φ y) :
    convexHull ℝ (s : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ztgwg := by
  have hL : {x : Point | (-φ) x = -u} = {x | φ x = u} := by
    simp
  rw [← hL]
  exact convexHull_inter_level_le s _ _
    by_simp_all

/-- The triangle version of `convexHull_inter_level_le`. -/
theorem triangle_inter_level_le (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (ha : φ a ≤ u) (hb : φ b ≤ u) (hc : φ c ≤ u) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ztfav := by
  classical
  have h := convexHull_inter_level_le ({a, b, c} : Finset Point) φ u (by
    simp_all)
  zuhqg

/-- The triangle version of `convexHull_inter_level_ge`. -/
theorem triangle_inter_level_ge (φ : Point →ₗ[ℝ] ℝ) (u : ℝ)
    (ha : u ≤ φ a) (hb : u ≤ φ b) (hc : u ≤ φ c) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ {x | φ x = u} =
      convexHull ℝ ztfav := by
  classical
  have h := convexHull_inter_level_ge ({a, b, c} : Finset Point) φ u (by
    simp_all)
  zuhqg

/-! ### Intersections of convex hulls on a line -/

/-- A point of the convex hull of `A ⊆ ℝ` is bracketed by two points of `A`. -/
theorem exists_le_le_of_mem_convexHull_real {x : ℝ} (hx : x ∈ convexHull ℝ A) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≤ x ∧ x ≤ a₂ := by
  suffices hS : convexHull ℝ A ⊆ {y : ℝ | ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≤ y ∧ y ≤ a₂} from hS hx
  zumjb
  · grind
  · rw [convex_iff_ordConnected]
    refine ⟨?_⟩
    grind

/-- A real number between two points of `A` lies in the convex hull of `A`. -/
theorem mem_convexHull_real_of_between {a₁ a₂ y : ℝ} (h₁ : a₁ ∈ A) (h₂ : a₂ ∈ A)
    (hy₁ : a₁ ≤ y) (hy₂ : y ≤ a₂) : y ∈ convexHull ℝ A := by
  have : y ∈ _root_.segment ℝ a₁ a₂ := by
    rw [segment_eq_Icc (hy₁.trans hy₂)]; simp_all
  exact _root_.segment_subset_convexHull h₁ h₂ this

/-- On the real line: if no point of `B` lies in the hull of `A` unless it belongs to `A`,
and symmetrically, then the two hulls meet exactly in the hull of `A ∩ B`. -/
theorem convexHull_inter_convexHull_real {A B : Set ℝ}
    (hAB : ∀ y ∈ B, y ∈ convexHull ℝ A → y ∈ A)
    (hBA : ∀ y ∈ A, y ∈ convexHull ℝ B → y ∈ B) :
    convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ ztnis := by
  zuldc
  · zujgj
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa₁, hxa₂⟩ := exists_le_le_of_mem_convexHull_real hxA
    obtain ⟨b₁, hb₁, b₂, hb₂, hxb₁, hxb₂⟩ := exists_le_le_of_mem_convexHull_real hxB
    have hlo : max a₁ b₁ ∈ A ∩ B := by
      rcases le_total a₁ b₁ with h | h
      · rw [max_eq_right h]
        exact ⟨hAB b₁ hb₁ (mem_convexHull_real_of_between ha₁ ha₂ h ztvwr), hb₁⟩
      · rw [max_eq_left h]
        exact ⟨ha₁, hBA a₁ ha₁ (mem_convexHull_real_of_between hb₁ hb₂ h ztvwq)⟩
    have hhi : min a₂ b₂ ∈ A ∩ B := by
      rcases le_total a₂ b₂ with h | h
      · rw [min_eq_left h]
        exact ⟨ha₂, hBA a₂ ha₂ (mem_convexHull_real_of_between hb₁ hb₂ ztvwr h)⟩
      · rw [min_eq_right h]
        exact ⟨hAB b₂ hb₂ (mem_convexHull_real_of_between ha₁ ha₂ ztvwq h), hb₂⟩
    exact mem_convexHull_real_of_between hlo hhi by_simp_all by_simp_all
  · exact Set.subset_inter ztvlm
      ztvln

/-- Transport of `convexHull_inter_convexHull_real` to a convex set `L` of the plane on which
some linear functional `ψ` is injective (e.g. a line). -/
theorem convexHull_inter_convexHull_of_injOn {L : Set Point} (hL : Convex ℝ L)
    (ψ : Point →ₗ[ℝ] ℝ) (hψ : Set.InjOn ψ L) {A B : Set Point} (hA : A ⊆ L) (hB : B ⊆ L)
    (hAB : ∀ y ∈ B, y ∈ convexHull ℝ A → y ∈ A)
    (hBA : ∀ y ∈ A, y ∈ convexHull ℝ B → y ∈ B) :
    convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ ztnis := by
  have hAL : convexHull ℝ A ⊆ L := by_simp_all
  have hBL : convexHull ℝ B ⊆ L := by_simp_all
  have hABL : convexHull ℝ ztnis ⊆ L := convexHull_min (Set.inter_subset_left.trans hA) hL
  zuldc
  · zujgj
    -- the images under `ψ`
    have hAB' : ∀ y ∈ ψ '' B, y ∈ convexHull ℝ ztufk → y ∈ ψ '' A := by
      zubsd

      have  := hψ (hAL hz) (hB hy) hzy
      grind
    have hBA' : ∀ y ∈ ψ '' A, y ∈ convexHull ℝ ztufl → y ∈ ψ '' B := by
      zubsd

      have  := hψ (hBL hz) (hA hy) hzy
      grind
    have hx' : ψ x ∈ convexHull ℝ ztufk ∩ convexHull ℝ ztufl := by
      rw [← LinearMap.image_convexHull, ← LinearMap.image_convexHull]
      grind
    rw [convexHull_inter_convexHull_real hAB' hBA', ← hψ.image_inter hA hB,
      ← LinearMap.image_convexHull] at hx'
    obtain ⟨z, hz, hzx⟩ := hx'
    have  := hψ (hABL hz) (hAL hxA) hzx
    grind
  · exact Set.subset_inter ztvlm
      ztvln

/-! ### The conformity criterion -/

/-- **Conformity criterion.**  Two nondegenerate triangles with disjoint interiors, such that
every vertex of either lying in the other triangle is a vertex of it, meet exactly in the
convex hull of their common vertices. -/
theorem conforming_of_disjoint_interiors {a b c d e f : Point}
    (habc : det a b c ≠ 0) (hdef : det d e f ≠ 0)
    (hdisj : Disjoint ztbahy
      (interior (convexHull ℝ ({d, e, f} : Set Point))))
    (hv₁ : ∀ v ∈ ({d, e, f} : Set Point),
      v ∈ convexHull ℝ ({a, b, c} : Set Point) → v ∈ ({a, b, c} : Set Point))
    (hv₂ : ∀ v ∈ ({a, b, c} : Set Point),
      v ∈ convexHull ℝ ({d, e, f} : Set Point) → v ∈ ({d, e, f} : Set Point)) :
    convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) =
      convexHull ℝ (({a, b, c} : Set Point) ∩ {d, e, f}) := by
  -- separate the interiors by a line
  obtain ⟨φ, u, h₁, h₂⟩ := geometric_hahn_banach_open_open
    (convex_triangle a b c).interior isOpen_interior
    (convex_triangle d e f).interior isOpen_interior hdisj
  set φl : Point →ₗ[ℝ] ℝ := (φ : Point →ₗ[ℝ] ℝ) with hφl
  have hφl_apply : ∀ x, φl x = φ x := fun _ => rfl
  -- `φ ≤ u` on the first closed triangle, `φ ≥ u` on the second
  have hT₁ : ∀ x ∈ convexHull ℝ ({a, b, c} : Set Point), φl x ≤ u := by
    zuh
    rw [← closure_interior_triangle habc] at hx
    exact closure_minimal (fun y hy => (h₁ y hy).le)
      (isClosed_le φ.continuous continuous_const) hx
  have hT₂ : ∀ x ∈ convexHull ℝ ({d, e, f} : Set Point), u ≤ φl x := by
    zuh
    rw [← closure_interior_triangle hdef] at hx
    exact closure_minimal (fun y hy => (h₂ y hy).le)
      (isClosed_le continuous_const φ.continuous) hx
  -- `φ` is not zero
  have hφ0 : φl ≠ 0 := by
    zubww
    obtain ⟨p, hp⟩ := interior_triangle_nonempty habc
    obtain ⟨q, hq⟩ := interior_triangle_nonempty hdef
    have h1 := h₁ p hp
    have h2 := h₂ q hq
    rw [← hφl_apply, h0] at h1 h2
    simp at h1 h2
    linarith
  set L : Set Point := {x | φl x = u} with hLdef
  have hL := convex_level φl u
  obtain ⟨ψ, hψ⟩ := exists_injOn_level hφ0 u
  -- the intersection lies on the line
  have hsub : convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) ⊆ L :=
    by grind
  have hV : ({a, b, c} : Set Point) ∩ {d, e, f} ⊆ L :=
    fun x ⟨hx₁, hx₂⟩ => hsub ⟨subset_convexHull ℝ _ hx₁, subset_convexHull ℝ _ hx₂⟩
  -- rewrite the intersection through the line
  have hface₁ := triangle_inter_level_le a b c φl u
    (hT₁ a (vertex_mem_triangle_left a b c)) (hT₁ b (vertex_mem_triangle_mid a b c))
    (hT₁ c (vertex_mem_triangle_right a b c))
  have hface₂ := triangle_inter_level_ge d e f φl u
    (hT₂ d (vertex_mem_triangle_left d e f)) (hT₂ e (vertex_mem_triangle_mid d e f))
    (hT₂ f (vertex_mem_triangle_right d e f))
  have hinter : convexHull ℝ ({a, b, c} : Set Point) ∩ convexHull ℝ ({d, e, f} : Set Point) =
      (convexHull ℝ ({a, b, c} : Set Point) ∩ L) ∩ (convexHull ℝ ({d, e, f} : Set Point) ∩ L) := by
    zumx
    constructor
    · intro hx; exact ⟨by_grind, by_grind⟩
    · zudte
  rw [hinter, hface₁, hface₂]
  -- the two faces on the line
  have hAB : ∀ y ∈ ({d, e, f} : Set Point) ∩ L,
      y ∈ convexHull ℝ (({a, b, c} : Set Point) ∩ L) → y ∈ ({a, b, c} : Set Point) ∩ L := by
    grind
  have hBA : ∀ y ∈ ({a, b, c} : Set Point) ∩ L,
      y ∈ convexHull ℝ (({d, e, f} : Set Point) ∩ L) → y ∈ ({d, e, f} : Set Point) ∩ L := by
    rintro y ⟨hy, hyL⟩ hmem
    grind
  rw [convexHull_inter_convexHull_of_injOn hL ψ hψ Set.inter_subset_right Set.inter_subset_right
    hAB hBA]
  zucr
  zumx
  constructor
  · zudte
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hV ⟨h1, h2⟩⟩, ⟨h2, hV ⟨h1, h2⟩⟩⟩

/-- The conformity criterion for the specification's triangles: two valid triangles of `P`
with disjoint interiors, such that every vertex of either lying in the other triangle is one
of its vertices, meet exactly in the convex hull of their common vertices. -/
theorem triSet_inter_triSet_of_disjoint_interiors {P : Polygon} {s t : Polygon.Triangle}
    (hs : P.validTriangle s) (ht : P.validTriangle t)
    (hdisj : Disjoint ztqrt ztqru)
    (hv₁ : ∀ v ∈ P.triVertices t, v ∈ P.triSet s → v ∈ P.triVertices s)
    (hv₂ : ∀ v ∈ P.triVertices s, v ∈ P.triSet t → v ∈ P.triVertices t) :
    P.triSet s ∩ P.triSet t = convexHull ℝ (P.triVertices s ∩ P.triVertices t) :=
  conforming_of_disjoint_interiors (det_ne_zero_of_validTriangle hs)
    (det_ne_zero_of_validTriangle ht) hdisj hv₁ hv₂
end
end Geometry
namespace Machine
@[expose] public section
variable {α : Type} (f : ℕ → α) (i : ℕ) (v : α)
@[simp] theorem upd_same : upd f i v i = v := by
  simp [upd]
@[simp] theorem upd_other {j : ℕ} (h : j ≠ i) :
    upd f i v j = f j := by
  zunrb
theorem upd_apply (j : ℕ) :
    upd f i v j = if j = i then v else f j := rfl
@[simp] theorem upd_upd_same (v w : α) :
    upd (upd f i v) i w = upd f i w := by
  funext j; by_cases h : j = i <;> zunrb
@[simp] theorem upd_eq_self : upd f i (f i) = f := by
  funext j; by_cases h : j = i <;> zunrb

/-- Bound on all entries after an update. -/
theorem upd_le {f : ℕ → ℕ} {W : ℕ} (hf : ∀ j, f j ≤ W) {i v : ℕ} (hv : v ≤ W) (j : ℕ) :
    upd f i v j ≤ W := by
  by_cases h : j = i <;> simp [upd, h, hv, hf]

/-! ### One lemma per instruction -/
section step
variable {prog : Program} {P : Polygon} {c : Config}
theorem step_jump {l : ℕ} (h : prog[c.pc]? = some (.jump l)) :
    step prog P c = some { c with pc := l } := by
  simp [step, h]
variable {a b l : ℕ}
theorem step_brLtN_true (h : prog[c.pc]? = some ztria)
    (ht : c.nreg a < c.nreg b) : step prog P c = some { c with pc := l } := by
  zuckn
theorem step_brLtN_false (h : prog[c.pc]? = some ztria)
    (ht : ¬ c.nreg a < c.nreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  zuckn
theorem step_brLtR_true (h : prog[c.pc]? = some ztrib)
    (ht : c.rreg a < c.rreg b) : step prog P c = some { c with pc := l } := by
  zuckn
theorem step_brLtR_false (h : prog[c.pc]? = some ztrib)
    (ht : ¬ c.rreg a < c.rreg b) : step prog P c = some { c with pc := c.pc + 1 } := by
  zuckn
end step

/-! ### `run` -/
section run
variable {prog : Program} {P : Polygon}
@[simp] theorem run_zero (c : Config) : run prog P 0 c = some c := rfl
theorem run_succ (k : ℕ) (c : Config) :
    run prog P zts c = (step prog P c).bind (run prog P k) := rfl
theorem run_succ_of_step {k : ℕ} {c c₁ : Config} (h : step prog P c = some c₁) :
    run prog P zts c = run prog P k c₁ := by
  rw [run_succ, h, Option.bind_some]

/-- Running `a + b` steps is running `a` steps and then `b` steps. -/
theorem run_add (a b : ℕ) (c : Config) :
    run prog P ztth c = (run prog P a c).bind (run prog P b) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, run_succ, run_succ, Option.bind_assoc]
    cases step prog P c with
    | none => rfl
    | some c₁ => simp [ih]
theorem run_add_of_run {a b : ℕ} {c c₁ : Config} (h : run prog P a c = some c₁) :
    run prog P ztth c = run prog P b c₁ := by
  rw [run_add, h, Option.bind_some]
end run

/-! ### Word bounds and `RunsWithin` -/
theorem WordsBounded.mono {W W' : ℕ} {c : Config} (h : WordsBounded W c) (hW : W ≤ W') :
    WordsBounded W' c :=
  ⟨fun r => (h.1 r).trans hW, fun a => (h.2 a).trans hW⟩
@[simp] theorem wordsBounded_setPc {W : ℕ} {c : Config} {p : ℕ} :
    WordsBounded W { c with pc := p } ↔ WordsBounded W c := Iff.rfl
theorem WordsBounded.nreg {W : ℕ} {c : Config} (h : WordsBounded W c) (r : ℕ) : c.nreg r ≤ W :=
  h.1 r

/-- Updating a natural register with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nreg {W : ℕ} {c : Config} (h : WordsBounded W c) {r v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nreg := upd c.nreg r v } :=
  ⟨upd_le h.1 hv, h.2⟩

/-- Updating a natural memory cell with a value `≤ W` preserves the word bound. -/
theorem WordsBounded.upd_nmem {W : ℕ} {c : Config} (h : WordsBounded W c) {a v : ℕ}
    (hv : v ≤ W) (pc : ℕ) : WordsBounded W { c with pc := pc, nmem := upd c.nmem a v } :=
  ⟨h.1, upd_le h.2 hv⟩

/-! ### Bounded runs

`BoundedRun prog P W k c` says that the `k`-step run from `c` succeeds and every configuration
visited (including the first and the last) is `WordsBounded W`.  `RunsTo` adds the final
configuration.  These compose (`RunsTo.trans`) and give `RunsWithin` directly
(`runsWithin_of_runsTo`). -/

/-- The `k`-step run from `c` does not fault and every visited configuration is
`WordsBounded W`. -/
def BoundedRun (prog : Program) (P : Polygon) (W k : ℕ) (c : Config) : Prop :=
  ∀ i, i ≤ k → ∃ c', run prog P i c = some c' ∧ WordsBounded W c'

/-- The `k`-step run from `c` ends in `c'`, and every visited configuration is `WordsBounded W`. -/
def RunsTo (prog : Program) (P : Polygon) (W k : ℕ) (c c' : Config) : Prop :=
  run prog P k c = some c' ∧ BoundedRun prog P W k c
section runsTo
variable {prog : Program} {P : Polygon} {W : ℕ}
variable {k : ℕ} {a b : ℕ}
theorem BoundedRun.wb_start {c : Config} (h : BoundedRun prog P W k c) :
    WordsBounded W c := by
  obtain ⟨c', hc, hw⟩ := h 0 ztbg
  simp_all
theorem BoundedRun.zero {c : Config} (h : WordsBounded W c) : BoundedRun prog P W 0 c := by
  zug
  simp_all
theorem BoundedRun.cons {c c₁ : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : BoundedRun prog P W k c₁) :
    BoundedRun prog P W zts c := by
  zug
  cases i with
  | zero => exact ⟨c, rfl, hw⟩
  | succ i =>
    obtain ⟨c', hc, hw'⟩ := h i (Nat.le_of_succ_le_succ hi)
    exact ⟨c', by rw [run_succ_of_step hs, hc], hw'⟩
theorem BoundedRun.add {c c₁ : Config} (h₁ : BoundedRun prog P W a c)
    (hr : run prog P a c = some c₁) (h₂ : BoundedRun prog P W b c₁) :
    BoundedRun prog P W ztth c := by
  zug
  by_cases hia : i ≤ a
  · tauto
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le hia)
    obtain ⟨c', hc, hw⟩ := h₂ d by_omega
    exact ⟨c', by rw [run_add_of_run hr, hc], hw⟩
theorem RunsTo.wb_start {c c' : Config} (h : RunsTo prog P W k c c') :
    WordsBounded W c := h.2.wb_start
theorem RunsTo.wb_end {c c' : Config} (h : RunsTo prog P W k c c') :
    WordsBounded W c' := by
  obtain ⟨c'', hc, hw⟩ := h.2 k le_rfl
  rw [h.1, Option.some.injEq] at hc
  simp_all
theorem RunsTo.zero {c : Config} (h : WordsBounded W c) : RunsTo prog P W 0 c c :=
  ⟨rfl, BoundedRun.zero h⟩

/-- Prepend one step. -/
theorem RunsTo.cons {c c₁ c' : Config} (hw : WordsBounded W c)
    (hs : step prog P c = some c₁) (h : RunsTo prog P W k c₁ c') :
    RunsTo prog P W zts c c' :=
  ⟨by rw [run_succ_of_step hs, h.1], BoundedRun.cons hw hs h.2⟩

/-- A single step between two bounded configurations. -/
theorem RunsTo.single {c c₁ : Config} (hw : WordsBounded W c) (hw₁ : WordsBounded W c₁)
    (hs : step prog P c = some c₁) : RunsTo prog P W 1 c c₁ :=
  RunsTo.cons hw hs (RunsTo.zero hw₁)
theorem RunsTo.trans {c c₁ c' : Config} (h₁ : RunsTo prog P W a c c₁)
    (h₂ : RunsTo prog P W b c₁ c') : RunsTo prog P W ztth c c' :=
  ⟨by rw [run_add_of_run h₁.1, h₂.1], BoundedRun.add h₁.2 h₁.1 h₂.2⟩

/-- Append one step. -/
theorem RunsTo.snoc {c c₁ c' : Config} (h : RunsTo prog P W k c c₁)
    (hs : step prog P c₁ = some c') (hw : WordsBounded W c') :
    RunsTo prog P W zts c c' :=
  h.trans (RunsTo.single h.wb_end hw hs)

/-- Replace the step count by an equal one (for arithmetic normalisation). -/
theorem RunsTo.cast {k k' : ℕ} {c c' : Config} (h : RunsTo prog P W k c c') (hk : k = k') :
    RunsTo prog P W k' c c' := hk ▸ h

/-- `RunsWithin` from a bounded run of `initConfig` ending at a `halt`. -/
theorem runsWithin_of_runsTo {c : Config} (h : RunsTo prog P W k initConfig c)
    (hh : AtHalt prog c) : RunsWithin prog P W zts c.output :=
  ⟨k, le_rfl, h.2, c, h.1, hh, rfl⟩
end runsTo
end
end Machine
namespace Instr
@[expose] public section

/-- Is the instruction a control instruction (`halt`, `jump`, `brLtN`, `brLtR`)? -/
def isControl : Instr → Bool
  | .halt => true
  | .jump _ => true
  | .brLtN _ _ _ => true
  | .brLtR _ _ _ => true
  | _ => false

/-- A straight-line instruction: anything but `halt`, `jump`, `brLtN`, `brLtR`.  Straight-line
instructions always advance the program counter by one and never depend on it. -/
def IsStraight (ins : Instr) : Prop := ins.isControl = false
@[simp] theorem isStraight_halt : ¬ IsStraight .halt := by tauto
@[simp] theorem isStraight_jump (l : ℕ) : ¬ IsStraight (.jump l) := by tauto
variable (a b l : ℕ) (r : ℕ)
@[simp] theorem isStraight_brLtN : ¬ IsStraight (.brLtN a b l) := by
  tauto
@[simp] theorem isStraight_brLtR : ¬ IsStraight (.brLtR a b l) := by
  tauto
@[simp] theorem isStraight_inputSize : IsStraight (.inputSize r) := rfl
@[simp] theorem isStraight_constN (r k : ℕ) : IsStraight (.constN r k) := rfl
@[simp] theorem isStraight_copyN (r a : ℕ) : IsStraight (.copyN r a) := rfl
@[simp] theorem isStraight_addN (r a b : ℕ) : IsStraight (.addN r a b) := rfl
@[simp] theorem isStraight_subN (r a b : ℕ) : IsStraight (.subN r a b) := rfl
@[simp] theorem isStraight_loadN (r a : ℕ) : IsStraight (.loadN r a) := rfl
@[simp] theorem isStraight_storeN (a r : ℕ) : IsStraight (.storeN a r) := rfl
@[simp] theorem isStraight_constR (z : ℤ) : IsStraight (.constR r z) := rfl
@[simp] theorem isStraight_copyR (r a : ℕ) : IsStraight (.copyR r a) := rfl
@[simp] theorem isStraight_addR (r a b : ℕ) : IsStraight (.addR r a b) := rfl
@[simp] theorem isStraight_subR (r a b : ℕ) : IsStraight (.subR r a b) := rfl
@[simp] theorem isStraight_mulR (r a b : ℕ) : IsStraight (.mulR r a b) := rfl
@[simp] theorem isStraight_divR (r a b : ℕ) : IsStraight (.divR r a b) := rfl
@[simp] theorem isStraight_loadR (r a : ℕ) : IsStraight (.loadR r a) := rfl
@[simp] theorem isStraight_storeR (a r : ℕ) : IsStraight (.storeR a r) := rfl
@[simp] theorem isStraight_readX (r a : ℕ) : IsStraight (.readX r a) := rfl
@[simp] theorem isStraight_readY (r a : ℕ) : IsStraight (.readY r a) := rfl
@[simp] theorem isStraight_emit (a b d : ℕ) : IsStraight (.emit a b d) := rfl
end
end Instr
namespace Machine
@[expose] public section

/-! ### Frame lemmas

What a single step leaves unchanged, classified by the instruction executed. -/
section frame
variable {prog : Program} {P : Polygon} {c c' : Config} {ins : Instr}
end frame
end
end Machine
namespace Instr
@[expose] public section
def relocate (off : ℕ) : Instr → Instr
  | .jump l => .jump ztocl
  | .brLtN a b l => .brLtN a b ztocl
  | .brLtR a b l => .brLtR a b ztocl
  | ins => ins
@[simp] theorem relocate_zero (ins : Instr) : ins.relocate 0 = ins := by
  cases ins <;> rfl

/-- Relocation does not touch straight-line instructions. -/
@[simp] theorem relocate_of_isStraight {ins : Instr} (h : ins.IsStraight) (off : ℕ) :
    ins.relocate off = ins := by
  cases ins <;> first | rfl | simp at h
end
end Instr
namespace Program
@[expose] public section

/-- Relocate every instruction of a program. -/
def relocate (off : ℕ) (p : Program) : Program := p.map (Instr.relocate off)
@[simp] theorem relocate_zero (p : Program) : p.relocate 0 = p := by
  rw [relocate, show Instr.relocate 0 = id from funext Instr.relocate_zero, List.map_id]
end
end Program
namespace Machine
@[expose] public section

/-! ### Placement of a program inside a larger one -/

/-- The program `p` sits verbatim at address `base` inside `q`. -/
def SubAt (p q : Program) (base : ℕ) : Prop :=
  ∀ i ins, p[i]? = some ins → q[base + i]? = some ins
@[simp] theorem SubAt.nil (q : Program) (base : ℕ) : SubAt [] q base := by
  tauto
theorem SubAt.refl (p : Program) : SubAt p p 0 := by
  intro i ins h; simp_all
variable {ins : Instr} {p q : Program} {base : ℕ} (p₁ p₂ : Program)
theorem SubAt.cons_iff :
    SubAt (ins :: p) q base ↔ q[base]? = some ins ∧ SubAt p q ztfpf := by
  constructor
  · zuq
    refine ⟨by simpa using h 0 ins rfl, fun i ins' hi => ?_⟩
    have := h ztg ins' by_simp_all
    grind
  · rintro ⟨h0, h⟩ i ins' hi
    cases i with
    | zero => simp at hi; subst hi; simpa using h0
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have := h i ins' hi
      rw [show base + ztg = base + 1 + i by omega]; exact this
theorem SubAt.head (h : SubAt (ins :: p) q base) :
    q[base]? = some ins :=
  (SubAt.cons_iff.mp h).1
theorem SubAt.tail (h : SubAt (ins :: p) q base) :
    SubAt p q ztfpf :=
  (SubAt.cons_iff.mp h).2
theorem SubAt.singleton_iff {q : Program} {base : ℕ} :
    SubAt [ins] q base ↔ q[base]? = some ins := by
  simp [SubAt.cons_iff]
theorem SubAt.append_iff {p₁ p₂ q : Program} {base : ℕ} :
    SubAt ztefm q base ↔ SubAt p₁ q base ∧ SubAt p₂ q zttgp := by
  constructor
  · zuq
    refine ⟨fun i ins hi => h i ins ?_, fun i ins hi => ?_⟩
    · grind
    · have := h (p₁.length + i) ins (by
        grind)
      grind
  · rintro ⟨h₁, h₂⟩ i ins hi
    by_cases hlt : i < p₁.length
    · rw [List.getElem?_append_left hlt] at hi; tauto
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hi
      have := h₂ _ ins hi
      simp_all
theorem SubAt.of_append_left {p₁ p₂ q : Program} {base : ℕ} (h : SubAt ztefm q base) :
    SubAt p₁ q base :=
  (SubAt.append_iff.mp h).1
theorem SubAt.of_append_right {p₁ p₂ q : Program} {base : ℕ} (h : SubAt ztefm q base) :
    SubAt p₂ q zttgp :=
  (SubAt.append_iff.mp h).2

/-- The lookup lemma for concatenation. -/
theorem getElem?_append_length_add (i : ℕ) :
    ztefm[p₁.length + i]? = p₂[i]? := by
  grind

/-- The first half of a concatenation sits at address `0`. -/
theorem SubAt.append_left : SubAt p₁ ztefm 0 := by
  zulmz

/-- The second half of a concatenation sits at address `p₁.length`. -/
theorem SubAt.append_right : SubAt p₂ ztefm p₁.length := by
  zulmz

/-! ### Shifting the program counter -/

/-- The configuration `c` with its program counter shifted by `off`. -/
def shiftPc (off : ℕ) (c : Config) : Config := { c with pc := c.pc + off }

/-! ### The relocation theorem -/
end
end Machine
end Chazelle
section
set_option hygiene false
local macro "zqbgh" : tactic => `(tactic| (simp only [compile] at hq
                                           have h0 : q[base]? = some _ := hq.head))
local macro "zqbgi" : tactic => `(tactic| have hw : WordsBounded W { c with pc := base } := hrun.wb_start)
local macro "zqbgk" : tactic => `(tactic| (have hw' : WordsBounded W { c with pc := base } := hw
                                           have hw1 : WordsBounded W { c with pc := base + 1 } := hw
                                           have hw3 : WordsBounded W { c with pc := base + 3 + codeSize body } := hw))
local macro "zqbgl" : tactic => `(tactic| exact (((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).trans hrest).cast by_omega)
set_option hygiene true

/-!
# A structured language and a cost-exact compiler

* `Instr.effect P ins c`: the effect of a straight-line instruction on the state, leaving the
  program counter unchanged (`none` on a division by zero or on a control instruction).
  `step_eq_effect` relates it to `step`.
* `Stmt`: skip, straight-line instruction, sequence, `if a < b`, `while a < b` (on natural
  or on real registers).
* `compile s base : Program`, `codeSize s`, with `(compile s base).length = codeSize s`.

  **Layout and exact costs** (all costs count executed machine instructions):

  | statement            | code at `base`                                                     | size            | cost |
  |----------------------|--------------------------------------------------------------------|-----------------|------|
  | `skip`               | (nothing)                                                          | `0`             | `0` |
  | `instr i`            | `[i]`                                                              | `1`             | `1` |
  | `seq s t`            | `compile s base ++ compile t (base + codeSize s)`                  | `|s| + |t|`     | `k_s + k_t` |
  | `ifLtN a b t e`      | `brLtN a b (base+2+|e|) :: compile e (base+1) ++ jump (base+2+|e|+|t|) :: compile t (base+2+|e|)` | `|t| + |e| + 2` | test true: `k_t + 1`; test false: `k_e + 2` |
  | `ifLtR a b t e`      | same with `brLtR`                                                  | `|t| + |e| + 2` | same |
  | `whileLtN a b body`  | `brLtN a b (base+2) :: jump (base+3+|body|) :: compile body (base+2) ++ [jump base]` | `|body| + 3` | exit (test false): `2`; each iteration: `k_body + 2` |
  | `whileLtR a b body`  | same with `brLtR`                                                  | `|body| + 3`    | same |

  A loop that iterates `m` times with body costs `k₁, …, kₘ` costs exactly
  `(k₁ + 2) + ⋯ + (kₘ + 2) + 2`.
* `Exec P W s c c' k`: big-step cost semantics counting exactly the machine instructions the
  compiled code executes.  Every configuration at which an instruction runs, plus the final
  one, is required to be `WordsBounded W`, and `divR` is never executed with a zero divisor.
  `Exec` never changes the program counter (`Exec.pc_eq`) and is insensitive to it
  (`Exec.setPc`).
* Simulation (`Exec.runsTo`): if `compile s base` sits at `base` inside `q`, then running `q`
  for exactly `k` steps from `c` with `pc := base` ends at `c'` with
  `pc := base + codeSize s`, every visited configuration `WordsBounded W`.
* Top level (`runsWithin_of_exec`): `Exec P W s initConfig c' k` gives
  `RunsWithin (compile s 0 ++ [halt]) P W (k + 1) c'.output`.
* Per-instruction rules `Exec.constN`, …, and loop rules with a potential
  (`Exec.whileLtN_potential`, `Exec.whileLtR_potential`, and the `_bounded` variants).
-/
namespace Chazelle
namespace Instr
@[expose] public section
noncomputable def effect (P : Polygon) : Instr → Config → Option Config
  | .inputSize r, c => some { c with nreg := upd c.nreg r P.n }
  | .constN r k, c => some { c with nreg := upd c.nreg r k }
  | .copyN r a, c => some { c with nreg := upd c.nreg r (c.nreg a) }
  | .addN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) }
  | .subN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) }
  | .loadN r a, c => some { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) }
  | .storeN a r, c => some { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) }
  | .constR r z, c => some { c with rreg := upd c.rreg r (z : ℝ) }
  | .copyR r a, c => some { c with rreg := upd c.rreg r (c.rreg a) }
  | .addR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) }
  | .subR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) }
  | .mulR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) }
  | .divR r a b, c =>
      if c.rreg b = 0 then none else some { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) }
  | .loadR r a, c => some { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) }
  | .storeR a r, c => some { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) }
  | .readX r a, c => some { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).1 }
  | .readY r a, c => some { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).2 }
  | .emit a b d, c => some { c with output := c.output ++ [(c.nreg a, c.nreg b, c.nreg d)] }
  | .halt, _ => none
  | .jump _, _ => none
  | .brLtN _ _ _, _ => none
  | .brLtR _ _ _, _ => none
variable {P : Polygon} {c : Config}
variable (r : ℕ) (a b l : ℕ) {prog : Program} {ins : Instr}
@[simp] theorem effect_inputSize :
    (Instr.inputSize r).effect P c = some { c with nreg := upd c.nreg r P.n } := rfl
@[simp] theorem effect_constN (r k : ℕ) :
    (Instr.constN r k).effect P c = some { c with nreg := upd c.nreg r k } := rfl
@[simp] theorem effect_copyN (r a : ℕ) :
    (Instr.copyN r a).effect P c = some { c with nreg := upd c.nreg r (c.nreg a) } := rfl
@[simp] theorem effect_addN (r a b : ℕ) :
    (Instr.addN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } := rfl
@[simp] theorem effect_subN (r a b : ℕ) :
    (Instr.subN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } := rfl
@[simp] theorem effect_loadN (r a : ℕ) :
    (Instr.loadN r a).effect P c =
      some { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) } := rfl
@[simp] theorem effect_storeN (a r : ℕ) :
    (Instr.storeN a r).effect P c =
      some { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } := rfl
@[simp] theorem effect_constR (z : ℤ) :
    (Instr.constR r z).effect P c = some { c with rreg := upd c.rreg r (z : ℝ) } := rfl
@[simp] theorem effect_copyR (r a : ℕ) :
    (Instr.copyR r a).effect P c = some { c with rreg := upd c.rreg r (c.rreg a) } := rfl
@[simp] theorem effect_addR (r a b : ℕ) :
    (Instr.addR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) } := rfl
@[simp] theorem effect_subR (r a b : ℕ) :
    (Instr.subR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) } := rfl
@[simp] theorem effect_mulR (r a b : ℕ) :
    (Instr.mulR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) } := rfl
theorem effect_divR (r a b : ℕ) (hb : c.rreg b ≠ 0) :
    (Instr.divR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) } := by
  simp [effect, hb]
@[simp] theorem effect_loadR (r a : ℕ) :
    (Instr.loadR r a).effect P c =
      some { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) } := rfl
@[simp] theorem effect_storeR (a r : ℕ) :
    (Instr.storeR a r).effect P c =
      some { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) } := rfl
@[simp] theorem effect_readX (r a : ℕ) :
    (Instr.readX r a).effect P c =
      some { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).1 } := rfl
@[simp] theorem effect_readY (r a : ℕ) :
    (Instr.readY r a).effect P c =
      some { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).2 } := rfl
@[simp] theorem effect_emit (a b d : ℕ) :
    (Instr.emit a b d).effect P c =
      some { c with output := c.output ++ [(c.nreg a, c.nreg b, c.nreg d)] } := rfl
@[simp] theorem effect_halt : (Instr.halt).effect P c = none := rfl
@[simp] theorem effect_jump (l : ℕ) : (Instr.jump l).effect P c = none := rfl
@[simp] theorem effect_brLtN : (Instr.brLtN a b l).effect P c = none := rfl
@[simp] theorem effect_brLtR : (Instr.brLtR a b l).effect P c = none := rfl

/-- The effect is insensitive to the program counter. -/
theorem effect_setPc (ins : Instr) (p : ℕ) :
    ins.effect P { c with pc := p } = (ins.effect P c).map (fun c' => { c' with pc := p }) := by
  cases ins <;> simp only [effect, Option.map_some, Option.map_none]
  grind

/-- `step` on a straight-line instruction is `effect` followed by `pc + 1`. -/
theorem step_eq_effect (h : prog[c.pc]? = some ins)
    (hs : ins.IsStraight) :
    step prog P c = (ins.effect P c).map (fun c' => { c' with pc := c.pc + 1 }) := by
  cases ins <;> simp only [step, effect, h, Option.map_some, Option.map_none] <;>
    first
    | rfl
    | (split <;> rfl)
    | simp at hs

/-- `step` on a straight-line instruction whose effect is `c'`. -/
theorem step_of_effect {c' : Config} (h : prog[c.pc]? = some ins)
    (hs : ins.IsStraight) (he : ins.effect P c = some c') :
    step prog P c = some { c' with pc := c.pc + 1 } := by
  rw [step_eq_effect h hs, he]; rfl
end
end Instr
namespace Machine
@[expose] public section

/-! ### The structured language -/

/-- Structured statements over straight-line instructions. -/
inductive Stmt : Type
  /-- No code. -/
  | skip
  /-- One straight-line instruction (`Instr.IsStraight` is required by the semantics). -/
  | instr (i : Instr)
  /-- Sequencing. -/
  | seq (s t : Stmt)
  /-- `if nreg a < nreg b then thenS else elseS`. -/
  | ifLtN (a b : ℕ) (thenS elseS : Stmt)
  /-- `if rreg a < rreg b then thenS else elseS`. -/
  | ifLtR (a b : ℕ) (thenS elseS : Stmt)
  /-- `while nreg a < nreg b do body`. -/
  | whileLtN (a b : ℕ) (body : Stmt)
  /-- `while rreg a < rreg b do body`. -/
  | whileLtR (a b : ℕ) (body : Stmt)
namespace Stmt

/-- Number of machine instructions in the compiled code. -/
def codeSize : Stmt → ℕ
  | .skip => 0
  | .instr _ => 1
  | .seq s t => codeSize s + codeSize t
  | .ifLtN _ _ t e => codeSize t + codeSize e + 2
  | .ifLtR _ _ t e => codeSize t + codeSize e + 2
  | .whileLtN _ _ body => codeSize body + 3
  | .whileLtR _ _ body => codeSize body + 3

/-- Compile a statement to machine code placed at address `base`. -/
def compile : Stmt → ℕ → Program
  | .skip, _ => []
  | .instr i, _ => [i]
  | .seq s t, base => compile s base ++ compile t (base + codeSize s)
  | .ifLtN a b t e, base =>
      .brLtN a b ztcyu :: compile e ztfpf ++
        .jump ztlgg :: compile t ztcyu
  | .ifLtR a b t e, base =>
      .brLtR a b ztcyu :: compile e ztfpf ++
        .jump ztlgg :: compile t ztcyu
  | .whileLtN a b body, base =>
      .brLtN a b ztdtw :: .jump ztoya ::
        compile body ztdtw ++ [.jump base]
  | .whileLtR a b body, base =>
      .brLtR a b ztdtw :: .jump ztoya ::
        compile body ztdtw ++ [.jump base]
@[simp] theorem codeSize_skip : codeSize .skip = 0 := rfl
variable (i : Instr) (a b : ℕ) (t e : Stmt) (body : Stmt) (l : List Instr)
@[simp] theorem codeSize_instr : codeSize (.instr i) = 1 := rfl
@[simp] theorem codeSize_seq (s t : Stmt) : codeSize (.seq s t) = codeSize s + codeSize t := rfl
@[simp] theorem codeSize_ifLtN :
    codeSize ztva = codeSize t + codeSize e + 2 := rfl
@[simp] theorem codeSize_ifLtR :
    codeSize ztejq = codeSize t + codeSize e + 2 := rfl
@[simp] theorem codeSize_whileLtN :
    codeSize ztpx = codeSize body + 3 := rfl
@[simp] theorem codeSize_whileLtR :
    codeSize zthqn = codeSize body + 3 := rfl

/-- The compiled code has exactly `codeSize` instructions. -/
@[simp] theorem length_compile (s : Stmt) (base : ℕ) : (compile s base).length = codeSize s := by
  induction s generalizing base with
  | skip => rfl
  | instr i => rfl
  | seq s t ihs iht => simp [compile, ihs, iht]
  | ifLtN a b t e iht ihe => zuocg; omega
  | ifLtR a b t e iht ihe => zuocg; omega
  | whileLtN a b body ih => zuoqa
  | whileLtR a b body ih => zuoqa

/-- A block of straight-line instructions, as nested sequences ending in `skip`. -/
def block : List Instr → Stmt
  | [] => .skip
  | i :: l => .seq ztbgj ztgfk
@[simp] theorem block_nil : block [] = .skip := rfl
@[simp] theorem block_cons :
    block (i :: l) = .seq ztbgj ztgfk := rfl
@[simp] theorem codeSize_block : codeSize (block l) = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [block, ih, Nat.add_comm]

/-- A block compiles to exactly its list of instructions, at any base address. -/
@[simp] theorem compile_block (base : ℕ) : compile (block l) base = l := by
  induction l generalizing base with
  | nil => rfl
  | cons i l ih => simp [block, compile, ih]
end Stmt
open Stmt

/-! ### Big-step cost semantics -/

/-- `Exec P W s c c' k`: from state `c`, the statement `s` runs to completion in state `c'`
executing exactly `k` machine instructions of its compiled code.  Every configuration at
which an instruction runs, and the final configuration, is `WordsBounded W`; `divR` is never
executed with a zero divisor (the effect must be `some`).  The program counter is carried
along unchanged. -/
inductive Exec (P : Polygon) (W : ℕ) : Stmt → Config → Config → ℕ → Prop
  | skip {c : Config} : WordsBounded W c → Exec P W .skip c c 0
  | instr {ins : Instr} {c c' : Config} : ins.IsStraight → ins.effect P c = some c' →
      WordsBounded W c → WordsBounded W c' → Exec P W (.instr ins) c c' 1
  | seq {s t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} :
      Exec P W s c c₁ k₁ → Exec P W t c₁ c₂ k₂ → Exec P W ztfmm c c₂ ztbct
  | ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.nreg a < c.nreg b →
      Exec P W t c c' k → Exec P W ztva c c' zts
  | ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.nreg a < c.nreg b →
      Exec P W e c c' k → Exec P W ztva c c' ztcnq
  | ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.rreg a < c.rreg b →
      Exec P W t c c' k → Exec P W ztejq c c' zts
  | ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.rreg a < c.rreg b →
      Exec P W e c c' k → Exec P W ztejq c c' ztcnq
  | whileLtN_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.nreg a < c.nreg b →
      WordsBounded W c → Exec P W ztpx c c 2
  | whileLtN_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b →
      Exec P W body c c₁ k₁ → Exec P W ztpx c₁ c' k₂ →
      Exec P W ztpx c c' ztgkq
  | whileLtR_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.rreg a < c.rreg b →
      WordsBounded W c → Exec P W zthqn c c 2
  | whileLtR_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.rreg a < c.rreg b →
      Exec P W body c c₁ k₁ → Exec P W zthqn c₁ c' k₂ →
      Exec P W zthqn c c' ztgkq
namespace Exec
variable {P : Polygon} {W : ℕ}
variable {s : Stmt}
/-- The final configuration of an execution is word-bounded. -/
theorem wb_right {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) :
    WordsBounded W c' := by
  induction h with
  | skip hw => exact hw
  | instr _ _ _ hw => exact hw
  | seq _ _ _ ih₂ => exact ih₂
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ hw => exact hw
  | whileLtN_true _ _ _ _ ih => exact ih
  | whileLtR_false _ hw => exact hw
  | whileLtR_true _ _ _ _ ih => exact ih

/-- Replace the cost by an equal one. -/
theorem cast {c c' : Config} {k k' : ℕ} (h : Exec P W s c c' k) (hk : k = k') :
    Exec P W s c c' k' := by_simp_all

/-- Replace the final configuration by an equal one. -/
theorem cast_end {c c' c'' : Config} {k : ℕ} (h : Exec P W s c c' k) (hc : c' = c'') :
    Exec P W s c c'' k := by_simp_all

/-! #### Per-instruction rules

Each rule gives the exact next state, cost `1`, and the side conditions: the written natural
value must be `≤ W` (for `inputSize`, `constN`, `addN`), and `divR` needs a nonzero divisor. -/
section instrRules
variable {c : Config} (hw : WordsBounded W c)
include hw
variable (r : ℕ)
theorem inputSize (hn : P.n ≤ W) :
    Exec P W (.instr (.inputSize r)) c { c with nreg := upd c.nreg r P.n } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw hn c.pc)
theorem constN (r k : ℕ) (hk : k ≤ W) :
    Exec P W (.instr (.constN r k)) c { c with nreg := upd c.nreg r k } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw hk c.pc)
theorem copyN (r a : ℕ) :
    Exec P W ztdsf c { c with nreg := upd c.nreg r (c.nreg a) } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw ztvwp c.pc)
theorem addN (r a b : ℕ) (hab : c.nreg a + c.nreg b ≤ W) :
    Exec P W ztder c { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw hab c.pc)
theorem subN (r a b : ℕ) :
    Exec P W ztgwy c { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw ((Nat.sub_le _ _).trans ztvwp) c.pc)
theorem loadN (r a : ℕ) :
    Exec P W ztowa c { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nreg hw (hw.2 _) c.pc)
theorem storeN (a r : ℕ) :
    Exec P W ztowc c { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } 1 :=
  .instr by_simp rfl hw (WordsBounded.upd_nmem hw (hw.1 r) c.pc)
theorem constR (z : ℤ) :
    Exec P W (.instr (.constR r z)) c { c with rreg := upd c.rreg r (z : ℝ) } 1 :=
  .instr by_simp rfl hw hw
theorem copyR (r a : ℕ) :
    Exec P W (.instr (.copyR r a)) c { c with rreg := upd c.rreg r (c.rreg a) } 1 :=
  .instr by_simp rfl hw hw
theorem addR (r a b : ℕ) :
    Exec P W (.instr (.addR r a b)) c { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) } 1 :=
  .instr by_simp rfl hw hw
theorem subR (r a b : ℕ) :
    Exec P W (.instr (.subR r a b)) c { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) } 1 :=
  .instr by_simp rfl hw hw
theorem mulR (r a b : ℕ) :
    Exec P W (.instr (.mulR r a b)) c { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) } 1 :=
  .instr by_simp rfl hw hw
theorem divR (r a b : ℕ) (hb : c.rreg b ≠ 0) :
    Exec P W (.instr (.divR r a b)) c { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) } 1 :=
  .instr by_simp (Instr.effect_divR r a b hb) hw hw
theorem loadR (r a : ℕ) :
    Exec P W (.instr (.loadR r a)) c { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) } 1 :=
  .instr by_simp rfl hw hw
theorem storeR (a r : ℕ) :
    Exec P W (.instr (.storeR a r)) c { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) } 1 :=
  .instr by_simp rfl hw hw
theorem readX (r a : ℕ) :
    Exec P W (.instr (.readX r a)) c { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).1 } 1 :=
  .instr by_simp rfl hw hw
theorem readY (r a : ℕ) :
    Exec P W (.instr (.readY r a)) c { c with rreg := upd c.rreg r (P.vtx (c.nreg a)).2 } 1 :=
  .instr by_simp rfl hw hw
theorem emit (a b d : ℕ) :
    Exec P W (.instr (.emit a b d)) c
      { c with output := c.output ++ [(c.nreg a, c.nreg b, c.nreg d)] } 1 :=
  .instr by_simp rfl hw hw
end instrRules

/-! #### Blocks -/
theorem block_nil {c : Config} (hw : WordsBounded W c) : Exec P W zttgw c c 0 :=
  .skip hw

/-- Prepend one instruction to a block: cost `k + 1`. -/
theorem block_cons {i : Instr} {l : List Instr} {c c₁ c' : Config} {k : ℕ}
    (h₁ : Exec P W ztbgj c c₁ 1) (h₂ : Exec P W ztgfk c₁ c' k) :
    Exec P W ztoyd c c' zts :=
  (Exec.seq h₁ h₂).cast by_omega

/-! #### Loops with a potential -/
variable (test : Config → Prop) (body loop : Stmt) {a b : ℕ}
/-- Generic loop rule.  `test` is the loop test, `loop` the loop statement, with the two
loop rules as hypotheses.  Given an invariant `I` (implying the word bound) and a potential
`Φ` such that from any `I`-state with the test true one iteration of the body executes with
cost `k`, re-establishes `I`, and satisfies `Φ c' + k + 2 ≤ Φ c`, the whole loop executes from
any `I`-state with total cost `≤ Φ c + 2` and ends in an `I`-state with the test false. -/
theorem loop_potential
    (hfalse : ∀ c, ¬ test c → WordsBounded W c → Exec P W loop c c 2)
    (htrue : ∀ c c₁ c' k₁ k₂, test c → Exec P W body c c₁ k₁ → Exec P W loop c₁ c' k₂ →
      Exec P W loop c c' ztgkq)
    (I : Config → Prop) (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → test c → ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W loop c c' k ∧ I c' ∧ ¬ test c' ∧ k ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : test c
    · grind
    · grind

/-- Loop rule with a potential for `whileLtN a b body`: total cost `≤ Φ c + 2`. -/
theorem whileLtN_potential {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 :=
  loop_potential ztmjj body ztpx
    ztmjg
    zthwv I Φ hI hbody hc

/-- Loop rule with a bounded body cost `B` and a strictly decreasing measure `μ`: total cost
`≤ (B + 2) * μ c + 2`. -/
theorem loop_bounded
    (hfalse : ∀ c, ¬ test c → WordsBounded W c → Exec P W loop c c 2)
    (htrue : ∀ c c₁ c' k₁ k₂, test c → Exec P W body c c₁ k₁ → Exec P W loop c₁ c' k₂ →
      Exec P W loop c c' ztgkq)
    (I : Config → Prop) (μ : Config → ℕ) (B : ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → test c → ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W loop c c' k ∧ I c' ∧ ¬ test c' ∧ k ≤ zthb * μ c + 2 :=
  loop_potential test body loop hfalse htrue I (fun c => zthb * μ c) hI
    (fun c hc ht => by
      obtain ⟨c', k, he, hI', hk, hμ⟩ := hbody c hc ht
      refine ⟨c', k, he, hI', ?_⟩
      have : zthb * (μ c' + 1) ≤ zthb * μ c := by_simp_all
      grind) hc

/-- `whileLtN` with a bounded body cost `B` and a strictly decreasing measure `μ`. -/
theorem whileLtN_bounded {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (B : ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ zthb * μ c + 2 :=
  loop_bounded ztmjj body ztpx
    ztmjg
    zthwv I μ B hI hbody hc
end Exec

/-! ### Simulation -/

/-- Placement casts. -/
theorem SubAt.cast {p q : Program} {b b' : ℕ} (h : SubAt p q b) (hb : b = b') : SubAt p q b' :=
  by simp_all

/-- Two configurations differing only in an equal program counter are equal. -/
theorem setPc_congr {c : Config} {p p' : ℕ} (h : p = p') :
    ({ c with pc := p } : Config) = { c with pc := p' } := by zvmwc

/-- Replace the final configuration of a bounded run by an equal one. -/
theorem RunsTo.cast_end {prog : Program} {P : Polygon} {W k : ℕ} {c c' c'' : Config}
    (h : RunsTo prog P W k c c') (hc : c' = c'') : RunsTo prog P W k c c'' := by_simp_all

/-- **Simulation.**  If `compile s base` sits at `base` inside `q`, an execution
`Exec P W s c c' k` is realised by running `q` for exactly `k` steps from `c` with
`pc := base`, ending at `c'` with `pc := base + codeSize s`, every visited configuration
`WordsBounded W`. -/
theorem Exec.runsTo {P : Polygon} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) {q : Program} {base : ℕ} (hq : SubAt (compile s base) q base) :
    RunsTo q P W k { c with pc := base } { c' with pc := base + codeSize s } := by
  induction h generalizing q base with
  | @skip c hw =>
    exact (RunsTo.zero (wordsBounded_setPc.mpr hw)).cast_end by_simp_all
  | @instr ins c c' hs he hw hw' =>
    have hq0 : q[base]? = some ins := SubAt.singleton_iff.mp hq
    have hst : step q P { c with pc := base } = some { c' with pc := base + 1 } := by
      have := Instr.step_of_effect (c := { c with pc := base }) hq0 hs
        (by rw [Instr.effect_setPc, he]; rfl)
      omega
    exact RunsTo.single hw hw' hst
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    simp only [compile] at hq
    have h₁ := ih₁ hq.of_append_left
    have h₂ := ih₂ (hq.of_append_right.cast by_simp)
    exact (h₁.trans h₂).cast_end (setPc_congr (by rw [codeSize_seq]; omega))
  | @ifLtN_true a b t e c c' k ht _ ih =>
    zqbgh
    have hqt : ztbacd :=
      hq.tail.of_append_right.tail.cast ztnuc
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 + codeSize e } :=
      step_brLtN_true h0 ht
    have hrun := ih hqt
    zqbgi
    exact (RunsTo.cons hw hst hrun).cast_end
      ztkwy
  | @ifLtN_false a b t e c c' k ht _ ih =>
    zqbgh
    have hqe : ztumh := hq.tail.of_append_left
    have hj : ztjad :=
      hq.tail.of_append_right.cast by_simp |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtN_false h0 ht
    zulld
    have hstj : step q P { c' with pc := base + 1 + codeSize e } =
        some { c' with pc := base + 2 + codeSize e + codeSize t } :=
      step_jump hj
    zqbgi
    exact ((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).cast_end
      ztkwy
  | @ifLtR_true a b t e c c' k ht _ ih =>
    zqbgh
    have hqt : ztbacd :=
      hq.tail.of_append_right.tail.cast ztnuc
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 + codeSize e } :=
      step_brLtR_true h0 ht
    have hrun := ih hqt
    zqbgi
    exact (RunsTo.cons hw hst hrun).cast_end
      ztkwz
  | @ifLtR_false a b t e c c' k ht _ ih =>
    zqbgh
    have hqe : ztumh := hq.tail.of_append_left
    have hj : ztjad :=
      hq.tail.of_append_right.cast by_simp |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtR_false h0 ht
    zulld
    have hstj : step q P { c' with pc := base + 1 + codeSize e } =
        some { c' with pc := base + 2 + codeSize e + codeSize t } :=
      step_jump hj
    zqbgi
    exact ((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).cast_end
      ztkwz
  | @whileLtN_false a b body c ht hw =>
    zqbgh
    have h1 : ztlyq := hq.tail.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtN_false h0 ht
    have hstj : step q P { c with pc := base + 1 } =
        some { c with pc := base + 3 + codeSize body } := step_jump h1
    zqbgk
    exact (RunsTo.cons hw' hst ztrkg).cast_end
      (setPc_congr (by rw [codeSize_whileLtN]; omega))
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    zubwm
    zqbgh
    have hqb : ztbace :=
      hq.tail.tail.of_append_left.cast by_omega
    have hj : ztjae :=
      hq.tail.tail.of_append_right.cast by_simp |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 } :=
      step_brLtN_true h0 ht
    zulle
    have hstj : step q P { c₁ with pc := base + 2 + codeSize body } =
        some { c₁ with pc := base } := step_jump hj
    have hrest := ih₂ hq'
    zqbgi
    zqbgl
  | @whileLtR_false a b body c ht hw =>
    zqbgh
    have h1 : ztlyq := hq.tail.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtR_false h0 ht
    have hstj : step q P { c with pc := base + 1 } =
        some { c with pc := base + 3 + codeSize body } := step_jump h1
    zqbgk
    exact (RunsTo.cons hw' hst ztrkg).cast_end
      (setPc_congr (by rw [codeSize_whileLtR]; omega))
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    zubwm
    zqbgh
    have hqb : ztbace :=
      hq.tail.tail.of_append_left.cast by_omega
    have hj : ztjae :=
      hq.tail.tail.of_append_right.cast by_simp |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 } :=
      step_brLtR_true h0 ht
    zulle
    have hstj : step q P { c₁ with pc := base + 2 + codeSize body } =
        some { c₁ with pc := base } := step_jump hj
    have hrest := ih₂ hq'
    zqbgi
    zqbgl

/-- **Top level.**  An execution of `s` from the initial configuration gives a
`RunsWithin` for the program `compile s 0 ++ [halt]` with `k + 1` steps. -/
theorem runsWithin_of_exec {P : Polygon} {W : ℕ} {s : Stmt} {c' : Config} {k : ℕ}
    (h : Exec P W s initConfig c' k) :
    RunsWithin ztghs P W zts c'.output := by
  have hsub : SubAt _ ztghs 0 := SubAt.append_left _ _
  have hrun := h.runsTo hsub
  rw [Nat.zero_add] at hrun
  have hinit : ({ initConfig with pc := 0 } : Config) = initConfig := rfl
  rw [hinit] at hrun
  have hh : AtHalt ztghs { c' with pc := codeSize s } := by
    unfold AtHalt
    simp
  have := runsWithin_of_runsTo hrun hh
  omega
