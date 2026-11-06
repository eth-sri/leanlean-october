module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# WP-J, part 1: the greedy dyadic cover of Lemma 4.1

The portion `[x, b]` of the curve is cut greedily: at the current position `x`, take the largest
grade `g < λ` with `2^g ∣ x` and `x + 2^g ≤ b` (`nextG`), emit the piece `(g, x)`, continue at
`x + 2^g` (`cover`). The pieces are aligned full chains of grades `< λ` and tile `[x, b]`
(`cover_sum`, `mem_cover`). There are at most `2λ` of them when `b - x ≤ 2^λ` (`cover_length_le`).
-/

namespace Chazelle.Core.L41

@[expose] public section

/-- The grade condition at `x`. -/
def GradeOK (b x g : ℕ) : Prop := 2 ^ g ∣ x ∧ x + 2 ^ g ≤ b

instance (b x g : ℕ) : Decidable (GradeOK b x g) := by unfold GradeOK; infer_instance

/-- **The greedy grade**: the largest `g ≤ λ - 1` with `2^g ∣ x` and `x + 2^g ≤ b`. -/
def nextG (lam b x : ℕ) : ℕ := Nat.findGreatest (GradeOK b x) (lam - 1)

theorem gradeOK_zero {b x : ℕ} (h : x < b) : GradeOK b x 0 := ⟨by simp, by sio⟩

theorem gradeOK_mono {b x g g' : ℕ} (h : GradeOK b x g) (hg : g' ≤ g) : GradeOK b x g' :=
  ⟨(Nat.pow_dvd_pow 2 hg).trans h.1, by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hg; have := h.2; omega⟩

theorem nextG_spec {lam b x : ℕ} (h : x < b) : GradeOK b x (nextG lam b x) :=
  Nat.findGreatest_spec (P := GradeOK b x) (Nat.zero_le _) (gradeOK_zero h)

theorem nextG_le (lam b x : ℕ) : nextG lam b x ≤ lam - 1 := Nat.findGreatest_le _

theorem le_nextG {lam b x g : ℕ} (hg : g ≤ lam - 1) (h : GradeOK b x g) : g ≤ nextG lam b x :=
  Nat.le_findGreatest hg h

/-- The greedy grade is maximal. -/
theorem not_gradeOK_succ {lam b x : ℕ} (hl : nextG lam b x + 1 ≤ lam - 1) :
    ¬ GradeOK b x (nextG lam b x + 1) := fun h => by
  have := le_nextG hl h; omega

/-- **The greedy cover** of `[x, b]` (pieces `(grade, start)`). -/
def cover (lam b x : ℕ) : List (ℕ × ℕ) :=
  if h : x < b then (nextG lam b x, x) :: cover lam b (x + 2 ^ nextG lam b x) else []
termination_by b - x
decreasing_by have := Nat.one_le_two_pow (n := nextG lam b x); omega

theorem cover_of_lt {lam b x : ℕ} (h : x < b) :
    cover lam b x = (nextG lam b x, x) :: cover lam b (x + 2 ^ nextG lam b x) := by
  rw [cover, dite_eq_left h]

theorem cover_of_ge {lam b x : ℕ} (h : b ≤ x) : cover lam b x = [] := by
  rw [cover, dite_eq_right (by omega)]

/-- Induction along the cover (on `b - x`). -/
theorem cover_ind {b : ℕ} {Pr : ℕ → Prop}
    (h : ∀ x, (∀ y, b - y < b - x → Pr y) → Pr x) (x : ℕ) : Pr x := by
  suffices H : ∀ d x, b - x = d → Pr x from H _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih => intro x hx; exact h x (fun y hy => ih (b - y) (by omega) y rfl)

theorem step_lt {lam b x : ℕ} (h : x < b) : b - (x + 2 ^ nextG lam b x) < b - x := by
  have := Nat.one_le_two_pow (n := nextG lam b x); omega

/-- **The pieces are aligned full chains** inside `[x, b]`. -/
theorem mem_cover {lam b : ℕ} (x : ℕ) : ∀ q ∈ cover lam b x,
    q.1 ≤ lam - 1 ∧ 2 ^ q.1 ∣ q.2 ∧ x ≤ q.2 ∧ q.2 + 2 ^ q.1 ≤ b := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    intro q hq
    by_cases hx : x < b
    · rw [cover_of_lt hx] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · have := nextG_spec (lam := lam) hx
        exact ⟨nextG_le _ _ _, this.1, le_rfl, this.2⟩
      · obtain ⟨a1, a2, a3, a4⟩ := ih _ (step_lt hx) q hq
        have := Nat.one_le_two_pow (n := nextG lam b x)
        exact ⟨a1, a2, by omega, a4⟩
    · rw [cover_of_ge (by omega)] at hq; simp at hq

/-- **The pieces tile `[x, b]`.** -/
theorem cover_sum {lam b : ℕ} (x : ℕ) :
    ((cover lam b x).map fun q => 2 ^ q.1).sum = b - x := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    by_cases hx : x < b
    · rw [cover_of_lt hx, List.map_cons, List.sum_cons, ih _ (step_lt hx)]
      have := (nextG_spec (lam := lam) hx).2; dsimp; omega
    · rws [cover_of_ge (by omega)]; omega

/-- The descending phase: from a position aligned to `2^h` with less than `2^h` to go, at most
`h` pieces. -/
theorem cover_length_desc {lam b : ℕ} (h : ℕ) : ∀ x, h ≤ lam → 2 ^ h ∣ x → b - x < 2 ^ h →
    (cover lam b x).length ≤ h := by
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro x hl hd hb
    by_cases hx : x < b
    · rw [cover_of_lt hx, List.length_cons]
      set g := nextG lam b x with hg
      have hs := nextG_spec (lam := lam) hx
      rw [← hg] at hs
      have hgh : g < h := by
        by_contra hc
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
        have := hs.2; omega
      have hrest : b - (x + 2 ^ g) < 2 ^ g := by
        by_contra hc
        have hgh1 : g + 1 < h := by
          by_contra hc2
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc2)
          rwo [pow_succ] at this
        have hok : GradeOK b x (g + 1) := by
          refine ⟨(Nat.pow_dvd_pow 2 (by omega)).trans hd, ?_⟩
          rwo [pow_succ]
        have := le_nextG (lam := lam) (by omega) hok
        omega
      have := ih g hgh (x + 2 ^ g) (by omega) (Nat.dvd_add hs.1 dvd_rfl) hrest
      omega
    · rws [cover_of_ge (by omega)]

/-- The ascending phase. -/
theorem cover_length_asc {lam b : ℕ} (hl : 1 ≤ lam) (x : ℕ) : ∀ h, h < lam → 2 ^ h ∣ x →
    b - x ≤ 2 ^ lam → (cover lam b x).length ≤ 2 * lam - h := by
  induction x using cover_ind (b := b) with
  | h x ih =>
    intro h hh hd hb
    by_cases hx : x < b
    · rw [cover_of_lt hx, List.length_cons]
      set g := nextG lam b x with hg
      have hs := nextG_spec (lam := lam) hx
      rw [← hg] at hs
      have hgl : g ≤ lam - 1 := nextG_le _ _ _
      have hd' : 2 ^ g ∣ x + 2 ^ g := Nat.dvd_add hs.1 dvd_rfl
      by_cases hA : b < x + 2 ^ (g + 1)
      · have hr : b - (x + 2 ^ g) < 2 ^ g := by rwo [pow_succ] at hA
        have := cover_length_desc (lam := lam) (b := b) g (x + 2 ^ g) (by omega) hd' hr
        omega
      · push Not at hA
        by_cases hB : g + 1 ≤ lam - 1
        · have hnd : ¬ 2 ^ (g + 1) ∣ x := fun hc => not_gradeOK_succ (lam := lam) (b := b)
            (x := x) hB ⟨hc, hA⟩
          have hhg : h ≤ g := by
            by_contra hc
            exact hnd ((Nat.pow_dvd_pow 2 (by omega)).trans hd)
          obtain ⟨k, hk⟩ := hs.1
          have hodd : k % 2 = 1 := by
            by_contra hc
            apply hnd
            refine ⟨k / 2, ?_⟩
            rw [hk, pow_succ]
            have : k = 2 * (k / 2) := by omega
            conv_lhs => rw [this]
            ring
          have hd2 : 2 ^ (g + 1) ∣ x + 2 ^ g := by
            refine ⟨(k + 1) / 2, ?_⟩
            rw [hk, pow_succ]
            have : k + 1 = 2 * ((k + 1) / 2) := by omega
            calc 2 ^ g * k + 2 ^ g = 2 ^ g * (k + 1) := by ring
              _ = 2 ^ g * (2 * ((k + 1) / 2)) := by rw [← this]
              _ = 2 ^ g * 2 * ((k + 1) / 2) := by ring
          have hglt : g + 1 < lam := by omega
          have hb' : b - (x + 2 ^ g) ≤ 2 ^ lam := by omega
          have := ih (x + 2 ^ g) (step_lt hx) (g + 1) hglt hd2 hb'
          omega
        · have hge : g = lam - 1 := by omega
          have e2 : 2 ^ lam = 2 * 2 ^ g := by
            rw [hge, ← pow_succ']; congr 1; omega
          rw [pow_succ] at hA
          by_cases hC : b - (x + 2 ^ g) < 2 ^ g
          · have := cover_length_desc (lam := lam) (b := b) g (x + 2 ^ g) (by omega) hd' hC
            omega
          · have heq : x + 2 ^ g + 2 ^ g = b := by omega
            have hx' : x + 2 ^ g < b := by have := Nat.one_le_two_pow (n := g); omega
            rw [cover_of_lt hx']
            have hok : GradeOK b (x + 2 ^ g) g := ⟨hd', by omega⟩
            have hng : nextG lam b (x + 2 ^ g) = g := by
              have h1 := le_nextG (lam := lam) (by omega) hok
              have h2 := nextG_le lam b (x + 2 ^ g)
              omega
            rw [hng, cover_of_ge (by omega)]
            sio
    · rws [cover_of_ge (by omega)]

/-- **At most `2λ` pieces.** -/
theorem cover_length_le {lam b x : ℕ} (hl : 1 ≤ lam) (hb : b - x ≤ 2 ^ lam) :
    (cover lam b x).length ≤ 2 * lam := by
  have := cover_length_asc (b := b) hl x 0 (by omega) (by simp) hb
  omega

end

end Chazelle.Core.L41
