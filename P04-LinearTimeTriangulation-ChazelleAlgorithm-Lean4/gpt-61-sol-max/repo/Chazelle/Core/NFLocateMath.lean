module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.WalkKey

/-!
# Double identification: the mathematics (WP-C, target 2)

The procedure of `NFLocate` binary-searches the arc-sequence table of a valid normal form `N`
(arcs sorted by the key of their start) for the query key `q = key x`, with the predicate
`WalkKey.KeyPred` ("the start lies before `x`"), and answers the arc at the last position where
the predicate holds, or the last arc of the table if it holds nowhere (the arc wrapping around
the walk).  This file proves that this arc is a correct answer (`locate_pick`):

* if `q` is not a cut, the open key interval of the arc contains `q` (or the submap is empty);
* if `q` is a cut, the arc starts or ends at `q`.

The argument: (1) no start key of an arc lies strictly between the start `a` of the chosen arc
and `q` (cyclically; `pick_gap`); (2) if the arc `(a, b)` neither contains `q` nor ends at `q`,
its end `b` lies strictly between `a` and `q` (`sideInArc_swap`); `b` is a cut, and every cut
starts an arc, contradicting (1).

"Every cut starts an arc" (and "every submap has an arc") is a geometric fact about good models
that no specification states yet: it is recorded here as the WP-B obligation `ArcCoverSpec`.
-/

namespace Chazelle.Core

namespace NFLoc

open Chazelle.Chain (sideInArc)

@[expose] public section

/-- `getD` in range is indexing. -/
theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp_all

/-- **Cyclic order**: if `q` is not strictly inside the cyclic interval `(a, b)` and the three
keys are distinct, then `b` is strictly inside `(a, q)`. -/
theorem sideInArc_swap {a b q : ℝ} (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (h : ¬ sideInArc a b q) : sideInArc a q b := by
  core_grind

section
variable {M : Model} {Q : Polygon} {N : NF} (h : IsNF M Q N)
include M Q h
/-- The unpacked validity of a normal form: its region correspondence and arc records. -/
theorem isNF_arcs :
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ArcsOK M Q N reg ∧ SeqOK M Q N :=
  let ⟨_, _, _, reg, hR, _, hA, _, hS, _⟩ := h
  ⟨reg, hR, hA, hS⟩

/-- In a valid normal form, **every arc of every region is listed**. -/
theorem listed_of_isArc {U : Set Point}
    (hU : U ∈ M.regions (N.F M Q)) {a b : ℝ} (hab : M.IsArc (N.F M Q) U a b) :
    ∃ j, j < N.arcs.length ∧ M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
  obtain ⟨reg, hR, hA, -⟩ := isNF_arcs h
  obtain ⟨r, hr, rfl⟩ := hR.2.2 U hU
  ram_grind

/-- In a valid normal form, **every listed arc is an arc** of the submap. -/
theorem isArc_of_listed {j : ℕ}
    (hj : j < N.arcs.length) :
    ∃ U, M.IsArc (N.F M Q) U (M.key Q (N.arc j).s) (M.key Q (N.arc j).e) := by
  obtain ⟨reg, -, hA, -⟩ := isNF_arcs h
  exact ⟨_, (hA.1 j hj).2⟩

/-- The arc-sequence table is a permutation of the arc indices. -/
theorem seq_length :
    N.seq.length = N.arcs.length := by
  obtain ⟨-, -, -, hS⟩ := isNF_arcs h
  rw [hS.1.length_eq, List.length_range]

/-- Entries of the arc-sequence table are arc indices. -/
theorem seq_lt {i : ℕ}
    (hi : i < N.arcs.length) : N.seq.getD i 0 < N.arcs.length := by
  obtain ⟨-, -, -, hS⟩ := isNF_arcs h
  have hl := seq_length h
  rw [getD_of_lt 0 (by omega)]
  have hm : N.seq[i]'(by omega) ∈ List.range N.arcs.length := hS.1.subset (List.getElem_mem _)
  simp_all

/-- Every arc index occurs in the arc-sequence table. -/
theorem seq_surj {j : ℕ}
    (hj : j < N.arcs.length) : ∃ i, i < N.arcs.length ∧ N.seq.getD i 0 = j := by
  obtain ⟨-, -, -, hS⟩ := isNF_arcs h
  have hl := seq_length h
  have hm : j ∈ N.seq := hS.1.symm.subset (List.mem_range.2 hj)
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
  exact ⟨i, by omega, by grind⟩

/-- **The table is sorted** by start keys. -/
theorem seq_sorted {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < N.arcs.length) :
    M.key Q (N.arc (N.seq.getD i 0)).s ≤ M.key Q (N.arc (N.seq.getD i' 0)).s := by
  obtain ⟨-, -, -, hS⟩ := isNF_arcs h
  have hl := seq_length h
  rcases lt_or_eq_of_le hii with hlt | rfl
  · rw [getD_of_lt 0 (by omega), getD_of_lt 0 (by omega)]
    exact List.pairwise_iff_getElem.1 hS.2 i i' (by omega) (by omega) hlt
  simp_all


end

section
variable {M : Model} {Q : Polygon}
/-- `KeyPred` bounds the key from above, its negation from below. -/
theorem keyPred_le {x s : WPos} (h : WalkKey.KeyPred M Q x s) :
    M.key Q s ≤ M.key Q x := by
  core_grind

theorem le_of_not_keyPred {x s : WPos}
    (h : ¬ WalkKey.KeyPred M Q x s) : M.key Q x ≤ M.key Q s := by
  core_grind

/-- **The gap property of the chosen position** `p* = t - 1` (or the last position if `t = 0`)
of the partition point `t`: the start `a` of its arc is the query key, or no start key lies in
the open cyclic interval from `a` to the query key. -/
theorem pick_gap {N : NF} (h : IsNF M Q N) (x : WPos) {t : ℕ}
    (hA : 0 < N.arcs.length) (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → WalkKey.KeyPred M Q x (N.arc (N.seq.getD i 0)).s)
    (hpost : t < N.arcs.length → ¬ WalkKey.KeyPred M Q x (N.arc (N.seq.getD t 0)).s) :
    M.key Q (N.arc (N.seq.getD (if 0 < t then t - 1 else N.arcs.length - 1) 0)).s =
        M.key Q x ∨
      ∀ j, j < N.arcs.length → ¬ sideInArc
        (M.key Q (N.arc (N.seq.getD (if 0 < t then t - 1 else N.arcs.length - 1) 0)).s)
        (M.key Q x) (M.key Q (N.arc j).s) := by
  set q := M.key Q x
  by_cases h0 : 0 < t
  · rw [ite_eq_left h0]
    set a := M.key Q (N.arc (N.seq.getD (t - 1) 0)).s
    have haq : a ≤ q := keyPred_le (hpre (t - 1) (by omega))
    rcases eq_or_lt_of_le haq with he | hlt
    · simp_all
    right
    intro j hj hin
    unfold sideInArc at hin
    rw [ite_eq_left hlt] at hin
    obtain ⟨i, hi, rfl⟩ := seq_surj h hj
    by_cases hit : i < t
    · have := seq_sorted h (show i ≤ t - 1 by omega) (by omega)
      linarith
    · have hk := le_of_not_keyPred (hpost (by omega))
      have := seq_sorted h (show t ≤ i by omega) hi
      linarith
  · rw [ite_eq_right h0]
    have ht0 : t = 0 := by omega
    subst ht0
    set a := M.key Q (N.arc (N.seq.getD (N.arcs.length - 1) 0)).s
    have hall : ∀ i, i < N.arcs.length → q ≤ M.key Q (N.arc (N.seq.getD i 0)).s := fun i hi =>
      (le_of_not_keyPred (hpost hA)).trans (seq_sorted h (Nat.zero_le i) hi)
    have hqa : q ≤ a := hall _ (by omega)
    rcases eq_or_lt_of_le hqa with he | hlt
    · simp_all
    right
    intro j hj hin
    unfold sideInArc at hin
    rw [ite_eq_right (not_lt.2 hlt.le)] at hin
    obtain ⟨i, hi, rfl⟩ := seq_surj h hj
    have h1 := hall i hi
    have h2 := seq_sorted h (show i ≤ N.arcs.length - 1 by omega) (by omega)
    grind

/-- **Correctness of the pick** (the post of `LocateSpec` for the model and normal form of the
precondition), from the partition point `t` of the search. -/
theorem locate_pick {N : NF} (hcov : ∀ y : ℝ, M.IsCut (N.F M Q) y →
      ∃ U ∈ M.regions (N.F M Q), ∃ b : ℝ, M.IsArc (N.F M Q) U y b)
    (h : IsNF M Q N) (x : WPos) {t : ℕ} (hA : 0 < N.arcs.length) (ht : t ≤ N.arcs.length)
    (hpre : ∀ i, i < t → WalkKey.KeyPred M Q x (N.arc (N.seq.getD i 0)).s)
    (hpost : t < N.arcs.length → ¬ WalkKey.KeyPred M Q x (N.arc (N.seq.getD t 0)).s) :
    let j := N.seq.getD (if 0 < t then t - 1 else N.arcs.length - 1) 0
    j < N.arcs.length ∧
      (¬ M.IsCut (N.F M Q) (M.key Q x) →
        N.F M Q = ∅ ∨ sideInArc (M.key Q (N.arc j).s) (M.key Q (N.arc j).e) (M.key Q x)) ∧
      (M.IsCut (N.F M Q) (M.key Q x) →
        M.key Q (N.arc j).s = M.key Q x ∨ M.key Q (N.arc j).e = M.key Q x) := by
  intro j
  have hpos : (if 0 < t then t - 1 else N.arcs.length - 1) < N.arcs.length := by
    grind
  have hj : j < N.arcs.length := seq_lt h hpos
  refine ⟨hj, ?_⟩
  have hgap := pick_gap h x hA ht hpre hpost
  obtain ⟨U, hU⟩ := isArc_of_listed h hj
  set a := M.key Q (N.arc j).s
  set b := M.key Q (N.arc j).e
  set q := M.key Q x
  by_cases hF : N.F M Q = ∅
  · refine ⟨fun _ => Or.inl hF, fun hc => ?_⟩
    obtain ⟨c, hc, -⟩ := hc
    grind
  -- the chosen arc is a genuine arc between two distinct cuts
  obtain ⟨-, -, -, -, hends, hno, -⟩ := hU
  obtain ⟨hca, hcb, hab⟩ : M.IsCut (N.F M Q) a ∧ M.IsCut (N.F M Q) b ∧ a ≠ b := by
    simp_all
  -- the key claim
  have claim : sideInArc a b q ∨ b = q ∨ a = q := by
    grind [Chazelle.Core.NFLoc.sideInArc_swap, Chazelle.Core.NFLoc.listed_of_isArc]
  ram_grind


end

end

end NFLoc

end Chazelle.Core
