module

public import Chazelle.Core.GranRemove

/-!
# WP-F, part 3: the weight of a key interval by integer arithmetic

The weight `arcWt a b` of the open cyclic key interval from `a = e_a + t_a` to `b = e_b + t_b`
(`0 ≤ t < 1`) counts the counted walk edges whose open part meets it.  It is computed from the two
edge indices, the parameter test `0 < t_b` and the order of the keys (`arcWt_formula`):

* `a = b`: every counted edge (`cntIn 0 n`);
* `a < b`: the edges `e_a, …, e_b' - 1` with `e_b' = e_b + [0 < t_b]`;
* `b < a`: the edges `e_a, …, n - 1` and `0, …, min e_b' e_a - 1`.

The counted edges of the two models form an interval (`CountDesc`): all edges of the interior
model, the tour edges `6 … 2m + 5` of a chain model; `ncard_counted` counts them in `[l, r)`.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

/-- The number of counted edges in `[l, r)`: all edges (`ch = false`, the interior model), or
the edges of `[6, 2m + 6)` (`ch = true`, a chain model with `m` edges). -/
def cntIn (ch : Bool) (m l r : ℕ) : ℕ := if ch then min r (2 * m + 6) - max l 6 else r - l

/-- The counted-edge predicate of a model is an interval: all edges below `n` (interior model),
or `[6, 2m + 6)` (chain model). -/
def CountDesc (M : Model) (ch : Bool) (m : ℕ) : Prop :=
  (ch = true → 2 * m + 6 ≤ M.W.n) ∧
    ∀ p, p < M.W.n → (M.counted p ↔ (ch = false ∨ (6 ≤ p ∧ p < 2 * m + 6)))

/-- **Counting the counted edges of `[l, r)`.** -/
theorem ncard_counted {M : Model} {ch : Bool} {m : ℕ} (hD : CountDesc M ch m) {l r : ℕ}
    (hr : r ≤ M.W.n) :
    {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r}.ncard = cntIn ch m l r := by
  cases ch with
  | false =>
    have e : {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r} = Ico l r := by
      ext p
      simp only [mem_ofPred_eq, mem_Ico]
      constructor
      · rintro ⟨-, -, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, (hD.2 p (by omega)).2 (Or.inl rfl), h1, h2⟩
    rw [e, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
    rfl
  | true =>
    have e : {p : ℕ | p < M.W.n ∧ M.counted p ∧ l ≤ p ∧ p < r} =
        Ico (max l 6) (min r (2 * m + 6)) := by
      ext p
      simp only [mem_ofPred_eq, mem_Ico]
      constructor
      · rintro ⟨hp, hc, h1, h2⟩
        have := (hD.2 p hp).1 hc
        rcases this with h | h
        · exact absurd h (by decide)
        · refine ⟨max_le h1 h.1, lt_min h2 h.2⟩
      · rintro ⟨h1, h2⟩
        have h1' := le_of_max_le_left h1
        have h1'' := le_of_max_le_right h1
        have h2' := lt_of_lt_of_le h2 (min_le_left _ _)
        have h2'' := lt_of_lt_of_le h2 (min_le_right _ _)
        exact ⟨by omega, (hD.2 p (by omega)).2 (Or.inr ⟨h1'', h2''⟩), h1', h2'⟩
    rw [e, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
    rfl

/-- The edge bump `[0 < t]`. -/
noncomputable def bump (t : ℝ) : ℕ := if 0 < t then 1 else 0

/-- **The weight of a key interval by integer arithmetic.** -/
theorem arcWt_formula {M : Model} {ch : Bool} {m : ℕ} (hD : CountDesc M ch m) {ea eb : ℕ}
    {ta tb : ℝ} (ha : ea < M.W.n) (hb : eb < M.W.n) (ha0 : 0 ≤ ta) (ha1 : ta < 1)
    (hb0 : 0 ≤ tb) (hb1 : tb < 1) :
    M.arcWt (ea + ta) (eb + tb) =
      if (ea : ℝ) + ta = eb + tb then cntIn ch m 0 M.W.n
      else if (ea : ℝ) + ta < eb + tb then cntIn ch m ea (eb + bump tb)
      else cntIn ch m 0 (min (eb + bump tb) ea) + cntIn ch m ea M.W.n := by
  unfold Model.arcWt
  have hbump : ∀ p : ℕ, ((p : ℝ) < eb + tb ↔ p < eb + bump tb) := by
    intro p
    unfold bump
    split_ifs with ht
    · constructor
      · intro h
        by_contra h'
        have : (eb : ℝ) + 1 ≤ p := by exact_mod_cast (show eb + 1 ≤ p by omega)
        linarith
      · intro h
        have : (p : ℝ) ≤ eb := by exact_mod_cast (show p ≤ eb by omega)
        linarith
    · have ht0 : tb = 0 := le_antisymm (not_lt.1 ht) hb0
      rw [ht0, add_zero, Nat.add_zero]
      exact_mod_cast Iff.rfl
  -- `a < p + 1` for some point of the open edge iff `ea ≤ p`
  have hafter : ∀ p : ℕ, ((ea : ℝ) + ta < p + 1 ↔ ea ≤ p) := by
    intro p
    constructor
    · intro h
      by_contra h'
      have : (p : ℝ) + 1 ≤ ea := by exact_mod_cast (show p + 1 ≤ ea by omega)
      linarith
    · intro h
      have : (ea : ℝ) ≤ p := by exact_mod_cast h
      linarith
  split_ifs with h1 h2
  · -- the whole walk
    rw [← ncard_counted hD le_rfl]
    congr 1
    ext p
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hp, hc, -⟩; exact ⟨hp, hc, Nat.zero_le _, hp⟩
    · rintro ⟨hp, hc, -, -⟩
      refine ⟨hp, hc, ?_⟩
      -- some point of the open edge differs from the key
      by_cases hq : (p : ℝ) + 1 / 2 = ea + ta
      · refine ⟨1 / 4, by norm_num, by norm_num, ?_⟩
        unfold sideInArc; rw [← h1, ite_eq_right (lt_irrefl _)]
        right; linarith
      · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
        unfold sideInArc; rw [← h1, ite_eq_right (lt_irrefl _)]
        rcases lt_or_gt_of_ne hq with h | h
        · right; exact h
        · left; exact h
  · -- `a < b`
    have hr : eb + bump tb ≤ M.W.n := by unfold bump; split_ifs <;> omega
    rw [← ncard_counted hD hr]
    congr 1
    ext p
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hp, hc, t, ht0, ht1, hin⟩
      unfold sideInArc at hin
      rw [ite_eq_left h2] at hin
      refine ⟨hp, hc, (hafter p).1 (by linarith [hin.1]), (hbump p).1 (by linarith [hin.2])⟩
    · rintro ⟨hp, hc, hl, hr'⟩
      refine ⟨hp, hc, ?_⟩
      have e1 := (hafter p).2 hl
      have e2 := (hbump p).2 hr'
      -- a point of `(max a p, min b (p + 1))`
      set lo := max ((ea : ℝ) + ta) p
      set hi := min ((eb : ℝ) + tb) (p + 1)
      have hlohi : lo < hi := by
        simp only [lo, hi]
        refine max_lt (lt_min h2 e1) (lt_min e2 (by linarith))
      refine ⟨(lo + hi) / 2 - p, ?_, ?_, ?_⟩
      · have : (p : ℝ) ≤ lo := le_max_right _ _
        linarith
      · have : hi ≤ (p : ℝ) + 1 := min_le_right _ _
        linarith
      · unfold sideInArc
        rw [ite_eq_left h2]
        have : (ea : ℝ) + ta ≤ lo := le_max_left _ _
        have : hi ≤ (eb : ℝ) + tb := min_le_left _ _
        constructor <;> linarith
  · -- `b < a`: the wrap-around
    have hr : min (eb + bump tb) ea ≤ M.W.n := (min_le_right _ _).trans ha.le
    have hdisj : Disjoint {p : ℕ | p < M.W.n ∧ M.counted p ∧ 0 ≤ p ∧ p < min (eb + bump tb) ea}
        {p : ℕ | p < M.W.n ∧ M.counted p ∧ ea ≤ p ∧ p < M.W.n} := by
      rw [Set.disjoint_left]
      rintro p ⟨-, -, -, h1'⟩ ⟨-, -, h2', -⟩
      have := lt_of_lt_of_le h1' (min_le_right _ _)
      omega
    have hf1 : {p : ℕ | p < M.W.n ∧ M.counted p ∧ 0 ≤ p ∧ p < min (eb + bump tb) ea}.Finite :=
      (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1
    have hf2 : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ea ≤ p ∧ p < M.W.n}.Finite :=
      (Set.finite_lt_nat M.W.n).subset fun p hp => hp.1
    rw [← ncard_counted hD hr, ← ncard_counted hD le_rfl, ← Set.ncard_union_eq hdisj hf1 hf2]
    · congr 1
      ext p
      simp only [mem_ofPred_eq, mem_union]
      constructor
      · rintro ⟨hp, hc, t, ht0, ht1, hin⟩
        unfold sideInArc at hin
        rw [ite_eq_right h2] at hin
        rcases hin with hin | hin
        · exact Or.inr ⟨hp, hc, (hafter p).1 (by linarith), hp⟩
        · have e2 := (hbump p).1 (by linarith)
          by_cases hpe : p < ea
          · exact Or.inl ⟨hp, hc, Nat.zero_le _, lt_min e2 hpe⟩
          · exact Or.inr ⟨hp, hc, by omega, hp⟩
      · rintro (⟨hp, hc, -, hr'⟩ | ⟨hp, hc, hl, -⟩)
        · have e2 := (hbump p).2 (lt_of_lt_of_le hr' (min_le_left _ _))
          set hi := min ((eb : ℝ) + tb) (p + 1)
          have hphi : (p : ℝ) < hi := lt_min e2 (by linarith)
          have hhi1 : hi ≤ (p : ℝ) + 1 := min_le_right _ _
          have hhi2 : hi ≤ (eb : ℝ) + tb := min_le_left _ _
          refine ⟨hp, hc, (hi - p) / 2, by linarith, by linarith, ?_⟩
          unfold sideInArc
          rw [ite_eq_right h2]
          right
          linarith
        · have e1 := (hafter p).2 hl
          set lo := max ((ea : ℝ) + ta) p
          have hlo1 : lo < (p : ℝ) + 1 := max_lt e1 (by linarith)
          have hlo2 : (p : ℝ) ≤ lo := le_max_right _ _
          have hlo3 : (ea : ℝ) + ta ≤ lo := le_max_left _ _
          refine ⟨hp, hc, (lo + p + 1) / 2 - p, by linarith, by linarith, ?_⟩
          unfold sideInArc
          rw [ite_eq_right h2]
          left
          linarith

end

end Gran

end Chazelle.Core
