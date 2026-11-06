module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleShD

/-!
# WP-M (E7-B, part 12): the sub-queries of an interior query

An interior query from `⟨e₁, h₁⟩` to `⟨e₂, h₂⟩` (proper positions of the interior walk of `Q`)
is normalized (`h₂' = nh e₂ h₂`, `ee = eeOf …`, `L = spanL ee h₂'`, `plan_arc`) and served by

* one sub-query from `⟨e₁, h₁⟩` with `ee`, `h₂'` when `L ≤ n - 1` (`plan_one`);
* two sub-queries when `L ≥ n`: from `⟨e₁, h₁⟩` over two edges to the vertex `(e₁ + 2) mod n`, then
  from there with `ee - 2`, `h₂'` (`plan_two`).

In both cases the sub-queries are `SubOK`, their weights are at most the weight of the query, and
the point sets of the sub-queries make up the point set of the query.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set

variable {Q : Polygon}

/-- The facts of a normalized query. -/
structure QFacts (Q : Polygon) (e₁ h₁ e₂ h₂ : ℕ) : Prop where
  hn : 3 ≤ Q.n
  hD : DistinctHeights Q
  he₁ : e₁ < Q.n
  he₂ : e₂ < Q.n
  hs : ProperPos (interiorModel Q) Q Q.n ⟨e₁, h₁⟩
  he : ProperPos (interiorModel Q) Q Q.n ⟨e₂, h₂⟩

section

variable {e₁ h₁ e₂ h₂ : ℕ} (q : QFacts Q e₁ h₁ e₂ h₂)

include q in
/-- The end of the normalized query has the key of the end of the query. -/
theorem qkey_nh : (interiorModel Q).key Q ⟨e₂, nh Q e₂ h₂⟩ = (interiorModel Q).key Q ⟨e₂, h₂⟩ := by
  Ξ key_eq, key_eq, param_nh q.he₂

include q in
/-- **The plan of a normalized query.** -/
theorem qplan :
    let ee := eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)
    let L := spanL ee (nh Q e₂ h₂)
    (interiorModel Q).arcSet ((interiorModel Q).key Q ⟨e₁, h₁⟩)
        ((interiorModel Q).key Q ⟨e₂, h₂⟩) =
      oset (interiorWalk Q) e₁ ((interiorModel Q).param Q ⟨e₁, h₁⟩)
        (ee + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩) ∧
    (interiorModel Q).param Q ⟨e₁, h₁⟩ < ee + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ ∧
    (e₁ + ee) % Q.n = e₂ ∧ ee ≤ Q.n ∧
    ((nh Q e₂ h₂ = 0 ∧ ee = L) ∨
      (nh Q e₂ h₂ ≠ 0 ∧ ee + 1 = L ∧ 0 < (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩)) ∧
    1 ≤ L ∧
    (L ≤ Q.n → (interiorModel Q).arcWt ((interiorModel Q).key Q ⟨e₁, h₁⟩)
      ((interiorModel Q).key Q ⟨e₂, h₂⟩) = L) ∧
    (Q.n < L → (interiorModel Q).arcWt ((interiorModel Q).key Q ⟨e₁, h₁⟩)
      ((interiorModel Q).key Q ⟨e₂, h₂⟩) = Q.n) := by
  intro ee L
  have hx := q.hs
  have hy : 0 ≤ (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ ∧
      (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ < 1 := by
    rw [param_nh q.he₂]; exact ⟨q.he.1, q.he.2.1⟩
  have hnz : nh Q e₂ h₂ = 0 ∨ 0 < (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ := by
    by_cases h0 : nh Q e₂ h₂ = 0
    · exact Or.inl h0
    · exact Or.inr (param_pos_nh q.hD (by have := q.hn; omega) q.he₂ q.he.2.2 q.he.1 h0)
  have := plan_arc q.hn q.he₁ q.he₂ ⟨hx.1, hx.2.1⟩ hy hnz
  rw [qkey_nh q] at this
  exact this

include q in
/-- **One sub-query** (`L ≤ n - 1`). -/
theorem plan_one (hL : spanL (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂) + 1 ≤ Q.n) :
    SubOK Q e₁ (spanL (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂)) h₁
      (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂) ∧
    (interiorModel Q).arcSet ((interiorModel Q).key Q ⟨e₁, h₁⟩)
        ((interiorModel Q).key Q ⟨e₂, h₂⟩) =
      oset (interiorWalk Q) e₁ ((interiorModel Q).param Q ⟨e₁, h₁⟩)
        (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂) + (interiorModel Q).param Q
          ⟨(e₁ + eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) % Q.n, nh Q e₂ h₂⟩) ∧
    (interiorModel Q).arcWt ((interiorModel Q).key Q ⟨e₁, h₁⟩)
      ((interiorModel Q).key Q ⟨e₂, h₂⟩) = spanL (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂) := by
  obtain ⟨hS, hxy, hmod, -, hee, h1, hwt, -⟩ := qplan q
  Ξ hmod
  have hpe : ProperPos (interiorModel Q) Q Q.n ⟨e₂, nh Q e₂ h₂⟩ :=
    ⟨by rw [param_nh q.he₂]; exact q.he.1, by rw [param_nh q.he₂]; exact q.he.2.1,
      le_trans nh_le q.he.2.2⟩
  refine ⟨⟨q.he₁, h1, hL, q.hs, by rw [hmod]; exact hpe, by rw [hmod]; exact hee,
    by rw [hmod]; exact hxy⟩, hS, hwt (⋄)⟩

include q in
/-- **Two sub-queries** (`L ≥ n`): two edges to the vertex `(e₁ + 2) mod n`, then the rest. -/
theorem plan_two (hL : Q.n ≤ spanL (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂)) :
    SubOK Q e₁ 2 h₁ 2 0 ∧
    SubOK Q ((e₁ + 2) % Q.n) (spanL (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂)) (nh Q e₂ h₂) - 2) 0
      (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂) - 2) (nh Q e₂ h₂) ∧
    (interiorModel Q).arcSet ((interiorModel Q).key Q ⟨e₁, h₁⟩)
        ((interiorModel Q).key Q ⟨e₂, h₂⟩) =
      oset (interiorWalk Q) e₁ ((interiorModel Q).param Q ⟨e₁, h₁⟩)
          ((2 : ℕ) + (interiorModel Q).param Q ⟨(e₁ + 2) % Q.n, 0⟩) ∪
        oset (interiorWalk Q) ((e₁ + 2) % Q.n) ((interiorModel Q).param Q ⟨(e₁ + 2) % Q.n, 0⟩)
          ((eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂) - 2 : ℕ) + (interiorModel Q).param Q
            ⟨((e₁ + 2) % Q.n + (eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂) - 2)) % Q.n, nh Q e₂ h₂⟩) ∧
    (interiorModel Q).arcWt ((interiorModel Q).key Q ⟨e₁, h₁⟩)
      ((interiorModel Q).key Q ⟨e₂, h₂⟩) = Q.n := by
  obtain ⟨hS, hxy, hmod, heen, hee, h1, hwt, hwt'⟩ := qplan q
  set ee := eeOf Q e₁ h₁ e₂ (nh Q e₂ h₂) with heed
  set L := spanL ee (nh Q e₂ h₂) with hLd
  have hn := q.hn
  have hn0 : 0 < Q.n := by omega
  have hee2 : 2 ≤ ee := by rcases hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
  have hLn : L ≤ Q.n + 1 := by rcases hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
  have hmod2 : ((e₁ + 2) % Q.n + (ee - 2)) % Q.n = e₂ := by
    rw [Nat.mod_add_mod, show e₁ + 2 + (ee - 2) = e₁ + ee by omega, hmod]
  have hpe : ProperPos (interiorModel Q) Q Q.n ⟨e₂, nh Q e₂ h₂⟩ :=
    ⟨by rw [param_nh q.he₂]; exact q.he.1, by rw [param_nh q.he₂]; exact q.he.2.1,
      le_trans nh_le q.he.2.2⟩
  have hv0 : ∀ e, ProperPos (interiorModel Q) Q Q.n ⟨e, 0⟩ := fun e =>
    ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩
  have hp0 : ∀ e, (interiorModel Q).param Q ⟨e, 0⟩ = 0 := fun e => rfl
  have hx1 := q.hs.2.1
  have hx0 := q.hs.1
  refine ⟨⟨q.he₁, by norm_num, by omega, q.hs, hv0 _, Or.inl ⟨rfl, rfl⟩, by
      rw [hp0]; push_cast; linarith⟩,
    ⟨Nat.mod_lt _ hn0, by omega, by omega, hv0 _, by rw [hmod2]; exact hpe, ?_, ?_⟩, ?_, ?_⟩
  · rw [hmod2]
    rcases hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
    · exact Or.inl ⟨h0, by omega⟩
    · exact Or.inr ⟨h0, by omega, hp⟩
  · rw [hp0, hmod2]
    rcases hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
    · have : (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ = 0 := by rw [h0]; rfl
      rw [this, add_zero]
      exact_mod_cast (show 0 < ee - 2 by omega)
    · have : (0 : ℝ) ≤ ((ee - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · rw [hS, hp0, hmod2, add_zero]
    have hiw : (interiorWalk Q).n = Q.n := Trans.iw_n
    have e1 : oset (interiorWalk Q) ((e₁ + 2) % Q.n) 0
        (((ee - 2 : ℕ) : ℝ) + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩) =
        oset (interiorWalk Q) e₁ ((2 : ℕ) + 0)
          ((2 : ℕ) + (((ee - 2 : ℕ) : ℝ) + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩)) := by
      rw [← hiw, oset_mod, oset_shift _ _ _ le_rfl]
    rw [e1, add_zero]
    have hc : ((2 : ℕ) : ℝ) + (((ee - 2 : ℕ) : ℝ) + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩) =
        ee + (interiorModel Q).param Q ⟨e₂, nh Q e₂ h₂⟩ := by
      rw [Nat.cast_sub hee2]; push_cast; ring
    rw [hc, oset_union _ _ (by push_cast; linarith) (by
      have := q.he.1
      rw [← param_nh q.he₂] at this
      have : ((2 : ℕ) : ℝ) ≤ ee := by exact_mod_cast hee2
      linarith)]
  · rcases (show L = Q.n ∨ Q.n < L by omega) with h' | h'
    · rw [hwt (by omega), h']
    · exact hwt' h'


end

end

end IOrc

end Chazelle.Core
