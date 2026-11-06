module

public import PaperStatements
public import Mathlib.Analysis.Complex.ExponentialBounds
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Tasks

@[expose] public section

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 21(b): repeated squaring computes the distances

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights (`theorem_21b_repeated_squaring`,
`theorem_21b_entries_bounded`).

Under this hypothesis, after `t` squarings the entry at `(i, j)` is the least weight of a walk from
`i` to `j` with at most `2^t` edges: it is the weight of such a walk (`exists_walk_of_entry`) and at
most the weight of every such walk (`entry_le_walkWeight`).  Cutting closed pieces out of a walk
shows that fewer than `n` edges are enough (`exists_short_walk`), and a walk of finite weight with
`k` edges has weight at most `kU` in absolute value (`abs_walkWeight_le`).
-/


namespace ThreeSumApsp

namespace Theorem21

/-- The end of a walk that is followed by a second walk. -/
theorem walkEnd_append {n : ℕ} (i : Fin n) (p q : List (Fin n)) :
    walkEnd i (p ++ q) = walkEnd (walkEnd i p) q := by
  induction p generalizing i with
  | nil => rfl
  | cons j p ih => exact ih j

/-- The weight of a walk that is followed by a second walk is the sum of the two weights. -/
theorem walkWeight_append {R : Type} [AddCommGroup R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (i : Fin n) (p q : List (Fin n)) :
    walkWeight w i (p ++ q) = walkWeight w i p + walkWeight w (walkEnd i p) q := by
  induction p generalizing i with
  | nil => simp [walkWeight, walkEnd]
  | cons j p ih => simp [walkWeight, walkEnd, ih, add_assoc]

/-- Every entry of the matrix after `t` squarings is the weight of a walk with at most `2^t` edges.
-/
theorem exists_walk_of_entry {R : Type} [AddCommGroup R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (t : ℕ) (i j : Fin n) :
    ∃ rest : List (Fin n), walkEnd i rest = j ∧ rest.length ≤ 2 ^ t ∧
      walkWeight w i rest = minPlusSquares w t i j := by
  induction t generalizing i j with
  | zero =>
    by_cases hij : i = j
    · subst hij
      exact ⟨[], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix]⟩
    · exact ⟨[j], rfl, by simp, by simp [walkWeight, minPlusSquares, weightMatrix, hij]⟩
  | succ t ih =>
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩
      fun k => minPlusSquares w t i k + minPlusSquares w t k j
    obtain ⟨p, hpend, hplen, hpweight⟩ := ih i k
    obtain ⟨q, hqend, hqlen, hqweight⟩ := ih k j
    refine ⟨p ++ q, ?_, ?_, ?_⟩
    · rw [walkEnd_append, hpend, hqend]
    · rw [List.length_append, pow_succ]
      omega
    · rw [walkWeight_append, hpend, hpweight, hqweight]
      exact hk.symm

/-- A walk with at least `n` edges visits some vertex twice: it consists of a walk `p`, a closed
walk `c` with at least one edge, and a walk `q`. -/
theorem exists_closed_piece {n : ℕ} (i : Fin n) (rest : List (Fin n))
    (h : n ≤ rest.length) :
    ∃ p c q : List (Fin n),
      rest = p ++ c ++ q ∧ c ≠ [] ∧ walkEnd (walkEnd i p) c = walkEnd i p := by
  -- Among the `rest.length + 1` vertices that the walk visits, two are equal.
  obtain ⟨a, b, hab, hb, hrep⟩ : ∃ a b : ℕ, a < b ∧ b ≤ rest.length ∧
      walkEnd i (rest.take a) = walkEnd i (rest.take b) := by
    obtain ⟨a, b, hne, hrep⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (rest.length + 1) => walkEnd i (rest.take k)) (by simp; omega)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact ⟨a, b, hlt, by omega, hrep⟩
    · exact ⟨b, a, hlt, by omega, hrep.symm⟩
  have htake : rest.take b = rest.take a ++ (rest.drop a).take (b - a) := by
    rw [← List.take_add, Nat.add_sub_cancel' hab.le]
  refine ⟨rest.take a, (rest.drop a).take (b - a), rest.drop b, ?_, ?_, ?_⟩
  · rw [← htake, List.take_append_drop]
  · refine List.ne_nil_of_length_pos ?_
    rw [List.length_take, List.length_drop]
    omega
  · rw [← walkEnd_append, ← htake, hrep]

/-- If no closed walk has negative weight, every walk can be replaced by a walk with the same ends,
fewer than `n` edges, no more edges than before, and no larger weight: cut out closed pieces. -/
theorem exists_short_walk {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (i : Fin n) (rest : List (Fin n)) :
    ∃ rest' : List (Fin n), walkEnd i rest' = walkEnd i rest ∧ rest'.length < n ∧
      rest'.length ≤ rest.length ∧ walkWeight w i rest' ≤ walkWeight w i rest := by
  induction hlen : rest.length using Nat.strong_induction_on generalizing rest with
  | _ len ih =>
    rcases lt_or_ge rest.length n with hshort | hlong
    · exact ⟨rest, rfl, hshort, hlen.le, le_rfl⟩
    · -- The walk is `p`, then the closed walk `c`, then `q`; go on with `p`, then `q`.
      obtain ⟨p, c, q, rfl, hc, hclosed⟩ := exists_closed_piece i rest hlong
      have hend : walkEnd i (p ++ q) = walkEnd i (p ++ c ++ q) := by
        simp only [walkEnd_append, hclosed]
      have hweight : walkWeight w i (p ++ q) ≤ walkWeight w i (p ++ c ++ q) := by
        simp only [walkWeight_append, walkEnd_append, hclosed]
        gcongr
        exact le_add_of_nonneg_right (hw _ _ hclosed)
      have hless : (p ++ q).length < len := by
        have := List.length_pos_iff.mpr hc
        simp only [List.length_append] at hlen ⊢
        omega
      obtain ⟨rest', hend', hlt, hle, hweight'⟩ := ih _ hless (p ++ q) rfl
      exact ⟨rest', hend'.trans hend, hlt, by omega, hweight'.trans hweight⟩

/-- If no closed walk has negative weight, the entry after `t` squarings is at most the weight of
every walk with at most `2^t` edges. -/
theorem entry_le_walkWeight {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]
    {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (t : ℕ) (i : Fin n)
    (rest : List (Fin n)) (hlen : rest.length ≤ 2 ^ t) :
    minPlusSquares w t i (walkEnd i rest) ≤ walkWeight w i rest := by
  induction t generalizing i rest with
  | zero =>
    match rest, hlen with
    | [], _ => simp [walkWeight, walkEnd, minPlusSquares, weightMatrix]
    | [j], _ =>
      by_cases hij : i = j
      · -- The diagonal entry is 0, and a loop has weight at least 0.
        subst hij
        have h := hw i [i] rfl
        simpa [walkEnd, minPlusSquares, weightMatrix] using h
      · simp [walkWeight, walkEnd, minPlusSquares, weightMatrix, hij]
    | _ :: _ :: _, h => simp at h
  | succ t ih =>
    -- The walk is `p`, its first `2^t` edges, followed by `q`, the others.
    obtain ⟨p, q, rfl, hp, hq⟩ : ∃ p q, rest = p ++ q ∧ p.length ≤ 2 ^ t ∧ q.length ≤ 2 ^ t := by
      refine ⟨rest.take (2 ^ t), rest.drop (2 ^ t), (List.take_append_drop _ _).symm,
        List.length_take_le _ _, ?_⟩
      rw [List.length_drop]
      rw [pow_succ] at hlen
      omega
    rw [walkEnd_append, walkWeight_append]
    calc minPlusSquares w (t + 1) i (walkEnd (walkEnd i p) q)
        ≤ minPlusSquares w t i (walkEnd i p)
            + minPlusSquares w t (walkEnd i p) (walkEnd (walkEnd i p) q) :=
          Finset.inf_le (f := fun k =>
            minPlusSquares w t i k + minPlusSquares w t k (walkEnd (walkEnd i p) q))
            (Finset.mem_univ _)
      _ ≤ walkWeight w i p + walkWeight w (walkEnd i p) q := add_le_add (ih i p hp) (ih _ q hq)

/-- If the edge weights are at most `U` in absolute value, a walk of finite weight with `k` edges
has weight at most `kU` in absolute value. -/
theorem abs_walkWeight_le {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (U : R) (hwU : EdgeWeightsBoundedBy w U) (i : Fin n)
    (rest : List (Fin n)) (x : R) (hx : walkWeight w i rest = (x : WithTop R)) :
    |x| ≤ rest.length • U := by
  induction rest generalizing i x with
  | nil =>
    obtain rfl : x = 0 := (WithTop.coe_injective (hx : ((0 : R) : WithTop R) = x)).symm
    simp
  | cons j rest ih =>
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.mp hx
    rw [← hab, List.length_cons, succ_nsmul']
    exact (abs_add_le a b).trans (add_le_add (hwU i j a ha.symm) (ih j b hb.symm))

end Theorem21

/-- For **Theorem 21(b)**, repeated squaring: if no closed walk has negative weight, then squaring
the weight matrix `⌈log₂ n⌉` times in the (min,+)-product yields the distance matrix.
(`Nat.clog 2 n` is `⌈log₂ n⌉`.)  Stated for weights in any linearly ordered commutative group, so
that it covers integer and real weights. -/
theorem theorem_21b_repeated_squaring {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) :
    IsDistanceMatrix w (minPlusSquares w (Nat.clog 2 n)) := by
  intro i j
  constructor
  · obtain ⟨rest, hend, -, hweight⟩ := Theorem21.exists_walk_of_entry w (Nat.clog 2 n) i j
    exact ⟨rest, hend, hweight⟩
  · rintro x ⟨rest, rfl, rfl⟩
    -- A shortest walk needs fewer than `n ≤ 2^⌈log₂ n⌉` edges.
    obtain ⟨rest', hend, hlt, -, hle⟩ := Theorem21.exists_short_walk w hw i rest
    rw [← hend]
    exact (Theorem21.entry_le_walkWeight w hw _ i rest'
      (hlt.le.trans (Nat.le_pow_clog (by norm_num) n))).trans hle

/-- For **Theorem 21(b)**, repeated squaring: a bound on the entries.  If the edge weights have
absolute value at most `U`, every finite entry of every matrix of the repeated squaring has absolute
value at most `nU`; with `U = n^ν` this is `n^{ν+1}`.

NOTE.  A missing edge has the weight `⊤` here, while the (min,+)-product of Theorem 21(b) is on
integer matrices with entries of absolute value at most `U` (`IsMinPlusProduct`).  Nothing is stated
here about replacing `⊤` by a large number. -/
theorem theorem_21b_entries_bounded {R : Type} [AddCommGroup R] [LinearOrder R]
    [IsOrderedAddMonoid R] {n : ℕ} (w : Fin n → Fin n → WithTop R) (hw : NoNegativeCycle w) (U : R)
    (hU : 0 ≤ U) (hwU : EdgeWeightsBoundedBy w U) (t : ℕ) (i j : Fin n) (x : R)
    (hx : minPlusSquares w t i j = (x : WithTop R)) : |x| ≤ n • U := by
  -- The entry is the weight of a walk with at most `2^t` edges.  Cutting it short gives a walk with
  -- fewer than `n` edges, whose weight is no larger, and no smaller because the entry is a minimum.
  obtain ⟨rest, hend, hlen, hweight⟩ := Theorem21.exists_walk_of_entry w t i j
  obtain ⟨rest', hend', hlt, hlen', hle⟩ := Theorem21.exists_short_walk w hw i rest
  have hge := Theorem21.entry_le_walkWeight w hw t i rest' (hlen'.trans hlen)
  rw [hend', hend, hx] at hge
  have hshort : walkWeight w i rest' = (x : WithTop R) :=
    le_antisymm (hle.trans (hweight.trans hx).le) hge
  exact (Theorem21.abs_walkWeight_le w U hwU i rest' x hshort).trans
    (nsmul_le_nsmul_left hU hlt.le)

end ThreeSumApsp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Repeated squaring on lists of integers

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix `⌈log₂ n⌉`
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most `nU`, where `U` bounds the edge weights. The matrices of the repeated
squaring have entries that may be `+∞`, while a solver for the (min,+)-product works on integers.
Here `+∞` is written as the integer `3nU`.

* `squareList n U ADJ W t` is the list, row by row, after `t` rounds.  A round is a (min,+)-product
  of the list with itself, after which every entry above `nU` is set back to `3nU`.
* One round is right (`Encodes.square`): finite entries have absolute value at most `nU`, so a sum
  with an infinite term is at least `2nU`, and a finite sum is the sum of the two codes.
* By induction the list holds the matrix `minPlusSquares` of the repeated squaring, entry
  by entry (`encodes_squareList`), and after `⌈log₂ n⌉` rounds it holds the distances
  (`squareList_distances`).
-/


namespace ThreeSumApsp.Spec

/-! ## Entries that may be infinite, as integers -/

/-- The list `L` holds, row by row, the matrix `D`, with `INF` for `+∞`: the code `d.untopD INF` of
an entry `d` is the number itself, or `INF` if `d = +∞`. -/
def Encodes (n : ℕ) (INF : ℤ) (L : List ℤ) (D : Fin n → Fin n → WithTop ℤ) : Prop :=
  ∀ i j : Fin n, entry n L i j = (D i j).untopD INF

/-- Every number above `thr` becomes `INF`. -/
def clip (thr INF x : ℤ) : ℤ := if thr < x then INF else x

/-- A code is at least `-B` if `3B` stands for `+∞` and the numbers are bounded by `B`. -/
theorem neg_le_untopD {B : ℤ} (hB : 0 ≤ B) {d : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) : -B ≤ d.untopD (3 * B) := by
  cases d with
  | top => rw [WithTop.untopD_top]; omega
  | coe x => exact (abs_le.1 (hd x rfl)).1

/-- If a sum of two entries is `+∞`, then the two codes add up to at least `2B`. -/
theorem two_mul_le_untopD_add_untopD {B : ℤ} (hB : 0 ≤ B) {d d' : WithTop ℤ}
    (hd : ∀ x : ℤ, d = (x : WithTop ℤ) → |x| ≤ B) (hd' : ∀ x : ℤ, d' = (x : WithTop ℤ) → |x| ≤ B)
    (h : d + d' = ⊤) : 2 * B ≤ d.untopD (3 * B) + d'.untopD (3 * B) := by
  have hlow := neg_le_untopD hB hd
  have hlow' := neg_le_untopD hB hd'
  rcases WithTop.add_eq_top.1 h with rfl | rfl
  · rw [WithTop.untopD_top]; omega
  · rw [WithTop.untopD_top]; omega

/-- If a sum of two entries is a number, then the two codes add up to this number. -/
theorem untopD_add_untopD_of_coe {INF y : ℤ} {d d' : WithTop ℤ}
    (h : d + d' = (y : WithTop ℤ)) : d.untopD INF + d'.untopD INF = y := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := WithTop.add_eq_coe.1 h
  exact hab

/-! ## The lists of the repeated squaring -/

/-- The weight matrix of the graph (0 on the diagonal), row by row, with `INF` where there is no
edge. -/
def weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    if q / n = q % n then 0 else if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The matrix after `t` squarings, row by row, with `3nU` for `+∞`. -/
def squareList (n U : ℕ) (ADJ W : List ℤ) : ℕ → List ℤ
  | 0 => weightList n (3 * (n * U : ℕ)) ADJ W
  | t + 1 =>
    (minPlusList n (squareList n U ADJ W t) (squareList n U ADJ W t)).map
      (clip (n * U : ℕ) (3 * (n * U : ℕ)))

/-- Each list of the repeated squaring has `n²` entries. -/
theorem length_squareList (n U : ℕ) (ADJ W : List ℤ) (t : ℕ) :
    (squareList n U ADJ W t).length = n * n := by
  cases t <;> simp [squareList, weightList, length_minPlusList]

/-- The list of the weights holds the weight matrix of the graph. -/
theorem encodes_weightList (n : ℕ) (INF : ℤ) (ADJ W : List ℤ) :
    Encodes n INF (weightList n INF ADJ W) (weightMatrix (graphOf n ADJ W)) := by
  intro i j
  rw [entry, weightList, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Nat.mul_add_div_of_lt j.isLt,
    Nat.mul_add_mod_of_lt j.isLt]
  simp only [weightMatrix, Matrix.of_apply, graphOf, Fin.ext_iff]
  split_ifs <;> rfl

/-- **One round.**  If a list holds a matrix `D` whose finite entries are bounded by `B`, with `3B`
for `+∞`, and the finite entries of the (min,+)-product of `D` with itself are bounded by `B` too,
then the (min,+)-product of the list with itself, with every entry above `B` set to `3B`, holds that
product. -/
theorem Encodes.square {n : ℕ} {B : ℤ} (hB : 1 ≤ B) {L : List ℤ}
    {D : Matrix (Fin n) (Fin n) (WithTop ℤ)} (hL : Encodes n (3 * B) L D)
    (hD : ∀ i j (x : ℤ), D i j = (x : WithTop ℤ) → |x| ≤ B)
    (hD' : ∀ i j (x : ℤ), minPlus D D i j = (x : WithTop ℤ) → |x| ≤ B) :
    Encodes n (3 * B) ((minPlusList n L L).map (clip B (3 * B))) (minPlus D D) := by
  intro i j
  have hB0 : 0 ≤ B := by omega
  rw [entry, minPlusList, List.map_map, List.getD_map_range _ (Nat.mul_add_lt_mul i.isLt j.isLt),
    Function.comp_apply, Nat.mul_add_div_of_lt j.isLt, Nat.mul_add_mod_of_lt j.isLt]
  -- The entry `m` of the product of the lists is the smallest sum of two codes, attained at `k₁`.
  obtain ⟨k₁, hk₁, hmin⟩ := exists_minPlusEntry_eq i.pos L L i j
  lift k₁ to Fin n using hk₁
  rw [hL i k₁, hL k₁ j] at hmin
  have hle : ∀ k : Fin n,
      minPlusEntry n L L i j ≤ (D i k).untopD (3 * B) + (D k j).untopD (3 * B) := fun k => by
    rw [← hL i k, ← hL k j]
    exact minPlusEntry_le n L L i j k.isLt
  generalize minPlusEntry n L L i j = m at hmin hle
  -- The entry of the product of the matrices is the smallest sum of two entries, attained at `k₀`.
  have hinf : ∀ k, minPlus D D i j ≤ D i k + D k j := fun k => Finset.inf_le (Finset.mem_univ k)
  obtain ⟨k₀, -, hk₀⟩ : ∃ k₀ ∈ Finset.univ, minPlus D D i j = D i k₀ + D k₀ j :=
    Finset.exists_mem_eq_inf Finset.univ ⟨i, Finset.mem_univ i⟩ fun k => D i k + D k j
  cases hx : minPlus D D i j with
  | top =>
    -- Every sum is `+∞`, so `m ≥ 2B > B`, and `m` is set to `3B`.
    have := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) (top_le_iff.1 (hx ▸ hinf k₁))
    rw [WithTop.untopD_top, clip, if_pos (by omega)]
  | coe x =>
    -- The smallest sum is a number `x ≤ B`.  Then `m = x`, and `m` is not changed.
    have := abs_le.1 (hD' i j x hx)
    have : m ≤ x := (hle k₀).trans_eq (untopD_add_untopD_of_coe (hk₀.symm.trans hx))
    have : x ≤ m := by
      cases hy : D i k₁ + D k₁ j with
      | top =>
        -- `x ≤ B ≤ 2B ≤ m`
        have := two_mul_le_untopD_add_untopD hB0 (hD i k₁) (hD k₁ j) hy
        omega
      | coe y =>
        rw [hmin, untopD_add_untopD_of_coe hy]
        exact WithTop.coe_le_coe.1 (hx ▸ hy ▸ hinf k₁)
    rw [WithTop.untopD_coe, clip, if_neg (by omega)]
    omega

/-- The edge weights of the graph read from lists are bounded if the list of the weights is. -/
theorem edgeWeightsBoundedBy_graphOf {n : ℕ} {ADJ W : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hW : AbsLe W U) : EdgeWeightsBoundedBy (graphOf n ADJ W) U := by
  intro i j x hx
  rw [graphOf] at hx
  split_ifs at hx
  · obtain rfl := WithTop.coe_injective hx
    exact AbsLe.abs_getD_le hU hW _
  · exact absurd hx WithTop.top_ne_coe

variable {n U : ℕ} {ADJ W : List ℤ}

/-- For Theorem 21(b): the finite entries of the matrices of the repeated squaring have absolute
value at most `nU`. -/
theorem abs_minPlusSquares_le (hW : AbsLe W U) (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ)
    (i j : Fin n) (x : ℤ)
    (hx : minPlusSquares (graphOf n ADJ W) t i j = (x : WithTop ℤ)) : |x| ≤ ((n * U : ℕ) : ℤ) := by
  simpa using theorem_21b_entries_bounded (graphOf n ADJ W) hc (U : ℤ) (by positivity)
    (edgeWeightsBoundedBy_graphOf (by positivity) hW) t i j x hx

/-- **Repeated squaring on lists.**  After `t` rounds the list holds the matrix after `t` squarings
(`minPlusSquares`). -/
theorem encodes_squareList (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    Encodes n (3 * (n * U : ℕ)) (squareList n U ADJ W t) (minPlusSquares (graphOf n ADJ W) t) := by
  induction t with
  | zero => exact encodes_weightList _ _ _ _
  | succ t ih =>
    exact Encodes.square (by exact_mod_cast Nat.mul_pos hn hU) ih (abs_minPlusSquares_le hW hc t)
      (abs_minPlusSquares_le hW hc (t + 1))

/-- The entries of the lists of the repeated squaring are bounded by `3nU`. -/
theorem abs_squareList_le (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) (t : ℕ) :
    AbsLe (squareList n U ADJ W t) (3 * (n * U) : ℕ) := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (length_squareList n U ADJ W t ▸ hq)
  rw [← List.getD_eq_getElem _ 0 hq, ← entry, encodes_squareList hn hU hW hc t ⟨a, ha⟩ ⟨b, hb⟩]
  cases hd : minPlusSquares (graphOf n ADJ W) t ⟨a, ha⟩ ⟨b, hb⟩ with
  | top =>
    rw [WithTop.untopD_top, abs_of_nonneg (by positivity)]
    exact le_of_eq (by push_cast; rfl)
  | coe y =>
    have := abs_minPlusSquares_le hW hc t _ _ y hd
    rw [WithTop.untopD_coe]
    omega

/-- **The answer.**  After `⌈log₂ n⌉` rounds the list holds the distances: an entry is `3nU` if and
only if the distance is `+∞`, and it is the distance otherwise. -/
theorem squareList_distances (hn : 1 ≤ n) (hU : 1 ≤ U) (hW : AbsLe W U)
    (hc : NoNegativeCycle (graphOf n ADJ W)) :
    ∃ dist : Fin n → Fin n → WithTop ℤ, IsDistanceMatrix (graphOf n ADJ W) dist ∧ ∀ i j : Fin n,
      (dist i j = ⊤ → entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = 3 * (n * U : ℕ)) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        entry n (squareList n U ADJ W (Nat.clog 2 n)) i j = z ∧ z ≠ 3 * (n * U : ℕ) := by
  refine ⟨minPlusSquares (graphOf n ADJ W) (Nat.clog 2 n), theorem_21b_repeated_squaring _ hc,
    fun i j => ⟨fun h => ?_, fun z h => ?_⟩⟩
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_top]
  · rw [encodes_squareList hn hU hW hc _ i j, h, WithTop.untopD_coe]
    have := abs_le.1 (abs_minPlusSquares_le hW hc _ i j z h)
    have : 1 ≤ n * U := Nat.mul_pos hn hU
    exact ⟨rfl, by omega⟩

end ThreeSumApsp.Spec
end

section
namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## clip -/

namespace Clip

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The threshold. -/
abbrev Thresh : ℕ := 1
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 2
/-- The address of the source. -/
abbrev Src : ℕ := 3
/-- The address of the destination. -/
abbrev Dst : ℕ := 4
/-- The counter q. -/
abbrev Idx : ℕ := 5

end Clip

open Clip in
/-- clip(len, thr, INF, src, dst): for q < len, dst[q] := INF if src[q] > thr, and src[q]
otherwise. -/
def clipBody : Stmt :=
  .for Idx (v Len) (
    .ite (v Thresh <' M (v Src +' v Idx))
      (.store (v Dst +' v Idx) (v Big))
      (.store (v Dst +' v Idx) (M (v Src +' v Idx))))

/-- **clip** writes the clipped list to dst, changes nothing else, and takes at most 23 len + 6
steps. -/
theorem clip_meets {p : ℕ} (hp : P[p]? = some clipBody) {μ : ℕ → ℤ} {src dst : ℕ} {thr INF : ℤ}
    {L : List ℤ} (hL : Seg μ src L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + L.length ≤ lim.space) (hdst : dst + L.length ≤ lim.space)
    (hsep : src + L.length ≤ dst ∨ dst + L.length ≤ src) :
    Meets lim P p d [L.length, thr, INF, src, dst] μ (23 * L.length + 6) fun _ μ' =>
      Seg μ' dst (L.map (clip thr INF)) ∧ SameOutside μ μ' dst L.length := by
  refine .of_body hp ?_
  refine Ends.forFrame (fun j μ' => μ' = wrote μ dst (fun i => clip thr INF (L.getD i 0)) j)
    L.length wrote_zero.symm ?round ?done (hT := by simp; omega)
  case round =>
    intro j μ' hj hμ
    have hread : μ' (src + j) = L.getD j 0 :=
      hμ ▸ (wrote_rest (by omega)).trans (hL.getD hj 0)
    have hnext : Function.update μ' (dst + j) (clip thr INF (L.getD j 0)) = _ := hμ ▸ wrote_succ
    -- from here on x = src[j]
    generalize L.getD j 0 = x at hread hnext
    -- if Thresh < mem[Src + Idx]
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · have hc' : thr < x := by simpa [hread] using hc
      rw [clip, if_pos hc'] at hnext
      -- mem[Dst + Idx] := Big
      light_store (dst + j) INF
      exact ⟨rfl, hnext⟩
    · have hc' : ¬ thr < x := by simpa [hread] using hc
      rw [clip, if_neg hc'] at hnext
      -- mem[Dst + Idx] := mem[Src + Idx]
      light_store (dst + j) x using hread
      exact ⟨rfl, hnext⟩
  case done =>
    rintro _ rfl
    dsimp only
    exact ⟨seg_wrote_map _ L, sameOutside_wrote le_rfl⟩

/-! ## apInit -/

namespace ApInit

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of A. -/
abbrev Mat : ℕ := 4
/-- The counter of both passes. -/
abbrev Idx : ℕ := 5
/-- n², in the first pass. -/
abbrev Cells : ℕ := 6
/-- The address of the diagonal cell, in the second pass. -/
abbrev Diag : ℕ := 6

end ApInit

open ApInit in
/-- The round of the first pass: A[q] := w[q] if adj[q] = 1, and INF otherwise. -/
def apInitFill : Stmt :=
  .ite (M (v AdjAt +' v Idx) =' k 1) (.store (v Mat +' v Idx) (M (v WtsAt +' v Idx)))
    (.store (v Mat +' v Idx) (v Big))

open ApInit in
/-- The round of the second pass: the diagonal cell becomes 0; the next one is n + 1 cells on. -/
def apInitDiag : Stmt := .store (v Diag) (k 0) ;; .set Diag (v Diag +' v Verts +' k 1)

open ApInit in
/-- apInit(n, INF, adj, w, A): the first pass fills the n² cells of A, the second pass puts 0 on the
diagonal. -/
def apInitBody : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .for Idx (v Cells) apInitFill ;;
  .set Diag (v Mat) ;;
  .for Idx (v Verts) apInitDiag

/-- The entry number q of the weight matrix, the diagonal apart. -/
def apInitCell (INF : ℤ) (ADJ W : List ℤ) (q : ℕ) : ℤ :=
  if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The memory μ after the first j diagonal cells of the matrix at A have become 0. -/
def zeroedDiag (μ : ℕ → ℤ) (A n j : ℕ) : ℕ → ℤ :=
  fun a => if ∃ i < j, a = A + i * (n + 1) then 0 else μ a

theorem zeroedDiag_zero {μ : ℕ → ℤ} {A n : ℕ} : zeroedDiag μ A n 0 = μ := by
  funext a
  simp [zeroedDiag]

/-- What round j of the second pass writes. -/
theorem zeroedDiag_succ {μ : ℕ → ℤ} {A n : ℕ} (j : ℕ) :
    Function.update (zeroedDiag μ A n j) (A + j * (n + 1)) 0 = zeroedDiag μ A n (j + 1) := by
  funext a
  simp only [zeroedDiag, Nat.exists_lt_succ_right, Function.update_apply]
  by_cases h : a = A + j * (n + 1) <;> simp [h]

/-- After both passes the weight matrix stands at A. -/
theorem seg_zeroedDiag_wrote {μ : ℕ → ℤ} {A n : ℕ} {INF : ℤ} {ADJ W : List ℤ} :
    Seg (zeroedDiag (wrote μ A (apInitCell INF ADJ W) (n * n)) A n n) A
      (weightList n INF ADJ W) := by
  intro q hq
  have : q < n * n := by simpa [weightList] using hq
  have hdiag : (∃ i < n, A + q = A + i * (n + 1)) ↔ q / n = q % n :=
    ⟨fun ⟨i, hi, h⟩ => by
      obtain ⟨h1, h2⟩ := (Nat.eq_mul_succ_iff hi).1 (Nat.add_left_cancel h)
      rw [h1, h2],
    fun h => ⟨q % n, Nat.mod_lt_of_lt_mul this, congrArg (A + ·)
      ((Nat.eq_mul_succ_iff (Nat.mod_lt_of_lt_mul this)).2 ⟨h, rfl⟩)⟩⟩
  simp only [zeroedDiag, hdiag, wrote_done this, weightList, List.getElem_map, List.getElem_range,
    apInitCell]

/-- Both passes change the n² cells of A only. -/
theorem sameOutside_zeroedDiag {μ μ' : ℕ → ℤ} {A n j : ℕ} (h : SameOutside μ μ' A (n * n))
    (hj : j ≤ n) : SameOutside μ (zeroedDiag μ' A n j) A (n * n) := by
  intro a ha
  have hno : ¬ ∃ i < j, a = A + i * (n + 1) := by
    rintro ⟨i, hi, rfl⟩
    have := Nat.mul_add_lt_mul (show i < n by omega) (show i < n by omega)
    rw [Nat.mul_succ] at ha
    simp only [Outside] at ha
    omega
  rw [zeroedDiag, if_neg hno]
  exact h a ha

/-- The invariant of the second pass of apInit before round j; μ is the memory after the first
pass. -/
def ApInitInv (μ : ℕ → ℤ) (n adj w A : ℕ) (INF : ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [n, INF, adj, w, A, j, (A + j * (n + 1) : ℕ)], zeroedDiag μ A n j⟩

/-- **One round of the first pass of apInit**, for the cells adj[j] = x and w[j] = y: the weight y
where there is an edge, and INF where there is none. -/
theorem apInitFill_spec {μ : ℕ → ℤ} {adj w A j : ℕ} {n INF nn x y : ℤ}
    (hx : μ (adj + j) = x) (hy : μ (w + j) = y) (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : adj + j < lim.space ∧ w + j < lim.space ∧ A + j < lim.space) :
    Ends lim P d apInitFill ⟨frame [n, INF, adj, w, A, j, nn], μ⟩ apInitFill.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, nn],
        Function.update μ (A + j) (if x = 1 then y else INF)⟩ := by
  unfold apInitFill
  -- if mem[AdjAt + Idx] = 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = 1 := by simpa [hx] using hc
    rw [if_pos hc']
    -- mem[Mat + Idx] := mem[WtsAt + Idx]
    light_store (A + j) y using hy
    rfl
  · have hc' : x ≠ 1 := by simpa [hx] using hc
    rw [if_neg hc']
    -- mem[Mat + Idx] := Big
    light_store (A + j) INF
    rfl

/-- **One round of the second pass of apInit**, for the address o of the diagonal cell.  The next
address o + n + 1 is computed also in the last round, so it has to fit. -/
theorem apInitDiag_spec {μ : ℕ → ℤ} {n o : ℕ} {INF adj w A j : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (ho : o + n + 1 ≤ lim.space) :
    Ends lim P d apInitDiag ⟨frame [n, INF, adj, w, A, j, o], μ⟩ apInitDiag.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, (o + (n + 1) : ℕ)], Function.update μ o 0⟩ := by
  unfold apInitDiag
  -- mem[Diag] := 0 ; Diag := Diag + Verts + 1
  light_store o 0
  light_set (o + (n + 1) : ℕ)
  rfl

/-- **apInit** writes the weight matrix to A, changes nothing else, and takes at most
23 n² + 17 n + 18 steps.  Only n² cells are written; the space 2 n² is asked for because after the
last round of the second pass the local Diag holds A + n (n + 1), which has to fit. -/
theorem apInit_meets {p : ℕ} (hp : P[p]? = some apInitBody) {μ : ℕ → ℤ} {n adj w A : ℕ} {INF : ℤ}
    {ADJ W : List ℤ} (hn : 1 ≤ n) (lenADJ : ADJ.length = n * n) (lenW : W.length = n * n)
    (segADJ : Seg μ adj ADJ) (segW : Seg μ w W) (hw : (lim.space : ℤ) ≤ lim.word)
    (hadj : adj + n * n ≤ lim.space) (hwt : w + n * n ≤ lim.space)
    (hA : A + 2 * (n * n) ≤ lim.space) (sepADJ : adj + n * n ≤ A ∨ A + n * n ≤ adj)
    (sepW : w + n * n ≤ A ∨ A + n * n ≤ w) :
    Meets lim P p d [n, INF, adj, w, A] μ (23 * (n * n) + 17 * n + 18) fun _ μ' =>
      Seg μ' A (weightList n INF ADJ W) ∧ SameOutside μ μ' A (n * n) := by
  refine .of_body hp ?_
  have : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have : (n : ℤ) * n ≤ lim.word := by exact_mod_cast (show ((n * n : ℕ) : ℤ) ≤ _ by omega)
  have : 0 ≤ (n : ℤ) * n := by positivity
  unfold apInitBody
  -- Cells := Verts * Verts
  light_set (n * n : ℕ)
  -- for Idx < Cells: the first pass
  refine Ends.next _ (Ends.forFrame (fun j μ' => μ' = wrote μ A (apInitCell INF ADJ W) j)
    (n * n) wrote_zero.symm ?round ?done (hT := le_rfl)) (by simp [apInitFill]; omega)
  case round =>
    rintro j _ hj rfl
    -- the cells adj[j] and w[j] are as at the start
    have hadjCell : wrote μ A (apInitCell INF ADJ W) j (adj + j) = ADJ.getD j 0 :=
      (wrote_rest (by omega)).trans (segADJ.getD (lenADJ ▸ hj) 0)
    have hwtCell : wrote μ A (apInitCell INF ADJ W) j (w + j) = W.getD j 0 :=
      (wrote_rest (by omega)).trans (segW.getD (lenW ▸ hj) 0)
    refine (apInitFill_spec hadjCell hwtCell hw (by omega)).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, wrote_succ⟩
  case done =>
    rintro _ rfl
    -- Diag := Mat
    refine Ends.setToThen A ?_ (hT := by simp [apInitFill]; omega)
    -- for Idx < Verts: the second pass
    refine Ends.for (ApInitInv (wrote μ A (apInitCell INF ADJ W) (n * n)) n adj w A INF) n
      apInitDiag.blockCost ?start ?round ?done ?bound (by omega)
      (by simp [apInitFill, apInitDiag]; omega)
    case start =>
      rw [ApInitInv, zeroedDiag_zero, Nat.zero_mul, Nat.add_zero]
      exact congrArg (State.mk · _) (update_frame_setLocal _ _ _)
    case round =>
      rintro j _ hj - rfl
      have hrow := Nat.mul_add_le_mul hj (le_refl (n + 1))
      rw [Nat.mul_succ n n] at hrow
      refine (apInitDiag_spec hw (by omega)).mono le_rfl ?_
      rintro _ rfl
      exact ⟨rfl, by rw [ApInitInv, update_frame_setLocal, Nat.cast_succ, zeroedDiag_succ,
        Nat.succ_mul, Nat.add_assoc]; rfl⟩
    case done =>
      rintro _ - rfl
      exact ⟨seg_zeroedDiag_wrote, sameOutside_zeroedDiag (sameOutside_wrote le_rfl) le_rfl⟩
    case bound =>
      rintro j _ - - rfl
      exact ⟨trivial, rfl⟩

/-! ## apOut -/

namespace ApOut

/-- The number of cells of A. -/
abbrev Len : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of A. -/
abbrev Mat : ℕ := 2
/-- The address of the output. -/
abbrev Out : ℕ := 3
/-- The counter q. -/
abbrev Idx : ℕ := 4
/-- The address out + 2q. -/
abbrev Pos : ℕ := 5

end ApOut

open ApOut in
/-- The two cells of the output for the cell A[q]. -/
def apOutWrite : Stmt :=
  .ite (M (v Mat +' v Idx) =' v Big)
    (.store (v Pos) (k 0) ;; .store (v Pos +' k 1) (k 0))
    (.store (v Pos) (k 1) ;; .store (v Pos +' k 1) (M (v Mat +' v Idx)))

open ApOut in
/-- The round of apOut for the cell A[q]. -/
def apOutRound : Stmt := apOutWrite ;; .set Pos (v Pos +' k 2)

open ApOut in
/-- apOut(len, INF, A, out): for q < len, the cells out[2q], out[2q + 1] become 0, 0 if A[q] = INF,
and 1, A[q] otherwise. -/
def apOutBody : Stmt := .set Pos (v Out) ;; .for Idx (v Len) apOutRound

/-- Cell number c of the output: cells 2q and 2q + 1 are 0, 0 if L[q] = INF, and 1, L[q]
otherwise. -/
def apOutCell (INF : ℤ) (L : List ℤ) (c : ℕ) : ℤ :=
  if L.getD (c / 2) 0 = INF then 0 else if c % 2 = 0 then 1 else L.getD (c / 2) 0

/-- What round q writes. -/
theorem wrote_apOutCell_succ {μ : ℕ → ℤ} {out : ℕ} {INF : ℤ} {L : List ℤ} (q : ℕ) :
    Function.update (Function.update (wrote μ out (apOutCell INF L) (2 * q)) (out + 2 * q)
      (if L.getD q 0 = INF then 0 else 1)) (out + 2 * q + 1)
      (if L.getD q 0 = INF then 0 else L.getD q 0) =
        wrote μ out (apOutCell INF L) (2 * (q + 1)) := by
  have heven : apOutCell INF L (2 * q) = if L.getD q 0 = INF then 0 else 1 := by
    simp only [apOutCell, Nat.mul_div_cancel_left q Nat.two_pos, Nat.mul_mod_right, if_true]
  have hodd : apOutCell INF L (2 * q + 1) = if L.getD q 0 = INF then 0 else L.getD q 0 := by
    simp only [apOutCell, show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega,
      one_ne_zero, if_false]
  rw [← heven, wrote_succ, Nat.add_assoc, ← hodd, wrote_succ]
  rfl

/-- The invariant of the loop of apOut before round j. -/
def ApOutInv (μ : ℕ → ℤ) (A out : ℕ) (INF : ℤ) (L : List ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩

/-- **The two stores of a round of apOut**, for the cell A[j] = x and the address o of the output.
-/
theorem apOutWrite_spec {μ : ℕ → ℤ} {A out o j : ℕ} {n INF x : ℤ} (hread : μ (A + j) = x)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : A + j < lim.space ∧ o + 1 < lim.space ∧ A + j ≠ o) :
    Ends lim P d apOutWrite ⟨frame [n, INF, A, out, j, o], μ⟩ apOutWrite.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, A, out, j, o], Function.update (Function.update μ o
        (if x = INF then 0 else 1)) (o + 1) (if x = INF then 0 else x)⟩ := by
  unfold apOutWrite
  -- if mem[Mat + Idx] = Big
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = INF := by simpa [hread] using hc
    rw [if_pos hc', if_pos hc']
    -- mem[Pos] := 0 ; mem[Pos + 1] := 0
    light_store o 0
    light_store (o + 1) 0
    rfl
  · have hc' : x ≠ INF := by simpa [hread] using hc
    rw [if_neg hc', if_neg hc']
    -- mem[Pos] := 1 ; mem[Pos + 1] := mem[Mat + Idx]
    light_store o 1
    light_store (o + 1) x using Function.update_of_ne hplace.2.2, hread
    rfl

/-- **One round of apOut** writes the pair for the cell A[j] and moves Pos on by two. -/
theorem apOutRound_spec {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ} {L : List ℤ} (hL : Seg μ A L)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : A + L.length ≤ lim.space)
    (hout : out + 2 * L.length ≤ lim.space) (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A)
    {j : ℕ} (hj : j < L.length) :
    Ends lim P d apOutRound
      ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩
      apOutRound.blockCost fun σ' =>
        σ' = ⟨frame [L.length, INF, A, out, j, (out + 2 * (j + 1) : ℕ)],
          wrote μ out (apOutCell INF L) (2 * (j + 1))⟩ := by
  have hread : wrote μ out (apOutCell INF L) (2 * j) (A + j) = L.getD j 0 :=
    (wrote_rest (by omega)).trans (hL.getD hj 0)
  rw [← wrote_apOutCell_succ]
  refine Ends.next _ ((apOutWrite_spec hread hw (by omega)).mono le_rfl ?_)
    (by simp [apOutRound])
  rintro _ rfl
  -- Pos := Pos + 2
  exact Ends.setTo (out + 2 * (j + 1) : ℕ) rfl (by light_side) (by simp [apOutRound])

/-- What apOut leaves from the address `out` on: for each number of the list `L` a pair of cells.
Its first cell holds 0 if the number is `INF`; otherwise the pair holds 1 and the number. -/
def PairsAt (μ' : ℕ → ℤ) (out : ℕ) (INF : ℤ) (L : List ℤ) : Prop :=
  ∀ i (hi : i < L.length), (L[i] = INF → μ' (out + 2 * i) = 0) ∧
    (L[i] ≠ INF → μ' (out + 2 * i) = 1 ∧ μ' (out + 2 * i + 1) = L[i])

/-- **apOut** writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. -/
theorem apOut_meets {p : ℕ} (hp : P[p]? = some apOutBody) {μ : ℕ → ℤ} {A out : ℕ} {INF : ℤ}
    {L : List ℤ} (hL : Seg μ A L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : A + L.length ≤ lim.space) (hout : out + 2 * L.length ≤ lim.space)
    (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A) :
    Meets lim P p d [L.length, INF, A, out] μ (30 * L.length + 8) fun _ μ' =>
      PairsAt μ' out INF L ∧ SameOutside μ μ' out (2 * L.length) := by
  refine .of_body hp ?_
  unfold apOutBody
  -- Pos := Out
  light_set out
  refine Ends.for (ApOutInv μ A out INF L) L.length apOutRound.blockCost ?start ?round ?done ?bound
    (by omega) (by simp [apOutRound, apOutWrite]; omega)
  case start =>
    rw [ApOutInv, wrote_zero]
    exact congrArg (State.mk · μ) (update_frame_setLocal _ _ _)
  case round =>
    rintro j _ hj - rfl
    refine (apOutRound_spec hL hw hA hout hsep hj).mono le_rfl ?_
    rintro _ rfl
    exact ⟨rfl, by rw [ApOutInv, update_frame_setLocal, Nat.cast_succ]; rfl⟩
  case done =>
    rintro _ - rfl
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    change (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 0) ∧
      (_ → wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i) = 1 ∧
        wrote μ out (apOutCell INF L) (2 * L.length) (out + 2 * i + 1) = L[i])
    rw [wrote_done (by omega), Nat.add_assoc, wrote_done (by omega), apOutCell, apOutCell,
      show 2 * i / 2 = i by omega, show (2 * i + 1) / 2 = i by omega,
      List.getD_eq_getElem _ _ hi]
    exact ⟨fun h => if_pos h, fun h => ⟨by simp [h], by simp [h]⟩⟩
  case bound =>
    rintro j _ - - rfl
    exact ⟨trivial, rfl⟩

end Light.Sec3
end

section
namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace ApspHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of the answer. -/
abbrev Out : ℕ := 4
/-- The free pointer, where the current matrix is kept. -/
abbrev Free : ℕ := 5
/-- n². -/
abbrev Cells : ℕ := 6
/-- nU. -/
abbrev Thresh : ℕ := 7
/-- 3nU, which stands for +∞. -/
abbrev Big : ℕ := 8
/-- fr + n², where the product is written. -/
abbrev ProdAt : ℕ := 10
/-- fr + 2n², the free pointer of the solver. -/
abbrev SolverFree : ℕ := 11
/-- The power of two that counts the rounds. -/
abbrev Power : ℕ := 12
/-- Takes the results of the calls. -/
abbrev Res : ℕ := 13

end ApspHost

open ApspHost in
/-- One round: the product of the matrix with itself, clipped and copied back. -/
def apRound (pMP pClip : ℕ) : Stmt :=
  .call pMP [v Verts, v Big, v Free, v Free, v ProdAt, v SolverFree] Res ;;
  .call pClip [v Cells, v Thresh, v Big, v ProdAt, v Free] Res ;;
  .set Power (v Power +' v Power)

open ApspHost in
/-- ap(n, U, adj, w, out, fr), over the procedures number pMP (a solver of the (min,+)-product),
pInit, pClip and pOut (the three passes). -/
def apBody (pMP pInit pClip pOut : ℕ) : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .set Thresh (v Verts *' v Bound) ;;
  .set Big (k 3 *' v Thresh) ;;
  .set ProdAt (v Free +' v Cells) ;;
  .set SolverFree (v ProdAt +' v Cells) ;;
  .call pInit [v Verts, v Big, v AdjAt, v WtsAt, v Free] Res ;;
  .set Power (k 1) ;;
  .while (v Power <' v Verts) (apRound pMP pClip) ;;
  .call pOut [v Cells, v Big, v Free, v Out] Res

/-- The time of the host, given the time of the solver: `⌈log₂ n⌉` products at the bound `3nU`, and
`O(n²)` steps for each product and at both ends. -/
def apTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  Nat.clog 2 n * (T n (3 * (n * U)) + 23 * (n * n) + 29) + 53 * (n * n) + 17 * n + 65

/-- The need of the host, given the need of the solver. -/
def apNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := max (r n (3 * (n * U))).word (3 * (n * U))
  cells := 2 * (n * n) + (r n (3 * (n * U))).cells
  depth := (r n (3 * (n * U))).depth + 1

namespace ApspHost

/-- The locals of the host during the loop; pw is the power of two that counts the rounds, res the
result of the last call.  Local 9 is not used and stays 0. -/
abbrev locals (x : GraphInst) (fr : ℕ) (pw res : ℤ) : List ℤ :=
  [x.n, x.U, x.adj, x.w, x.out, fr, (x.n * x.n : ℕ), (x.n * x.U : ℕ), 3 * (x.n * x.U : ℕ), 0,
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), pw, res]

/-- The invariant of the loop before round t: the matrix after t squarings stands at the free
pointer, and nothing below it has changed. -/
def Inv (x : GraphInst) (μ : ℕ → ℤ) (fr t : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals x fr (2 ^ t : ℕ) res), μ'⟩ ∧
    Seg μ' fr (squareList x.n x.U x.ADJ x.W t) ∧ Kept μ μ' fr

/-- The program has the solver and the three passes, the instance is as the task prescribes, and the
limits allow for the need of the host. -/
structure Ctx (P₀ R₀ : Program) (pMP pInit pClip pOut : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves mpTask P₀ pMP T r
  init : (P₀ ++ R₀)[pInit]? = some apInitBody
  clip : (P₀ ++ R₀)[pClip]? = some clipBody
  out : (P₀ ++ R₀)[pOut]? = some apOutBody
  pre : x.Pre μ fr
  ok : (apNeed r x.n x.U).Ok lim fr d

variable {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The arithmetic facts of the hypotheses as one conjunction: what the limits allow and what the
instance satisfies. -/
theorem Ctx.places (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 3 * ((x.n : ℤ) * x.U) ≤ lim.word ∧
      ((r x.n (3 * (x.n * x.U))).word : ℤ) ≤ lim.word ∧
      fr + (2 * (x.n * x.n) + (r x.n (3 * (x.n * x.U))).cells) ≤ lim.space ∧
      d + ((r x.n (3 * (x.n * x.U))).depth + 1) ≤ lim.depth) ∧
      x.n ≤ x.n * x.n ∧ 1 ≤ x.n * x.U ∧ x.adj + x.n * x.n ≤ fr ∧ x.w + x.n * x.n ≤ fr ∧
      x.out + 2 * (x.n * x.n) ≤ fr :=
  ⟨⟨C.ok.space, by exact_mod_cast le_trans (Nat.cast_le.2 (le_max_right _ _)) C.ok.word,
    le_trans (by exact_mod_cast le_max_left _ _) C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.le_mul_of_pos_left _ C.pre.n_pos, Nat.mul_pos C.pre.n_pos C.pre.U_pos, C.pre.belowADJ,
    C.pre.belowW, C.pre.belowOut⟩

/-- The pairs that apOut writes for the matrix after ⌈log₂ n⌉ squarings are the answer. -/
theorem answer_correct (hpre : x.Pre μ fr) {μ' : ℕ → ℤ}
    (hans : PairsAt μ' x.out (3 * (x.n * x.U : ℕ))
      (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n))) :
    ∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
      ∀ i j : Fin x.n, (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
        ∀ z : ℤ, dist i j = (z : WithTop ℤ) → μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z := by
  obtain ⟨dist, hdist, hentries⟩ :=
    squareList_distances hpre.n_pos hpre.U_pos hpre.leW hpre.noNegativeCycle
  refine ⟨dist, hdist, fun i j => ?_⟩
  have hq : i.val * x.n + j.val < (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length := by
    rw [length_squareList]
    exact Nat.mul_add_lt_mul i.isLt j.isLt
  obtain ⟨htop, hfin⟩ := hentries i j
  rw [entry, List.getD_eq_getElem _ _ hq] at htop hfin
  obtain ⟨hzero, hone⟩ := hans _ hq
  refine ⟨fun h => hzero (htop h), fun z hz => ?_⟩
  obtain ⟨hval, hne⟩ := hfin z hz
  exact hval ▸ hone (hval ▸ hne)

/-- **One round of the host** squares the matrix at the free pointer: a (min,+)-product, the
clipping of the large entries, and the doubling of Power. -/
theorem round_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {t : ℕ}
    (ht : 2 ^ t < x.n) {σ : State} (hσ : Inv x μ fr t σ) :
    Ends lim (P₀ ++ R₀) d (apRound pMP pClip) σ (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
      (Inv x μ fr (t + 1)) := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have := C.places
  have hw := C.ok.space
  set L := squareList x.n x.U x.ADJ x.W t
  have hlen : L.length = x.n * x.n := length_squareList _ _ _ _ _
  have hlenP : (minPlusList x.n L L).length = x.n * x.n := length_minPlusList _ _ _
  have hle : AbsLe L ((3 * (x.n * x.U) : ℕ) : ℤ) :=
    abs_squareList_le C.pre.n_pos C.pre.U_pos C.pre.leW C.pre.noNegativeCycle t
  unfold apRound
  -- Res := pMP(Verts, Big, Free, Free, ProdAt, SolverFree)
  refine Ends.callToThen (C.solver.meets R₀
    (⟨x.n, 3 * (x.n * x.U), fr, fr, fr + x.n * x.n, L, L⟩ : MatInst) (fr + 2 * (x.n * x.n))
    ⟨C.pre.n_pos, by simp only; omega, hlen, hlen, hseg, hseg, hle, hle, by simp only; omega,
      by simp only; omega, by simp only; omega, Or.inl le_rfl, Or.inl le_rfl⟩
    { word := by simp only [mpTask]; omega
      cells := by simp only [mpTask]; omega
      space := hw
      depth := by simp only [mpTask]; omega }) ?_ (by simp [mpTask]) (by omega)
        (by simp [mpTask]; omega)
  rintro r₁ μ₁ ⟨hprod, hkept₁⟩
  simp only at hprod hkept₁
  -- Res := pClip(Cells, Thresh, Big, ProdAt, Free)
  refine Ends.callToThen (clip_meets C.clip (thr := (x.n * x.U : ℕ)) (INF := 3 * (x.n * x.U : ℕ))
    (dst := fr) hprod hw (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlenP])
    (by omega) (by simp [mpTask, hlenP]; omega)
  rintro r₂ μ₂ ⟨hseg₂, hsame₂⟩
  rw [hlenP] at hsame₂
  -- Power := Power + Power
  refine Ends.setTo (2 ^ (t + 1) : ℕ) ⟨r₂, μ₂, rfl, hseg₂, fun a ha => ?_⟩ ?_
    (by simp [mpTask, hlenP]; omega)
  · light_keep
  · have hpow : (2 : ℤ) ^ t < x.n := by exact_mod_cast ht
    have : (0 : ℤ) ≤ 2 ^ t := by positivity
    simp [abs_le, pow_succ]
    omega

/-- **The end of the host**: the answer is written. -/
theorem out_spec (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) {σ : State}
    (hσ : Inv x μ fr (Nat.clog 2 x.n) σ) :
    Ends lim (P₀ ++ R₀) d (.call pOut [v Cells, v Big, v Free, v Out] Res) σ (30 * (x.n * x.n) + 14)
      fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  obtain ⟨res, μ', rfl, hseg, hkept⟩ := hσ
  have := C.places
  have hw := C.ok.space
  have hlen : (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length = x.n * x.n :=
    length_squareList _ _ _ _ _
  -- Res := pOut(Cells, Big, Free, Out)
  refine Ends.callTo (apOut_meets C.out (INF := 3 * (x.n * x.U : ℕ)) (out := x.out) hseg hw
    (by omega) (by omega) (Or.inr (by omega))) ?_ (by simp [hlen]) (hT := by rw [hlen]; light_time)
  rintro r₂ μ₂ ⟨hans, hsame₂⟩
  rw [hlen] at hsame₂
  exact ⟨answer_correct C.pre hans, fun a ⟨ha, hout⟩ => (hsame₂ a hout).trans (hkept a ha)⟩

end ApspHost

open ApspHost in
/-- **The host is correct**, in every program that begins with the solver's program and has the
three passes. -/
theorem ap_spec {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}
    (C : Ctx P₀ R₀ pMP pInit pClip pOut T r lim d x μ fr) :
    Ends lim (P₀ ++ R₀) d (apBody pMP pInit pClip pOut) ⟨frame (apTask.args x ++ [(fr : ℤ)]), μ⟩
      (apTime T x.n x.U) fun σ' => apTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have := C.places
  have hw := C.ok.space
  have hpre := C.pre
  have : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  have : (0 : ℤ) ≤ (x.n : ℤ) * x.U := by positivity
  unfold apBody apTime
  change Ends _ _ _ _ ⟨frame [(x.n : ℤ), x.U, x.adj, x.w, x.out, fr], μ⟩ _ _
  -- Cells := Verts * Verts ; Thresh := Verts * Bound ; Big := 3 * Thresh
  light_set (x.n * x.n : ℕ)
  light_set (x.n * x.U : ℕ)
  light_set (3 * (x.n * x.U : ℕ))
  -- ProdAt := Free + Cells ; SolverFree := ProdAt + Cells
  light_set (fr + x.n * x.n : ℕ)
  light_set (fr + 2 * (x.n * x.n) : ℕ)
  -- Res := pInit(Verts, Big, AdjAt, WtsAt, Free)
  light_call (apInit_meets C.init (INF := 3 * (x.n * x.U : ℕ)) (A := fr) hpre.n_pos
    hpre.lenADJ hpre.lenW hpre.segADJ hpre.segW hw (by omega) (by omega) (by omega)
    (Or.inl hpre.belowADJ) (Or.inl hpre.belowW)) with r₁ μ₁ ⟨hseg₁, hsame₁⟩
  -- Power := 1
  light_set (2 ^ 0 : ℕ)
  -- while Power < Verts: the rounds
  refine Ends.next _ (Ends.whileConst (Inv x μ fr) (Nat.clog 2 x.n)
    (T x.n (3 * (x.n * x.U)) + 23 * (x.n * x.n) + 25)
    ⟨r₁, μ₁, rfl, hseg₁, fun a ha => hsame₁ a (Or.inl ha)⟩ ?round ?done le_rfl)
  case round =>
    rintro t σ ht hσ
    have hpow : 2 ^ t < x.n := Nat.pow_lt_of_lt_clog ht
    refine ⟨?_, ?_, round_spec C hpow hσ⟩ <;> obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((2 : ℤ) ^ t < x.n))
  case done =>
    intro σ hσ
    have hpow : x.n ≤ 2 ^ Nat.clog 2 x.n := Nat.le_pow_clog (by norm_num) x.n
    refine ⟨?_, ?_, (out_spec C hσ).mono (by light_time) fun _ h => h⟩ <;>
      obtain ⟨res, μ', rfl, -, -⟩ := hσ
    · exact ⟨trivial, trivial⟩
    · simpa using (by exact_mod_cast hpow : ((x.n : ℤ) ≤ 2 ^ Nat.clog 2 x.n))

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_apNeed {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (apNeed r) := by
  unfold apNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **APSP from the (min,+)-product**, as a host. -/
theorem isHost_ap : IsHost mpTask apTask apTime apNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => polyNeed_apNeed hr⟩
  refine ⟨[apInitBody, clipBody, apOutBody, apBody p P.length (P.length + 1) (P.length + 2)],
    P.length + 3, apBody p P.length (P.length + 1) (P.length + 2), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact ap_spec ⟨hs, by simp, by simp, by simp, hpre, hok⟩

end Light.Sec3
end
