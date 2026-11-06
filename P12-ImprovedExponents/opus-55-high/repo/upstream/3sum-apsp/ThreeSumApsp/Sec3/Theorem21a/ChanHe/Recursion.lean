/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Collisions

/-!
# Theorem 21(a), the reduction of Chan and He: one node, and the recursion for three sets

This file proves that the reduction for three sets, `reduction n U`, is correct and makes
polylogarithmically many instances.  It follows the proof of [CH20, Theorem 5.1], one of the
reductions behind Theorem 21(a).  A node of the recursion tree consists of three sets and a
modulus `M`.

* One node.  The elements that are alone in their residue class modulo `M` are called light.  The
  first two arrays hold each light element of the first two sets at the index of its remainder.  The
  third array holds `-c`, for each light element `c` of the third set, at the remainder of `-c` and
  once more `M` cells further on.  All other cells hold padding.  Padding is too large to take part
  in a solution, and `a + b + c = 0` makes the remainders of `a` and `b` add up to that of `-c`, or
  to that plus `M`.  So the Convolution-3SUM instance of the node has a solution iff the light
  elements of the three sets have a 3SUM solution (`node_correct`).
* The recursion.  A 3SUM solution consists of three light elements, or one of its elements is heavy
  (`hasSol_split`).  The three children of a node replace one set each by its heavy elements.
* The depth.  A set that has been replaced `j` times has at most `n / d_j` elements, where `d₀ = 1`
  and `d_{j+1} = 2 d_j²` (`Replaced.heavy`).  Since `d_j > n` for `j = height n` (`lt_dSeq_height`),
  it is then empty (`Replaced.eq_empty`), so no node lies below the `fuel n` levels of the tree that
  are built.  This gives `nodes_correct`, by induction on the number of levels, and
  `reduction_correct`, whose hypotheses on the three sets are collected in `Admissible`.
* The size.  A ternary tree with `fuel n` levels has at most `3 ^ fuel n ≤ (2⌊log₂ n⌋ + 2)⁵` nodes
  (`length_reduction_le`).  The entries of the arrays are bounded in `abs_arrXY_le` and
  `abs_arrZ_le`, and the count for the searches of one node in `scan_node_le`.
-/


namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## Light elements and the cells of the arrays -/

section cells

variable {S : Finset ℤ} {M U : ℕ}

/-- The elements of `S` that are alone in their residue class modulo `M`.  They play the role of
the good elements of [CH20]. -/
def light (S : Finset ℤ) (M : ℕ) : Finset ℤ := S \ heavy S M

variable {x : ℤ}

/-- An element is light iff it collides with no other element. -/
theorem mem_light : x ∈ light S M ↔ x ∈ S ∧ ∀ y ∈ S, y ≠ x → ¬ (M : ℤ) ∣ x - y := by
  grind [light, heavy]

/-- Light elements are elements. -/
theorem light_subset (S : Finset ℤ) (M : ℕ) : light S M ⊆ S := sdiff_subset

/-- Heavy elements are elements. -/
theorem heavy_subset (S : Finset ℤ) (M : ℕ) : heavy S M ⊆ S := filter_subset _ _

/-- A subset of a bounded set is bounded. -/
theorem Bdd.mono {S T : Finset ℤ} (h : Bdd U S) (hT : T ⊆ S) : Bdd U T := by tauto

/-- The bucket of a light element contains nothing else. -/
theorem bucket_of_light (hx : x ∈ light S M) : bucket S M (x % (M : ℤ)) = {x} := by
  obtain ⟨hxS, halone⟩ := mem_light.mp hx
  refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨hxS, rfl⟩, fun y hy => ?_⟩
  obtain ⟨hyS, hmod⟩ := mem_filter.mp hy
  grind [natCast_dvd_sub_iff_emod_eq]

/-- A light element sits in the cell of its remainder. -/
theorem arr_of_light (hx : x ∈ light S M) (pd : ℤ) {i : ℕ}
    (hi : (i : ℤ) = x % (M : ℤ)) : arr S M pd i = x := by
  rw [arr, hi, bucket_of_light hx, card_singleton, if_pos rfl, sum_singleton]

/-- A cell of the array holds a light element or padding. -/
theorem arr_mem_light_or_eq (S : Finset ℤ) (M : ℕ) (pd : ℤ) (i : ℕ) :
    arr S M pd i ∈ light S M ∨ arr S M pd i = pd := by
  unfold arr
  split_ifs with h
  · left
    obtain ⟨x, hx⟩ := card_eq_one.mp h
    have hmem : ∀ y, y ∈ bucket S M i ↔ y = x := by simp_all
    obtain ⟨hxS, hxi⟩ := mem_filter.mp ((hmem x).mpr rfl)
    rw [hx, sum_singleton]
    refine mem_light.mpr ⟨hxS, fun y hy hne hd => hne ((hmem y).mp (mem_filter.mpr ⟨hy, ?_⟩))⟩
    grind [natCast_dvd_sub_iff_emod_eq]
  omega

/-- Negation preserves lightness. -/
theorem neg_mem_light_neg (S : Finset ℤ) (M : ℕ) (c : ℤ) :
    -c ∈ light (S.image fun c => -c) M ↔ c ∈ light S M := by
  simp only [mem_light, mem_image, neg_inj, exists_eq_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ne_eq, ← neg_sub', dvd_neg]

/-- A cell of the first or second array holds a light element or `pad U`. -/
theorem arrXY_cases (M : ℕ) (h : Bdd U S) (i : ℕ) :
    (arrXY S M U i ∈ light S M ∧ |arrXY S M U i| ≤ U) ∨ arrXY S M U i = pad U :=
  (arr_mem_light_or_eq S M _ i).imp_left fun hx => ⟨hx, h _ (light_subset S M hx)⟩

/-- A cell of the third array holds `-c` for a light element `c`, or `-pad U`. -/
theorem arrZ_cases (M : ℕ) (h : Bdd U S) (k : ℕ) :
    (∃ c ∈ light S M, |c| ≤ U ∧ arrZ S M U k = -c) ∨ arrZ S M U k = -pad U := by
  unfold arrZ
  split_ifs with hk
  · refine (arr_mem_light_or_eq _ M _ _).imp_left fun hx => ?_
    rw [← neg_neg (arr _ _ _ _), neg_mem_light_neg] at hx
    exact ⟨_, hx, h _ (light_subset S M hx), by omega⟩
  omega

/-- For a light element `c`, the third array holds `-c` in the two cells below `2M` whose index is
congruent to `-c`. -/
theorem arrZ_of_light {c : ℤ} (hc : c ∈ light S M) (U : ℕ) {k : ℕ} (hk : k < 2 * M)
    (hkc : ((k % M : ℕ) : ℤ) = -c % (M : ℤ)) : arrZ S M U k = -c := by
  rw [arrZ, if_pos hk]
  exact arr_of_light (by grind [neg_mem_light_neg]) _ hkc


/-- The entries of the array made from the first or the second set of a node have absolute value at
most `2U + 1`. -/
theorem abs_arrXY_le (M : ℕ) (h : Bdd U S) (i : ℕ) : |arrXY S M U i| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrXY_cases M h i with ⟨-, hb⟩ | he
  · omega
  aesop

/-- The entries of the third array of a node have absolute value at most `2U + 1`. -/
theorem abs_arrZ_le (M : ℕ) (h : Bdd U S) (k : ℕ) : |arrZ S M U k| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrZ_cases M h k with ⟨c, -, hb, he⟩ | he
  · grind
  aesop

end cells

variable {N : ℕ} {S₂ S₁ S₃ : Finset ℤ}

/-! ## One node -/

/-- **Correctness of one node.**  Its Convolution-3SUM instance, read at any length `N ≥ 2M`, has a
solution iff the light elements of the three sets have a 3SUM solution. -/
theorem node_correct {U M : ℕ} (hM : 1 ≤ M) (hN : 2 * M ≤ N)
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    ConvSol N (arrXY S₁ M U) (arrXY S₂ M U) (arrZ S₃ M U) ↔
      HasSol (light S₁ M) (light S₂ M) (light S₃ M) := by
  constructor
  · rintro ⟨i, j, -, heq⟩
    rcases arrXY_cases M h₁ i with ⟨ha, ha'⟩ | ha <;>
      rcases arrXY_cases M h₂ j with ⟨hb, hb'⟩ | hb <;>
      rcases arrZ_cases M h₃ (i + j) with ⟨c, hc, hc', hz⟩ | hz
    · exact ⟨_, ha, _, hb, c, hc, by omega⟩
    -- in all other cases a cell holds `±(2U + 1)`, which the other two cells cannot balance
    all_goals
      grind [pad]
  · rintro ⟨a, ha, b, hb, c, hc, hsum⟩
    have hM0 : (M : ℤ) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hM0)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hM0)
    have hiM := a.emod_lt_of_pos (by omega : (0 : ℤ) < M)
    have hjM := b.emod_lt_of_pos (by omega : (0 : ℤ) < M)
    have hij : (i + j) % M = -c % M := by
      rw [← hi, ← hj]
      grind
    refine ⟨i, j, by omega, ?_⟩
    rw [arrXY, arr_of_light ha _ hi.symm, arrXY, arr_of_light hb _ hj.symm,
      arrZ_of_light hc U (by omega) hij]
    omega

/-! ## The sizes of the sets along the recursion -/

/-- The sequence `d₀ = 1`, `d_{j+1} = 2 d_j²` of [CH20], in closed form. -/
def dSeq (j : ℕ) : ℕ := 2 ^ (2 ^ j - 1)

/-- The recurrence `d_{j+1} = 2 d_j²`. -/
theorem dSeq_succ (j : ℕ) : dSeq (j + 1) = 2 * dSeq j ^ 2 := by
  have hexp : 2 ^ (j + 1) - 1 = 1 + (2 ^ j - 1) * 2 := by
    grind
  simp_all [dSeq, pow_add, pow_mul, pow_one]

/-- The sequence `dSeq` is nondecreasing. -/
theorem dSeq_mono {i j : ℕ} (h : i ≤ j) : dSeq i ≤ dSeq j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (by simp_all [Nat.pow_le_pow_right]) 1)

/-- `d_h > n` at `h = height n`. -/
theorem lt_dSeq_height (n : ℕ) : n < dSeq (height n) := by
  have hclog : Nat.log 2 n + 2 ≤ 2 ^ height n := Nat.le_pow_clog (by norm_num) _
  calc n < 2 ^ (Nat.log 2 n + 1) := by grind [Nat.lt_pow_succ_log_self]
    _ ≤ dSeq _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `height n` is at least 1, so the subtraction in `fuel` does not truncate. -/
theorem height_pos (n : ℕ) : 1 ≤ height n :=
  Nat.clog_pos (by norm_num) (by omega)

/-- `2^(height n) ≤ 2⌊log₂ n⌋ + 2`. -/
theorem two_pow_height_le (n : ℕ) : 2 ^ height n ≤ 2 * Nat.log 2 n + 2 := by
  have hlt : 2 ^ (height n - 1) < Nat.log 2 n + 2 :=
    Nat.pow_pred_clog_lt_self (x := Nat.log 2 n + 2) (by norm_num) (by omega)
  rw [← Nat.sub_add_cancel (height_pos n)]
  omega

/-- What is known about a set `T` that has been replaced `j` times by its heavy elements: its
elements have absolute value at most `U`, and there are at most `n / d_j` of them. -/
structure Replaced (n U j : ℕ) (T : Finset ℤ) : Prop where
  /-- The elements have absolute value at most `U`. -/
  bdd : Bdd U T
  /-- There are at most `n / d_j` elements. -/
  card : #T * dSeq j ≤ n

namespace Replaced

variable {n U j : ℕ} {T : Finset ℤ}

/-- At the root no set has been replaced. -/
theorem zero (hb : Bdd U T) (hc : #T ≤ n) : Replaced n U 0 T :=
  ⟨hb, by grind [dSeq]⟩

/-- One more replacement: if at most `|T|²/(2n)` elements of `T` are heavy, then these are at most
`n / d_{j+1}`. -/
theorem heavy (h : Replaced n U j T) (hn : 1 ≤ n) {M : ℕ}
    (hM : 2 * n * #(ChanHe.heavy T M) ≤ #T ^ 2) : Replaced n U (j + 1) (ChanHe.heavy T M) := by
  refine ⟨h.bdd.mono (heavy_subset T M), Nat.le_of_mul_le_mul_left ?_ hn⟩
  calc n * (#(ChanHe.heavy T M) * dSeq _)
      = 2 * n * #(ChanHe.heavy T M) * dSeq j ^ 2 := by grind [dSeq_succ]
    _ ≤ #T ^ 2 * dSeq j ^ 2 := Nat.mul_le_mul_right _ hM
    _ = #T * dSeq j * (#T * dSeq j) := by ring
    _ ≤ n * n := Nat.mul_le_mul h.card h.card

/-- After `height n` replacements a set is empty. -/
theorem eq_empty (h : Replaced n U j T) (hj : height n ≤ j) : T = ∅ := by
  by_contra hne
  have hcard : 1 ≤ #T := by grind
  -- `n < d_{height n} ≤ d_j ≤ |T| d_j ≤ n`
  have := lt_dSeq_height n
  have := dSeq_mono hj
  have := Nat.mul_le_mul_right (dSeq j) hcard
  have := h.card
  omega

end Replaced

variable {j₃ j₂ j₁ : ℕ} {T₁ T₂ T₃ : Finset ℤ}

/-- After `3 (height n) - 2` replacements in all, one of the three sets is empty. -/
theorem exists_eq_empty {n U : ℕ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃) (hj : 3 * height n - 2 ≤ j₁ + j₂ + j₃) :
    T₁ = ∅ ∨ T₂ = ∅ ∨ T₃ = ∅ := by
  rcases (by omega : height n ≤ j₁ ∨ height n ≤ j₂ ∨ height n ≤ j₃) with h | h | h
  · exact .inl (r₁.eq_empty h)
  · exact .inr (.inl (r₂.eq_empty h))
  · exact .inr (.inr (r₃.eq_empty h))

/-! ## The recursion tree -/

/-- A solution stays a solution when the sets grow. -/
theorem HasSol.mono (h : HasSol S₁ S₂ S₃) (h₁ : S₁ ⊆ T₁)
    (h₂ : S₂ ⊆ T₂) (h₃ : S₃ ⊆ T₃) : HasSol T₁ T₂ T₃ :=
  let ⟨a, ha, b, hb, c, hc, hs⟩ := h
  ⟨a, h₁ ha, b, h₂ hb, c, h₃ hc, hs⟩

/-- If one of the three sets is empty there is no solution. -/
theorem not_hasSol_of_empty (h : S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅) :
    ¬ HasSol S₁ S₂ S₃ := by
  rintro ⟨a, ha, b, hb, c, hc, -⟩
  grind

/-- A solution consists of three light elements, or it contains a heavy one.  The brackets are those
of the list of the children in `nodes`. -/
theorem hasSol_split (S₁ S₂ S₃ : Finset ℤ) (M : ℕ) :
    HasSol S₁ S₂ S₃ ↔ HasSol (light S₁ M) (light S₂ M) (light S₃ M) ∨
      (HasSol (heavy S₁ M) S₂ S₃ ∨ HasSol S₁ (heavy S₂ M) S₃) ∨ HasSol S₁ S₂ (heavy S₃ M) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hs⟩
    by_contra hno
    simp [not_or] at hno
    obtain ⟨hlight, ⟨hheavy₁, hheavy₂⟩, hheavy₃⟩ := hno
    exact hlight ⟨a, mem_sdiff.mpr ⟨ha, fun h => hheavy₁ ⟨a, h, b, hb, c, hc, hs⟩⟩,
      b, mem_sdiff.mpr ⟨hb, fun h => hheavy₂ ⟨a, ha, b, h, c, hc, hs⟩⟩,
      c, mem_sdiff.mpr ⟨hc, fun h => hheavy₃ ⟨a, ha, b, hb, c, h, hs⟩⟩, hs⟩
  · rintro (h | (h | h) | h)
    · exact h.mono (light_subset _ _) (light_subset _ _) (light_subset _ _)
    · exact h.mono (heavy_subset _ _) Subset.rfl Subset.rfl
    · exact h.mono Subset.rfl (heavy_subset _ _) Subset.rfl
    · exact h.mono Subset.rfl Subset.rfl (heavy_subset _ _)

variable (Q : Finset ℕ) (Λ f : ℕ)

/-- The first `f` levels of the tree have at most `(3^f - 1)/2` nodes. -/
theorem length_nodes_le (S₁ S₂ S₃ : Finset ℤ) :
    2 * (nodes Q Λ f S₁ S₂ S₃).length + 1 ≤ 3 ^ f := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => rfl
  | succ f ih =>
    unfold nodes
    grind

/-- The sets of a node are subsets of the sets at the root. -/
theorem nodes_subset (S₁ S₂ S₃ : Finset ℤ) :
    ∀ ν ∈ nodes Q Λ f S₁ S₂ S₃, ν.S₁ ⊆ S₁ ∧ ν.S₂ ⊆ S₂ ∧ ν.S₃ ⊆ S₃ := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => tauto
  | succ f ih =>
    grind [nodes, heavy_subset]

/-- The hypotheses on the set `Q` of candidates for the two searches: primes, all at most `m`, and
enough of them for `card_heavy_modulus_le`. -/
structure Candidates (n U m : ℕ) (Q : Finset ℕ) : Prop where
  /-- The candidates are primes. -/
  prime : ∀ p ∈ Q, p.Prime
  /-- The candidates are at most `m`. -/
  le : ∀ p ∈ Q, p ≤ m
  /-- There are at least `√(18n) Λ` candidates. -/
  card : 18 * Lam U ^ 2 * n ≤ #Q ^ 2

/-- The primes up to `mPar n U`, among which `reduction n U` searches, meet the hypotheses. -/
theorem candidates_primesLE (n U : ℕ) :
    Candidates n U (mPar n U) (Nat.primesLE (mPar n U)) :=
  ⟨fun _ => Nat.prime_of_mem_primesLE, fun _ => Nat.le_of_mem_primesLE,
    le_card_primesLE_mPar_sq n U⟩

/-- The induction behind `reduction_correct`.  If the `i`-th set has been replaced `j_i` times, then
`f` levels of the tree are enough as soon as `f + j₁ + j₂ + j₃ ≥ 3 (height n) - 2`. -/
theorem nodes_correct {n U m : ℕ} (hn : 1 ≤ n) {Q : Finset ℕ} (hQ : Candidates n U m Q)
    (hN : 2 * m ^ 2 ≤ N) (f : ℕ) (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃)
    (hf : 3 * height n - 2 ≤ f + j₁ + j₂ + j₃) :
    HasSol T₁ T₂ T₃ ↔ ∃ ν ∈ nodes Q (Lam U) f T₁ T₂ T₃, ν.Conv U N := by
  induction f generalizing T₁ T₂ T₃ j₁ j₂ j₃ with
  | zero => grind [nodes, not_hasSol_of_empty, exists_eq_empty]
  | succ f ih =>
    unfold nodes
    split_ifs with he
    · grind [not_hasSol_of_empty]
    obtain ⟨hM1, hMm⟩ := modulus_bounds (nonempty_of_le_card_sq hQ.card hn) hQ.prime hQ.le
      r₁.bdd r₂.bdd r₃.bdd
    have hheavy := card_heavy_modulus_le hQ.prime hQ.card hn r₁.bdd r₂.bdd r₃.bdd
    rw [hasSol_split T₁ T₂, ← node_correct (N := N) hM1 (by omega) r₁.bdd r₂.bdd r₃.bdd, ih (r₁.heavy hn (by tauto)) r₂ r₃ (by omega), ih r₁ (r₂.heavy hn (by tauto)) r₃ (by omega), ih r₁ r₂ (r₃.heavy hn (by tauto)) (by omega)]
    simp only [List.mem_cons, List.mem_append, or_and_right, exists_or, exists_eq_left]
    -- `Node.Conv` of the new node is by definition the instance of `node_correct`
    rfl

/-! ## The reduction for three sets -/

/-- The hypotheses on an input of `reduction n U`: each of the three sets has at most `n` elements,
all of absolute value at most `U`. -/
structure Admissible (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop where
  /-- The first set has at most `n` elements. -/
  card₁ : #S₁ ≤ n
  /-- The second set has at most `n` elements. -/
  card₂ : #S₂ ≤ n
  /-- The third set has at most `n` elements. -/
  card₃ : #S₃ ≤ n
  /-- The elements of the first set have absolute value at most `U`. -/
  bdd₁ : Bdd U S₁
  /-- The elements of the second set have absolute value at most `U`. -/
  bdd₂ : Bdd U S₂
  /-- The elements of the third set have absolute value at most `U`. -/
  bdd₃ : Bdd U S₃

/-- The sets of a node satisfy the hypotheses that the sets at the root satisfy. -/
theorem Admissible.of_mem {n U : ℕ} (h : Admissible n U S₁ S₂ S₃) {ν : Node}
    (hν : ν ∈ reduction n U S₁ S₂ S₃) : Admissible n U ν.S₁ ν.S₂ ν.S₃ :=
  let ⟨s₁, s₂, s₃⟩ := nodes_subset _ _ _ _ _ _ ν hν
  ⟨(card_le_card s₁).trans h.card₁, (card_le_card s₂).trans h.card₂,
    (card_le_card s₃).trans h.card₃, h.bdd₁.mono s₁, h.bdd₂.mono s₂, h.bdd₃.mono s₃⟩

/-- **Correctness of the reduction for three sets.**  Let the three sets have at most `n ≥ 1`
elements each, all of absolute value at most `U`, and let `N ≥ 2 * mPar n U ^ 2`.  Then 3SUM has a
solution iff the Convolution-3SUM instance of some node has one at length `N`. -/
theorem reduction_correct {n U : ℕ} (hn : 1 ≤ n) (hN : 2 * mPar n U ^ 2 ≤ N)
    (h : Admissible n U S₁ S₂ S₃) :
    HasSol S₁ S₂ S₃ ↔ ∃ ν ∈ reduction n U S₁ S₂ S₃, ν.Conv U N :=
  nodes_correct hn (candidates_primesLE n U) hN _ (.zero h.bdd₁ h.card₁)
    (.zero h.bdd₂ h.card₂) (.zero h.bdd₃ h.card₃) le_rfl

/-- A ternary tree with `fuel n` levels has polylogarithmically many nodes. -/
theorem three_pow_fuel_le (n : ℕ) : 3 ^ fuel n ≤ (2 * Nat.log 2 n + 2) ^ 5 :=
  calc 3 ^ fuel n ≤ 3 ^ (3 * height n) := Nat.pow_le_pow_right (by norm_num) (by tauto)
    _ = 27 ^ height n := by grind [pow_mul]
    _ ≤ 32 ^ height n := by simp_all [Nat.pow_le_pow_left]
    _ = (2 ^ height n) ^ 5 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (2 * Nat.log 2 n + 2) ^ 5 := Nat.pow_le_pow_left (two_pow_height_le n) 5
