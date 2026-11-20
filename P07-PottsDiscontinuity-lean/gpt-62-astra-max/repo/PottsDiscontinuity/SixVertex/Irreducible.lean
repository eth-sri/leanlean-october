module

public import PottsDiscontinuity.SixVertex.TransferMatrix
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Irreducibility and primitivity of the blocks `V^{[n]}`

For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` of the transfer matrix is irreducible and primitive
(some power has all entries positive); this is the statement "each block `V^{[n]}` satisfies the
assumption of the Perron–Frobenius theorem" of the paper (companion paper `blocks-are-Perron-Frobenius`).

Proof: a "single particle jump" `x ↦ (x \ {i}) ∪ {j}` (`j < i`, `i ∈ x`, `j ∉ x`) produces an interlaced
pair (the counting functions differ by the indicator of `[j, i)`), hence a positive entry of `V`;
by such jumps every `x` reaches the packed state `{0, …, n-1}`; the diagonal of `V` is `2 > 0`, so
irreducibility implies primitivity.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ} {c : ℝ}

/-! ### Generic facts on nonnegative matrices -/

section Generic

variable {S : Type*} [Fintype S] [DecidableEq S] {A : Matrix S S ℝ}

variable (hA : ∀ i j, 0 ≤ A i j)

include hA in
theorem pow_succ_apply_pos {k : ℕ} {a b c : S}
    (h1 : 0 < (A ^ k) a b) (h2 : 0 < A b c) : 0 < (A ^ (k + 1)) a c := by
  refine Finset.sum_pos' (fun d _ => mul_nonneg (Matrix.pow_apply_nonneg hA k a d) (hA d c)) ⟨b, mem_univ b, mul_pos h1 h2⟩

include hA in
theorem exists_pow_pos_of_reflTransGen {a b : S}
    (h : Relation.ReflTransGen (fun i j => 0 < A i j) a b) : ∃ k, 0 < (A ^ k) a b := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, pow_succ_apply_pos hA hk hbc⟩

theorem reflTransGen_symm_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hR _ _ hbc) ih

include hA in
/-- A nonnegative matrix with positive diagonal in which every entry is positive in some power
is primitive. -/
theorem isPrimitive_of_pos_diag (hd : ∀ i, 0 < A i i)
    (hpow : ∀ i j, ∃ k, 0 < (A ^ k) i j) : A.IsPrimitive := by
  choose k hk using hpow
  have hpad : ∀ i j K, k i j ≤ K → 0 < (A ^ K) i j := by
    intro i j K hK
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
    induction d with
    | zero => grind
    | succ d ih =>
      grind [pow_succ_apply_pos]
  let f' := fun p : S × S => k p.1 p.2
  refine ⟨hA, (Finset.univ.sup f') + 1, Nat.succ_pos _, fun i j => ?_⟩
  refine hpad i j _ ?_
  have : k i j ≤ Finset.univ.sup f' :=
    Finset.le_sup (f := f') (mem_univ (i, j))
  omega

end Generic

/-! ### Counting along a particle jump -/

/-- The state obtained from `p` by moving the entry `i` to the vacant position `j`. -/
def jump (p : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) := insert j (p.erase i)

section
variable {p : Finset (Fin N)} {i j : Fin N} (hi : i ∈ p) (hj : j ∉ p) (hji : j < i)
include hi hj

include hji in
theorem cnt_jump
    (t : Fin N) :
    cnt (jump p i j) t = cnt p t + if j ≤ t ∧ t < i then 1 else 0 := by
  unfold cnt jump
  have hjF : j ∉ p.filter (· ≤ t) := by grind
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases hjt : j ≤ t
  · by_cases hit : i ≤ t
    · grind
    · simp [*]
  · have hit := fun h => hjt (le_trans hji.le h)
    have hiF : i ∉ p.filter (· ≤ t) := by grind
    simp [*]

theorem card_jump :
    (jump p i j).card = p.card := by
  unfold jump
  grind

include hji in
theorem interlaced_jump : Interlaced p (jump p i j) := by
  rw [interlaced_iff]
  refine ⟨(card_jump hi hj).symm, Or.inr fun t => ?_⟩
  grind [cnt_jump hi hj hji]

end

/-! ### Reaching the packed state -/

/-- The packed state `{0, …, n - 1}`. -/
def packedSet (N n : ℕ) : Finset (Fin N) := univ.filter fun a => a.val < n

section
variable {n : ℕ} (hn : n ≤ N)
include hn

theorem card_packedSet : (packedSet N n).card = n := by
  unfold packedSet
  rw [← card_image_of_injective _ Fin.val_injective]
  have : (univ.filter fun a : Fin N => a.val < n).image Fin.val = range n := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    constructor
    · grind
    · intro hk; exact ⟨⟨k, lt_of_lt_of_le hk hn⟩, hk, rfl⟩
  grind

/-- The packed state as an element of `State N n`. -/
def packed : State N n := ⟨packedSet N n, card_packedSet hn⟩

end

/-- The relation "`V^{[n]}` has a positive entry" generates a connected graph. -/
theorem reach_packed (hc : 0 < c) (hn : n ≤ N) :
    ∀ m : ℕ, ∀ x : State N n, (x.1.filter fun a => n ≤ a.val).card = m →
      Relation.ReflTransGen (fun a b : State N n => 0 < transferBlock N c n a b) x (packed hn) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hsub : x.1 ⊆ packedSet N n := by
      intro a ha
      by_contra hna
      have : a ∈ x.1.filter fun a => n ≤ a.val := by
        rw [mem_filter]
        refine ⟨ha, ?_⟩
        have : ¬ a.val < n := fun h => hna (by simp [packedSet, h])
        omega
      grind
    have  :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_packedSet hn, x.2])
    have hxp : x = packed hn := Subtype.ext this
    grind
  | succ m ih =>
    intro x hx
    have hne : (x.1.filter fun a => n ≤ a.val).Nonempty := by
      rw [← card_pos, hx]; exact Nat.succ_pos _
    obtain ⟨i, hi⟩ := hne
    rw [mem_filter] at hi
    -- a vacant position below `n`
    have hj : ∃ j, j.val < n ∧ j ∉ x.1 := by
      by_contra hcon
      push Not at hcon
      have hsub : packedSet N n ⊆ x.1 := fun a ha => hcon a (by simpa [packedSet] using ha)
      have  :=
        Finset.eq_of_subset_of_card_le hsub (by rw [card_packedSet hn, x.2])
      grind [packedSet]
    obtain ⟨j, hjn, hjx⟩ := hj
    have hji : j < i := by
      omega
    let q : State N n := ⟨jump x.1 i j, by rw [card_jump hi.1 hjx, x.2]⟩
    exact Relation.ReflTransGen.head (by
      rw [transferBlock_pos_iff hc]
      exact Or.inr (interlaced_jump hi.1 hjx hji)) (ih q (by
      have : q.1.filter (fun a => n ≤ a.val) = (x.1.filter fun a => n ≤ a.val).erase i := by
        show (jump x.1 i j).filter _ = _
        unfold jump
        grind
      grind))

theorem exists_pow_pos_block (hc : 0 < c) (hn : n ≤ N) (x y : State N n) :
    ∃ k, 0 < (transferBlock N c n ^ k) x y := by
  exact exists_pow_pos_of_reflTransGen (transferBlock_nonneg (N := N) hc.le n)
    ((reach_packed hc hn _ x rfl).trans (reflTransGen_symm_of_symm (by simp [transferBlock_apply, transferMatrix_symm]) (reach_packed hc hn _ y rfl)))

/-- For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is primitive. -/
theorem transferBlock_isPrimitive (hc : 0 < c) (hn : n ≤ N) :
    (transferBlock N c n).IsPrimitive :=
  isPrimitive_of_pos_diag (transferBlock_nonneg hc.le n)
    (fun x => by norm_num) (exists_pow_pos_block hc hn)

end PottsDiscontinuity.SixVertex
