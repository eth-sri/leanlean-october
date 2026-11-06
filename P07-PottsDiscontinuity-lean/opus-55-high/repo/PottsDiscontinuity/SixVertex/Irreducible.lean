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

section
variable (hA : ∀ i j, 0 ≤ A i j)
include hA
theorem pow_succ_apply_pos {k : ℕ} {a b c : S}
    (h1 : 0 < (A ^ k) a b) (h2 : 0 < A b c) : 0 < (A ^ (k + 1)) a c := by
  refine Finset.sum_pos' (fun d _ => mul_nonneg (Matrix.pow_apply_nonneg hA k a d) (hA d c))
    ⟨b, mem_univ b, mul_pos h1 h2⟩

theorem exists_pow_pos_of_reflTransGen {a b : S}
    (h : Relation.ReflTransGen (fun i j => 0 < A i j) a b) : ∃ k, 0 < (A ^ k) a b := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, pow_succ_apply_pos hA hk hbc⟩
end

theorem reflTransGen_symm_of_symm {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {a b : α} (h : Relation.ReflTransGen R a b) : Relation.ReflTransGen R b a := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact .head (hR _ _ hbc) ih

/-- A nonnegative matrix with positive diagonal in which every entry is positive in some power
is primitive. -/
theorem isPrimitive_of_pos_diag (hA : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < A i i)
    (hpow : ∀ i j, ∃ k, 0 < (A ^ k) i j) : A.IsPrimitive := by
  choose k hk using hpow
  have hpad : ∀ i j (K : ℕ), k i j ≤ K → 0 < (A ^ K) i j := by
    intro i j K hK
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
    induction d with
    | zero => simp_all
    | succ d ih =>
      grind [pow_succ_apply_pos]
  refine ⟨hA, (Finset.univ.sup fun p : S × S => k p.1 p.2) + 1, Nat.succ_pos _, fun i j => ?_⟩
  refine hpad i j _ ?_
  have : k i j ≤ Finset.univ.sup fun p : S × S => k p.1 p.2 :=
    Finset.le_sup (f := fun p : S × S => k p.1 p.2) (mem_univ (i, j))
  omega

end Generic

/-! ### Counting along a particle jump -/

/-- The state obtained from `p` by moving the entry `i` to the vacant position `j`. -/
def jump (p : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) := insert j (p.erase i)

section
variable {p : Finset (Fin N)} {i j : Fin N} (hi : i ∈ p) (hj : j ∉ p)
include hi hj
theorem cnt_jump (hji : j < i)
    (t : Fin N) :
    cnt (jump p i j) t = cnt p t + if j ≤ t ∧ t < i then 1 else 0 := by
  unfold cnt jump
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases hjt : j ≤ t
  · by_cases hit : i ≤ t
    · grind
    simp_all
  · have hit : ¬ i ≤ t := by omega
    aesop

theorem card_jump  :
    (jump p i j).card = p.card := by
  grind [jump]

theorem interlaced_jump (hji : j < i) : Interlaced p (jump p i j) := by
  rw [interlaced_iff]
  grind [card_jump, cnt_jump]
end

/-! ### Reaching the packed state -/

/-- The packed state `{0, …, n - 1}`. -/
def packedSet (N n : ℕ) : Finset (Fin N) := univ.filter fun a => a.val < n

theorem card_packedSet {n : ℕ} (hn : n ≤ N) : (packedSet N n).card = n := by
  unfold packedSet
  rw [← card_image_of_injective _ Fin.val_injective]
  have : (univ.filter fun a : Fin N => a.val < n).image Fin.val = range n := by
    ext k
    simp
    constructor
    · omega
    · intro hk; exact ⟨⟨k, lt_of_lt_of_le hk hn⟩, hk, rfl⟩
  simp_all

/-- The packed state as an element of `State N n`. -/
def packed (hn : n ≤ N) : State N n := ⟨packedSet N n, card_packedSet hn⟩

section
variable (hc : 0 < c) (hn : n ≤ N)
include hc hn
/-- The relation "`V^{[n]}` has a positive entry" generates a connected graph. -/
theorem reach_packed  :
    ∀ m : ℕ, ∀ x : State N n, (x.1.filter fun a => n ≤ a.val).card = m →
      Relation.ReflTransGen (fun a b : State N n => 0 < transferBlock N c n a b) x (packed hn) := by
  intro m
  induction m with
  | zero =>
    intro x hx
    have hsub : x.1 ⊆ packedSet N n := by
      intro a ha
      simp_all [packedSet]
    have  :=
      Finset.eq_of_subset_of_card_le hsub (by grind [card_packedSet])
    grind [packed]
  | succ m ih =>
    intro x hx
    have hne : (x.1.filter fun a => n ≤ a.val).Nonempty := by
      rw [← card_pos, hx]; omega
    obtain ⟨i, hi⟩ := hne
    have hj : ∃ j : Fin N, j.val < n ∧ j ∉ x.1 := by
      by_contra hcon
      push Not at hcon
      have hsub : packedSet N n ⊆ x.1 := fun a ha => hcon a (by simp_all [packedSet])
      have  :=
        Finset.eq_of_subset_of_card_le hsub (by grind [card_packedSet])
      grind [packedSet]
    obtain ⟨j, hjn, hjx⟩ := hj
    let q : State N n := ⟨jump x.1 i j, by grind [card_jump]⟩
    have hq : (q.1.filter fun a => n ≤ a.val).card = m := by
      have : q.1.filter (fun a => n ≤ a.val) = (x.1.filter fun a => n ≤ a.val).erase i := by
        grind [jump]
      simp_all
    have hstep : 0 < transferBlock N c n x q := by
      rw [transferBlock_pos_iff hc]
      grind [interlaced_jump]
    exact Relation.ReflTransGen.head hstep (ih q hq)

theorem exists_pow_pos_block (x y : State N n) :
    ∃ k, 0 < (transferBlock N c n ^ k) x y := by
  have hxp := reach_packed hc hn _ x rfl
  have hsymm : ∀ a b : State N n, 0 < transferBlock N c n a b → 0 < transferBlock N c n b a := by
    intro a b h
    rw [transferBlock_apply, transferMatrix_symm] at h
    positivity
  exact exists_pow_pos_of_reflTransGen (transferBlock_nonneg hc.le n)
    (hxp.trans (reflTransGen_symm_of_symm hsymm (reach_packed hc hn _ y rfl)))

/-- For `c > 0` and `0 ≤ n ≤ N` the block `V^{[n]}` is primitive. -/
theorem transferBlock_isPrimitive  :
    (transferBlock N c n).IsPrimitive :=
  isPrimitive_of_pos_diag (transferBlock_nonneg hc.le n)
    (fun x => by simp) (exists_pow_pos_block hc hn)
end

end PottsDiscontinuity.SixVertex
