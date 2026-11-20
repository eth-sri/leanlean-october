module
public import Mathlib

/-!
# Alternating-block normal forms and their enumeration

Write `a, b, c` for generators `0, 1, 2`. In the `a,c` dihedral factor use the
alternating blocks starting with `a` of lengths `0 ≤ j < p`; on the other side
use `b,c` and `q`. A code consists of an optional leading `c`, a possibly empty
`a`-block and then positive blocks on alternating sides, beginning on the `b`-side.

We construct the three reflections on these codes and enumerate the codes by their
written length. No identification with group elements is assumed here: the two-sided
inverse and the comparison with Coxeter length are proved in `Triangle`.
-/

@[expose] public section

namespace TriangleGrowth

open Finset PowerSeries Function

/-- Positive block lengths, with alternating upper bounds. -/
def ValidTail : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | p, q, k :: r => 0 < k ∧ k < p ∧ ValidTail q p r

/-- `c ^ e`, a leading block of length `j` (possibly zero), then the tail. -/
abbrev Raw := Bool × ℕ × List ℕ

/-- Admissibility in the chart whose leading block is on the `p`-side.
The condition `0 < q` allows uniform counting over natural labels: even the empty
tail needs the choice `k = 0` in `range q` in the terminal constructor below. -/
abbrev Valid (p q : ℕ) (v : Raw) := v.2.1 < p ∧ 0 < q ∧ ValidTail q p v.2.2
abbrev Label := {p : ℕ // 2 ≤ p}
abbrev NF (p q : Label) := {v // Valid p q v}
def len (v : Raw) := v.1.toNat + v.2.1 + v.2.2.sum

/-- Read the same block list starting on the opposite side. A zero in the tail
is inadmissible; fixing `(0, 0 :: r)` makes this an involution on *all* codes. -/
def shift : ℕ × List ℕ → ℕ × List ℕ
  | (0, []) => (0, [])
  | (0, 0 :: r) => (0, 0 :: r)
  | (0, (k + 1) :: r) => (k + 1, r)
  | (j + 1, r) => (0, (j + 1) :: r)

def swap : Equiv.Perm Raw := (Equiv.refl Bool).prodCongr
  (Involutive.toPerm shift (by intro t; fun_cases shift t <;> rfl))

@[simp] theorem swap_symm : swap.symm = swap := rfl

variable {p q : ℕ}

@[simp] theorem swap_valid (v : Raw) : Valid p q (swap v) ↔ Valid q p v := by
  rcases v with ⟨e, t⟩
  fun_cases shift t <;> simp [swap, shift, Involutive.toPerm, Valid, ValidTail] <;> grind

@[simp] theorem len_swap (v : Raw) : len (swap v) = len v := by
  rcases v with ⟨e, t⟩
  fun_cases shift t <;> simp +arith [swap, shift, Involutive.toPerm, len]

/-- Prepend `a` and rewrite just the dihedral head. With a leading `c` the
new alternating word has length `j + 2`; at the far side of the dihedral cycle
use its complementary word. Without a leading `c`, cancel the first `a` if present. -/
def move (m : ℕ) : Raw → Raw
  | (e, j, r) =>
    if e then
      if j + 2 < m then (false, j + 2, r) else (true, 2 * m - j - 3, r)
    else
      if j < 2 then (false, 1 - j, r) else (true, j - 2, r)

section Action
variable {p q : Label}
local notation "PermNF" => Equiv.Perm (NF p q)

attribute [local simp] move Involutive.toPerm

def a : PermNF := Involutive.toPerm (fun v => ⟨move p v, by simp; grind⟩) (by
  intro v
  apply Subtype.ext
  simp
  grind [Prod.ext_iff])

def c : PermNF := Involutive.toPerm (fun v => ⟨(!v.val.1, v.val.2), v.2⟩) (by intro v; simp)

def chart : NF p q ≃ NF q p := swap.subtypeEquiv (by simp)

/-- The second generator acts by the first generator's rule in the opposite chart. -/
def gen : Fin 3 → PermNF
  | 0 => a
  | 1 => chart.permCongrHom a
  | 2 => c

@[simp] theorem inv_gen (i : Fin 3) : (gen i : PermNF)⁻¹ = gen i := by fin_cases i <;> rfl

@[simp] theorem gen_sq (i : Fin 3) : (gen i * gen i : PermNF) = 1 :=
  _root_.eq_inv_iff_mul_eq_one.mp (inv_gen i).symm

/-- `a * c` advances two places around the `2p`-cycle. -/
theorem ac_rel : (a * c : PermNF) ^ p.val = 1 := by
  ext v : 1
  let pos (v : Raw) := if v.1 then 2 * p.val - 1 - v.2.1 else v.2.1
  -- In at most p steps there can be at most one wrap; the tail never changes.
  let D (n : ℕ) (u : NF p q) := u.val.2.2 = v.val.2.2 ∧
    (pos u = pos v + 2 * n ∨ pos u + 2 * p.val = pos v + 2 * n)
  have lap (n : ℕ) (hn : n ≤ p) : D n (((a * c : PermNF) ^ n) v) := by
    induction n with
    | zero =>
      change D 0 v
      simp [D]
    | succ n ih =>
      specialize ih (by omega)
      rw [pow_succ']
      change D _ (a (c _))
      simp [D, a, c, pos] at *
      grind
  suffices ∀ u, D p u → u = v from this _ (lap p le_rfl)
  intro u hu
  apply Subtype.ext
  simp [D, pos] at *
  grind [Prod.ext_iff]

/-- Changing chart commutes with `c` (it leaves the Boolean alone). Transport the lap. -/
theorem bc_rel : (gen 1 * gen 2 : PermNF) ^ q.val = 1 := by
  have hc : chart.permCongrHom (c : Equiv.Perm (NF q p)) = c := by
    ext v : 1
    exact congrArg c (chart.apply_symm_apply v)
  simpa only [gen, map_pow, map_one, map_mul, hc] using congrArg chart.permCongrHom (@ac_rel q p)

theorem len_a (v : NF p q) : len (a v) ≤ len v + 1 := by
  simp [a, len]
  grind

theorem len_gen (i : Fin 3) (v : NF p q) : len (gen i v) ≤ len v + 1 := by
  fin_cases i
  · exact len_a v
  · simpa [gen, chart] using len_a (chart v)
  · cases h : v.val.1 <;> simp +arith [gen, c, len, h]

/-- Either empty, or reducible by a simple generator. -/
theorem descent (v : NF p q) : v.val = (false, 0, []) ∨ ∃ i, len (gen i v) < len v := by
  obtain ⟨⟨e, j, r⟩, h⟩ := v
  refine or_iff_not_imp_left.mpr fun hz => ⟨if e then 2 else if j = 0 then 1 else 0, ?_⟩
  cases e <;> cases j <;> cases r <;>
    simp_all [gen, a, c, chart, swap, shift, len, Valid] <;> grind [ValidTail]

end Action

/-! ### A two-block grammar

If there is at most one tail block, the entire code is specified by a terminal
triple `(e, j, k)`, with `k = 0` for the empty tail. Otherwise remove the first
two tail blocks: their lengths are positive and the remainder uses the original
chart. Thus the terminal choices give the numerator and the removed block pairs
give the nonconstant part of the denominator. -/

scoped notation:max "S₊ " m:arg x:arg => (∑ i ∈ Ico 1 m, x ^ i)
scoped notation:max "Rₓ " m:arg => (∑ i ∈ range m, (X : ℤ⟦X⟧) ^ i)

abbrev degree (u : ℕ × ℕ) := u.1 + u.2

theorem geom_mul {R : Type*} [Semiring R] (x : R) (P Q : Finset ℕ) :
    (∑ i ∈ P, x ^ i) * (∑ j ∈ Q, x ^ j) = ∑ u ∈ P ×ˢ Q, x ^ degree u := by
  simp [sum_mul_sum, sum_product, degree, pow_add]

abbrev Head := Bool × ℕ × ℕ
abbrev heads (p q : ℕ) := (univ : Finset Bool) ×ˢ range p ×ˢ range q
abbrev weight (h : Head) := h.1.toNat + degree h.2
abbrev pairs (p q : ℕ) := Ico 1 p ×ˢ Ico 1 q

/-- Assemble the two disjoint cases. A pair `(i, k)` from the product of the
`p`- and `q`-intervals is prepended to the *tail* in the order `k, i`. -/
def assemble {s : Finset (ℕ × ℕ)} : Head ⊕ (Σ _ : s, Raw) ↪ Raw where
  toFun
    | .inl (e, j, k) => (e, j, if k = 0 then [] else [k])
    | .inr ⟨⟨(i, k), _⟩, e, j, r⟩ => (e, j, k :: i :: r)
  inj' := by rintro (h | ⟨u, v⟩) (h' | ⟨u', v'⟩) <;> grind [Prod.ext_iff, Subtype.ext_iff]

/-- Finite, computable enumeration at a given length, recursing only on admissible pairs. -/
def forms (p q n : ℕ) : Finset Raw :=
  (((heads p q).filter (weight · = n)).disjSum
    (((pairs p q).filter (degree · ≤ n)).attach.sigma
      fun u => forms p q (n - degree u.val))).map assemble
termination_by n
decreasing_by grind

@[simp] theorem mem_forms (v : Raw) : v ∈ forms p q n ↔ Valid p q v ∧ len v = n := by
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    rw [forms]
    obtain ⟨e, j, r⟩ := v
    cases e <;> rcases r with _ | ⟨k, _ | ⟨i, r⟩⟩ <;>
      simp [mem_map, Sum.exists, Sigma.exists, Subtype.exists, Prod.exists, mem_sigma,
        assemble, heads, pairs, weight, degree, Valid, ValidTail, len] <;> grind [len]

abbrev count (p q n : ℕ) := (forms p q n).card

theorem count_all (p q n : ℕ) : count p q n = ((heads p q).filter (weight · = n)).card +
    ∑ u ∈ (pairs p q).filter (degree · ≤ n), count p q (n - degree u) := by
  rw [count, forms]
  simp [card_sigma, count]
  symm
  rw [← sum_attach]

/-- Above the maximum terminal weight the count obeys the homogeneous recursion. -/
theorem count_rec (hn : p + q ≤ n) : count p q n = ∑ u ∈ pairs p q, count p q (n - degree u) := by
  rw [count_all]
  simp (disch := grind [Bool.toNat_le]) [filter_false_of_mem, filter_true_of_mem]

theorem forms_series (p q : ℕ) :
    (mk fun n => (count p q n : ℤ)) * (1 - S₊ p X * S₊ q X) = (1 + X) * Rₓ p * Rₓ q := by
  have numerator : (∑ h ∈ heads p q, (X : ℤ⟦X⟧) ^ weight h) = (1 + X) * Rₓ p * Rₓ q := by
    simp [heads, weight, degree, sum_product, pow_add, ← sum_mul, ← mul_sum, mul_assoc, add_comm X 1]
  rw [← numerator, mul_sub, mul_one, sub_eq_iff_eq_add, geom_mul]
  ext n
  simpa [pairs, count, sum_filter, mul_sum, coeff_mul_X_pow', coeff_X_pow, eq_comm] using
    congrArg (Nat.cast (R := ℤ)) (count_all p q n)

end TriangleGrowth
