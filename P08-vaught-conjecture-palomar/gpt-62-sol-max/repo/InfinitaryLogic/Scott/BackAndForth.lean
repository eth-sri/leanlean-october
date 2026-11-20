/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Scott.AtomicDiagram
public import Architect
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]

variable {M : Type w} [L.Structure M]

variable {N : Type w'} [L.Structure N]

open FirstOrder Structure Fin Ordinal

/-- Back-and-forth equivalence at ordinal α between tuples a in M and b in N.

At level 0: same atomic type.
At successor α + 1: same atomic type, plus:
  - (forth) for every m in M, there exists n in N with BFEquiv α (snoc a m) (snoc b n)
  - (back) for every n in N, there exists m in M with BFEquiv α (snoc a m) (snoc b n)
At limit λ: BFEquiv β for all β < λ.

The definition itself needs no relational language: the file's `[L.IsRelational]` variable
does not enter it, and `BFEquiv.zero`, `succ`, `limit`, `of_succ`, `forth`, `back` and
`monotone` (like `refl`, `symm`, `trans` and the ordinal-lift transports) carry
`omit [L.IsRelational] in`.  Relationality is required by the consumers that compare `BFEquiv`
with agreement on formulas of bounded quantifier rank, e.g. `BFEquiv_implies_agreeQR`
(`Karp/CarrierTheorem.lean`).  Without relationality the level-0 clause `SameAtomicType` sees
only atoms whose arguments are variables (see its docstring), so the comparison with formula
agreement fails: with one unary function symbol `f`, the empty tuples of `(ℕ, id)` and
`(ℕ, succ)` are `BFEquiv` at every level, yet `∀ x, f x = x`, of rank `1`, separates them.
-/
@[blueprint "def:BFEquiv"
  (title := /-- Back-and-forth equivalence -/)
  (statement := /-- Back-and-forth equivalence $\BFEquiv_\alpha(a,b)$ for tuples
    $a \in M^n$, $b \in N^n$ at ordinal $\alpha$, defined by transfinite recursion:
    atomic agreement at $0$, forth-and-back extension at successor, conjunction at limit. -/)]
noncomputable def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  Ordinal.limitRecOn α
    -- Zero case: same atomic type
    (fun (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      SameAtomicType (L := L) (M := M) (N := N) a' b')
    -- Successor case
    (fun _β ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ih k a' b' ∧
      (∀ m : M, ∃ n' : N, ih (k + 1) (snoc a' m) (snoc b' n')) ∧
      (∀ n' : N, ∃ m : M, ih (k + 1) (snoc a' m) (snoc b' n')))
    -- Limit case
    (fun _β _hβ ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ∀ γ (hγ : γ < _β), ih γ hγ k a' b')
    n a b

variable {n : ℕ}

omit [L.IsRelational] in
theorem BFEquiv.zero (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b := by simp [BFEquiv, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem BFEquiv.succ (α : Ordinal) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (Order.succ α) n a b ↔
      BFEquiv (L := L) α n a b ∧
      (∀ m : M, ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) := by simp [BFEquiv, Order.succ_eq_add_one, Ordinal.limitRecOn_add_one]

omit [L.IsRelational] in
theorem BFEquiv.limit (α : Ordinal) (hα : Order.IsSuccLimit α) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∀ β, β < α → BFEquiv (L := L) β n a b := by
  unfold BFEquiv
  simp_all

omit [L.IsRelational] in
/-- BF-equivalence at level α + 1 implies BF-equivalence at level α. -/
theorem BFEquiv.of_succ {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) : BFEquiv (L := L) α n a b :=
  (by grind [BFEquiv.succ])

omit [L.IsRelational] in
/-- BF-equivalence is monotone: higher ordinals imply lower ordinals. -/
theorem BFEquiv.monotone {α β : Ordinal} (hαβ : α ≤ β)
    {a : Fin n → M} {b : Fin n → N} (h : BFEquiv (L := L) β n a b) :
    BFEquiv (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    simp_all
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one] at hαβ h
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · rw [Order.lt_succ_iff] at hαβ'
      exact ih hαβ' (BFEquiv.of_succ h)
    · exact h
  | limit γ hγ _ih =>
    grind [BFEquiv.limit]

omit [L.IsRelational] in
/-- The "forth" property at a successor level. -/
theorem BFEquiv.forth {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (m : M) :
    ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.1 m

omit [L.IsRelational] in
/-- The "back" property at a successor level. -/
theorem BFEquiv.back {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (n' : N) :
    ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.2 n'

omit [L.IsRelational] in
/-- BF-equivalence is reflexive at all levels. -/
theorem BFEquiv.refl (α : Ordinal) (a : Fin n → M) :
    BFEquiv (L := L) (M := M) (N := M) α n a a := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero => exact (BFEquiv.zero a a).mpr (SameAtomicType.refl a)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    tauto
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    tauto

omit [L.IsRelational] in
/-- BF-equivalence is symmetric at all levels. -/
theorem BFEquiv.symm {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) (M := N) (N := M) α n b a := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [BFEquiv.zero] at h ⊢
    exact h.symm
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ] at h ⊢
    exact ⟨ih h.1, fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at h ⊢
    tauto

omit [L.IsRelational] in
/-- BF-equivalence is transitive at all levels.
If a and b are BF-equivalent, and b and c are BF-equivalent, then a and c are BF-equivalent.
Note that a, b, c may be tuples in different structures. -/
theorem BFEquiv.trans {P : Type*} [L.Structure P]
    {α : Ordinal} {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}
    (hab : BFEquiv (L := L) α n a b) (hbc : BFEquiv (L := L) α n b c) :
    BFEquiv (L := L) α n a c := by
  induction α using Ordinal.limitRecOn generalizing n a b c with
  | zero =>
    rw [BFEquiv.zero] at hab hbc ⊢
    exact fun idx => (hab idx).trans (hbc idx)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ] at hab hbc ⊢
    refine ⟨ih hab.1 hbc.1, fun m => ?_, fun p => ?_⟩
    · let ⟨nb, hnb⟩ := hab.2.1 m; let ⟨p, hp⟩ := hbc.2.1 nb; tauto
    · let ⟨nb, hnb⟩ := hbc.2.2 p; let ⟨m, hm⟩ := hab.2.2 nb; tauto
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at hab hbc ⊢
    grind

end Language

end FirstOrder
