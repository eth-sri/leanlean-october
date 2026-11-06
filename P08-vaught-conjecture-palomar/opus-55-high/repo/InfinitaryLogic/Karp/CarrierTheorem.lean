/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Karp.PotentialIso
public import InfinitaryLogic.Scott.AtomicDiagram
public import InfinitaryLogic.Scott.BackAndForth
public import PalomarProof.Infinitary.QuantifierRank
public import Architect

/-!
# Karp's theorem at a common branching carrier

Karp's theorem for the fixed-carrier infinitary syntax: two structures are potentially
isomorphic if and only if they satisfy the same `L∞ω` sentences.

The point of the fixed-carrier formulation is where the quantifier over index types lives.
In a syntax whose `iSup`/`iInf` nodes each carry their own index type, the theorem has to
quantify over index types *inside* every node, which forces the index universe to track the
structure universe. Here each formula branches over a single carrier `ι`, so the quantifier
sits outside the syntax, in `InfEquivW`, and the backward direction needs only **one**
carrier — any `κ` admitting codings of both structures.

## Main definitions

- `InfEquivAt L ι M N`: agreement on all `L∞ω` sentences branching over the carrier `ι`.
  The structures may live in different universes.
- `InfEquivW L M N`: agreement at every carrier in the structures' shared universe.

## Main results

- `karp_theorem_at`: potential isomorphism is equivalent to `InfEquivAt L κ M N` for **any**
  carrier `κ` admitting codings `IndexCoding M κ` and `IndexCoding N κ`.
- `karp_theorem_on_sum`: the canonical specialization at `κ := M ⊕ N`.
- `karp_theorem_w`: the packaged same-universe endpoint, `Nonempty (PotentialIso L M N) ↔
  InfEquivW L M N`. This is the public statement of Karp's theorem.

The separating conjunctions in the backward direction are `iInfAlong` along the two given
codings — a conjunction indexed by one structure's carrier, expressed at `κ`. That is the
whole content of "any common carrier suffices": the sum is canonical, not necessary.

## References

- Carol R. Karp, *Finite-quantifier equivalence*, in **The Theory of Models** (Addison,
  Henkin, Tarski, eds.), North-Holland, 1965, pp. 407–412. The theorem.
- Carol R. Karp, *Languages with Expressions of Infinite Length*, North-Holland, 1964 —
  the infinitary languages themselves.
- H. Jerome Keisler and Julia F. Knight, *Barwise: infinitary logic and admissible sets*,
  Bull. Symbolic Logic **10** (2004), 4–36, doi:10.2178/bsl/1080330272. Theorem 1.2.1 is
  the statement formalized here.

The common-carrier formulation with `IndexCoding` is this formalization's presentation, not
a statement made in those sources; the mathematics is Karp's.
-/

@[expose] public section

universe u v w w' uι uκ

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι}

open FirstOrder Structure BoundedFormulaInf

/-! ### Equivalence at a carrier -/

section KarpAtCarrier

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- In a relational language every term is a variable. -/
private theorem term_eq_var {γ : Type*} (t : L.Term γ) : ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact (IsEmpty.false f).elim

end KarpAtCarrier

/-! ### The quantifier-rank forward lemma

Back-and-forth equivalence at level `α` implies agreement on every formula of rank at most `α`.
This is stated at an arbitrary branching carrier, with independent structure universes, and
with `BFEquiv`'s ordinal in the *same* universe as `qrank` — so no `Ordinal.lift` enters the
induction. Callers whose ordinal genuinely lives elsewhere bridge at the boundary with
`BFEquiv.ofOrdinalLift` / `.toOrdinalLift`.

The tuple sits in free-variable positions here, because that is what the consumers need; the
`Fin.append` plumbing below is the cost of that choice, and is confined to these two lemmas. -/

section AgreementQR

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

omit [L.IsRelational] in
/-- `Sum.elim v xs` agrees with `Fin.append v xs ∘ finSumFinEquiv`. -/
private theorem sumElim_eq_append_comp {γ : Type*} {n k}
    (v : Fin n → γ) (xs : Fin k → γ) :
    Sum.elim v xs = Fin.append v xs ∘ finSumFinEquiv :=
  (Fin.append_comp_sumElim (xs := v) (ys := xs)).symm

omit [L.IsRelational] in
/-- `Fin.snoc` distributes into `Fin.append` on the right component. -/
private theorem snoc_append_eq_append_snoc {γ : Type*} {n k}
    (v : Fin n → γ) (xs : Fin k → γ) x :
    Fin.snoc (Fin.append v xs) x = Fin.append v (Fin.snoc xs x) :=
  (Fin.append_snoc v xs x).symm

/-- The rank-bounded agreement lemma, generalized to allow bound variables. -/
private theorem BFEquiv_implies_agree_aux (α : Ordinal.{uι}) {n k : ℕ}
    (φ : L.BoundedFormulaInf ι (Fin n) k) (hφ : φ.qrank ≤ α)
    (v : Fin n → M) (w : Fin n → N) (xs : Fin k → M) (ys : Fin k → N)
    (hBF : BFEquiv (L := L) α (n + k) (Fin.append v xs) (Fin.append w ys)) :
    (φ.Realize v xs ↔ φ.Realize w ys) := by
  induction φ generalizing α with
  | falsum => simp
  | equal t₁ t₂ =>
    obtain ⟨x₁, rfl⟩ := term_eq_var t₁
    obtain ⟨x₂, rfl⟩ := term_eq_var t₂
    simp only [realize_equal, Term.realize]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone bot_le hBF)
    rw [sumElim_eq_append_comp v xs, sumElim_eq_append_comp w ys]
    simp only [Function.comp]
    exact hSAT (.eq (finSumFinEquiv x₁) (finSumFinEquiv x₂))
  | rel R ts =>
    simp only [realize_rel]
    have hSAT : SameAtomicType (L := L) (Fin.append v xs) (Fin.append w ys) :=
      (BFEquiv.zero _ _).mp (BFEquiv.monotone bot_le hBF)
    have hvars : ∀ i, ∃ x, ts i = Term.var x := fun i => term_eq_var (ts i)
    choose ts_var hts using hvars
    have hM : (RelMap R fun i => (ts i).realize (Sum.elim v xs)) ↔
              RelMap R (Fin.append v xs ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp v xs, Function.comp]
    have hN : (RelMap R fun i => (ts i).realize (Sum.elim w ys)) ↔
              RelMap R (Fin.append w ys ∘ (fun i => finSumFinEquiv (ts_var i))) := by
      constructor <;> intro h <;> convert h using 1 <;> ext i <;>
        simp [hts i, sumElim_eq_append_comp w ys, Function.comp]
    rw [hM, hN]
    exact hSAT (.rel R (fun i => finSumFinEquiv (ts_var i)))
  | imp φ ψ ihφ ihψ =>
    simp only [realize_imp, BoundedFormulaInf.qrank_imp] at hφ ⊢
    exact imp_congr
      (ihφ α (le_of_max_le_left hφ) xs ys hBF)
      (ihψ α (le_of_max_le_right hφ) xs ys hBF)
  | all φ ih =>
    simp only [realize_all, BoundedFormulaInf.qrank_all] at hφ ⊢
    have hBF' := BFEquiv.monotone hφ hBF
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := BFEquiv.back hBF' y
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hm
      exact (ih φ.qrank le_rfl (Fin.snoc xs m) (Fin.snoc ys y) hm).mp (hAll m)
    · intro hAll x
      obtain ⟨y, hy⟩ := BFEquiv.forth hBF' x
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hy
      exact (ih φ.qrank le_rfl (Fin.snoc xs x) (Fin.snoc ys y) hy).mpr (hAll y)
  | iSup φs ih =>
    simp only [realize_iSup, BoundedFormulaInf.qrank_iSup] at hφ ⊢
    exact exists_congr fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF
  | iInf φs ih =>
    simp only [realize_iInf, BoundedFormulaInf.qrank_iInf] at hφ ⊢
    exact forall_congr' fun i =>
      ih i α (le_trans (Ordinal.le_iSup (fun i => (φs i).qrank) i) hφ) xs ys hBF

/-- **The Karp lemma, forward direction**: back-and-forth equivalence at level `α` implies
agreement on every formula of quantifier rank at most `α`.

Carrier-polymorphic, with independent structure universes, and with the `BFEquiv` ordinal in
the same universe as the rank. -/
theorem BFEquiv_implies_agreeQR (α : Ordinal.{uι}) {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : BFEquiv (L := L) α n a b)
    (φ : L.BoundedFormulaInf ι (Fin n) 0) (hφ : φ.qrank ≤ α) :
    (FormulaInf.Realize φ a ↔ FormulaInf.Realize φ b) := by
  have ha : Fin.append a (Fin.elim0 : Fin 0 → M) = a := by simp [Fin.append_elim0]
  have hb : Fin.append b (Fin.elim0 : Fin 0 → N) = b := by simp [Fin.append_elim0]
  exact BFEquiv_implies_agree_aux α φ hφ a b Fin.elim0 Fin.elim0 (by rwa [ha, hb])

end AgreementQR

end Language

end FirstOrder
