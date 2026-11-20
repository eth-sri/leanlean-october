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

@[expose] public section

universe u v w w' uι uκ

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι}

open FirstOrder Structure BoundedFormulaInf

section KarpAtCarrier

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- In a relational language every term is a variable. -/
private theorem term_eq_var {γ : Type*} (t : L.Term γ) : ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact (IsEmpty.false f).elim

end KarpAtCarrier

section AgreementQR

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

omit [L.IsRelational] in
/-- `Sum.elim v xs` agrees with `Fin.append v xs ∘ finSumFinEquiv`. -/
private theorem sumElim_eq_append_comp {γ : Type*} {n k : ℕ}
    (v : Fin n → γ) (xs : Fin k → γ) :
    Sum.elim v xs = Fin.append v xs ∘ finSumFinEquiv :=
  by aesop

omit [L.IsRelational] in
/-- `Fin.snoc` distributes into `Fin.append` on the right component. -/
private theorem snoc_append_eq_append_snoc {γ : Type*} {n k : ℕ}
    (v : Fin n → γ) (xs : Fin k → γ) (x : γ) :
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
    grind
  | all φ ih =>
    simp only [realize_all, BoundedFormulaInf.qrank_all] at hφ ⊢
    have hBF' := BFEquiv.monotone hφ hBF
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := BFEquiv.back hBF' y
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hm
      grind
    · intro hAll x
      obtain ⟨y, hy⟩ := BFEquiv.forth hBF' x
      rw [snoc_append_eq_append_snoc, snoc_append_eq_append_snoc] at hy
      grind
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
