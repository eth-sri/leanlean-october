/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Operations
public import InfinitaryLogic.Util

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {N : Type w} [L.Structure N] {n : ℕ}

open FirstOrder Structure Fin BoundedFormulaω

/-- Maps `j : Fin k` to `⟨j.val + 1, ...⟩ : Fin (1 + k)`. Used for bound variable shifting. -/
private def finSuccShift {k : ℕ} : Fin k → Fin (1 + k) :=
  fun j => ⟨j.val + 1, by omega⟩

/-- Helper lemma: the composition of `Sum.elim v xs` with `relabelAux insertLastBound k`
equals `Sum.elim (snoc v (xs 0)) (xs ∘ finSuccShift)`. This is the key for proving
semantics of relabeling for formulas with k bound variables. -/
private lemma sum_elim_relabelAux_insertLastBound {k : ℕ} (v : Fin n → N) (xs : Fin (1 + k) → N) :
    Sum.elim v xs ∘ BoundedFormulaω.relabelAux insertLastBound k =
    Sum.elim (snoc v (xs 0)) (xs ∘ finSuccShift) := by
  funext x
  cases x with
  | inl i =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inl, Sum.elim_inl,
      insertLastBound]
    split_ifs with h
    · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, snoc, h, dite_true]
      congr 1
    · simp only [Equiv.sumAssoc_apply_inl_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_left]
      have hi : i = last n := by grind
      aesop
  | inr j =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inr, Sum.elim_inr]
    simp only [Equiv.sumAssoc_apply_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_right,
      finSuccShift]
    congr 1; grind

/-- Helper: composition of snoc with succShift. -/
private lemma snoc_comp_succShift_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    snoc xs y ∘ finSuccShift = snoc (xs ∘ finSuccShift) y := by
  funext j
  simp only [Function.comp_apply]
  cases j using lastCases with
  | last =>
    simp only [snoc_last]
    have hsuc : finSuccShift (last k) = last (1 + k) := by
      ext; simp only [finSuccShift, last]; omega
    simp_all
  | cast j' =>
    simp only [snoc_castSucc]; unfold snoc
    have hlt : (finSuccShift (castSucc j')).val < 1 + k := by simp [finSuccShift, castSucc]; omega
    aesop

/-- Helper: snoc xs y at position 0 equals xs at position 0. -/
private lemma snoc_zero_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    (snoc (α := fun _ => N) xs y) (0 : Fin (1 + k + 1)) = xs (0 : Fin (1 + k)) := by simp

/-- The general semantics lemma for relabeling with `insertLastBound`:
    For a formula with k bound variables, relabeling shifts the last free variable
    to bound position 0, while bound variables shift up by 1.

This handles all cases including `all`, which appears in Scott formulas due to
`forallLastVar` applications at earlier stages. -/
private theorem realize_relabel_insertLastBound {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω (Fin (n + 1)) k) (v : Fin n → N) (xs : Fin (1 + k) → N),
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) (xs ∘ finSuccShift) := by
  intro k φ
  induction φ with
  | falsum => tauto
  | equal t₁ t₂ =>
    intro v xs
    simp [relabel, realize_equal, Term.realize_relabel, sum_elim_relabelAux_insertLastBound]
  | rel R ts =>
    intro v xs; simp only [relabel, realize_rel]
    have key := sum_elim_relabelAux_insertLastBound (k := _) v xs
    simp_all
  | imp φ ψ ih_φ ih_ψ =>
    intro v xs; simp only [relabel, realize_imp]; grind
  | all φ ih =>
    intro v xs; simp only [relabel, realize_all]
    constructor <;> intro hall y
    -- Use realize_castLE_self which handles any proof of n ≤ n, not just le_refl
    · specialize hall y
      rw [realize_castLE_self] at hall
      rw [ih v (snoc xs y)] at hall
      rwa [snoc_zero_eq, snoc_comp_succShift_eq] at hall
    · rw [realize_castLE_self, ih v (snoc xs y), snoc_zero_eq, snoc_comp_succShift_eq]; exact hall y
  | iSup φs ih =>
    intro v xs; simp only [relabel, realize_iSup]; grind
  | iInf φs ih =>
    intro v xs; simp only [relabel, realize_iInf]; grind

/-- The key semantics lemma for formulas with 0 bound variables: relabeling with `insertLastBound`
    shifts the last free variable to a bound variable position.

For `φ : L.Formulaω (Fin (n+1))` (a formula with n+1 free vars and 0 bound vars):
- `φ.relabel insertLastBound : L.BoundedFormulaω (Fin n) 1` has n free vars and 1 bound var
- When we evaluate with free var assignment `v : Fin n → N` and bound var assignment
  `xs : Fin 1 → N`, this corresponds to evaluating the original formula with
  `snoc v (xs 0) : Fin (n+1) → N` -/
theorem realize_relabel_insertLastBound_zero {n : ℕ} (φ : L.Formulaω (Fin (n + 1)))
    (v : Fin n → N) (xs : Fin 1 → N) :
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) := by
  have h := realize_relabel_insertLastBound (k := 0) φ v xs
  rwa [show (xs ∘ finSuccShift : Fin 0 → N) = Fin.elim0 from Fin.eq_elim0 _] at h

end Language

end FirstOrder
