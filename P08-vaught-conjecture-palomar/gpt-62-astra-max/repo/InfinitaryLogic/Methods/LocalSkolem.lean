/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.SkolemClosure

/-!
# Local (family-restricted) Skolem language `localSkolem`

The full Skolem language `skolem₁ω L` adjoins a function symbol for **every** `L_{ω₁ω}` formula, so
it is **uncountable** (`BoundedFormulaω` is uncountable). That makes the colimit `skolemColim L` and
its de-substituted atom diagram uncountable, which is fatal for the Ehrenfeucht–Mostowski term model:
the extracted tail-indiscernible family `Γ` would have to be uncountable, but the cheap infinite-Ramsey
extraction (`MorleyHanfExtractionTail`) only produces indiscernibility over a **countable** family.

The fix is to Skolemize only a **countable family** `Γ` of formulas. `localSkolem L Γ` adjoins one
arity-`n` function symbol per `(n+1)`-ary formula *in `Γ`*. When `Γ` is countable, `localSkolem L Γ`
is countable — the first ingredient of the countable local Skolem tower `Llocal`/`Γlocal` that will
re-base the EM term model (keeping `skolemColim` as exploratory infrastructure).

This file builds the language, its Hilbert-choice structure, and its countability. The mutually
recursive language/closure tower is a later chunk.
-/

@[expose] public section

universe u v w

namespace FirstOrder.Language

variable (L : Language.{0, 0})

/-- The **local Skolem language** over a family `Γ` of `L`-formulas: an arity-`n` function symbol for
each `(n+1)`-ary formula **that lies in `Γ`** (witnessing its last existential), and no relation
symbols. Unlike `skolem₁ω L` (which Skolemizes *all* formulas and is uncountable), this stays
countable whenever `Γ` is. -/
def localSkolem (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : Language.{0, 0} where
  Functions n := {φ : L.BoundedFormulaω Empty (n + 1) //
    (⟨n + 1, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Γ}
  Relations _ := Empty

variable {L}

/-- The **local Skolem structure** on `M`: each symbol (a formula `φ` of `Γ`) is interpreted as a
Hilbert-choice witness for `∃ xₙ, φ`, exactly as in `skolem₁ωStructure` but only for the symbols of
the restricted family. -/
noncomputable instance localSkolemStructure {M : Type w} [L.Structure M] [Nonempty M]
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) : (localSkolem L Γ).Structure M where
  funMap {_} φ x := Classical.epsilon fun a => φ.1.Realize (Empty.elim : Empty → M) (Fin.snoc x a)
  RelMap {_} r := r.elim

/-- The full (all-arity) function-symbol type of `localSkolem L Γ` is countable when `Γ` is. -/
theorem localSkolem_sigma_functions_countable (Γ : Set (Σ n, L.BoundedFormulaω Empty n))
    (hΓ : Γ.Countable) : Countable (Σ n, (localSkolem L Γ).Functions n) := by
  have : Countable ↥Γ := hΓ.to_subtype
  have hinj : Function.Injective
      (fun p : (Σ n, (localSkolem L Γ).Functions n) => (⟨⟨p.1 + 1, p.2.1⟩, p.2.2⟩ : ↥Γ)) := by
    rintro ⟨na, φa, ha⟩ ⟨nb, φb, hb⟩ h
    simp only [Subtype.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨hn, hφ⟩ := h
    obtain rfl : na = nb := Nat.succ_injective hn
    obtain rfl : φa = φb := eq_of_heq hφ
    rfl
  exact hinj.countable

/-- `localSkolem L Γ` has no relation symbols, so its relation-symbol type is (trivially) countable. -/
theorem localSkolem_sigma_relations_countable
    (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Countable (Σ n, (localSkolem L Γ).Relations n) :=
  (show Function.Injective
      (fun p : (Σ n, (localSkolem L Γ).Relations n) => (p.2.elim : ℕ)) from
    fun a _ _ => a.2.elim).countable

end FirstOrder.Language
