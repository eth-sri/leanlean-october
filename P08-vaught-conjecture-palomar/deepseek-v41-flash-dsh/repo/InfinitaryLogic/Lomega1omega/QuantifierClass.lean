/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Operations

/-!
# The universal and existential quantifier classes (issue #15, Unit 0)

The `∀₁`/`∃₁` classes of Harrison-Trainor–Kretschmer §2 (their hierarchy for counting quantifier
alternations in infinitary formulas), realized as a **signed quantifier traversal** on the existing
syntax:

* atomic formulas lie in **both** classes (they have no quantifier);
* an antecedent **flips** the class — `¬φ` is universal exactly when `φ` is existential;
* countable conjunctions and disjunctions **preserve** the class and are *not* counted as
  quantifiers (the source's clause 3, which is what distinguishes `∀n`/`∃n` from `Πn`/`Σn`);
* `∀` is **universal only**: in this syntax `ex φ = (φ.not.all).not`, so an existential quantifier
  *is* an `all` occurring negatively.

One `Bool`-parameterised recursion carries both classes, so their mutual dependence through negation
is definitional rather than a second induction — the same design as `Lomega1omega/Polarity.lean`,
and, as there, **no negation-normal form is constructed anywhere**.

This module is deliberately neutral: it depends only on the syntax layer and is intended to be
reused by any preservation theorem (issue #15's interpolation and relative preservation, and issue
#16's end extensions), not to live inside the interpolation development.
-/

@[expose] public section

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-- **The signed quantifier class.**  `universalSigned true φ` says `φ` is *universal* (`∀₁`) and
`universalSigned false φ` says `φ` is *existential* (`∃₁`).  An antecedent flips the sign, the
countable connectives preserve it, and `all` is admissible only at the universal sign. -/
def universalSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => True
  | _, _, .equal _ _ => True
  | _, _, .rel _ _ => True
  | _, s, .imp φ ψ => universalSigned (!s) φ ∧ universalSigned s ψ
  | _, s, .all φ => s = true ∧ universalSigned s φ
  | _, s, .iSup φs => ∀ i, universalSigned s (φs i)
  | _, s, .iInf φs => ∀ i, universalSigned s (φs i)

/-! ## Constructor equations -/

@[simp] theorem universalSigned_falsum {n : ℕ} (s : Bool) :
    universalSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := trivial

@[simp] theorem universalSigned_bot {n : ℕ} (s : Bool) :
    universalSigned s (⊥ : L.BoundedFormulaω α n) := trivial

@[simp] theorem universalSigned_equal {n : ℕ} (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.equal t₁ t₂) := trivial

@[simp] theorem universalSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.rel R ts) := trivial

@[simp] theorem universalSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    universalSigned s (φ.imp ψ) ↔ universalSigned (!s) φ ∧ universalSigned s ψ := Iff.rfl

@[simp] theorem universalSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    universalSigned s φ.all ↔ s = true ∧ universalSigned s φ := Iff.rfl

@[simp] theorem universalSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iSup φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

@[simp] theorem universalSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iInf φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

/-! ## The acceptance equations -/

/-- Negation **exchanges** the two classes. -/
@[simp] theorem universalSigned_not {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    universalSigned s φ.not ↔ universalSigned (!s) φ := by
  show universalSigned (!s) φ ∧ universalSigned s
    (BoundedFormulaω.falsum : L.BoundedFormulaω α n) ↔ _
  simp

/-! ## The derived connectives -/

@[simp] theorem universalSigned_top {n : ℕ} (s : Bool) :
    universalSigned s (⊤ : L.BoundedFormulaω α n) := ⟨trivial, trivial⟩

@[simp] theorem universalSigned_and {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    universalSigned s (φ.and ψ) ↔ universalSigned s φ ∧ universalSigned s ψ := by
  show universalSigned s ((φ.imp ψ.not).not) ↔ _
  simp

@[simp] theorem universalSigned_or {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    universalSigned s (φ.or ψ) ↔ universalSigned s φ ∧ universalSigned s ψ := by
  show universalSigned s (φ.not.imp ψ) ↔ _
  simp

/-! ## Stability under the variable operations -/

end BoundedFormulaω

end FirstOrder.Language
