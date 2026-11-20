/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Lomega1omega.Syntax
public import PalomarProof.Infinitary.Semantics

@[expose] public section

universe u v w w' u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {M : Type w} [L.Structure M]

variable {α : Type u'} {n : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaω

/-- Realization of a bounded Lω₁ω formula, as a qualified name.
`Mathlib`'s `BoundedFormulaInf.Realize` is the definition; this alias is `@[reducible]` and
reproduces the project's historical argument order `L M inst α n φ v xs`. -/
abbrev Realize (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  BoundedFormulaInf.Realize φ v xs

variable {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_bot

@[simp]
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaω α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_equal

@[simp]
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaω α n).Realize v xs ↔
      RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_rel

@[simp]
theorem realize_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  BoundedFormulaInf.realize_imp

@[simp]
theorem realize_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_all

@[simp]
theorem realize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSup

@[simp]
theorem realize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInf

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaω α n).Realize v xs ↔ True :=
  BoundedFormulaInf.realize_top

@[simp]
theorem realize_not (φ : L.BoundedFormulaω α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  BoundedFormulaInf.realize_not

@[simp]
theorem realize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_ex

@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by simp_all [BoundedFormulaω.and, realize_not, realize_imp]

@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  realize_and φ ψ

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [einf, realize_iInf]
  constructor
  · intro h i
    simpa [Encodable.encodek] using h (Encodable.encode i)
  aesop

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [esup, realize_iSup]
  constructor
  · aesop
  · rintro ⟨i, hi⟩
    use Encodable.encode i
    simp only [Encodable.encodek, hi]

/-- Realization of `einfWith`: the supplied encoding does not affect the semantics. -/
@[simp] theorem realize_einfWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (einfWith e φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  @realize_einf L M _ α n v xs ι e φs

/-- Realization of `esupWith`. -/
@[simp] theorem realize_esupWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (esupWith e φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  @realize_esup L M _ α n v xs ι e φs

end BoundedFormulaω

namespace Embedding

variable {N : Type w'} [L.Structure N] (f : M ↪[L] N) {v : α → M} {xs : Fin n → M}

/-- An embedding preserves and reflects the atomic formula `t₁ = t₂`. -/
theorem realize_equal_comp (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (BoundedFormulaω.equal t₁ t₂).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.equal t₁ t₂).Realize v xs := by simp_all [BoundedFormulaω.realize_equal, ← Sum.comp_elim, HomClass.realize_term]

/-- An embedding preserves and reflects the atomic formula `R ts`. -/
theorem realize_rel_comp {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (BoundedFormulaω.rel R ts).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.rel R ts).Realize v xs := by
  simp only [BoundedFormulaω.realize_rel, ← Sum.comp_elim, HomClass.realize_term]
  apply f.map_rel

end Embedding

/-- Realization of Lω₁ω formulas is preserved by language isomorphisms.

Given an isomorphism `e : M ≃[L] N`, a formula realized in M with variable assignments
`v` and `xs` is also realized in N with the transported assignments `e ∘ v` and `e ∘ xs`. -/
theorem BoundedFormulaω.realize_equiv.{u_1} {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type u_1} {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => exact (e.toEmbedding.realize_equal_comp t₁ t₂).symm
  | rel R ts => exact (e.toEmbedding.realize_rel_comp R ts).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.Realize]
    grind
  | all φ ih =>
    simp only [BoundedFormulaInf.Realize]
    constructor
    · intro h y
      have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
    grind [← Fin.comp_snoc]
  | iSup φs ih =>
    simp only [BoundedFormulaInf.Realize]
    grind
  | iInf φs ih =>
    simp only [BoundedFormulaInf.Realize]
    grind

namespace Formulaω

/-- Realization of an Lω₁ω formula, as a qualified name. Mathlib's `FormulaInf.Realize` is the
definition; it fills the arity-0 valuation with `default`, which is definitionally the project's
historical `Fin.elim0` (gated below). -/
abbrev Realize (φ : L.Formulaω α) (v : α → M) : Prop :=
  FormulaInf.Realize φ v

variable {φ : L.Formulaω α} {v : α → M}

@[simp]
theorem realize_not : Realize φ.not v ↔ ¬Realize φ v := BoundedFormulaω.realize_not φ

@[simp]
theorem realize_inf (φ ψ : L.Formulaω α) :
    Realize (φ ⊓ ψ) v ↔ Realize φ v ∧ Realize ψ v := BoundedFormulaω.realize_inf φ ψ

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.einf φs) v ↔ ∀ i, Realize (φs i) v := BoundedFormulaω.realize_einf φs

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.esup φs) v ↔ ∃ i, Realize (φs i) v := BoundedFormulaω.realize_esup φs

end Formulaω

namespace Sentenceω

/-- Truth of an Lω₁ω sentence in a structure, as a qualified name. Mathlib's
`SentenceInf.Realize` is the definition. -/
abbrev Realize (φ : L.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  SentenceInf.Realize φ M

/-- The level-crossing lemma: sentence truth *is* bounded-formula realization at the empty
valuation and the empty tuple. See `Formulaω.realize_def` for why this is needed and why it is
not a `simp` lemma. -/
theorem realize_def (φ : L.Sentenceω) (M : Type w) [L.Structure M] :
    Realize φ M ↔ BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

end Sentenceω

end Language

end FirstOrder
