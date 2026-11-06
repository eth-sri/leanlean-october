/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import PalomarProof.Infinitary.Syntax
import Mathlib.Logic.Encodable.Basic

/-!
# Lω₁ω Syntax — compatibility facade over the fixed-carrier syntax

`BoundedFormulaω`, `Formulaω` and `Sentenceω` are no longer declared here. They come from
`Mathlib.ModelTheory.Infinitary.Syntax`, where `BoundedFormulaω L α n` is an **abbrev** for
`BoundedFormulaInf L ℕ α n`. This file re-exports that syntax under the module path and namespace
the project already uses, and adds only what Mathlib does not provide.

## Why an abbrev and not a `def`

The specialization must stay *definitional*, not merely propositional. Since Lean 4.34 a goal has
to be type-correct at `implicit` transparency before `rw`/`simp` will act on it, so a semireducible
wrapper around `BoundedFormulaInf ℕ` would silently break rewriting across the whole ω consumer
surface. The probes at the end of this file certify the identification with no `change`, rewrite,
or explicit cast — their *absence* is the certification.

## What this file still owns

- the qualified `BoundedFormulaω.*` constructor surface, for consumers that name constructors
  explicitly rather than through dot-notation (dot-notation resolves through the head symbol
  `BoundedFormulaInf` and needs no help);
- the derived connectives Mathlib does not define: `and`, `or`, `iff`, with their `Min`/`Max`
  instances;
- the `Encodable`-indexed connectives `einf`/`esup` and their explicit-encoding forms
  `einfWith`/`esupWith`;
- the scoped notation.

`Bot`, `Top`, `Inhabited`, `not` and `ex` now come from Mathlib and are deliberately **not**
redeclared. `BoundedFormulaInf.verum` plays the role of the old `top` and is definitionally equal to it
(`not falsum` reduces to `imp falsum falsum`).
-/

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-! ### Qualified constructor surface

The constructors live in the `BoundedFormulaInf` namespace. Dot-notation on a
`BoundedFormulaω` already resolves there, but consumers naming a constructor explicitly as
`BoundedFormulaω.falsum` need these. Each is an `abbrev`, so it unfolds by `rfl`, and each is
`@[match_pattern]`, so it may still be used in pattern position. -/

local notation "BoundedFormulaω₀" => L.BoundedFormulaω α n

@[match_pattern] abbrev falsum : BoundedFormulaω₀ := BoundedFormulaInf.falsum

@[match_pattern] abbrev equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaω₀ :=
  BoundedFormulaInf.equal t₁ t₂

@[match_pattern] abbrev rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    BoundedFormulaω₀ :=
  BoundedFormulaInf.rel R ts

@[match_pattern] abbrev imp (φ ψ : BoundedFormulaω₀) : BoundedFormulaω₀ :=
  BoundedFormulaInf.imp φ ψ

@[match_pattern] abbrev all (φ : L.BoundedFormulaω α (n + 1)) : BoundedFormulaω₀ :=
  BoundedFormulaInf.all φ

@[match_pattern] abbrev iSup (φs : ℕ → BoundedFormulaω₀) : BoundedFormulaω₀ :=
  BoundedFormulaInf.iSup φs

@[match_pattern] abbrev iInf (φs : ℕ → BoundedFormulaω₀) : BoundedFormulaω₀ :=
  BoundedFormulaInf.iInf φs

/-- Negation, as a qualified name. `BoundedFormulaInf.not` is the definition. -/
@[match_pattern] protected abbrev not (φ : BoundedFormulaω₀) : BoundedFormulaω₀ :=
  BoundedFormulaInf.not φ

/-- Existential quantification, as a qualified name. -/
@[match_pattern] protected abbrev ex (φ : L.BoundedFormulaω α (n + 1)) : BoundedFormulaω₀ :=
  BoundedFormulaInf.ex φ

/-! Production's `not` and `ex` were `@[match_pattern]`; Mathlib's are not, and the attribute
**cannot** be added downstream ("cannot add attribute to a declaration in an imported module").
The qualified `BoundedFormulaω.not`/`.ex` above are declared here and so do carry it, which covers
consumers that name them explicitly; dot-notation *patterns* (`| .not φ => …`) resolve through the
head symbol to `BoundedFormulaInf.not` and are therefore not available. If a consumer needs them,
the fix belongs upstream on the fork, not here. -/

/-! ### Derived connectives Mathlib does not provide -/

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : BoundedFormulaω₀) :=
  (φ.imp ψ.not).not

instance : Min (BoundedFormulaω₀) := ⟨BoundedFormulaω.and⟩

/-- Indexed conjunction over any `Encodable` type. This extends `iInf` from ℕ-indexed
to general countable indices by encoding. -/
def einf {ι : Type*} [Encodable ι] (φs : ι → BoundedFormulaω₀) :=
  iInf fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊤

/-- Indexed disjunction over any `Encodable` type. This extends `iSup` from ℕ-indexed
to general countable indices by encoding. -/
def esup {ι : Type*} [Encodable ι] (φs : ι → BoundedFormulaω₀) :=
  iSup fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊥

/-! ### Explicit-encoding forms

`einf`/`esup` take their encoding by instance search.  A consumer that must use a *specific*
enumeration — one supplied as data rather than found — is otherwise forced into a local `letI`,
which is fragile and makes the resulting syntax look instance-dependent when it is not.

These are **thin wrappers**, deliberately: `einf`/`esup` are *not* redefined in terms of them.
Reversing that dependency would disturb definitional reductions across many existing consumers. -/

/-- `einf` along an explicitly supplied encoding. -/
def einfWith {ι : Type*} (e : Encodable ι) (φs : ι → BoundedFormulaω₀) :=
  @einf L α n ι e φs

/-- `esup` along an explicitly supplied encoding. -/
def esupWith {ι : Type*} (e : Encodable ι) (φs : ι → BoundedFormulaω₀) :=
  @esup L α n ι e φs

end BoundedFormulaω

-- Notation
scoped[Lomega1omega] infixr:62 " ⟹ω " => FirstOrder.Language.BoundedFormulaω.imp

scoped[Lomega1omega] prefix:110 "∀'ω " => FirstOrder.Language.BoundedFormulaω.all

scoped[Lomega1omega] prefix:arg "∼ω" => FirstOrder.Language.BoundedFormulaω.not

scoped[Lomega1omega] prefix:110 "∃'ω " => FirstOrder.Language.BoundedFormulaω.ex

scoped[Lomega1omega] infixl:61 " ⇔ω " => FirstOrder.Language.BoundedFormulaω.iff

/-! ## Facade transparency gates

These must elaborate with **no** `change`, rewrite, or explicit cast. That is precisely what
certifies that the ω names remain a definitional specialization — the property Lean 4.34's
`implicit`-transparency requirement makes load-bearing for every `rw`/`simp` in the ω tower. -/



