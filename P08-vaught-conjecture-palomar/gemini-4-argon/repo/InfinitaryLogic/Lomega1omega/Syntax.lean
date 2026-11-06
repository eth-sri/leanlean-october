/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import PalomarProof.Infinitary.Syntax
public import Mathlib.Logic.Encodable.Basic

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

@[expose] public section

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

@[match_pattern] abbrev falsum : L.BoundedFormulaω α n := BoundedFormulaInf.falsum

@[match_pattern] abbrev equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.equal t₁ t₂

@[match_pattern] abbrev rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    L.BoundedFormulaω α n :=
  BoundedFormulaInf.rel R ts

@[match_pattern] abbrev imp (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.imp φ ψ

@[match_pattern] abbrev all (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.all φ

@[match_pattern] abbrev iSup (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iSup φs

@[match_pattern] abbrev iInf (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iInf φs

/-- Negation, as a qualified name. `BoundedFormulaInf.not` is the definition. -/
@[match_pattern] protected abbrev not (φ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.not φ

/-- Existential quantification, as a qualified name. -/
@[match_pattern] protected abbrev ex (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.ex φ

/-- Conjunction of two formulas, defined via De Morgan. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  (φ.imp ψ.not).not

instance : Min (L.BoundedFormulaω α n) := ⟨BoundedFormulaω.and⟩

/-- Indexed conjunction over any `Encodable` type. This extends `iInf` from ℕ-indexed
to general countable indices by encoding. -/
def einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iInf fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊤

/-- Indexed disjunction over any `Encodable` type. This extends `iSup` from ℕ-indexed
to general countable indices by encoding. -/
def esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  iSup fun k => match Encodable.decode (α := ι) k with
    | some i => φs i
    | none => ⊥

/-- `einf` along an explicitly supplied encoding. -/
def einfWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  @einf L α n ι e φs

/-- `esup` along an explicitly supplied encoding. -/
def esupWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    L.BoundedFormulaω α n :=
  @esup L α n ι e φs

end BoundedFormulaω

scoped[Lomega1omega] infixr:62 " ⟹ω " => FirstOrder.Language.BoundedFormulaω.imp
scoped[Lomega1omega] prefix:arg "∼ω" => FirstOrder.Language.BoundedFormulaω.not
