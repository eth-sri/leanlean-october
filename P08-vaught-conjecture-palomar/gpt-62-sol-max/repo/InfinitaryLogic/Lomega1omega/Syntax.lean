/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import PalomarProof.Infinitary.Syntax
public import Mathlib.Logic.Encodable.Basic

@[expose] public section

universe u v u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

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

end Language

end FirstOrder
