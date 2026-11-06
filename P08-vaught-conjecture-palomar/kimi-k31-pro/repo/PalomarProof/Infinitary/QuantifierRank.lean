/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import PalomarProof.Infinitary.Reindex
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Quantifier rank of infinitary formulas

The quantifier rank of an infinitary formula: `0` on atoms, `max` on implication, successor
under `∀`, and the supremum over the branching carrier at an infinitary node.

## The universe of the rank

Because the infinitary cases take a supremum over the carrier `ι`, the natural target is
`Ordinal.{uι}` — the carrier's own ordinal universe. At `ι := ℕ` this is exactly
`Ordinal.{0}`, which is where Scott analysis wants it; no lifting appears in the `L_{ω₁ω}`
case.

Transport between carriers is therefore stated up to `Ordinal.lift`: `qrank_reindex` says
`reindex` preserves rank once both sides are lifted into a common universe. Padding is
invisible to rank, since the padded branches are `⊤`/`⊥`, both of rank `0` — which is why the
statement holds for empty carriers too, where every branch is padding.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf.qrank`

## Main results

- `qrank_reindex`: rank is preserved by carrier transport, up to `Ordinal.lift`.
- `qrank_alls`, `qrank_exs`: closing all free bound-variable slots adds exactly `n`.
- `qrank_toInf`: the finitary embedding's rank is carrier-independent (up to `Ordinal.lift`),
  since a finitary formula has no infinitary nodes.
-/

@[expose] public section

universe u v u' uι uκ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The quantifier rank of an infinitary formula, valued in the branching carrier's own
ordinal universe. -/
noncomputable def qrank : ∀ {n}, L.BoundedFormulaInf ι α n → Ordinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => Order.succ (qrank φ)
  | _, .iSup φs => ⨆ i, qrank (φs i)
  | _, .iInf φs => ⨆ i, qrank (φs i)

section Equations




@[simp]
theorem qrank_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).qrank = max φ.qrank ψ.qrank := rfl

@[simp]
theorem qrank_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank := rfl

@[simp]
theorem qrank_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp]
theorem qrank_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := rfl











