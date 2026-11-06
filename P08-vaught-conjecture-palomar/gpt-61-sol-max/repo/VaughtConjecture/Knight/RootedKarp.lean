/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.RootedPotentialIso
import VaughtConjecture.Knight.SelectedCommonCharts
import VaughtConjecture.Knight.PairedTrace
import VaughtConjecture.Knight.ChartKarp
import VaughtConjecture.Knight.CommonChartSupply

/-! # Root-preserving classification: chain adapters and compatibility signatures

This module is the historical import path for root-preserving classification. It re-exports

* `Knight/RootedPotentialIso.lean` — `rootedPotentialIso`, `exists_equiv_of_mem`,
  `exists_iso_of_potentialIso_mem`, `exists_iso_of_commonCharts_mem`: a potential isomorphism
  yields, on countable carriers, an isomorphism extending any member pair literally;
* `Knight/SelectedCommonCharts.lean` — the direct consumer
  `exists_iso_of_selectedCommonCharts`: one good seed and restricted one-step supply already
  give the root-preserving isomorphism, with no fair chart chain and no `Nonempty` carriers;
* `Knight/CommonChartChain.lean` — the historical fair-chain vocabulary.

It keeps the chain adapter `exists_iso_of_fairCommonChartChain`, for applications that have an
actual chain, and the compatibility signatures `exists_iso_of_commonChartStepSupply` and
`exists_iso_of_restrictedCommonChartStepSupply`, which are now proved by the direct consumer and
build no chain. -/

namespace VaughtConjecture.Knight


universe w

namespace KnightRealization

variable {M₁ M₂ : Type w} {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

local notation "CommonChartNode₀" => CommonChartNode (A₁ := A₁) (A₂ := A₂)

/-- Root-preserving one-step-density cashout: the isomorphism extends the seed chart. This is
the direct consumer with every chart good; the `Nonempty` instances are no longer used. -/
def exists_iso_of_commonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (seed : CommonChartNode₀)
    (supply : CommonChartStepSupply (A₁ := A₁) (A₂ := A₂)) :=
  exists_iso_of_selectedCommonCharts hA₁ hA₂ (fun _ => True) seed trivial
    (restrictedCommonChartStepSupply_true supply)

/-- Root-preserving restricted cashout: the isomorphism extends the good seed chart. Kept as the
compatibility signature of `exists_iso_of_selectedCommonCharts`; the `Nonempty` instances are no
longer used. -/
def exists_iso_of_restrictedCommonChartStepSupply
    [Countable M₁] [Countable M₂] [Nonempty M₁] [Nonempty M₂]
    (hA₁ : A₁.IsExactParentConsistent) (hA₂ : A₂.IsExactParentConsistent)
    (Good : CommonChartNode₀ → Prop)
    (seed : CommonChartNode₀)
    (seed_good : Good seed)
    (supply : RestrictedCommonChartStepSupply (A₁ := A₁) (A₂ := A₂) Good) :=
  exists_iso_of_selectedCommonCharts hA₁ hA₂ Good seed seed_good supply


