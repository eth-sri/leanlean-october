module

public import VaughtConjecture.Knight.FairPairedChain
public import VaughtConjecture.Knight.EmptySeedBoundary
public import VaughtConjecture.Knight.CommonChartSupply
public import VaughtConjecture.Knight.SelectedCommonCharts

/-! # The source-level common-chart chain: the lowest classification consumer

**Review-directed graduation, queue item 3** (2026-08-31; scratch-compiled by the
reviewer across two rounds, adapted with credit; graduation review verified the
acceptance test: THE ISOMORPHISM PROOF CONSUMES NO CONSECUTIVE LABEL-MAP
COMPATIBILITY — `FairCommonChartChain` carries only tuple-restriction laws, each family
member's chart certificate uses only its own node's shared source type, and forth/back
are coordinate bookkeeping).

* `CommonChartNode` / `FairCommonChartChain` — one common full source chart per node (no
  higher-stage witness attached); a monotone exhaustive chain with unrelated consecutive
  labels; `nonempty_iso_of_fairCommonChartChain` gives the source isomorphism.
* `CommonChartStepSupply` / `RestrictedCommonChartStepSupply Good` — forcing-lite local
  density (Rasiowa–Sikorski without set-theoretic machinery), and its
  construction-selected restriction: `RestrictedCommonChartStepSupply Good` is THE
  LOWEST CLASSIFICATION PRODUCER; `nonempty_iso_of_commonChartStepSupply_of_isModel` is
  the final boundary with the empty seed from model covering.
* `HeightFlexibleCommonChartExtension` and its adapters — each scheduled step may
  independently choose convenient higher stages and fresh linked witnesses, prove one
  finite paired occurrence, and forget all high data after projecting the next common
  source chart: NO compatibility between successive high witnesses is consumed, so
  persistent high recurrence is off the classification route.
* The paired-occurrence/`ScheduledPairedRun` layer and
  `FairPairedChain.toFairCommonChartChain` — the merged high-witness chain FORGETS onto
  this quotient: its inter-node label maps are certification scaffolding, not consumed
  classification data.

`CommonChartNode` and the step-supply vocabulary live in `Knight/CommonChartSupply.lean`
(re-exported here, names unchanged). The `Nonempty` classification cashouts below go through the
direct selected-chart consumer (`Knight/SelectedCommonCharts.lean`) and build no chain; the chain
constructors remain for applications that want an actual chain.

Not root-exported, like the boundary vocabulary it serves. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open TypeTower
open Value

universe w

namespace KnightRealization

variable {β₁ β₂ : LimitStage} {M₁ M₂ : Type w}
variable {hβ₁ : blockStage 0 ≤ β₁} {hβ₂ : blockStage 0 ≤ β₂}
variable {W₁ : KnightRealization β₁ M₁} {W₂ : KnightRealization β₂ M₂}
variable {R₁ : KnightRealization (blockStage 0) M₁}
variable {R₂ : KnightRealization (blockStage 0) M₂}

namespace PairedOccurrences

end PairedOccurrences

namespace PairedExtensionData

end PairedExtensionData

namespace ScheduledPairedRun

end ScheduledPairedRun

/-! ## A still smaller, source-level consumer

The proof of `nonempty_iso_of_fairPairedChain` does not consume the label-map
fields of `PairedStep`.  It only consumes a monotone sequence of common source
charts.  The following direct formulation makes that quotient explicit; its nodes
are the `CommonChartNode`s of `Knight/CommonChartSupply.lean`. -/

variable {α : LimitStage}
variable {A₁ : KnightRealization α M₁} {A₂ : KnightRealization α M₂}

/-! ## Height-flexible certification scaffolding

The source-level consumer never compares the higher witnesses used at two
successive construction steps.  A producer may therefore choose fresh stages
and fresh linked witnesses for each scheduled requirement, prove one paired
occurrence there, and immediately forget them after projecting its common
source chart.  This is strictly an adapter statement: it does not construct
the paired occurrence. -/

/-- One common-chart extension certified at arbitrary convenient higher
stages.  The stages and witnesses are existential scaffolding local to this
single step. -/
structure HeightFlexibleCommonChartExtension
    (nd : CommonChartNode (A₁ := A₁) (A₂ := A₂))
    (z : M₁ ⊕ M₂) where
  β₁ : LimitStage
  β₂ : LimitStage
  hβ₁ : α ≤ β₁
  hβ₂ : α ≤ β₂
  W₁ : KnightRealization β₁ M₁
  W₂ : KnightRealization β₂ M₂
  reduct₁ : W₁.reduct hβ₁ = A₁
  reduct₂ : W₂.reduct hβ₂ = A₂
  arity : ℕ
  tuple₁ : Fin arity ↪ M₁
  tuple₂ : Fin arity ↪ M₂
  type₁ : S β₁.1 arity
  type₂ : S β₂.1 arity
  eval₁ : W₁.eval tuple₁ = some type₁
  eval₂ : W₂.eval tuple₂ = some type₂
  reduced_eq :
    reduceType α.2 hβ₁ type₁ = reduceType α.2 hβ₂ type₂
  source_eval₁ : A₁.eval tuple₁ = some (reduceType α.2 hβ₁ type₁)
  source_eval₂ : A₂.eval tuple₂ = some (reduceType α.2 hβ₂ type₂)
  emb : Fin nd.arity ↪ Fin arity
  trans₁ : emb.trans tuple₁ = nd.tuple₁
  trans₂ : emb.trans tuple₂ = nd.tuple₂
  serves_left : ∀ x, z = Sum.inl x → ∃ i, tuple₁ i = x
  serves_right : ∀ y, z = Sum.inr y → ∃ i, tuple₂ i = y

namespace HeightFlexibleCommonChartExtension

end HeightFlexibleCommonChartExtension

namespace FairCommonChartChain

end FairCommonChartChain

end KnightRealization

end VaughtConjecture.Knight
