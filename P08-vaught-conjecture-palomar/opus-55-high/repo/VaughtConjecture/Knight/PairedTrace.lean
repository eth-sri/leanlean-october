/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Rank
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.ChartLanguage

/-! # The paired provenance trace (#57/#47 terminal boundary — vocabulary)

The pairing vocabulary of the based-Karp extension experiment, graduated to main: the
construction-private relation between two code-matched stopped witnesses whose members are
concrete per-node data — never `HasCommonChart` certificates.  This implements the #178
correction: *provenance constructs the relation; `HasCommonChart` is only a projection*
(`PairedCover.hasCommonChart_sources`).

Provenance: re-homed verbatim (minus the quarantined `HighCandidate` context) from
`VaughtConjecture/Knight/BasedKarp.lean` on `origin/e7/based-karp` (PR #195); the
`exactParent_typeMap` spelling is re-proved from mainline material (it was a one-line
unfolding in `PartialDensity.lean` on `origin/e7/high-candidate`, PR #194).  The supplies
and the compiled equivalence over this vocabulary are `Knight/TraceBoundary.lean`.

## The pairing objects

* `PairedCover` — one node: a common finite arity, one labelled cover of each witness
  (`W₁.LabelledExt` / `W₂.LabelledExt` data, unbundled to share the arity), and the single
  cross-model field `red_eq`: the two labels have EQUAL source reductions (a carrier-free
  stage type at `blockStage 0`).  Target-stage labels are NOT compared — only their
  reductions enter the chart projection, and the witnesses may sit at different stages.
* `PairedStep` — one trace letter: ONE shared embedding under which both covers restrict to
  the previous node, tuples and labels.  The label restrictions are DERIVED data:
  `PairedStep.ofEmb` shows exact parent consistency of the two witnesses reconstructs them
  from the tuple restrictions alone, so the genuine step datum is the shared embedding.
* `PairedTrace` — the construction-private provenance word: the reflexive-transitive
  data-carrying closure of `PairedStep` from a seed node.  `PairedTrace.seed_le` projects the
  composite shared embedding (every traced node carries the seed as a matched face);
  `PairedTrace.swap` mirrors a trace (back = symmetry, as the producer-word design demands).
* Seeding (`exists_pairedSeed_of_code_matched`): two stopped receipts with EQUAL COMPLETE
  codes (`StopCode`: run level, cutoff, both source labels, `⊤`-witness) seed the relation —
  the receipt face pair and copy pair, matched by code equality through the literal
  `reduct_base` links, with the shared embedding `Fin.castSuccEmb` between them.  Membership
  is by construction only; no `HasCommonChart` premise anywhere.

## The unconditional transfer content

`red_agree_on_base`: for ANY evaluated right cover extending a node's right occurrence along
the shared embedding, its source reduction agrees with the left cover's on EVERY base-face
cell — exact parent consistency of both witnesses plus the node's `red_eq`.  Whatever
residual transfer question is asked of a paired trace (`Knight/TraceBoundary.lean`) is
therefore confined to the label cells meeting the FRESH coordinates.

**Mainline placement**: this module is deliberately NOT root-exported (the
`TopProduction`/`StoppedReceipt` precedent): it is construction-facing vocabulary, imported
by `Knight/TraceBoundary.lean`.  It imports only mainline modules. -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

/-- Exact parent consistency, `typeMap`-spelled (the tower's `pull` is `typeMap`,
definitionally).  Re-proved from the mainline definition; the original one-liner is
`PartialDensity.lean` on `origin/e7/high-candidate` (PR #194). -/
theorem exactParent_typeMap {γ} {M} {B : KnightRealization γ M}
    (hB : B.IsExactParentConsistent) {n k} t (q : S γ.1 n)
    (f : Fin k ↪ Fin n) (hq : B.eval t = some q) : B.eval (f.trans t) = typeMap f q :=
  hB t q f hq

/-! ### The paired node: two labelled covers with equal source reductions -/

/-! ### The paired step and the provenance trace -/

end KnightRealization
end VaughtConjecture.Knight
