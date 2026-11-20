/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceOrbitRow
public import VaughtConjecture.Knight.CollisionAtController

set_option linter.privateModule false

/-! # Installing the donor row on the actual request inventory

The reviewer's assignment (2026-09-15): reuse the actual full-controller reference-orbit
construction (`Knight/ReferenceOrbitRow.lean`, ported with attribution) and install its unary
fresh reading on the actual request inventory at the unchanged threshold `N`; prove the exact
old-source, fresh-source, lower-domain and availability equations; identify the selected
section's controller-cap compatibility explicitly; then test bottom-cap sections and
positive-cap lifting; stop at the first concrete failed obligation.

**The donor.**  `C.FullController` (`exists_fullController`) is an actual old cell `F.cell`
of the context at `(univ, N)` dominating the cap, chosen by completeness and availability.
Its lower domain `F.Old` — the old cells of grade `≤ N` — is **literally the old part of the
inventory controller's lower set** (`oldPart`, `oldPart_surjective`: the lower-domain
equation).  The new controller is the remaining-index cell at `(univ, N)` of the inventory
(`controllerIndex`, threshold unchanged).

**The installed row** (`installedRow`): at an old cell the donor's own source, literally
(`installedRow_old`, the old-source equation); at a fresh request cell the donor's orbit source
for the request it answers — the visibility replacement of the donor's reading of the actual
representative (`installedRow_fresh`, the fresh-source equation); at a remaining-index cell of
the lower set, a reading `mixedRead` that this module does **not** construct.

**The selected section** (`selectedSection`): the context's labels capped at the donor's
value on old cells, the requested values at fresh cells, the donor's value at the new
controller.  Its **controller-cap compatibility** is explicit: the donor's value is
self-visible at `N` (`donor_selfVis`), every requested value lies strictly below it
(`request_lt_donor`: cap dominance and the donor's domination of the cap), and the faithful
witness carrying the installed row to the section capped at the donor is **the donor's own
exact witness** — one shifter with the step suppressor `gTop N` and unguarded clause 5
(`installed_transformsTo`, from `FullController.transformsTo`; no composition).  Availability
of the section **among the old cells** is the context's own (`section_old_respects`, from
`target_old_respects`).

**The first concrete obligation, where this stops.**  The lower set of the new controller
also contains the remaining-index cells of grade `≤ N` — the mixed indices `(B ∪ {last}, j)`.
The installed row needs readings there (`mixedRead`), the section needs values there, and
availability of a fresh cell toward every mixed index of its grade must be met by those
values; and each mixed cell needs its own row with restrictions coherent with the installed
row.  None of this is supplied by the donor row (its carrier is `F.Old ⊕ requests`), and the
readings cannot be mute (a mute reading forces the mixed cell to `⊥` under the controller,
contradicting availability from a nonbottom old or fresh cell of its grade).  This is the
reviewer's qualification 3, met here as the stop: **the mixed-cell readings and rows coherent
with the donor row**.  The bottom-cap section tests and the positive-cap lifting test are not
reached.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd
open CellScheme.restrictFace (pushGraded)

namespace ReferenceContext

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M} {n : ℕ} {t : Fin n ↪ M}
  {reqs : List BlockRequest} {C : ReferenceContext R t reqs} (F : C.FullController)
  (hblocks : ∀ r ∈ reqs, limitPart r.block = r.block)
  {Y : CellScheme (ι := Fin (n + 1)) Finset.univ}
  {Rp : Finset (Finset (Fin (C.m + 1)))} {hR : Plan.IsPlan Finset.univ Rp}
  {hRA : Plan.restrictPlan Rp (Finset.univ.image Fin.castSuccEmb) =
    C.p₀.scheme.scheme.plan.image (Finset.image Fin.castSuccEmb)}
  {hRB : Plan.restrictPlan Rp (Finset.univ.image (onePointProj C.proj)) =
    Y.plan.image (Finset.image (onePointProj C.proj))}
  (hn : ∀ i : Cell C.p₀.scheme.scheme, ¬ C.p₀.scheme.scheme.scope i ⊆ Finset.univ.image C.proj)

local notation "Inv" => requestInventory C.p₀.scheme.scheme Y C.proj Rp hR hRA hRB

/-! ## The lower-domain equation -/

/-! ## The installed row -/

/-! ## The selected section and its controller-cap compatibility -/

end ReferenceContext

end VaughtConjecture.Knight
