module

public import Chazelle.Core.NFDecompDepth

/-!
# Tree decomposition (WP-C), part 4: one round of the decomposition

The state `RS` of the decomposition between rounds (arrays indexed by chords or regions): removed
chords `rem`, chords cut in the previous round `pend`, active components `act` (at their tops),
the pending parent slot of each active component (`cpar`, `side`: `0` low, `1` high, `2` the root),
the decomposition nodes `dpar`, `dlo`, `dhi`, the leaf parents `lpar`, the root code and the number
`fin` of finished leaves.

`next` is one round, given the tops and best candidates of the top pass: the **chord pass** (a
chord cut in the previous round receives the codes of its two child components; a chord chosen
now is removed, marked pending and gets its parent code), the **root step**, and the **region
pass** (finished singletons get their leaf parent; cut components and the new components record
their pending slots).  Every entry is computed from the old state at its own index, as the RAM
loops do.

`RInv` is the round invariant; `rinv_next` is its preservation.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

set_option linter.unusedSectionVars false

/-- The state of the decomposition between rounds. -/
structure RS where
  /-- Removed chords (`1`). -/
  rem : ℕ → ℕ
  /-- Chords cut in the previous round (`1`). -/
  pend : ℕ → ℕ
  /-- Active components, at their tops (`1`). -/
  act : ℕ → ℕ
  /-- The chord of the pending parent slot of an active component. -/
  cpar : ℕ → ℕ
  /-- The side of the pending slot: `0` low, `1` high, `2` the root. -/
  side : ℕ → ℕ
  /-- Decomposition nodes: parent code. -/
  dpar : ℕ → ℕ
  /-- Decomposition nodes: low child code. -/
  dlo : ℕ → ℕ
  /-- Decomposition nodes: high child code. -/
  dhi : ℕ → ℕ
  /-- Leaf parents. -/
  lpar : ℕ → ℕ
  /-- The root code. -/
  root : ℕ
  /-- The number of finished leaves. -/
  fin : ℕ

/-- The code of the component with top `x` in the current round: its leaf if it is a singleton,
otherwise the node of the chord cut in it. -/
def code (best pch : ℕ → ℕ) (x : ℕ) : ℕ := if best x = x then 2 * x + 1 else 2 * pch (best x)

/-- Chord `e` is cut in this round. -/
abbrev Chosen (σ : RS) (top best chOf : ℕ → ℕ) (e : ℕ) : Prop :=
  σ.rem e ≠ 1 ∧ σ.act (top (chOf e)) = 1 ∧ best (top (chOf e)) = chOf e

/-- The top of the low child component of a chord cut in the previous round. -/
def loTop (prg isdn chOf top : ℕ → ℕ) (e : ℕ) : ℕ :=
  if isdn (chOf e) = 1 then chOf e else top (prg (chOf e))

/-- The top of the high child component of a chord cut in the previous round. -/
def hiTop (prg isdn chOf top : ℕ → ℕ) (e : ℕ) : ℕ :=
  if isdn (chOf e) = 1 then top (prg (chOf e)) else chOf e

/-- Chord pass: the new `pend`. -/
def nPend (K : ℕ) (chOf top best : ℕ → ℕ) (σ : RS) (e : ℕ) : ℕ :=
  if e < K then (if σ.pend e = 1 then 0 else if Chosen σ top best chOf e then 1 else σ.pend e)
  else σ.pend e

/-- One round of the decomposition. -/
def next (R K : ℕ) (prg pch isdn chOf top best : ℕ → ℕ) (σ : RS) : RS where
  rem e := if e < K then (if σ.pend e = 1 then σ.rem e else
    if Chosen σ top best chOf e then 1 else σ.rem e) else σ.rem e
  pend := nPend K chOf top best σ
  dpar e := if e < K then (if σ.pend e = 1 then σ.dpar e else
    if Chosen σ top best chOf e then
      (if σ.side (top (chOf e)) = 2 then 2 * e else 2 * σ.cpar (top (chOf e)))
    else σ.dpar e) else σ.dpar e
  dlo e := if e < K then (if σ.pend e = 1 then code best pch (loTop prg isdn chOf top e)
    else σ.dlo e) else σ.dlo e
  dhi e := if e < K then (if σ.pend e = 1 then code best pch (hiTop prg isdn chOf top e)
    else σ.dhi e) else σ.dhi e
  act r := if r < R then (if top r = r then (if σ.act r = 1 then (if best r = r then 0 else σ.act r)
      else σ.act r)
    else if nPend K chOf top best σ (pch r) = 1 then 1 else σ.act r) else σ.act r
  cpar r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then σ.cpar r else pch (best r)) else σ.cpar r)
    else if nPend K chOf top best σ (pch r) = 1 then pch r else σ.cpar r) else σ.cpar r
  side r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then σ.side r else (if isdn (best r) = 1 then 1 else 0)) else σ.side r)
    else if nPend K chOf top best σ (pch r) = 1 then (if isdn r = 1 then 0 else 1) else σ.side r)
    else σ.side r
  lpar r := if r < R then (if top r = r then (if σ.act r = 1 then
      (if best r = r then (if σ.side r = 2 then 2 * r + 1 else 2 * σ.cpar r) else σ.lpar r)
      else σ.lpar r) else σ.lpar r) else σ.lpar r
  root := if σ.act 0 = 1 then (if σ.side 0 = 2 then code best pch 0 else σ.root) else σ.root
  fin := σ.fin + ((range R).filter (fun r => top r = r ∧ σ.act r = 1 ∧ best r = r)).card

/-! ## The invariant -/

/-- Region `v` is on side `s` (`0` low, `1` high) of chord `e`: in the subtree of the child
endpoint `chOf e` iff that endpoint is the low endpoint (`isdn`) exactly when `s = 0`. -/
def OnSide (R : ℕ) (prg pch isdn chOf : ℕ → ℕ) (s e v : ℕ) : Prop :=
  AncX R prg pch rem0 (chOf e) v ↔ (isdn (chOf e) = 1 ↔ s = 0)

open Classical in
/-- The regions on side `s` of chord `e`. -/
noncomputable def sideSet (R : ℕ) (prg pch isdn chOf : ℕ → ℕ) (s e : ℕ) : Finset ℕ :=
  (range R).filter (OnSide R prg pch isdn chOf s e)

/-- The regions below a code (ghost `gc` for chord nodes). -/
def compOf (gc : ℕ → Finset ℕ) (x : ℕ) : Finset ℕ := if x % 2 = 0 then gc (x / 2) else {x / 2}

/-- The parent code of a code. -/
def pcode (σ : RS) (x : ℕ) : ℕ := if x % 2 = 0 then σ.dpar (x / 2) else σ.lpar (x / 2)

/-- A code already placed: a removed chord, or a finished leaf. -/
def ValidC (R K : ℕ) (pch : ℕ → ℕ) (σ : RS) (x : ℕ) : Prop :=
  (x % 2 = 0 ∧ x / 2 < K ∧ σ.rem (x / 2) = 1) ∨
    (x % 2 = 1 ∧ x / 2 < R ∧ IsTop pch σ.rem (x / 2) ∧ σ.act (x / 2) ≠ 1)

/-- **The round invariant** at the start of round `j`, with ghosts `gc` (the component in which a
removed chord was cut) and `cr` (the round in which it was cut). -/
structure RInv (R K D : ℕ) (prg pch isdn chOf : ℕ → ℕ) (j : ℕ) (σ : RS) (gc : ℕ → Finset ℕ)
    (cr : ℕ → ℕ) : Prop where
  i0 : ∀ e, e < K → σ.pend e = 1 → σ.rem e = 1
  i1 : ∀ e, e < K → σ.rem e = 1 →
    gc e ⊆ range R ∧ chOf e ∈ gc e ∧ prg (chOf e) ∈ gc e ∧ cr e < j ∧ cr e < rounds D K ∧
    ((σ.dpar e = 2 * e ∧ cr e = 0 ∧ σ.root = 2 * e ∧ gc e = range R) ∨
      (∃ p, p < K ∧ σ.rem p = 1 ∧ σ.dpar e = 2 * p ∧ cr p + 1 = cr e ∧ gc e ⊆ gc p))
  i2 : ∀ e, e < K → σ.rem e = 1 → σ.pend e ≠ 1 → ∀ s, s ≤ 1 →
    ValidC R K pch σ (if s = 0 then σ.dlo e else σ.dhi e) ∧
    compOf gc (if s = 0 then σ.dlo e else σ.dhi e) = gc e ∩ sideSet R prg pch isdn chOf s e ∧
    pcode σ (if s = 0 then σ.dlo e else σ.dhi e) = 2 * e
  i3 : ∀ e, e < K → σ.pend e = 1 → cr e + 1 = j ∧ ∀ s, s ≤ 1 → ∃ t, t < R ∧
    IsTop pch σ.rem t ∧ σ.act t = 1 ∧ σ.cpar t = e ∧ σ.side t = s ∧
    sub R prg pch σ.rem t = gc e ∩ sideSet R prg pch isdn chOf s e
  i4 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 →
    (σ.side t = 2 ∧ t = 0 ∧ j = 0) ∨
    (σ.side t ≤ 1 ∧ σ.cpar t < K ∧ σ.pend (σ.cpar t) = 1 ∧
      sub R prg pch σ.rem t = gc (σ.cpar t) ∩ sideSet R prg pch isdn chOf (σ.side t) (σ.cpar t))
  i5 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t ≠ 1 →
    sub R prg pch σ.rem t = {t} ∧
    ((σ.lpar t = 2 * t + 1 ∧ σ.root = 2 * t + 1 ∧ K = 0) ∨
      (∃ p, p < K ∧ σ.rem p = 1 ∧ σ.lpar t = 2 * p ∧ cr p + 1 ≤ rounds D K ∧ t ∈ gc p))
  i6 : ∀ t, t < R → IsTop pch σ.rem t → σ.act t = 1 →
    sz R prg pch σ.rem t ≤ (hstep D)^[j] K + 1 ∧ (j = 0 ∨ 1 ≤ (hstep D)^[j - 1] K)
  i7 : j = 0 → (∀ e, e < K → σ.rem e ≠ 1) ∧ σ.act 0 = 1 ∧ σ.side 0 = 2
  i8 : 1 ≤ j → ValidC R K pch σ σ.root ∧ compOf gc σ.root = range R ∧ pcode σ σ.root = σ.root
  i9 : σ.fin = ((range R).filter (fun t => IsTop pch σ.rem t ∧ σ.act t ≠ 1)).card

end

end Chazelle.Core.Dec
