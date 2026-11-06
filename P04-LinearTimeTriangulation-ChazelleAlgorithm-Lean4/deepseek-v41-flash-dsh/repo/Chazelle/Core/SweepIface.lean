module

public import Chazelle.Core.SweepMachine21
public import Chazelle.Core.SweepRamLog

/-!
# The sweep (WP-D): interfaces between the stages (finding S-1 design)

One sweep, along the `C₁` part of the walk of `C = J.whole` (side `0` of the old design), serves
both sides of `SweepSpec` (finding S-1).  Its stages communicate through the following
**mathematical** interfaces (this file) and the memory layouts below.  Notation:
`M = chainModel J.whole`, `M₂ = chainModel J.right`, `F = F₂plus J S₂`, offsets `oW` from the base
`gW = 6 + tpos J.whole J.m₁` (the copy of the shared vertex on the `C₂` side); the right stretch is
`(0, Lst)`, the `C₁` part is `[Lst, n)`.

* **Stage 2 → 3: stops** (`StopsOK`).  The *stop chords* (`StopChord2`) are the chords of `F`
  that the detection of stage 3 does not find: the shared chords (from the shared vertex), the
  wall pieces (from a box-wall endpoint of a chord of `S₂`), and the top chords (from the top of
  `C₂`).  The stop list is the sorted list of **all** their attachments on the `C₁` part.
* **Stage 3 → 4: the event log** (`LogOK`).  Keys of the `C₁` part in increasing offset, starting
  at the start key (offset `Lst`), with no cut of `F` strictly between consecutive keys or after
  the last one, each with a finite **label set** `Λ` containing every label of the region faced
  just after the key (up to the two gap labels, `GapLab`).  So every cut of the `C₁` part is a key.
* **Stage 3 → side-1 answers: the endpoint table** (`TabOK`).  For the endpoint query `j` of the
  chord `j / 2` of `N₂` (origin `a` its left end shooting east for even `j`, its right end shooting
  west for odd `j`): if the chord of `C` seen from `a` meets `C₁` first, the table holds the
  position of its far attachment (a key of the `C₁` part); otherwise it holds nothing and the
  chord seen from `a` in `C` is the one seen in `C₂`.

## Memory layouts (stage outputs, fresh memory at the allocator)

* stops: `5` words per record `(e, h, kind, k, b)`: the position `⟨e, h⟩` of the walk of `C`
  (`h` a height code), `kind` `0` shared / `1` wall piece / `2` top, `k` the chord index of `N₂`
  (wall pieces), `b` the direction code (`dirOf b`); the chord is `stopSet`.
* log: `7` words per record `(e, h, n, l₀, l₁, l₂, l₃)`: the key `⟨e, h⟩`, the number `n ≤ 4`
  of labels and the region indices `l₀ … l_{n-1}` of `N₂` (`regOf`); see `LogRecsAt`.
* table: `3` words per endpoint query `(f, e, h)`: `f = 1` and the position `⟨e, h⟩`, or `f = 0`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

variable (J : Merge.Junction)

/-! ## Offsets -/

/-- The base of the offsets: the copy of the shared vertex on the `C₂` side. -/
noncomputable def gW : ℕ := 6 + tpos J.whole J.m₁

/-- The offset of a key of the walk of `C`. -/
noncomputable def oW (x : ℝ) : ℝ := off (chainModel J.whole).W.n (gW J : ℝ) x

/-- The length of the right stretch: the `C₁` part is the offsets `[Lst, n)`. -/
noncomputable def Lst : ℕ := rL1 J + rL2 J

/-- No cut of `F₂⁺` has its offset strictly between `a` and `b`. -/
def NoCutIn (S₂ : Set (Set Point)) (a b : ℝ) : Prop :=
  ∀ x, (chainModel J.whole).IsCut (F₂plus J S₂) x → 0 ≤ x → x < (chainModel J.whole).W.n →
    ¬ (a < oW J x ∧ oW J x < b)

/-- **The label set** `Λ` contains every label of the region faced just after `(p, t)`, up to the
gap labels. -/
def LabIn (S₂ : Set (Set Point)) (p : ℕ) (t : ℝ) (Λ : Set (Set Point)) : Prop :=
  ∀ G ∈ (chainModel J.whole).regions (F₂plus J S₂), AfterFaces (chainModel J.whole) p t G →
    ∀ V ∈ (chainModel J.right).regions S₂, RLabel J S₂ G V → V ∈ Λ ∨ GapLab J S₂ V

/-! ## Stage 3 → 4: the event log -/

/-- **The event log** (keys `(p, t)` of the walk of `C`, label sets). -/
def LogOK (S₂ : Set (Set Point)) (es : List (ℕ × ℝ × Set (Set Point))) : Prop :=
  es ≠ [] ∧
  (∀ x ∈ es, x.1 < (chainModel J.whole).W.n ∧ 0 ≤ x.2.1 ∧ x.2.1 < 1 ∧
    (Lst J : ℝ) ≤ oW J (x.1 + x.2.1)) ∧
  (∀ x ∈ es.head?, oW J (x.1 + x.2.1) = Lst J) ∧
  es.Pairwise (fun x y => oW J (x.1 + x.2.1) < oW J (y.1 + y.2.1)) ∧
  (∀ i, i + 1 < es.length →
    NoCutIn J S₂ (oW J ((es.getD i (0, 0, ∅)).1 + (es.getD i (0, 0, ∅)).2.1))
      (oW J ((es.getD (i + 1) (0, 0, ∅)).1 + (es.getD (i + 1) (0, 0, ∅)).2.1))) ∧
  (∀ x ∈ es.getLast?, NoCutIn J S₂ (oW J (x.1 + x.2.1)) (chainModel J.whole).W.n) ∧
  ∀ x ∈ es, LabIn J S₂ x.1 x.2.1 x.2.2

/-! ## Stage 2 → 3: the stops -/

/-- **The stop chords**: the shared chords and the wall pieces (`StopChord`), and the top chords
(chords of `C` through the top of `C₂`, shot from it). -/
def StopChord2 (S₂ : Set (Set Point)) (e : Set Point) : Prop :=
  StopChord J S₂ e ∨
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ FreeAt J.whole J.right.top σ ∧
      e = Merge.shoot J.whole J.right.top σ

/-- **The stop list**: exactly the attachments on the `C₁` part of the stop chords of `F₂⁺`,
sorted by offset (keys `(p, t)` and chords). -/
def StopsOK (S₂ : Set (Set Point)) (ss : List (ℕ × ℝ × Set Point)) : Prop :=
  (∀ s ∈ ss, s.2.2 ∈ F₂plus J S₂ ∧ StopChord2 J S₂ s.2.2 ∧
    SideAttach (chainModel J.whole).W s.2.2 s.1 s.2.1 ∧ (Lst J : ℝ) ≤ oW J (s.1 + s.2.1)) ∧
  (∀ e ∈ F₂plus J S₂, StopChord2 J S₂ e → ∀ (p : ℕ) (t : ℝ),
    SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J (p + t) → (p, t, e) ∈ ss) ∧
  ss.Pairwise (fun x y => oW J (x.1 + x.2.1) ≤ oW J (y.1 + y.2.1)) ∧ ss.Nodup

/-! ## Stage 3 → side-1 answers: the endpoint table -/

/-- The origin of the endpoint query `j` of a chord list in the model `M₂`: the left end of chord
`j / 2` for even `j`, its right end for odd `j`. -/
noncomputable def endOrigin (Q : Polygon) (N : NF) (j : ℕ) : Point :=
  if j % 2 = 0 then Merge.lend ((N.chord (j / 2)).toSet (chainModel J.right) Q)
  else Merge.rend ((N.chord (j / 2)).toSet (chainModel J.right) Q)

/-- The direction of the endpoint query `j` (east for even `j`). -/
noncomputable def endDir (j : ℕ) : ℝ := if j % 2 = 0 then 1 else -1

/-- **The endpoint table** for the chords of `N₂` whose origin is a point of `C₂` other than the
shared vertex and the top of `C₂` (the other origins give stop chords): `some (p, t)` is the far
attachment, on the `C₁` part, of the chord of `C` seen from the origin; `none` says that this chord
does not end on `C₁` (it is the chord seen in `C₂`). -/
def TabOK (Q : Polygon) (N : NF) (T : ℕ → Option (ℕ × ℝ)) : Prop :=
  ∀ j, j < 2 * N.nChords → endOrigin J Q N j ∈ J.right.set → endOrigin J Q N j ≠ J.shared →
    endOrigin J Q N j ≠ J.right.top →
    FreeAt J.whole (endOrigin J Q N j) (endDir j) ∧
    match T j with
    | some (p, t) =>
        SideAttach (chainModel J.whole).W
            (Merge.shoot J.whole (endOrigin J Q N j) (endDir j)) p t ∧
          sidePt (chainModel J.whole).W p t =
            rayPt (endOrigin J Q N j) (endDir j)
              (J.whole.hitParam (endOrigin J Q N j) (endDir j)) ∧
          (Lst J : ℝ) ≤ oW J (p + t)
    | none => J.whole.hitParam (endOrigin J Q N j) (endDir j) =
        J.right.hitParam (endOrigin J Q N j) (endDir j)

/-! ## Region indices of a normal form -/

/-- The region correspondence of a valid normal form (a fixed choice; proofs only). -/
noncomputable def regOf (M : Model) (Q : Polygon) (N : NF) : ℕ → Set Point := by
  classical
  exact if h : IsNF M Q N then Classical.choose h.2.2.2 else fun _ => ∅

theorem regOf_spec {M : Model} {Q : Polygon} {N : NF} (h : IsNF M Q N) :
    RegionCorr M Q N (regOf M Q N) ∧ ChordSidesOK M Q N (regOf M Q N) ∧
      ArcsOK M Q N (regOf M Q N) ∧ RegionsOK M Q N (regOf M Q N) ∧ SeqOK M Q N ∧
      (∀ i, i < N.nChords → (N.chord i).h < Q.n) ∧
      ∀ j, j < N.arcs.length → ProperPos M Q Q.n (N.arc j).s ∧ ProperPos M Q Q.n (N.arc j).e := by
  classical
  unfold regOf
  rw [dite_eq_left h]
  exact Classical.choose_spec h.2.2.2

/-! ## Memory layouts -/

/-- The chord of a stop record: kind `0` shared, `1` wall piece of chord `k`, `2` top. -/
noncomputable def stopSet (Q : Polygon) (N : NF) (kind k b : ℕ) : Set Point :=
  if kind = 0 then Merge.shoot J.whole J.shared (dirOf b)
  else if kind = 1 then
    Merge.shoot J.whole (endOrigin J Q N (2 * k + (if dirOf b = 1 then 0 else 1))) (dirOf b)
  else Merge.shoot J.whole J.right.top (dirOf b)

/-- `S` stop records of five words at `A`. -/
def StopRecsAt (m : ℕ → ℕ) (A : ℕ) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < rs.length →
    m (A + 5 * i) = (rs.getD i (0, 0, 0, 0, 0)).1 ∧
    m (A + 5 * i + 1) = (rs.getD i (0, 0, 0, 0, 0)).2.1 ∧
    m (A + 5 * i + 2) = (rs.getD i (0, 0, 0, 0, 0)).2.2.1 ∧
    m (A + 5 * i + 3) = (rs.getD i (0, 0, 0, 0, 0)).2.2.2.1 ∧
    m (A + 5 * i + 4) = (rs.getD i (0, 0, 0, 0, 0)).2.2.2.2

/-- The stop list of the records. -/
noncomputable def stopsOf (Q : Polygon) (N : NF) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    List (ℕ × ℝ × Set Point) :=
  rs.map fun r => (r.1, (chainModel J.whole).param Q ⟨r.1, r.2.1⟩,
    stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2)

/-- `E` log records of seven words at `A`: key `(e, h)`, label count `n ≤ 4`, four labels. -/
def LogRecsAt (m : ℕ → ℕ) (A : ℕ) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < rs.length →
    m (A + 7 * i) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).1 ∧
    m (A + 7 * i + 1) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.1 ∧
    m (A + 7 * i + 2) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.1 ∧
    m (A + 7 * i + 3) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.1 ∧
    m (A + 7 * i + 4) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.1 ∧
    m (A + 7 * i + 5) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.1 ∧
    m (A + 7 * i + 6) = (rs.getD i (0, 0, 0, 0, 0, 0, 0)).2.2.2.2.2.2

/-- The label set of a log record: the regions (`regOf`) of its first `n ≤ 4` labels. -/
noncomputable def labSet (Q : Polygon) (N : NF) (n l₀ l₁ l₂ l₃ : ℕ) : Set (Set Point) :=
  (regOf (chainModel J.right) Q N) ''
    {l | (0 < n ∧ l = l₀) ∨ (1 < n ∧ l = l₁) ∨ (2 < n ∧ l = l₂) ∨ (3 < n ∧ l = l₃)}

/-- The event log of the records. -/
noncomputable def logOf (Q : Polygon) (N : NF) (rs : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    List (ℕ × ℝ × Set (Set Point)) :=
  rs.map fun r => (r.1, (chainModel J.whole).param Q ⟨r.1, r.2.1⟩,
    labSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2)

/-- The endpoint table at `A`: three words `(f, e, h)` per query. -/
noncomputable def tabOf (Q : Polygon) (m : ℕ → ℕ) (A : ℕ) (j : ℕ) : Option (ℕ × ℝ) :=
  if m (A + 3 * j) = 1 then
    some (m (A + 3 * j + 1), (chainModel J.whole).param Q ⟨m (A + 3 * j + 1), m (A + 3 * j + 2)⟩)
  else none

end Sweep

end

end Chazelle.Core
