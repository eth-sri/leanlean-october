module

public import Chazelle.Core.SweepEvStopRA
public import Chazelle.Core.SweepEvStopM3

/-!
# The sweep (WP-D), stage 2: contracts of the per-origin step, the parent scan

* `OrgTask` (RAM): the raw stop records of one origin code `(kind, k, b)`
  (registers `oKd, oKk, oB`), appended at `gRB + 11 gRC`; `RawV` the facts of a raw record.
  With `OrgTask` and `SortTask`, stage 2 is the loop over all codes (`(0, 0, b)`, `(2, 0, b)`,
  `(1, k, b)` for `k < K₂`, `b ≤ 1`), then the sort (`stopsOK_of`, `SweepEvStopL.lean`).
* `ParTask` (RAM): the scan of the chords of `N₂` for an end at a given position of the walk of
  `C₂` (the parent of a shared or top chord).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## The per-origin step -/

/-- **The facts of a raw record** `i` at `RB`: a valid record of an attachment on the `C₁` part
(`RawOK`), a `PosW` position, and the auxiliary data of its chord (`AuxOK`). -/
def RawV (P : Polygon) (J : Merge.Junction) (N : NF) (m : ℕ → ℕ) (RB i : ℕ) : Prop :=
  RawOK P J N (rawRec m RB i) (rawDc m RB i) ∧ PosW P J (rawRec m RB i).1 (rawRec m RB i).2.1 ∧
    AuxOK P J N (rSet P J N (rawRec m RB i)) (rawAux m RB i)

/-- The registers the per-origin step may write (besides the oracle bands and the allocator):
the count `gRC`, the scratch of stage 2 and the origin registers `sw 4010 … sw 4199`. -/
def SOrgR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ r = gRC ∨ (sw 3000 ≤ r ∧ r < sw 4000) ∨
    (sw 4010 ≤ r ∧ r < sw 4200) ∨ (sw 5000 ≤ r ∧ r < sw 6000)

/-- **The post of the per-origin step** for the code `(kind, k, b)` (`RC = gRC`, `RB = gRB`): at
most two new raw records `RC ≤ i < gRC'`, valid (`RawV`); if the code is admissible with a free
direction (`OrgD`), every attachment of its stop chord on the `C₁` part is one of them; the
memory below the allocator is kept except the two raw slots; registers outside `SOrgR` kept. -/
def OrgOut (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) (c c' : Config) : Prop :=
  c.nreg gRC ≤ c'.nreg gRC ∧ c'.nreg gRC ≤ c.nreg gRC + 2 ∧
    (∀ i, c.nreg gRC ≤ i → i < c'.nreg gRC → RawV P J N c'.nmem (c.nreg gRB) i) ∧
    (OrgD P J N kind k b → ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W (stopSet J (Qof P) N kind k b) p t →
      (Lst J : ℝ) ≤ oW J (p + t) → ∃ i, c.nreg gRC ≤ i ∧ i < c'.nreg gRC ∧
        (rawRec c'.nmem (c.nreg gRB) i).1 = p ∧ rPar P J (rawRec c'.nmem (c.nreg gRB) i) = t ∧
        rSet P J N (rawRec c'.nmem (c.nreg gRB) i) = stopSet J (Qof P) N kind k b) ∧
    (∀ a, a < c.nreg ALLOC → (a < c.nreg gRB + 11 * c.nreg gRC ∨
      c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ a) → c'.nmem a = c.nmem a) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ SOrgR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task O: the per-origin step** for any code `kind ≤ 2`, `b ≤ 1`, `kind = 1 → k < K₂`
(no records unless the code is admissible), with the model context of `C₂` at `gMD2, gCD2`, at
cost `κ D · (1 or K₁ + K₂ + 1) · (F γ + TLR + 1)` (the factor `K₁ + K₂ + 1` for the shared and
top codes only). -/
def OrgTask : Prop :=
  ∃ (org : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c →
      c.nreg oKd ≤ 2 → c.nreg oB ≤ 1 → (c.nreg oKd = 1 → c.nreg oKk < N₂.nChords) →
      c₀.nreg ALLOC ≤ c.nreg gRB → c.nreg gRB + 11 * (c.nreg gRC + 2) ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) ≤ W →
      IRS P W c₀ (org sh) c (κ (c₀.nreg (sw 6)) * (if c.nreg oKd = 1 then 1 else
          N₁.nChords + N₂.nChords + 1) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1))
        (OrgOut P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c)

/-! ## The parent scan -/

def pE2 : ℕ := sw 4025
def pH2 : ℕ := sw 4026
def oPar : ℕ := sw 4064

/-- The registers the parent scan may write (besides the oracle bands). -/
def ParR (r : ℕ) : Prop := r = oPar ∨ (sw 4068 ≤ r ∧ r < sw 4080)

/-- **The post of the parent scan**: `oPar = i + 1` for a chord `i` of `N₂` whose end in the
direction of code `oB` (`lpos` for `1`, `rpos` for `0`) has the key of the position
`(pE2, pH2)` of the walk of `C₂`, or `0` if there is none. -/
def ParOut (P : Polygon) (J : Merge.Junction) (N : NF) (c c' : Config) : Prop :=
  c'.nreg oPar ≤ N.nChords ∧
    (0 < c'.nreg oPar → (chainModel J.right).key (Qof P) (endPos N (c'.nreg oPar - 1)
      (1 - c.nreg oB)) = (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩) ∧
    (c'.nreg oPar = 0 → ∀ i, i < N.nChords → (chainModel J.right).key (Qof P)
      (endPos N i (1 - c.nreg oB)) ≠ (chainModel J.right).key (Qof P) ⟨c.nreg pE2, c.nreg pH2⟩) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ ParR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task P: the parent scan**, from a proper position `(pE2, pH2)` of the walk of `C₂` (code
`0` only at a tour vertex), cost `κ (K₂ + 1)`. -/
def ParTask : Prop :=
  ∃ (ps : Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg pE2 < (chainModel J.right).W.n →
      ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg pE2, c.nreg pH2⟩ →
      (c.nreg pH2 = 0 → 6 ≤ c.nreg pE2) → c.nreg oB ≤ 1 →
      c.nreg ALLOC + κ * (N₂.nChords + 1) ≤ W →
      IRS P W c₀ ps c (κ * (N₂.nChords + 1)) (ParOut P J N₂ c)

end

end SweepEv

end Chazelle.Core
