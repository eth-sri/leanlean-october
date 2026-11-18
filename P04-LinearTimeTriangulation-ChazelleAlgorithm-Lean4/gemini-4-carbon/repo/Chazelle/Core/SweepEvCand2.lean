module

public import Chazelle.Core.SweepEvOffer
public import Chazelle.Core.SweepEvCand3

/-!
# The sweep (WP-D), stage 3: one candidate (RAM)

`evCand sh g`: the shot from the origin (`evShot`), and if it hits with an arrival: the
genuineness check `g` (bit `cG`, a reverse local hit, `GenOK`), the far-end test (`farChk`), the
map to the walk of `C` (`mapC`, `mapE`), the table write (`tabW`) and the offer (`offerC`).

`CandRes`: rejected (memory and best candidate unchanged) or accepted at a position `(e, h)` with
`CandOK` (table record `j` written, offered).  Completeness (`evCand_irs`): a chord of `C` from the
origin ending on the `C₁` part (beyond the start, before the far end of the chord of `C₂`), whose
hit lies on the gathered arcs, is accepted at its attachment.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)

@[expose] public section

def cG : ℕ := sw 2250

/-- The registers the genuineness check may write. -/
def GR (r : ℕ) : Prop := (sw 700 ≤ r ∧ r < sw 2200) ∨ r = cG ∨ (sw 3000 ≤ r ∧ r < sw 4000)

/-- **The contract of the genuineness check** `g` (cost `KG`): from an arrival position
`(eA + 1, eA + 2)` of the hit `rayPt a σ τ` of `C₁` (direction code `oD`, abscissa record of `a`
at `oAbsA`), the bit `cG` tells whether the hit is genuine. -/
def GenOK (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (g : Stmt) (KG : ℕ) : Prop :=
  ∀ (c₁ : Config) (a : Point) (σ τ : ℝ), IInv W c₀ c₁ → c₁.nreg ALLOC + KG ≤ W →
    c₁.nreg oD ≤ 1 → σ = dirOf (c₁.nreg oD) → AbsRec P c₁ oAbsA a.1 J.left.radius →
    a ∈ J.right.set → a ≠ J.shared → a.2 ≤ J.left.top.2 → 0 < τ →
    c₁.nreg (eA + 1) < (chainModel J.left).W.n →
    ProperPos (chainModel J.left) (Qof P) P.n ⟨c₁.nreg (eA + 1), c₁.nreg (eA + 2)⟩ →
    Arrival (chainModel J.left).W (rayPt a σ τ) σ (c₁.nreg (eA + 1))
      ((chainModel J.left).param (Qof P) ⟨c₁.nreg (eA + 1), c₁.nreg (eA + 2)⟩) →
    IRS P W c₀ g c₁ KG (fun c' => BitIs c' cG (Genuine J.left a σ τ) ∧ EFr GR c₁ c')

/-- The tail after a genuine hit before the far end. -/
def evAccT : Stmt := .seq mapC (.ifLtN K0 cV (.seq mapE (.seq tabW offerC)) .skip)

/-- **One candidate.** -/
def evCand (sh g : Stmt) : Stmt :=
  .seq (evShot sh) (.ifLtN K0 eF (.ifLtN K0 eA (.seq g (.ifLtN K0 cG
    (.seq farChk (.ifLtN K0 cFr evAccT .skip)) .skip)) .skip) .skip)

/-- The table after writing the record `j`. -/
def tabUpd (m : ℕ → ℕ) (T j e h : ℕ) : ℕ → ℕ :=
  upd (upd (upd m (T + 3 * j) 1) (T + 3 * j + 1) e) (T + 3 * j + 2) h

/-- **The offer relation** for a candidate `(e, h)` with labels `u, d`. -/
def OfferRel (P : Polygon) (J : Merge.Junction) (c c' : Config) (e h u d : ℕ) : Prop :=
  c'.nreg bF ≤ 1 ∧ c'.nreg bN ≤ 4 ∧
  (¬ offK P J (c.nreg kE) (c.nreg kH) < offK P J e h → BestSame c c') ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J e h →
    (c.nreg bF ≠ 1 ∨ offK P J e h < offK P J (c.nreg bE) (c.nreg bH)) →
    c'.nreg bF = 1 ∧ c'.nreg bE = e ∧ c'.nreg bH = h ∧ lblOf c' bN bL = [u, d] ∧ c'.nreg bN = 2) ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J e h → c.nreg bF = 1 →
    offK P J e h = offK P J (c.nreg bE) (c.nreg bH) →
    c'.nreg bF = 1 ∧ c'.nreg bE = c.nreg bE ∧ c'.nreg bH = c.nreg bH ∧
    lblOf c' bN bL = addL (addL (lblOf c bN bL) u) d) ∧
  (offK P J (c.nreg kE) (c.nreg kH) < offK P J e h → c.nreg bF = 1 →
    offK P J (c.nreg bE) (c.nreg bH) < offK P J e h → BestSame c c')

/-- A rejected candidate: memory below the allocator and best candidate unchanged. -/
def RejAt (c c' : Config) : Prop :=
  (∀ x, x < c.nreg ALLOC → c'.nmem x = c.nmem x) ∧ BestSame c c'

/-- A candidate accepted at the position `(e, h)`. -/
def AccAt (P : Polygon) (J : Merge.Junction) (S₂ : Set (Set Point)) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (c c' : Config) (e h : ℕ) : Prop :=
  CandOK P J S₂ a σ e h ∧ (∀ x, x < c.nreg ALLOC → c'.nmem x = tabUpd c.nmem T j e h x) ∧
    OfferRel P J c c' e h u d

/-- **The result of a candidate**: rejected, or accepted at a position with `CandOK`. -/
def CandRes (P : Polygon) (J : Merge.Junction) (S₂ : Set (Set Point)) (T j u d : ℕ) (a : Point)
    (σ : ℝ) (c c' : Config) : Prop :=
  RejAt c c' ∨ ∃ e h, AccAt P J S₂ T j u d a σ c c' e h

/-- The registers a candidate may write. -/
def CandR (r : ℕ) : Prop :=
  (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 2240 ≤ r ∧ r ≤ sw 2283) ∨ BestR r ∨ (sw 3000 ≤ r ∧ r < sw 4000)

end

end SweepEv

end Chazelle.Core
