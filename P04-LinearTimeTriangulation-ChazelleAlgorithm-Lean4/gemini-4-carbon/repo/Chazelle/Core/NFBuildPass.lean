module

public import Chazelle.Core.NFBuildPassMath
public import Chazelle.Core.NFBuildPassGap

/-!
# WP-C (BuildNF), RAM part 13: the invariant of the main pass

`PassFix`: the fixed data of the pass (inputs below `H`, table layout, counted interval);
`PassInv m`: after `m` codes, the stack holds `stk E m`, the chord records of the chords met so far
and the arc records (with weights) of the gap starts below `m` are written.
`passBody_step`: one iteration keeps the invariant.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open BuildNF (wposOf chordRec arcRec arcW cw stk topR gapP gapsB cf af)

@[expose] public section

/-- The fixed data of the main pass. -/
structure PassFix (P : Polygon) (W : ℕ) (M : Model) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (D H T SE B CT AT ST WT lo hd : ℕ) (mB : ℕ → ℕ) : Prop where
  inp : BuildNF.Input M (Qof P) L E
  good : GoodEnv P
  hwords : hostWords P.n ≤ W
  len : E.length = 2 * L.length
  wf : ModelDescWF P H mB D
  desc : ModelDescAt mB D (Qof P) M
  HW : H ≤ W
  recs : RecsAt mB T L
  TH : T + 8 * L.length ≤ H
  chl : ChordListAt mB B L
  BH : B + 3 * L.length ≤ H
  codes : ∀ j, j < E.length → mB (SE + j) = E.getD j 0
  SEH : SE + E.length ≤ H
  l1 : H ≤ CT
  l2 : CT + 5 * L.length ≤ AT
  l3 : AT + 5 * E.length ≤ ST
  l4 : ST + E.length ≤ WT
  l5 : WT + E.length ≤ W
  cnt : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < lo + hd)
  cntW : lo + hd ≤ M.W.n

/-- The registers the main pass writes. -/
def Bpass (r : ℕ) : Bool :=
  Bgap r || Bstep r || decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨ r = 42112 ∨
    r = 43113 ∨ r = 43114 ∨ r = 43115 ∨ r = 43116 ∨ r = 43117 ∨ r = 43100 ∨ r = 43103)

/-- **The invariant of the main pass** after `m` codes. -/
structure PassInv {P : Polygon} {W : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {D H T SE B CT AT ST WT lo hd : ℕ} {mB : ℕ → ℕ}
    (F : PassFix P W M L E D H T SE B CT AT ST WT lo hd mB) (c₀ d : Config) (m : ℕ) : Prop where
  m_le : m ≤ E.length
  r100 : d.nreg 43100 = m
  r103 : d.nreg 43103 = SE + m
  r104 : d.nreg 43104 = SE
  r101 : d.nreg 43101 = (stk E m).length
  sp_le : (stk E m).length ≤ m
  r102 : d.nreg 43102 = (gapsB M (Qof P) L E m).length
  rD : d.nreg 40000 = D
  rT : d.nreg 42000 = T
  rN : d.nreg 42001 = E.length
  r1a : d.nreg 42102 = 1
  rB : d.nreg 43001 = B
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  rCT : d.nreg 44001 = CT
  rAT : d.nreg 44002 = AT
  rST : d.nreg 44006 = ST
  rWT : d.nreg 44007 = WT
  rlo : d.nreg 44020 = lo
  rhd : d.nreg 44021 = hd
  r19 : d.nreg 41019 = 1
  r23 : d.nreg 41023 = mB D
  low : ∀ a, a < H → d.nmem a = mB a
  stack : ∀ k, k < (stk E m).length → d.nmem (ST + k) = (stk E m).getD k 0 + 1
  chords : ∀ x, x < L.length → x ∈ (cw E).take m → ∀ f, f < 5 →
    d.nmem (CT + 5 * x + f) = cf (chordRec M (Qof P) L E x) f
  arcs : ∀ j, j < (gapsB M (Qof P) L E m).length →
    (∀ f, f < 5 → d.nmem (AT + 5 * j + f) =
      af (arcRec M (Qof P) L E ((gapsB M (Qof P) L E m).getD j 0)) f) ∧
    d.nmem (WT + j) = arcW M (Qof P) (arcRec M (Qof P) L E ((gapsB M (Qof P) L E m).getD j 0))
  frame : FrameM Bpass c₀ d

end

end BuildRam

end Chazelle.Core
