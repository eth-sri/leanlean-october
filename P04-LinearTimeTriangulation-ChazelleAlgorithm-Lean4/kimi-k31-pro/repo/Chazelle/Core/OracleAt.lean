module

public import Chazelle.Core.OracleRamRest

/-!
# Lemma 3.6 (WP-H), part 14: the structure in memory

`QAt P m O E V H C N B k`: the memory `m` holds at `O` the structure of Lemma 3.6 for the chain
`C` (host `H`) of the geometry polygon, its normal form `N`, the two-page book `B` of its arcs
with a cluster decomposition for `k`, all below `E` (the word `O + 3`); `V` are the values read
by the query.

Layout at `O`: `O` chain descriptor, `O + 1` normal form, `O + 2` granularity, `O + 3` the bound
`E`, `O + 4` the number `A` of arcs, `O + 5` the inverse `POS` of the arc-sequence table,
`O + 6` the flags of `D*`, `O + 7` the labels, `O + 8`, `O + 9` the list of `D*`, `O + 10`,
`O + 11` the nodes sorted by label and their ranks, `O + 12`, `O + 13` the chords sorted by
height and left end, `O + 14` a model descriptor (for double identification), `O + 15`,
`O + 16` the table of powers of two, `O + 17` the number `μ` of nodes of the book.

`OAt P m O`: `QAt` for some values, robustly below `E` (so that it survives writes above `E`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleQ

@[expose] public section

open Classical in
/-- The abscissa of the endpoint `(w, h + 1)` of a chord of class `1`. -/
noncomputable def xpX' (P : Polygon) (C : Chain) (V : QV) (w h : ℕ) : ℝ :=
  ((xpSym C V P.n w h).eval (Qof P)).1

/-- **The order of the chord table**: by height vertex, then by the class of the left end, then
by the abscissa of the left end. -/
def ChLe (P : Polygon) (C : Chain) (V : QV) (m : ℕ → ℕ) (i j : ℕ) : Prop :=
  chH m V i < chH m V j ∨ (chH m V i = chH m V j ∧
    (xpClass (chL m V i) < xpClass (chL m V j) ∨ (xpClass (chL m V i) = xpClass (chL m V j) ∧
      (xpClass (chL m V i) = 1 →
        xpX' P C V (chL m V i) (chH m V i) ≤ xpX' P C V (chL m V j) (chH m V j)))))

/-- **The structure of Lemma 3.6 in memory.** -/
structure QAt (P : Polygon) (m : ℕ → ℕ) (O E : ℕ) (V : QV) (H : Host) (C : Chain) (N : NF)
    (B : OracleBook.BookData) (k : ℕ) : Prop where
  lD : m O = V.D
  lNB : m (O + 1) = V.NB
  lE : m (O + 3) = E
  lA : m (O + 4) = V.A
  lPOS : m (O + 5) = V.POS
  lFL : m (O + 6) = V.FL
  lLAB : m (O + 7) = V.LAB
  lDL : m (O + 8) = V.DL
  lnD : m (O + 9) = V.nD
  lORD : m (O + 10) = V.ORD
  lRK : m (O + 11) = V.RK
  lCH : m (O + 12) = V.CH
  lK : m (O + 13) = V.K
  lMD : m (O + 14) = V.MD
  lTB : m (O + 15) = V.TB
  lL : m (O + 16) = V.L
  lμ : m (O + 17) = V.μ
  O_le : O + 18 ≤ E
  -- the chain
  ds : m (V.D + 1) = V.s
  dm : m (V.D + 2) = V.m
  dt : m (V.D + 3) = V.tIdx
  dβ : m (V.D + 4) = V.β
  sS : V.sS = if V.β = 1 then V.tIdx else 2 * V.m - V.tIdx
  tv : V.tv = (V.s + V.tIdx) % P.n
  desc : ChainDescAt m V.D (Qof P) H C
  CQ : C.P = Qof P
  simple : C.P.Simple
  hostLen : H.length ≤ 64
  hostWF : HostWF P.n H
  D_le : V.D + 5 ≤ E
  host_le : m V.D + 3 * H.length + 4 ≤ E
  s_lt : C.s < C.P.n
  -- the normal form
  nCB : m (V.NB + 3) = V.CB
  nAB : m (V.NB + 4) = V.AB
  nRB : m (V.NB + 5) = V.RB
  nSB : m (V.NB + 6) = V.SB
  nLB : m (V.NB + 7) = V.LB
  nf : NFAt m V.NB N
  canon : IsCanonicalNF (chainModel C) (Qof P) N (m (O + 2)) 4
  hA : V.A = N.arcs.length
  hK : V.K = N.chords.length
  regs : ∀ r, r < N.regions.length → V.RB + 5 * r + 4 < E ∧
    ∀ t, t < (N.region r).arcs.length → V.LB + m (V.RB + 5 * r + 1) + t < E
  -- the inverse of the arc-sequence table
  pos : ∀ j, j < V.A → m (V.POS + j) < V.A ∧ N.seq.getD (m (V.POS + j)) 0 = j
  POS_le : V.POS + V.A ≤ E
  -- the book and its clusters
  gOK : GraphOK C (Qof P) N B
  μ : B.N = V.μ
  FL_le : V.FL + V.μ ≤ E
  LAB_le : V.LAB + V.μ ≤ E
  hlab : ∀ u v (w : (bookGraph B).Walk u v), (∀ x ∈ w.support, m (V.FL + x) ≠ 1) →
    m (V.LAB + u) = m (V.LAB + v)
  dl : ∀ i, i < V.nD → m (V.DL + i) < V.μ ∧ m (V.FL + m (V.DL + i)) = 1
  dl_all : ∀ v, v < V.μ → m (V.FL + v) = 1 → ∃ i, i < V.nD ∧ m (V.DL + i) = v
  DL_le : V.DL + V.nD ≤ E
  nD_le : V.nD ≤ 7 * k ^ 2
  clus : ∀ l, ((Finset.range V.μ).filter fun v => m (V.FL + v) ≠ 1 ∧ m (V.LAB + v) = l).card ≤ k ^ 2
  k_pos : 1 ≤ k
  μ_le : V.μ ≤ k ^ 3
  μ_A : V.μ ≤ V.A + 3
  k_min : k = 1 ∨ (k - 1) ^ 3 < V.μ
  -- the order by label
  ord_lt : ∀ i, i < V.μ → m (V.ORD + i) < V.μ
  ord_inj : ∀ i j, i < V.μ → j < V.μ → m (V.ORD + i) = m (V.ORD + j) → i = j
  ord_rk : ∀ u, u < V.μ → m (V.RK + u) < V.μ ∧ m (V.ORD + m (V.RK + u)) = u
  ord_sorted : ∀ i j, i ≤ j → j < V.μ → m (V.LAB + m (V.ORD + i)) ≤ m (V.LAB + m (V.ORD + j))
  ORD_le : V.ORD + V.μ ≤ E
  RK_le : V.RK + V.μ ≤ E
  -- the chord table
  ch_lt : ∀ q, q < V.K → m (V.CH + q) < V.K
  ch_inj : ∀ q q', q < V.K → q' < V.K → m (V.CH + q) = m (V.CH + q') → q = q'
  ch_sorted : ∀ q q', q ≤ q' → q' < V.K → ChLe P C V m (m (V.CH + q)) (m (V.CH + q'))
  -- the table of powers
  tab : ∀ j, j < V.L → m (V.TB + j) = 2 ^ j
  A_lt : V.A < 2 ^ V.L
  K_lt : V.K < 2 ^ V.L
  L_le : V.L ≤ Nat.clog 2 (V.A + V.K) + 1
  TB_le : V.TB + V.L ≤ E
  CH_le : V.CH + V.K ≤ V.TB
  NB_TB : V.NB + 12 ≤ V.TB
  AB_TB : V.AB + 5 * V.A ≤ V.TB
  SB_TB : V.SB + V.A ≤ V.TB
  CB_TB : ∀ i, i < V.K → V.CB + 5 * i + 5 ≤ V.TB
  -- the model descriptor
  md0 : m V.MD = 0
  md : ∀ i, i < 5 → m (V.MD + 1 + i) = m (V.D + i)
  MD_le : V.MD + 6 ≤ E

/-- **The structure predicate of the oracle**: the structure, robustly below its bound. -/
def OAt (P : Polygon) (m : ℕ → ℕ) (O : ℕ) : Prop :=
  ∃ E, m (O + 3) = E ∧ O + 4 ≤ E ∧
    Robust E m fun m' => ∃ V H C N B k, QAt P m' O E V H C N B k

end

end OracleR

end Chazelle.Core
