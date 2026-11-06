module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBArc
public import Chazelle.Core.DownPhaseBaseSpec
public import Chazelle.Core.DownPhaseDrvRBktM
public import Chazelle.Core.RestoreDrvProg
public import Chazelle.Core.DownPhaseDrvRInv

/-!
# Down-phase base (D9): the contract of the region loop

The base case is split in two parts:

* **the region loop** (`RegLoopSpec`): for every region `r < K + 1` of the
  current normal form `N = buildNF I Q L E` (or the whole walk when `K = 0`), the vertex chords
  missing from the family whose domain part lies in the region (`regList`), appended to the new
  chord list `L₂ = newLB` at `B₂ = r212019`, with the buckets of their ends at `B₂ + 6 n`;
* **the top level** (prealloc, the splice `DrvR.splS`, `dropAug`, `buildNFSorted`, the cost):
  turns `RegLoopSpec` into `DrvR.BaseSpec`.

Registers of the contract (band `bDownDrv`):

* inputs: `210001` the model descriptor `MD`, `210003` the chord count `K`, `210005` the handle
  `H` of `N`, `212019` the base `B₂` of a reserved area `[B₂, B₂ + 10 n)` below the allocator;
* outputs: `216020` the number `K₂` of new chords, `212018` a bound `MX` on the number of points
  of a region (the buckets hold at most `4 MX` codes each); the registers `210000 … 210029` and
  `212019` are kept; the frame is `Restore.RF DrvR.drvBands B₂` (memory below `B₂` kept).

The cost is `κ (K + 1) (S₀ + 1) (Cm + 1)` for bounds `S₀` on the number of points of a region
and `Cm` on the number of walk edges of an arc (or `n` when `K = 0`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt
open BuildNF (codeLe)

@[expose] public section

/-- **The walk-order points of region `r`** (the whole walk when `K = 0`). -/
noncomputable def ptsB (li : Bool) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (r : ℕ) :
    List SymPt :=
  if L.length = 0 then wlist li (Host.pts Q.n [HostItem.run 0 (Q.n - 1)])
  else regPts li Q.n (BuildNF.buildNF (interiorModel Q) Q L E) r

/-- **The new chords, tagged by their region.** -/
noncomputable def tagLB (li : Bool) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    List (ℕ × (ℕ × ℕ × ℕ)) :=
  (List.range (L.length + 1)).flatMap fun r => (regList li Q (ptsB li Q L E r)).map fun x => (r, x)

/-- **The new chords of the base case** (`newL` for `K > 0`, `newL0` for `K = 0`). -/
noncomputable def newLB (li : Bool) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    List (ℕ × ℕ × ℕ) :=
  (tagLB li Q L E).map Prod.snd

theorem newLB_eq_flatMap (li : Bool) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    newLB li Q L E = (List.range (L.length + 1)).flatMap fun r => regList li Q (ptsB li Q L E r) := by
  unfold newLB tagLB
  Ξ List.map_flatMap
  congr 1
  funext r
  Ξ List.map_map
  exact List.map_id' _

/-- **`newLB` is `newL`** for `K > 0`. -/
theorem newLB_pos (li : Bool) (Q : Polygon) {L : List (ℕ × ℕ × ℕ)} (E : List ℕ)
    (hK : 0 < L.length) :
    newLB li Q L E = newL li Q (BuildNF.buildNF (interiorModel Q) Q L E) := by
  Ξ newLB_eq_flatMap
  unfold newL
  have hR : (BuildNF.buildNF (interiorModel Q) Q L E).nRegions = L.length + 1 := by
    Θ NF.nRegions, BuildNF.buildNF
  Ξ hR
  congr 1
  funext r
  unfold ptsB
  rw [ite_eq_right (⋄)]

/-- **`newLB` is `newL0`** for `K = 0`. -/
theorem newLB_zero (li : Bool) (Q : Polygon) {L : List (ℕ × ℕ × ℕ)} (E : List ℕ)
    (hK : L.length = 0) : newLB li Q L E = newL0 li Q := by
  Ξ newLB_eq_flatMap, hK
  unfold ptsB newL0
  Θ hK

/-- **The precondition of the region loop**, with bounds `S₀` (points of a region) and `Cm`
(walk edges of an arc of a region, or `n` when `K = 0`). -/
structure RegPre (P : Polygon) (W : ℕ) (c : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (S₀ Cm : ℕ) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hK : c.nreg 210003 = L.length
  hok : ChordTriplesOK (interiorModel (Qof P)) (Qof P) L
  hperm : E.Perm (List.range (2 * L.length))
  hsort : E.Pairwise (codeLe (interiorModel (Qof P)) (Qof P) L)
  hdeg : (interiorModel (Qof P)).DegLe
    ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4
  hNF : NFWithin c.nmem (c.nreg 210005) (c.nreg 212019)
    (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
  hMD : ModelDescAt c.nmem (c.nreg 210001) (Qof P) (interiorModel (Qof P))
  hMDW : c.nreg 210001 + 6 ≤ c.nreg 212019
  hroom : c.nreg 212019 + 10 * P.n ≤ c.nreg ALLOC
  hS₀ : ∀ r, r < L.length + 1 →
    (ptsB (liBit c.nmem (c.nreg 210001)) (Qof P) L E r).length ≤ S₀
  hCm0 : L.length = 0 → P.n ≤ Cm
  hCm : ∀ r, r < L.length + 1 → ∀ j ∈ ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs,
    arcCnt P.n ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arc j) ≤ Cm

/-- **The postcondition of the region loop**: the new chords `newLB` at `B₂ = r212019` (their
number in `216020`), the buckets `bk q = mem[B₂ + 6 n + q]` of their ends bounded by the number
of arcs, ordered by the event comparator, with at most `4 MX` codes per bucket
(`MX = r212018 ≤ S₀`). -/
structure RegPost (P : Polygon) (c c' : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (S₀ : ℕ) :
    Prop where
  keep : ∀ q, 210000 ≤ q → q < 210030 → c'.nreg q = c.nreg q
  keepB : c'.nreg 212019 = c.nreg 212019
  cnt : c'.nreg 216020 = (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length
  len : (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length ≤ 2 * P.n
  list : ChordListAt c'.nmem (c.nreg 212019) (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E)
  bkle : ∀ q, q < 2 * (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length →
    c'.nmem (c.nreg 212019 + 6 * P.n + q) ≤
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length
  bkmono : ∀ q q', q < 2 * (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length →
    q' < 2 * (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length →
    c'.nmem (c.nreg 212019 + 6 * P.n + q) < c'.nmem (c.nreg 212019 + 6 * P.n + q') →
    codeLe (interiorModel (Qof P)) (Qof P) (L ++ newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E)
      (2 * L.length + q) (2 * L.length + q')
  bcnt : ∀ b, DrvR.bcnt (fun q => c'.nmem (c.nreg 212019 + 6 * P.n + q))
    (2 * (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length) b ≤ 4 * c'.nreg 212018
  mx : c'.nreg 212018 ≤ S₀

/-- **The contract of the region loop of the base case.** -/
def RegLoopSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (c : Config) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (S₀ Cm : ℕ), WordsBounded W c → RegPre P W c L E S₀ Cm →
    c.nreg ALLOC + κ * (L.length + 1) * (S₀ + 1) * (Cm + 1) ≤ W →
    ∃ c' k, Exec P W s c c' k ∧ k ≤ κ * (L.length + 1) * (S₀ + 1) * (Cm + 1) ∧
      RegPost P c c' L E S₀ ∧ Restore.RF DrvR.drvBands (c.nreg 212019) c c' k

end

end DrvB

end Chazelle.Core
