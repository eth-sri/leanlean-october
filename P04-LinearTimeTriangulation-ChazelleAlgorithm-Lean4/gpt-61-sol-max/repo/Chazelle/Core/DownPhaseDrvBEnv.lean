module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBApp
public import Chazelle.Core.DownPhaseDrvBSpec

/-!
# Down-phase base (D9): the data of the region loop and the facts of a region

`BEnv`: the fixed data of the region loop (the polygon, the chord and event lists `L`, `E`, the
region correspondence `reg`, the memory `m₀` and the descriptor, normal-form and output bases
at its start); `BGood`: the facts about them (from `RegPre`).  Derived data: the points `pts r`
of region `r` (`ptsB`), its records `recs r`, the tagged records `TL r` of the regions `< r`, the
walk-edge ranges (`stF`, `cntF`, `nRg`) of the far-end scan.

Facts of a region `r < K + 1`:

* `BGood.pts_lt`: its points are symbolic points of `Q`;
* `BGood.far_ok`: an emitted index has an interior direction, and the walk edge of the far end
  lies in one of the ranges;
* `BGood.scan_ok`, `BGood.hex_ok` (`K > 0`): the arc scans of the ends of a record are well posed
  and find a match;
* `BGood.ld_ok`: the range loader reads the ranges.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt
open BuildNF (codeLe)
open Chazelle.Visibility (DirInterior chordEnd OpenEdgePt)
open DrvR (qE ivB)

@[expose] public section

/-- **The fixed data of the region loop.** -/
structure BEnv where
  P : Polygon
  W : ℕ
  L : List (ℕ × ℕ × ℕ)
  E : List ℕ
  reg : ℕ → Set Point
  m₀ : ℕ → ℕ
  MD : ℕ
  H : ℕ
  B₂ : ℕ
  S₀ : ℕ
  Cm : ℕ

namespace BEnv

variable (E : BEnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev I : Model := interiorModel E.Q

/-- The current normal form. -/
noncomputable abbrev N : NF := BuildNF.buildNF E.I E.Q E.L E.E

/-- The number of chords. -/
abbrev K : ℕ := E.L.length

/-- The `LeftInside` bit. -/
def li : Bool := liBit E.m₀ E.MD

/-- The bucket base. -/
def BK : ℕ := E.B₂ + 6 * E.P.n

section
variable (r : ℕ)
include r
/-- The pointer `RB + 5 r + 2` to the record of region `r`. -/
def RP : ℕ := E.m₀ (E.H + 5) + 2 + 5 * r

/-- The arc list of region `r`. -/
def LP : ℕ := E.m₀ (E.H + 7) + E.m₀ (E.m₀ (E.H + 5) + 5 * r + 1)

/-- The number of walk-edge ranges of region `r`. -/
noncomputable def nRg : ℕ := if E.K = 0 then 1 else (E.N.region r).arcs.length


end

section
variable (r t : ℕ)
include r t
/-- Arc `t` of region `r`. -/
noncomputable def arcR : ARec := E.N.arc ((E.N.region r).arcs.getD t 0)

/-- The first walk edge of range `t` of region `r`. -/
noncomputable def stF : ℕ := if E.K = 0 then 0 else (E.arcR r t).s.edge

/-- The number of walk edges of range `t` of region `r`. -/
noncomputable def cntF : ℕ := if E.K = 0 then E.P.n else arcCnt E.P.n (E.arcR r t)


end

section
variable (r : ℕ)
include r
/-- The walk-order points of region `r`. -/
noncomputable def pts : List SymPt := ptsB E.li E.Q E.L E.E r

/-- The records of region `r`. -/
noncomputable def recs : List (ℕ × ℕ × ℕ) := regList E.li E.Q (E.pts r)

/-- The tagged records of the regions `< r`. -/
noncomputable def TL : List (ℕ × (ℕ × ℕ × ℕ)) :=
  (List.range r).flatMap fun r' => (E.recs r').map fun x => (r', x)

theorem TL_succ : E.TL (r + 1) = E.TL r ++ (E.recs r).map fun x => (r, x) := by
  grind [TL, List.range_succ, List.flatMap_append, List.flatMap_singleton]


end

theorem TL_all : E.TL (E.K + 1) = tagLB E.li E.Q E.L E.E := rfl

end BEnv

/-- **The facts about the data of the region loop.** -/
structure BGood (E : BEnv) : Prop where
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hok : ChordTriplesOK E.I E.Q E.L
  hperm : E.E.Perm (List.range (2 * E.L.length))
  hsort : E.E.Pairwise (codeLe E.I E.Q E.L)
  hdeg : E.I.DegLe (E.N.F E.I E.Q) 4
  hregs : Restore.NFRegs E.I E.Q E.N E.reg
  hNF : NFWithin E.m₀ E.H E.B₂ E.N
  hMD : ModelDescAt E.m₀ E.MD E.Q E.I
  hMDW : E.MD + 6 ≤ E.B₂
  hBW : E.B₂ + 10 * E.P.n ≤ E.W
  hS₀ : ∀ r, r < E.K + 1 → (E.pts r).length ≤ E.S₀
  hCm : ∀ r, r < E.K + 1 → ∀ t, t < E.nRg r → E.cntF r t ≤ E.Cm

namespace BGood

variable {E : BEnv}

theorem pts_pos {r : ℕ} (hK : 0 < E.K) : E.pts r = regPts E.li E.Q.n E.N r := by
  have : E.L.length ≠ 0 := Nat.pos_iff_ne_zero.1 hK
  simp only [BEnv.pts, ptsB, this, ↓reduceIte]

theorem pts_zero {r : ℕ} (hK : E.K = 0) :
    E.pts r = wlist E.li (Host.pts E.Q.n [HostItem.run 0 (E.Q.n - 1)]) := by
  simp_all [BEnv.pts, ptsB, reduceIte] 

variable (hE : BGood E)
include hE

theorem hQ : E.Q.Simple := (shearInvariance (epsOf E.P) E.P).1 hE.hG.1

theorem hDH : DistinctHeights E.Q := (goodShear_epsOf hE.hG.2).2.1

omit hE in
theorem hQn (_hE : BGood E) : E.Q.n = E.P.n := shear_n _ _

theorem hn3 : 3 ≤ E.P.n := hE.hG.1.1

theorem hli : E.li = true ↔ Mountain.LeftInside E.Q := by
  unfold BEnv.li liBit
  rcases hE.hMD with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exfalso
    have := DrvD.desc_one hE.hMD
    omega
  simp_all

omit hE in
theorem nRegions (_hE : BGood E) : E.N.nRegions = E.K + 1 := by
  simp [NF.nRegions, BuildNF.buildNF]

/-- The context of the base case (`K > 0`). -/
theorem ctx (hK : 0 < E.K) : BaseCtx E.Q E.L E.E E.reg E.li :=
  ⟨hE.hQ, hE.hDH, hE.hok, hE.hperm, hE.hsort, hK, hE.hregs, hE.hli⟩


section
variable {r : ℕ} (hr : r < E.K + 1)
include hr
/-- **The points of a region are symbolic points of `Q`.** -/
theorem pts_lt : ∀ s ∈ E.pts r, s.Lt E.Q.n := by
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · rw [pts_zero hK]; exact run_pts_lt hE.hQ
  · rw [pts_pos hK]
    exact (region_facts ((hE.ctx hK).rc (by rw [hE.nRegions]; exact hr)) hE.hli).2

/-- **The shooting polygon of a region.** -/
theorem regOK :
    ∃ (S : Set (Set Point)) (R : Set Point), E.I.ChordFamily E.Q S ∧
      RegOK E.Q S R (polyOf E.Q (E.pts r)) := by
  rcases Nat.eq_zero_or_pos E.K with hK | hK
  · refine ⟨∅, E.I.D, ⟨Set.finite_empty, Set.empty_subset _, fun c hc => absurd hc
      (Set.notMem_empty c)⟩, ?_⟩
    rw [pts_zero hK]; exact regOK0 hE.hQ hE.hli
  · refine ⟨_, E.reg r, (hE.ctx hK).fam, ?_⟩
    rw [pts_pos hK]
    exact (region_facts ((hE.ctx hK).rc (by rw [hE.nRegions]; exact hr)) hE.hli).1


end

end BGood

/-! ## The registers and the output during the region loop -/

/-- The registers fixed during the region loop. -/
def FixB (q : ℕ) : Prop :=
  (210000 ≤ q ∧ q < 210030) ∨ (212000 ≤ q ∧ q < 212013) ∨ q = 212019 ∨ (216000 ≤ q ∧ q < 216020)

/-- **The registers fixed during the region loop.** -/
structure BRegs (E : BEnv) (c : Config) : Prop where
  c0 : c.nreg 212000 = 1
  c1 : c.nreg 212001 = 0
  c2 : c.nreg 212002 = 2
  n : c.nreg 212010 = E.P.n
  li : c.nreg 212011 = if E.li then 1 else 0
  K : c.nreg 212012 = E.K
  d02 : c.nreg 216002 = 1
  d03 : c.nreg 216003 = 0
  d05 : c.nreg 216005 = 2
  d14 : c.nreg 216014 = E.m₀ (E.H + 4)
  d16 : c.nreg 216016 = E.m₀ (E.H + 7)
  d17 : c.nreg 216017 = E.N.arcs.length
  md : c.nreg 210001 = E.MD
  h5 : c.nreg 210005 = E.H

theorem BRegs.congr {E : BEnv} {c c' : Config} (h : BRegs E c)
    (hc : ∀ q, FixB q → c'.nreg q = c.nreg q) : BRegs E c' := by
  ram_grind

/-- **The output so far**: the records of `T` at `B₂`, their buckets at `BK`, the memory below
`B₂` the initial one. -/
structure OutSt (E : BEnv) (c : Config) (T : List (ℕ × (ℕ × ℕ × ℕ))) : Prop where
  cnt : c.nreg 216020 = T.length
  dst : c.nreg 216021 = E.B₂ + 3 * T.length
  dstB : c.nreg 216022 = E.BK + 2 * T.length
  list : ChordListAt c.nmem E.B₂ (T.map Prod.snd)
  bk : 0 < E.K → DrvD.BktOK E.I E.Q E.N T (fun q => c.nmem (E.BK + q))
  bk0 : E.K = 0 → ∀ q, q < 2 * T.length → c.nmem (E.BK + q) = 0
  low : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a

end

end DrvB

end Chazelle.Core
