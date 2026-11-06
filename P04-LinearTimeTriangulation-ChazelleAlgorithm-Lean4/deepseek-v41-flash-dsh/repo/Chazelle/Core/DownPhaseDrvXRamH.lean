module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXRamG

/-!
# Down phase, extraction (D6), RAM part 8: one chord record

* `XV`: the values of the run (chain `m, T, β`, bit `li`, host `H` at `HB`, chords of `N_R` at
  `CB`, arcs of `N` at `AB`, the arc list of the region at `RA`, output bases);
* `XG v d`: the global registers hold them;
* `XE`: the facts of the run (memory below the entry allocator `A0`, bounds, the arc facts of
  `N`, and for every kept chord record the facts of its ends);
* `chS_exec`: one chord record: if it is kept, its interior triple and the buckets of its ends are
  stored.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open Chazelle.Chain (sideInArc)
open DrvR (ivB qE keyBkt)

@[expose] public section

/-- **The values of a run.** -/
structure XV where
  m : ℕ
  T : ℕ
  β : Bool
  li : Bool
  H : Host
  HB : ℕ
  K : ℕ
  CB : ℕ
  A : ℕ
  AB : ℕ
  nRA : ℕ
  RA : ℕ
  LxB : ℕ
  BkB : ℕ

/-- **The global registers.** -/
structure XG (P : Polygon) (v : XV) (d : Config) : Prop where
  r20 : d.nreg 217020 = (Qof P).n
  r21 : d.nreg 217021 = v.m
  r22 : d.nreg 217022 = 2 * v.m
  r25 : d.nreg 217025 = tS v.m v.T v.β
  r26 : d.nreg 217026 = liV v.li
  r27 : d.nreg 217027 = 1
  r28 : d.nreg 217028 = v.K
  r30 : d.nreg 217030 = v.A
  r31 : d.nreg 217031 = v.AB
  r32 : d.nreg 217032 = v.nRA
  r33 : d.nreg 217033 = v.RA
  r34 : d.nreg 217034 = v.H.length
  r35 : d.nreg 217035 = v.HB + 1
  r36 : d.nreg 217036 = v.LxB
  r37 : d.nreg 217037 = v.BkB
  r41 : d.nreg 217041 = 6
  r42 : d.nreg 217042 = 2 * v.m + 6
  r44 : d.nreg 217044 = 2

/-- The global registers. -/
def xgRegs : List ℕ := [217020, 217021, 217022, 217025, 217026, 217027, 217028, 217030, 217031,
  217032, 217033, 217034, 217035, 217036, 217037, 217041, 217042, 217044]

theorem XG.congr {P : Polygon} {v : XV} {d d' : Config} (h : XG P v d)
    (hr : ∀ r ∈ xgRegs, d'.nreg r = d.nreg r) : XG P v d' :=
  ⟨(hr _ (⊚ xgRegs)).trans h.r20, (hr _ (⊚ xgRegs)).trans h.r21,
    (hr _ (⊚ xgRegs)).trans h.r22, (hr _ (⊚ xgRegs)).trans h.r25,
    (hr _ (⊚ xgRegs)).trans h.r26, (hr _ (⊚ xgRegs)).trans h.r27,
    (hr _ (⊚ xgRegs)).trans h.r28, (hr _ (⊚ xgRegs)).trans h.r30,
    (hr _ (⊚ xgRegs)).trans h.r31, (hr _ (⊚ xgRegs)).trans h.r32,
    (hr _ (⊚ xgRegs)).trans h.r33, (hr _ (⊚ xgRegs)).trans h.r34,
    (hr _ (⊚ xgRegs)).trans h.r35, (hr _ (⊚ xgRegs)).trans h.r36,
    (hr _ (⊚ xgRegs)).trans h.r37, (hr _ (⊚ xgRegs)).trans h.r41,
    (hr _ (⊚ xgRegs)).trans h.r42, (hr _ (⊚ xgRegs)).trans h.r44⟩

theorem XG.frameM {P : Polygon} {v : XV} {d d' : Config} {B : ℕ → Bool} (h : XG P v d)
    (hf : FrameM B d d') (hB : xgRegs.all (fun r => !B r) = true) : XG P v d' :=
  h.congr fun r hr => hf.1 r (by
    have := List.all_eq_true.1 hB r hr
    simpa using this)

/-- The interior walk position of an end, from the values of a run. -/
noncomputable def xP (P : Polygon) (v : XV) (h p : ℕ) : WPos := xPos (Qof P).n v.H v.li v.m v.T v.β h p

/-- The kept test, from the values of a run. -/
def kR (P : Polygon) (v : XV) (c : CRec) : Prop :=
  KeptT (Qof P).n v.H v.li v.m v.T v.β c.h c.lp c.rp

noncomputable instance (P : Polygon) (v : XV) (c : CRec) : Decidable (kR P v c) := by
  unfold kR; infer_instance

/-- **The facts of a run** (`N` the interior normal form, `NR` the normal form of the region
chain, `ras` the arc list of the region, memory `mem0` below `A0`). -/
structure XE (P : Polygon) (W : ℕ) (v : XV) (N NR : NF) (ras : ℕ → ℕ) (A0 : ℕ)
    (mem0 : ℕ → ℕ) : Prop where
  hG : GoodEnv P
  hli : v.li = true ↔ Mountain.LeftInside (Qof P)
  hdh : DistinctHeights (Qof P)
  hn2 : 2 ≤ (Qof P).n
  hW : 256 * (Qof P).n + 16 ≤ W
  hK : NR.chords.length = v.K
  hA0 : A0 + 5 * v.K ≤ W
  hHost : ∀ mm : ℕ → ℕ, (∀ a, a < A0 → mm a = mem0 a) → HostAt mm v.HB v.H
  hwf : HostWF (Qof P).n v.H
  hlen : v.H.length ≤ 64
  hHB : v.HB + 3 * v.H.length + 1 ≤ A0
  hm1 : 1 ≤ v.m
  hmp : v.m + 1 = (v.H.pts (Qof P).n).length
  hT : v.T ≤ v.m
  hNRm : ∀ mm : ℕ → ℕ, (∀ a, a < A0 → mm a = mem0 a) → ∀ i, i < v.K →
    mm (v.CB + 5 * i) = (NR.chord i).h ∧ mm (v.CB + 5 * i + 1) = (NR.chord i).lp ∧
      mm (v.CB + 5 * i + 2) = (NR.chord i).rp
  hCB : ∀ i, i < v.K → v.CB + 5 * i + 4 < A0
  hch : ∀ i, i < v.K → (NR.chord i).h + 1 ≤ (Qof P).n ∧ (NR.chord i).lp ≤ 2 * v.m + 6 ∧
    (NR.chord i).rp ≤ 2 * v.m + 6
  hA : N.arcs.length = v.A
  hgood : ∀ j, j < v.A → GoodPos (Qof P) (N.arc j).s ∧ GoodPos (Qof P) (N.arc j).e
  hinc : ∀ j j', j < j' → j' < N.arcs.length →
    (interiorModel (Qof P)).key (Qof P) (N.arc j).s <
      (interiorModel (Qof P)).key (Qof P) (N.arc j').s
  hnext : ∀ j, j < N.arcs.length →
    (interiorModel (Qof P)).key (Qof P) (N.arc j).e =
      (interiorModel (Qof P)).key (Qof P) (N.arc ((j + 1) % N.arcs.length)).s
  hfree : ∀ j j', j < N.arcs.length → j' < N.arcs.length →
    ¬ sideInArc ((interiorModel (Qof P)).key (Qof P) (N.arc j).s)
      ((interiorModel (Qof P)).key (Qof P) (N.arc j).e)
      ((interiorModel (Qof P)).key (Qof P) (N.arc j').s)
  hAm : ∀ mm : ℕ → ℕ, (∀ a, a < A0 → mm a = mem0 a) → ∀ j, j < v.A →
    mm (v.AB + 5 * j + 1) = (N.arc j).s.edge ∧ mm (v.AB + 5 * j + 2) = (N.arc j).s.hgt ∧
      mm (v.AB + 5 * j + 3) = (N.arc j).e.edge ∧ mm (v.AB + 5 * j + 4) = (N.arc j).e.hgt
  hRm : ∀ mm : ℕ → ℕ, (∀ a, a < A0 → mm a = mem0 a) → ∀ t, t < v.nRA → mm (v.RA + t) = ras t
  hras : ∀ t, t < v.nRA → ras t < v.A
  hAW : ∀ j, j < v.A → v.AB + 5 * j + 4 < A0
  hRW : v.RA + v.nRA ≤ A0
  hnRA : v.nRA ≤ 32
  hA2 : 2 * v.A + 2 ≤ W
  hkf : ∀ i, i < v.K → kR P v (NR.chord i) →
    GoodPos (Qof P) (xP P v (NR.chord i).h (NR.chord i).lp) ∧
    GoodPos (Qof P) (xP P v (NR.chord i).h (NR.chord i).rp) ∧
    (∃ t, t < v.nRA ∧ OnArcP (Qof P) v.li N (ras t) (xP P v (NR.chord i).h (NR.chord i).lp)) ∧
    (∃ t, t < v.nRA ∧ OnArcP (Qof P) v.li N (ras t) (xP P v (NR.chord i).h (NR.chord i).rp))
  hLx : v.LxB = A0
  hBk : v.BkB = A0 + 3 * v.K

/-- The registers `chS` writes. -/
def Bch (r : ℕ) : Bool :=
  decide ((217038 ≤ r ∧ r ≤ 217040) ∨ (217045 ≤ r ∧ r ≤ 217046) ∨ (217050 ≤ r ∧ r ≤ 217199))

theorem wrM_ch : wrM Bch chS = true := ⌖

/-- The host point at the start of walk edge `p`. -/
noncomputable def sPt (P : Polygon) (v : XV) (p : ℕ) : SymPt := hpt (Qof P).n v.H (tK v.m v.T v.β p)

/-- The memory after storing a kept chord. -/
noncomputable def stMem (P : Polygon) (v : XV) (N : NF) (mm : ℕ → ℕ) (cnt : ℕ) (c : CRec) : ℕ → ℕ :=
  upd (upd (upd (upd (upd mm (v.LxB + 3 * cnt) c.h) (v.LxB + 3 * cnt + 1)
    (xP P v c.h c.lp).edge) (v.LxB + 3 * cnt + 2) (xP P v c.h c.rp).edge) (v.BkB + 2 * cnt)
      (keyBkt (Qof P) N (xP P v c.h c.lp))) (v.BkB + 2 * cnt + 1)
      (keyBkt (Qof P) N (xP P v c.h c.rp))

end

end DrvX

end Chazelle.Core
