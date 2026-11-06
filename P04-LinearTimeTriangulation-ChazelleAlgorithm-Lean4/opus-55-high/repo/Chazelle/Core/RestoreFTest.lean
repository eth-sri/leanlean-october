module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvBTopMain
public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.RestoreTestOK
public import Chazelle.Core.OraclePrepMain
public import Chazelle.Core.GranInitL3

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs

/-- The fixed data of a run of the search. -/
structure FEnv where
  P : Polygon
  W : ℕ
  M : Model
  N : NF
  X : MemCtx
  Ok : Polygon → Model → Prop
  cu : Stmt
  sT : Stmt
  Bc : Finset ℕ
  Bo : Finset ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  H : ℕ → ℕ
  κt : ℕ → ℕ
  A₀ : ℕ
  m₀ : ℕ → ℕ
  MD : ℕ
  NH : ℕ
  r : ℕ
  γ : ℕ
  g : ℕ
  d : ℕ
  D : ℕ

/-- The fixed facts of a run of the search started in `c₀`. -/
structure FGood (E : FEnv) (c₀ : Config) : Prop where
  hT : TestOK E.sT E.κt E.F E.X E.Ok E.Bo
  hcu : CutterOK E.cu E.Bc E.G E.H E.X E.Ok
  hBc : E.Bc ⊆ E.Bo
  hBo : oracleBands ⊆ E.Bo
  hB8 : bRestore ∉ E.Bo
  hloc : E.X.CapLocal
  hhalf : E.X.Halves
  hOkM : ∀ P M, E.Ok P M → OkModel P M ∨ M = interiorModel zta
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.g E.A₀
  hcap : E.γ ≤ E.X.cap E.P E.m₀ E.g
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ ztcsy zti H C → C.P.Simple
  hMD : ModelDescAt E.m₀ E.MD zti E.M
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hNW : NFWithin E.m₀ E.NH E.A₀ E.N
  hNF : IsNF E.M zti E.N
  hdeg : E.M.DegLe ztwky E.d
  hsg : E.M.Semigranular ztwky E.γ
  hr : E.r < E.N.nRegions
  a0 : c₀.nreg ALLOC = E.A₀
  m0 : c₀.nmem = E.m₀
  i0 : c₀.nreg 81000 = E.MD
  i1 : c₀.nreg 81001 = E.NH
  i2 : c₀.nreg 81002 = E.r
  i3 : c₀.nreg 81003 = E.γ
  i4 : c₀.nreg 81004 = E.g
  i5 : c₀.nreg 81005 = E.d
  i6 : c₀.nreg 81006 = E.D
  k0 : c₀.nreg 81011 = 0
  k1 : c₀.nreg 81012 = 1
  k2 : c₀.nreg 81013 = 2
  k3 : c₀.nreg 81014 = 3
  k5 : c₀.nreg 81015 = 5
  k7 : c₀.nreg 81016 = 7
  pn : c₀.nreg 81020 = E.P.n
  nE : c₀.nreg 81022 = 2 * ztnks
  hE2 : c₀.nreg 81023 = E.P.n / 2
  wn : c₀.nreg 81017 = E.M.W.n
  k10 : c₀.nreg 81024 = 10
  hvr : ∀ v, v < E.M.W.n → c₀.nreg 81021 ≤ v → v ≤ c₀.nreg 81019 →
    ∀ C : Chain, E.M = chainModel C → E.M.pos zti ztcfs ∈ C.set
  hvc : ∀ v, v < E.M.W.n →
    (∀ C : Chain, E.M = chainModel C → E.M.pos zti ztcfs ∈ C.set) →
    c₀.nreg 81021 ≤ v ∧ v ≤ c₀.nreg 81019
  vlo6 : ∀ C : Chain, E.M = chainModel C → 6 ≤ c₀.nreg 81021
  ehr : ∀ e h, e < E.M.W.n → c₀.nreg 81021 ≤ e → e < c₀.nreg 81025 →
    ProperPos E.M zti E.P.n ztcq →
    ∀ C : Chain, E.M = chainModel C → E.M.pos zti ztcq ∈ C.set
  ehc : ∀ e, e < E.M.W.n → E.M.counted e → c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025

/-- **The facts the test needs about a candidate** `x`, its height vertex `hv` and the direction
bit `σb`. -/
def CandOK (E : FEnv) (x : WPos) (hv σb : ℕ) : Prop :=
  x.edge < E.M.W.n ∧ ProperPos E.M zti E.P.n x ∧ (x.hgt = 0 ∨ 0 < E.M.param zti x) ∧
    (∀ C : Chain, E.M = chainModel C → E.M.pos zti x ∈ C.set) ∧ hv < E.P.n ∧
    ((Qof E.P).vtx hv).2 = (E.M.pos zti x).2 ∧ σb ≤ 1

/-! ## The test call -/

/-- The arguments of the test (candidate in `81060 … 81063`). -/
def tArgs : Stmt := block [.copyN 83000 81000, .copyN 83001 81001, .copyN 83002 81002,
  .copyN 83003 81003, .copyN 83004 81004, .copyN 83005 81060, .copyN 83006 81061,
  .copyN 83007 81062, .copyN 83008 81063, .copyN 83009 81005]

/-- Record a success. -/
def tWin : Stmt := block [.copyN 81008 83015, .copyN 81009 83016, .copyN 81010 83017,
  .constN 81007 1]

/-- **The test call**: skipped once the flag is set. -/
def tcall (sT : Stmt) : Stmt :=
  .ifLtN 81007 81012 (.seq tArgs (.seq sT ztpru)) .skip

/-! ## The precondition of the test -/
variable {E : FEnv} {c₀ c : Config}

/-- The memory below the initial allocator is the initial memory. -/
theorem FInv.agree (hE : FGood E c₀) (hI : FInv E.W c₀ c) :
    ∀ a, a < E.A₀ → c.nmem a = E.m₀ a := fun a ha => by
  rw [hI.hm a (by rw [hE.a0]; exact ha), hE.m0]
theorem FInv.allocA (hE : FGood E c₀) (hI : FInv E.W c₀ c) : E.A₀ ≤ c.nreg ALLOC := by
  rw [← hE.a0]; exact hI.hA

/-- **The precondition of the test** in a configuration of the search whose test registers hold
the inputs and a candidate. -/
theorem test_pre (hE : FGood E c₀) (hI : FInv E.W c₀ c) (h0 : c.nreg 83000 = E.MD)
    (h1 : c.nreg 83001 = E.NH) (h2 : c.nreg 83002 = E.r) (h3 : c.nreg 83003 = E.γ)
    (h4 : c.nreg 83004 = E.g) (h9 : c.nreg 83009 = E.d)
    (hc : CandOK E ztbcf ztqij ztviz) :
    GoodEnv E.P ∧ hostWords E.P.n ≤ E.W ∧
      E.X.holds E.P c.nmem ztmgp ztm ∧
      c.nreg 83003 ≤ E.X.cap E.P c.nmem ztmgp ∧
      ModelDescWF E.P ztm c.nmem ztdcs ∧
      (c.nmem ztdcs = 0 → ∀ H C, ChainDescAt c.nmem ztcms zti H C →
        HostRegular (Qof E.P).n H) ∧
      (c.nmem ztdcs = 0 → ∀ H C, ChainDescAt c.nmem ztcms zti H C →
        C.P.Simple) ∧ c.nreg 83008 ≤ 1 ∧
      ∃ M N, ModelDescAt c.nmem ztdcs zti M ∧ GoodModel M ∧ E.Ok E.P M ∧
        NFWithin c.nmem ztmgn ztm N ∧ IsNF M zti N ∧
        M.DegLe ztxvn ztqik ∧
        M.Semigranular ztxvn ztmgo ∧ c.nreg 83002 < N.nRegions ∧
        c.nreg 83005 < M.W.n ∧ ProperPos M zti E.P.n ztbcf ∧
        (c.nreg 83006 = 0 ∨ 0 < M.param zti ztbcf) ∧
        (OkModel E.P M ∨ M = interiorModel zti) ∧
        (∀ C : Chain, M = chainModel C →
          M.pos zti ztbcf ∈ C.set) ∧
        c.nreg 83007 < E.P.n ∧
        ((Qof E.P).vtx ztqij).2 = (M.pos zti ztbcf).2 := by
  zubnt

  zufyc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  rw [h0, h1, h2, h3, h4, h9]
  refine ⟨hE.hG, hE.hWh, ?_, ?_, hwf'.mono hA, hregKeep hE.hwf hE.hMD hE.hreg hag,
    simpKeep hE.hwf hE.hMD hE.hsimp hag, c7, E.M, E.N, hMD', hE.hGM, hE.hOk,
    (hE.hNW.transport hag).mono hA, hE.hNF, hE.hdeg, hE.hsg, hE.hr, c1, c2, c3,
    hE.hOkM _ _ hE.hOk, c4, c5, c6⟩
  · exact E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ by_simp_all hE.hX)
  · rw [hE.hloc E.P E.m₀ c.nmem E.g E.A₀ hag hE.hX]; exact hE.hcap

/-! ## The result of a test call -/

/-- The cost bound of a test call. -/
def tK (E : FEnv) : ℕ := E.κt E.d * ztriy + 20

/-- **What a test from a clear flag gives**: the contract of the test for the candidate of `c`,
read in `c'` (valid `83010`, hit `83011`, far `83012`, `83013`; the flag `81007` is the success
bit and the triple is in `81008 … 81010`). -/
def TOut (E : FEnv) (c c' : Config) : Prop :=
  c'.nreg 83010 ≤ 1 ∧ c'.nreg 83011 ≤ 1 ∧
  ∀ reg, NFRegs E.M zti E.N reg →
    let x : WPos := zteya
    let z := E.M.pos zti x
    let σ := dirOf zteqx
    let R := reg E.r
    let far : WPos := ⟨c'.nreg 83012, c'.nreg 83013⟩
    let tr := (c'.nreg 81008, c'.nreg 81009, c'.nreg 81010)
    (c'.nreg 81007 = 1 →
      (recOf tr).Attached E.M zti ∧ tr.1 < (Qof E.P).n ∧
      (recOf tr).toSet E.M zti ∈ E.M.Adm ∧
      SplitsWell E.M ztwky R ((recOf tr).toSet E.M zti)) ∧
    (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
      ∃ T > (0 : ℝ), (∀ t, 0 < t → t < T → Chazelle.Visibility.rayPt z σ t ∈ R) ∧
        E.M.pos zti far = Chazelle.Visibility.rayPt z σ T ∧ far.edge < E.M.W.n ∧
        ProperPos E.M zti E.P.n far ∧
        chordOf z σ T ∈ E.M.Adm ∧
        Chazelle.Chain.SideAttach E.M.W ztcmu x.edge ztztg ∧
        Chazelle.Chain.SideAttach E.M.W ztcmu far.edge (E.M.param zti far) ∧
        (c'.nreg 81007 = 1 ↔
          CountOK E.M ztwky R (E.M.key zti x) (E.M.key zti far))) ∧
    (Chazelle.Chain.sideLeft E.M.W x.edge ztztg
        (Chazelle.Visibility.rayPt z σ 1) →
      (E.N.region E.r).chords ≠ [] →
      (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T → Chazelle.Visibility.rayPt z σ t ∈ E.M.D) →
        Chazelle.Visibility.rayPt z σ T ∉ E.M.D →
        chordOf z σ T ∈ E.M.Adm → chordOf z σ T ∉ E.N.F E.M zti →
        chordOf z σ T ∩ E.M.D ⊆ R → c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1))

/-- The registers of the search a test call keeps: band `bRestore` from `81011` below
`83000`. -/
def TKeep (c c' : Config) : Prop := ∀ q, 81011 ≤ q → q < 83000 → c'.nreg q = c.nreg q

/-! ## The test call as a run step -/

/-- The instructions of `tArgs`. -/
def tArgsL : List Instr := [.copyN 83000 81000, .copyN 83001 81001, .copyN 83002 81002,
  .copyN 83003 81003, .copyN 83004 81004, .copyN 83005 81060, .copyN 83006 81061,
  .copyN 83007 81062, .copyN 83008 81063, .copyN 83009 81005]
variable (m f : ℕ → ℕ) {W : ℕ}
/-- The arguments of the test as a register effect. -/
theorem tArgs_eff :
    regB m tArgsL f 83000 = f 81000 ∧ regB m tArgsL f 83001 = f 81001 ∧
      regB m tArgsL f 83002 = f 81002 ∧ regB m tArgsL f 83003 = f 81003 ∧
      regB m tArgsL f 83004 = f 81004 ∧ regB m tArgsL f 83005 = f 81060 ∧
      regB m tArgsL f 83006 = f 81061 ∧ regB m tArgsL f 83007 = f 81062 ∧
      regB m tArgsL f 83008 = f 81063 ∧ regB m tArgsL f 83009 = f 81005 ∧
      ∀ q, ztofa → regB m tArgsL f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  all_goals try (simp [tArgsL, regB, regI, upd]; done)
  zuknp
  simp only [tArgsL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    zubzs

/-- The instructions of `tWin`. -/
def tWinL : List Instr := [.copyN 81008 83015, .copyN 81009 83016, .copyN 81010 83017,
  .constN 81007 1]

/-- The record of a success as a register effect. -/
theorem tWin_eff :
    regB m tWinL f 81008 = f 83015 ∧ regB m tWinL f 81009 = f 83016 ∧
      regB m tWinL f 81010 = f 83017 ∧ regB m tWinL f 81007 = 1 ∧
      ∀ q, ztoez → regB m tWinL f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  all_goals try (simp [tWinL, regB, regI, upd]; done)
  zuknp
  simp only [tWinL, List.mem_cons, List.not_mem_nil, or_false] at hi
  zubca
theorem okB_tArgs (m f : ℕ → ℕ) : okB W m tArgsL f := by
  simp only [tArgsL, okB, okI, FScr, FOut]; norm_num
theorem okB_tWin (hW : 1 ≤ W) (m f : ℕ → ℕ) : okB W m tWinL f := by
  simp only [tWinL, okB, okI, FScr, FOut]; simp_all

/-- **The test call** as a run step of the search. -/
theorem tcall_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hfl : c.nreg 81007 ≤ 1)
    (hcand : c.nreg 81007 = 0 →
      CandOK E zteya ztqie zteqx)
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ ztmou c ztqxe (fun c' => TKeep c c' ∧ c'.nreg 81007 ≤ 1 ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1 ∧ c'.nreg 81008 = c.nreg 81008 ∧
        c'.nreg 81009 = c.nreg 81009 ∧ c'.nreg 81010 = c.nreg 81010) ∧
      ztlky) := by
  have fx := hI.hin
  have k0 : ztuoi := by rw [fx _ ztbc, hE.k0]
  have k1 : ztgar := by rw [fx _ ztbc, hE.k1]
  zucb
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hfl with h0 | h1
  · -- the test runs
    have g : c.nreg 81007 < c.nreg 81012 := by_omega
    have hc := hcand h0
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, afr⟩ := tArgs_eff c.nmem c.nreg
    zuiwz
    unfold TestOK at hT
    refine (FRS.ifT g (FRS.seq (FRS.block hB tArgsL hI (okB_tArgs _ _))
      ztbzx)).mono (K := tArgsL.length + (E.κt E.d * (E.F E.γ + 1) + 6) + 2)
      (by simp only [tK, tArgsL, List.length_cons, List.length_nil]; omega) ztb
    subst h₁
    -- the registers after the arguments
    have i0 : ztuog := by rw [fx _ ztbc, hE.i0]
    have i1 : ztpmb := by rw [fx _ ztbc, hE.i1]
    have i2 : ztpmc := by rw [fx _ ztbc, hE.i2]
    have i3 : c.nreg 81003 = E.γ := by rw [fx _ ztbc, hE.i3]
    have i4 : ztuoh := by rw [fx _ ztbc, hE.i4]
    have i5 : c.nreg 81005 = E.d := by rw [fx _ ztbc, hE.i5]
    set c₁ : Config := { c with nreg := regB c.nmem tArgsL c.nreg } with hc₁
    have r0 : ztuqm := by_grind
    have r1 : c₁.nreg 83001 = E.NH := by_grind
    have r2 : c₁.nreg 83002 = E.r := by_grind
    have r3 : c₁.nreg 83003 = E.γ := by_grind
    have r4 : c₁.nreg 83004 = E.g := by_grind
    have r5 : c₁.nreg 83005 = c.nreg 81060 := by_omega
    have r6 : c₁.nreg 83006 = c.nreg 81061 := by_omega
    have r7 : c₁.nreg 83007 = c.nreg 81062 := by_omega
    have r8 : c₁.nreg 83008 = c.nreg 81063 := by_omega
    have r9 : c₁.nreg 83009 = E.d := by_grind
    have rfr : ∀ q, ztofa → c₁.nreg q = c.nreg q := by_omega
    have hA₁ : ztdc := rfr _ by_decide
    have hc' : CandOK E ztkkd (c₁.nreg 83007) (c₁.nreg 83008) := by
      grind
    have pre := test_pre hE hI₁ r0 r1 r2 r3 r4 r9 hc'
    have hcost : E.κt (c₁.nreg 83009) * (E.F (c₁.nreg 83003) + 1) =
        E.κt E.d * ztriy := by_grind
    refine FRS.seq ((FRS.call hT hBT hI₁ pre (by rw [hcost, hA₁]; unfold tK at hroom; omega)
      (fun c' hp q hq => hp.1 q (band8 zthfo zthfo)
        zthfo)).mono (le_of_eq hcost) (fun _ h => h))
      (fun c₂ hI₂ _ hp => ?_)
    obtain ⟨⟨hkeep, b10, b11, b14, hres⟩, -, -⟩ := hp
    have z₂ : zturh := by rw [hI₂.hin _ ztbc, hE.k0]
    -- the record of a success
    have hwin : FRS B E.P E.W c₀ ztpru c₂ 6 (fun c₃ =>
        (∀ q, ztoez → c₃.nreg q = c₂.nreg q) ∧
        (c₃.nreg 81007 = 1 ↔ c₂.nreg 83014 = 1) ∧ c₃.nreg 81007 ≤ 1 ∧
        (c₂.nreg 83014 = 1 → c₃.nreg 81008 = c₂.nreg 83015 ∧ c₃.nreg 81009 = c₂.nreg 83016 ∧
          c₃.nreg 81010 = c₂.nreg 83017)) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b14 with s0 | s1
      · have g' : ¬ c₂.nreg 81011 < c₂.nreg 83014 := by_omega
        refine (FRS.ifF g' (FRS.skip hI₂ (K := 0) (Q := fun c' => c' = c₂) rfl)).mono
          by_omega ?_
        zufxk
        zummw
        have e7 : ztpni := by
          rw [hkeep 81007 zthdw by_omega, rfr _ by_omega, h0]
        exact ⟨by_omega, by_omega, by_omega, fun h => by_omega⟩
      · have g' : c₂.nreg 81011 < c₂.nreg 83014 := by_omega
        refine (FRS.ifT g' (FRS.block hB tWinL hI₂ (okB_tWin hW1 _ _))).mono
          by_rfl ?_
        zufxk
        zummw
        obtain ⟨w8, w9, w10, w7, wfr⟩ := tWin_eff c₂.nmem c₂.nreg
        exact ⟨wfr, by simp only []; omega, by_rfl,
          fun _ => ⟨w8, w9, w10⟩⟩
    refine hwin.mono le_rfl (fun c₃ ⟨h3fr, h3s, h3le, h3t⟩ => ?_)
    have keep₂ := fun q h1 h2 =>
      hkeep q (band8 h1 by_omega) h2
    refine ⟨fun q h1 h2 => ?_, h3le, fun h => by_omega, fun _ => ?_⟩
    · rw [h3fr q by_omega, keep₂ q by_omega h2, rfr q by_omega]
    -- the contract of the test, for the candidate of `c`
    have e10 : c₃.nreg 83010 = c₂.nreg 83010 := h3fr _ by_omega
    have e11 : c₃.nreg 83011 = c₂.nreg 83011 := h3fr _ by_omega
    have e12 : ztsho := h3fr _ by_omega
    have e13 : c₃.nreg 83013 = c₂.nreg 83013 := h3fr _ by_omega
    refine ⟨by_omega, by_omega, fun reg hregs => ?_⟩
    have hag := hI.agree hE
    obtain ⟨hMD', -⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
    have hMD₁ : ModelDescAt c₁.nmem (c₁.nreg 83000) zti E.M := by rw [r0]; omega
    have hNA₁ : NFAt c₁.nmem (c₁.nreg 83001) E.N := by
      zvnal; exact NFWithin.nfAt (hE.hNW.transport hag)
    have hres' := hres E.M E.N reg hMD₁ hNA₁ hE.hNF hregs
    simp only [r2, r5, r6, r8] at hres'
    obtain ⟨p1, p2, p3⟩ := hres'
    simp only [e10, e11, e12, e13]
    refine ⟨fun hs => ?_, fun hv hh => ?_, p3⟩
    · have hs' := h3s.1 hs
      obtain ⟨t8, t9, t10⟩ := h3t hs'
      rw [t8, t9, t10]; exact p1 hs'
    · obtain ⟨T, hT0, q1, q2, q3, q4, q5, q6, q7, q8⟩ := p2 hv hh
      exact ⟨T, hT0, q1, q2, q3, q4, q5, q6, q7, h3s.trans q8⟩
  · -- the flag is set: nothing happens
    have g : ¬ c.nreg 81007 < c.nreg 81012 := by_omega
    refine (FRS.ifF g (FRS.skip hI (K := 0) rfl)).mono (by unfold tK; omega) ?_
    zuu
    exact ⟨fun q _ _ => rfl, hfl, by_omega, by_simp_all⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs

/-- The loop body of the halving. -/
def halfBodyL : List Instr := [.subN 81120 81120 81022, .addN 81121 81121 81023]

/-- The end of the halving: read the table, then the parity. -/
def halfEndL : List Instr := [.addN 81124 81004 81014, .loadN 81124 81124,
  .addN 81124 81124 81120, .loadN 81124 81124, .addN 81121 81121 81124,
  .addN 81124 81121 81121, .subN 81122 81123 81124]

/-- **Halving**: `81121 := 81120 / 2`, `81122 := 81120 % 2` (`81120`, `81123`, `81124` are
scratch). -/
def halfS : Stmt :=
  .seq (Stmt.block [.copyN 81123 81120, .constN 81121 0])
    (.seq (.whileLtN 81020 81120 ztvdj) (Stmt.block halfEndL))

/-! ## Register effects -/
variable (m f : ℕ → ℕ)
theorem halfBody_eff :
    regB m halfBodyL f 81120 = f 81120 - f 81022 ∧
      regB m halfBodyL f 81121 = f 81121 + f 81023 ∧
      ∀ q, q ≠ 81120 → q ≠ 81121 → regB m halfBodyL f q = f q := by
  refine ⟨by_rfl, by_rfl,
    fun q h1 h2 => regB_other m _ f ztdp⟩
  simp only [halfBodyL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> zvmwd <;> omega
theorem halfEnd_eff :
    regB m halfEndL f 81121 = f 81121 + m ztetz ∧
      regB m halfEndL f 81122 =
        f 81123 - (f 81121 + m ztetz +
          (f 81121 + m ztetz)) ∧
      ∀ q, q ≠ 81121 → q ≠ 81122 → q ≠ 81124 → regB m halfEndL f q = f q := by
  refine ⟨by_rfl, by_rfl,
    fun q h1 h2 h3 => regB_other m _ f ztdp⟩
  simp only [halfEndL, List.mem_cons, List.not_mem_nil, or_false] at hi
  zupt

/-- The cost bound of a halving of `x`. -/
def halfK (n x : ℕ) : ℕ := 4 * (x / ztnfa) + 11
variable {E : FEnv} {c₀ c : Config}

/-- The halving table in a configuration of the search. -/
theorem halves_at (hE : FGood E c₀) (hI : FInv E.W c₀ c) :
    c.nreg 81004 + 3 < c.nreg ALLOC ∧ ∀ x, x ≤ E.P.n →
      c.nmem ztrmi + x < c.nreg ALLOC ∧
      c.nmem (c.nmem ztrmi + x) = x / 2 := by
  zubnt

  have hX : E.X.holds E.P c.nmem E.g ztm :=
    E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ (fun a ha => (hag a ha).symm) hE.hX)
  have g4 : ztuoh := by rw [hI.hin _ by_tauto, hE.i4]
  rw [g4]
  exact hE.hhalf _ _ _ _ hX

/-- **Halving** as a run step of the search. -/
theorem halfS_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {x : ℕ} (hx : c.nreg 81120 = x) (hroom : c.nreg ALLOC + halfK E.P.n x ≤ E.W) :
    FRS B E.P E.W c₀ halfS c (halfK E.P.n x) (fun c' => c'.nreg 81121 = x / 2 ∧
      c'.nreg 81122 = x % 2 ∧ ∀ q, q ≠ 81120 → q ≠ 81121 → q ≠ 81122 → q ≠ 81123 →
        q ≠ 81124 → c'.nreg q = c.nreg q) := by
  have hn3 : 3 ≤ E.P.n := hE.hG.1.1
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81020 = E.P.n ∧ c'.nreg 81022 = 2 * ztnks ∧
      c'.nreg 81023 = E.P.n / 2 ∧ c'.nreg 81014 = 3 := fun c' hI' =>
    ⟨by zuoad,
      by rw [hI'.hin _ ztbc, hE.nE],
      by rw [hI'.hin _ ztbc, hE.hE2],
      by rw [hI'.hin _ ztbc, hE.k3]⟩
  have hxW : x ≤ E.W := by rw [← hx]; exact hI.hw.1 81120
  set nE := 2 * ztnks with hnE
  have hnE2 : 2 ≤ nE := by_omega
  have ok0 : okB E.W c.nmem [.copyN 81123 81120, .constN 81121 0] c.nreg := by
    simp [okB, okI, FScr, FOut]
  refine (FRS.seq (K₂ := 4 * (x / nE) + 9) ztemq
    ztbzx).mono (by simp [halfK, hnE]; omega) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81123 81120, .constN 81121 0] c.nreg q :=
    fun q => by zvnbm
  have c1a : c₁.nreg 81123 = x := by zumwx; tauto
  have c1b : c₁.nreg 81121 = 0 := by_tauto
  have c1c : ztuqk := by zumwx; tauto
  have c1fr : ∀ q, q ≠ 81121 → q ≠ 81123 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    zuib
  have hA₁ : ztdc := c1fr _ by_decide
    by_decide
  -- the loop
  let I : Config → Prop := fun c' => c'.nreg 81123 = x ∧ c'.nreg 81120 + 2 * c'.nreg 81121 = x ∧
    ∀ q, q ≠ 81120 → q ≠ 81121 → q ≠ 81122 → q ≠ 81123 → q ≠ 81124 → c'.nreg q = c.nreg q
  have hI1 : ztkzz := ⟨c1a, by_omega, fun q h1 h2 _ h4 _ => c1fr q h2 h4⟩
  obtain ⟨f20, f22, f23, f14⟩ := fx c hI
  have hpos : ∀ c', I c' → c'.nreg 81020 < c'.nreg 81120 → 0 < c'.nreg 81120 / nE := by
    intro c' hc' ht
    rw [hc'.2.2 81020 by_omega by_omega by_omega by_omega by_omega, f20] at ht
    exact Nat.div_pos by_omega by_omega
  have hbody : ∀ c', FInv E.W c₀ c' → I c' → c'.nreg 81020 < c'.nreg 81120 →
      c'.nreg ALLOC + 2 ≤ E.W →
      FRS B E.P E.W c₀ ztvdj c' 2
        (fun c'' => I c'' ∧ c''.nreg 81120 / nE < c'.nreg 81120 / nE) := by
    intro c' hI' hc' ht _
    obtain ⟨g20, g22, g23, -⟩ := fx c' hI'
    obtain ⟨i1, i2, i3⟩ := hc'
    rw [g20] at ht
    have ok : okB E.W c'.nmem halfBodyL c'.nreg := by
      simp only [halfBodyL, okB, okI, regI, FScr, FOut]
      refine ⟨Or.inl ztwmk, ⟨Or.inl (Or.inl ⟨by_norm_num,
        by norm_num⟩), ?_⟩, trivial⟩
      rw [upd_ne (show (81121 : ℕ) ≠ 81120 by norm_num),
        upd_ne (show (81023 : ℕ) ≠ 81120 by norm_num), g23]; omega
    refine (FRS.block hB halfBodyL hI' ok).mono by_rfl ztgix
    obtain ⟨b0, b1, bfr⟩ := halfBody_eff c'.nmem c'.nreg
    have e'' : ∀ q, c''.nreg q = regB c'.nmem halfBodyL c'.nreg q := fun q => by rw [h'']
    rw [g22] at b0
    rw [g23] at b1
    refine ⟨⟨by_grind, ?_, fun q h1 h2 h3 h4 h5 => ?_⟩,
      ?_⟩
    · grind
    · grind
    · have hsd := Nat.sub_mul_div (c'.nreg 81120) nE 1
      grind
  have hroom₁ : c₁.nreg ALLOC + ztssq * (c₁.nreg 81120 / nE) ≤ E.W := by
    rw [hA₁, c1c]; unfold halfK at hroom; grind
  refine FRS.seq (K₂ := 7) ((FRS.while I (fun c' => c'.nreg 81120 / nE) 2 hpos hbody hI₁ hI1
    hroom₁).mono (K' := 4 * (x / nE) + 2) (by rw [c1c]) (fun _ h => h))
    (fun c₂ hI₂ _ ⟨⟨j1, j2, j3⟩, jt⟩ => ?_)
  -- the end: the table
  obtain ⟨g20, -, -, g14⟩ := fx c₂ hI₂
  rw [g20, not_lt] at jt
  obtain ⟨hg3, htab⟩ := halves_at hE hI₂
  obtain ⟨ht1, ht2⟩ := htab _ jt
  zuivs
  have ok : okB E.W c₂.nmem halfEndL c₂.nreg := by
    simp only [halfEndL, okB, okI, regI, FScr, FOut]
    refine ⟨ztbaln,
      Or.inl ztwmk, ztbaqk,
      Or.inl ztwmk, ztbaqk,
      ⟨Or.inl ztcgx, ?_⟩, Or.inl ztcgx,
      trivial⟩ <;> simp [upd, g14] <;> omega
  refine (FRS.block hB halfEndL hI₂ ok).mono by_rfl ztcvh
  obtain ⟨e1, e2, efr⟩ := halfEnd_eff c₂.nmem c₂.nreg
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem halfEndL c₂.nreg q := fun q => by zunbh
  rw [g14, ht2] at e1 e2
  refine ⟨by rw [e₃, e1]; omega, by rw [e₃, e2, j1]; omega, fun q h1 h2 h3 h4 h5 => ?_⟩
  rw [e₃, efr q h2 h3 h5]; exact j3 q h1 h2 h3 h4 h5
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs

/-- The reads of the chord record. -/
def chordL : List Instr :=
  [.addN 81157 81121 81121, .addN 81157 81157 81157, .addN 81157 81157 81121,
    .addN 81158 81134 81014, .loadN 81158 81158, .addN 81157 81157 81158,
    .loadN 81152 81157, .addN 81157 81157 81012, .loadN 81153 81157,
    .addN 81157 81157 81012, .loadN 81154 81157, .addN 81157 81157 81012,
    .addN 81157 81157 81012, .loadN 81156 81157, .addN 81155 81152 81012]

/-- **Load the chord of the node `81150`.** -/
def chordLoad : Stmt := .seq ztoxv (.seq halfS (Stmt.block chordL))
theorem chordL_eff (m f : ℕ → ℕ) (h3 : f 81014 = 3) (h1 : f 81012 = 1) :
    let a := f 81121 + f 81121 + (f 81121 + f 81121) + f 81121 + m (f 81134 + 3)
    regB m chordL f 81152 = m a ∧ regB m chordL f 81153 = m ztdf ∧
      regB m chordL f 81154 = m ztqdi ∧ regB m chordL f 81156 = m (a + 1 + 1 + 1 + 1) ∧
      regB m chordL f 81155 = m a + 1 ∧
      ∀ q, q ≠ 81152 → q ≠ 81153 → q ≠ 81154 → q ≠ 81155 → q ≠ 81156 → q ≠ 81157 →
        q ≠ 81158 → regB m chordL f q = f q := by
  zumgj
  refine ⟨by simp [chordL, regB, regI, upd, h3, a], by zumyt,
    by zumyt, by zumyt,
    by zumyt, fun q q1 q2 q3 q4 q5 q6 q7 =>
      regB_other m _ f ztdp⟩
  simp only [chordL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> zvmwd <;> omega
variable {E : FEnv} {c₀ c : Config}

/-- The cost bound of `chordLoad`. -/
def clK (E : FEnv) (x : ℕ) : ℕ := halfK E.P.n x + 16
theorem chordLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N) {x : ℕ}
    (hx : c.nreg 81150 = x) (hk : x / 2 < N.nChords) (hh : (N.chord ztbhd).h + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + clK E x ≤ E.W) :
    FRS B E.P E.W c₀ chordLoad c (clK E x) (fun c' => c'.nreg 81121 = x / 2 ∧
      c'.nreg 81152 = (N.chord ztbhd).h ∧ c'.nreg 81153 = (N.chord ztbhd).lp ∧
      c'.nreg 81154 = (N.chord ztbhd).rp ∧ c'.nreg 81155 = (N.chord ztbhd).h + 1 ∧
      c'.nreg 81156 = (N.chord ztbhd).dn ∧
      ∀ q, ¬ ztnhy → ¬ (81152 ≤ q ∧ q ≤ 81158) → c'.nreg q = c.nreg q) := by
  have ok0 : ztmwh := by
    zumzu; exact ⟨Or.inl ztwmk, trivial⟩
  refine (FRS.seq (K₂ := halfK E.P.n x + 15) ztemq
    ztiy).mono (by simp [clK]; omega) (fun _ h => h)
  have e₁ : ztiei := fun q => by zvnbm
  have v20 : ztuqk := by zumwx; tauto
  have f₁ : ztkoj := fun q hq => by
    zutt
  zulp
  zuhwm
  refine (FRS.seq (K₂ := 15) (halfS_fs hE hB hI₁ v20 (by rw [hA₁']; unfold clK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨k2, _, f₂⟩ => ?_)).mono by_omega (fun _ h => h)
  have hN₂ : NFWithin c₂.nmem (c₂.nreg 81134) ztdq N := by
    rw [f₂ _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num,
      f₁ _ by_norm_num]
    exact Robust.transport hN (fun a ha => hI₂.hm a ha)
  have hNA := hN₂.nfAt
  obtain ⟨-, hch, -⟩ := nf_bounds hN₂
  have hk' : x / 2 < N.chords.length := hk
  obtain ⟨hB7, -⟩ := nf_bounds hN₂
  have hcb := hch _ hk
  have hA0 : c₀.nreg ALLOC ≤ c₂.nreg ALLOC := hI₂.hA
  zuivs
  obtain ⟨r1, r2, r3, r4, r5⟩ := hNA.2.2.2.2.2.1 _ hk'
  have k3 : zturi := by rw [hI₂.hin _ ztbc, hE.k3]
  zubrb
  set k := x / 2
  have hm5 : k + k + zttqc + k + c₂.nmem ztcze + 4 < E.W := by_omega
  have hh' : c₂.nmem (k + k + zttqc + k + c₂.nmem ztcze) + 1 ≤ E.W := by
    grind
  have hb3 : c₂.nreg 81134 + 3 ≤ E.W := by_omega
  have ok : okB E.W c₂.nmem chordL c₂.nreg := by
    simp only [chordL, okB, okI, regI, upd]
    simp only [FScr, FOut, k2, k3, k1]
    norm_num
    omega
  refine (FRS.block hB _ hI₂ ok).mono by_rfl ztcvh
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem chordL c₂.nreg q := fun q => by zunbh
  obtain ⟨u52, u53, u54, u56, u55, uf⟩ := chordL_eff c₂.nmem c₂.nreg k3 k1
  have ea : c₂.nreg 81121 + c₂.nreg 81121 + (c₂.nreg 81121 + c₂.nreg 81121) + c₂.nreg 81121 +
      c₂.nmem ztcze = c₂.nmem ztcze + 5 * k := by_omega
  rw [ea] at u52 u53 u54 u56 u55
  refine ⟨by rw [e₃, uf _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, k2], by rw [e₃, u52, r1], by rw [e₃, u53, r2],
    by rw [e₃, u54, show c₂.nmem ztcze + 5 * k + 1 + 1 = c₂.nmem ztcze + 5 * k + 2 by ring,
      r3], by rw [e₃, u55, r1],
    by rw [e₃, u56, show c₂.nmem ztcze + 5 * k + 1 + 1 + 1 + 1 = c₂.nmem ztcze + 5 * k + 4
      by ring, r5], fun q h1 h2 => ?_⟩
  rw [e₃, uf q by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
    f₂ q by_omega by_omega by_omega by_omega by_omega, f₁ q by_omega]
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs NFLoc

/-- The decomposition nodes lie below the bound of a protected normal form. -/
theorem dec_bound {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) {k : ℕ}
    (hk : k < N.dec.length) : m ztjgp + 3 * k + 2 < E := by
  have := robust_addr2 (b := B + 8) (o := 3 * k + 2) (v := (N.dnode k).hi)
    (fun m' hm' => by
      have := ((h m' hm').2.2.2.2.2.2.2.2.2.1 k hk).2.2
      omega)
  omega

/-- The reads of the reference arc: the arc-list offset of region `dn`. -/
def refL1 : List Instr :=
  [.addN 81116 81134 81015, .loadN 81116 81116, .addN 81116 81116 81156,
    .addN 81116 81116 81156, .addN 81116 81116 81156, .addN 81116 81116 81156,
    .addN 81116 81116 81156, .addN 81116 81116 81012, .loadN 81116 81116]

/-- The first arc of region `dn`. -/
def refL2 : List Instr :=
  [.addN 81117 81134 81016, .loadN 81117 81117, .addN 81116 81117 81116, .loadN 81116 81116]

/-- The start of that arc. -/
def refL3 : List Instr :=
  [.addN 81117 81134 81014, .addN 81117 81117 81012, .loadN 81117 81117,
    .addN 81117 81117 81116, .addN 81117 81117 81116, .addN 81117 81117 81116,
    .addN 81117 81117 81116, .addN 81117 81117 81116, .addN 81117 81117 81012,
    .loadN 81108 81117, .addN 81117 81117 81012, .loadN 81109 81117]

/-- **The reference arc.** -/
def refLoad : Stmt := .seq (Stmt.block refL1) (.seq (Stmt.block refL2) (Stmt.block refL3))

/-- The reads of the children. -/
def kidL : List Instr :=
  [.addN 81115 81134 81016, .addN 81115 81115 81012, .loadN 81115 81115,
    .addN 81115 81115 81121, .addN 81115 81115 81121, .addN 81115 81115 81121,
    .addN 81115 81115 81012, .loadN 81118 81115, .addN 81115 81115 81012, .loadN 81119 81115]

/-- **The children of the node.** -/
def kidLoad : Stmt := Stmt.block kidL
variable {E : FEnv} {c₀ c : Config}
theorem refLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N)
    (hdn : c.nreg 81156 < N.nRegions) (har : 0 < (N.region zthvc).arcs.length)
    (hj : (N.region zthvc).arcs.getD 0 0 < N.arcs.length) :
    FRS B E.P E.W c₀ refLoad c 25 (fun c' =>
      c'.nreg 81108 = (N.arc ztyml).s.edge ∧
      c'.nreg 81109 = (N.arc ztyml).s.hgt ∧
      ∀ q, q ≠ 81108 → q ≠ 81109 → q ≠ 81116 → q ≠ 81117 → c'.nreg q = c.nreg q) := by
  have hN' : ztzox :=
    Robust.transport hN zttj
  zuclx

  zubwb

  have hrl : c.nreg 81156 < N.regions.length := hdn
  zudqm
  have rj := hl 0 har
  rw [Nat.add_zero] at rj
  obtain ⟨-, s1, s2, -, -⟩ := hNA.2.2.2.2.2.2.1 _ hj
  have b1 := hrb _ hdn
  have b2 := hlb _ hdn 0 har
  rw [Nat.add_zero] at b2
  zujws
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81015 = 5 ∧ c'.nreg 81016 = 7 ∧ c'.nreg 81014 = 3 ∧
      c'.nreg 81012 = 1 := fun c' h =>
    ⟨by zuoaf, by zuoag,
      by zuoah, by zuoai⟩
  zueja
  -- stage 1
  have ok1 : okB E.W c.nmem refL1 c.nreg := by
    simp only [refL1, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k1]
    grind
  zuhiv
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem refL1 c.nreg q := fun q => by zvnbm
  zulp
  have v16 : c₁.nreg 81116 = c.nmem (c.nmem ztfqh + 5 * c.nreg 81156 + 1) := by
    zumwx; simp [refL1, regB, regI, upd, k5, k1]; grind
  have f₁ : ∀ q, q ≠ 81116 → c₁.nreg q = c.nreg q := fun q hq => by
    zugct
    simp only [refL1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> omega
  obtain ⟨-, k7₁, -, -⟩ := fx c₁ hI₁
  have w34 := f₁ 81134 by_norm_num
  -- stage 2
  have ok2 : okB E.W c₁.nmem refL2 c₁.nreg := by
    simp only [refL2, okB, okI, regI, upd]
    simp only [FScr, FOut, k7₁, w34, v16, m₁]
    grind
  refine FRS.seq (K₂ := 12) ztjiu ztcne
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem refL2 c₁.nreg q := fun q => by rw [h₂]
  zukik
  have v16' : c₂.nreg 81116 = (N.region zthvc).arcs.getD 0 0 := by
    zunag; simp [refL2, regB, regI, upd, k7₁, w34, v16, m₁]; exact rj
  have f₂ : ∀ q, q ≠ 81116 → q ≠ 81117 → c₂.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₂, regB_other _ _ _ ztdp, f₁ q h1]
    simp only [refL2, List.mem_cons, List.not_mem_nil, or_false] at hi
    zubca
  obtain ⟨-, -, k3₂, k1₂⟩ := fx c₂ hI₂
  have x34 := f₂ 81134 by_norm_num by_norm_num
  zujxl
  generalize hjdef : (N.region zthvc).arcs.getD 0 0 = j at v16' b3 s1 s2 ⊢
  -- stage 3
  have ok3 : okB E.W c₂.nmem refL3 c₂.nreg := by
    simp only [refL3, okB, okI, regI, upd]
    simp only [FScr, FOut, k3₂, k1₂, x34, v16', m₂]
    norm_num
    zujhw
    omega
  refine (FRS.block hB _ hI₂ ok3).mono by_rfl ztcvh
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem refL3 c₂.nreg q := fun q => by zunbh
  have ea : c.nmem zthvb + j + j + j + j + j + 1 =
      c.nmem zthvb + 5 * j + 1 := by_ring
  refine ⟨?_, ?_, fun q h1 h2 h3 h4 => ?_⟩
  · zumzv; zuncg; grind
  · zumzv; zuncg
    grind
  · rw [e₃, regB_other _ _ _ ztdp, f₂ q h3 h4]
    simp only [refL3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zubzs
theorem kidLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem zteqz ztdq N)
    (hk : c.nreg 81121 < N.dec.length) :
    FRS B E.P E.W c₀ kidLoad c 10 (fun c' =>
      c'.nreg 81118 = (N.dnode ztfgt).lo ∧ c'.nreg 81119 = (N.dnode ztfgt).hi ∧
      ∀ q, q ≠ 81115 → q ≠ 81118 → q ≠ 81119 → c'.nreg q = c.nreg q) := by
  have hN' : ztzox :=
    Robust.transport hN zttj
  zuglr
  have hdb := dec_bound hN' hk
  have hB8 : c.nreg 81134 + 11 < c₀.nreg ALLOC := by
    have := robust_addr (v := N.dec.length) fun m' hm' => (hN' m' hm').2.2.2.2.1
    omega
  zubwb

  obtain ⟨-, r1, r2⟩ := hNA.2.2.2.2.2.2.2.2.2.1 _ hk
  have k7 : ztpme := by rw [hI.hin _ ztbc, hE.k7]
  zuhr
  set k := c.nreg 81121
  set B8 := c.nmem (c.nreg 81134 + 8)
  have e8 : c.nreg 81134 + 7 + 1 = c.nreg 81134 + 8 := by_ring
  have ok : okB E.W c.nmem kidL c.nreg := by
    simp only [kidL, okB, okI, regI, upd]
    simp only [FScr, FOut, k7, k1]
    grind
  zucpb
  have e' : ∀ q, c'.nreg q = regB c.nmem kidL c.nreg q := fun q => by zvmxl
  have ea : B8 + k + k + k + 1 = B8 + 3 * k + 1 := by_ring
  refine ztkio
  · zucel
  · zucel
  · zvmwg
    zunn
    simp only [kidL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      omega
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim ShootCut

/-- The reversed index `n - 1 - e` of the interior walk. -/
def hvRev (a : ℕ) : Stmt := Stmt.block [.subN 81062 81020 81012, .subN 81062 81062 a]

/-- The interior model: `iIdx bit n e`. -/
def hvInt (a : ℕ) : Stmt :=
  .seq (Stmt.block [.addN 81064 81000 81012, .loadN 81064 81064])
    (.ifLtN 81012 81064 ztqqv (.ifLtN 81011 81064 (Stmt.block [.copyN 81062 a]) ztqqv))

/-- A chain model: the ordinate record of `ptKey`. -/
def hvChainL (a : ℕ) : List Instr := [.addN 50200 81000 81012, .copyN 50201 a, .constN 50202 0]
def hvChain (a : ℕ) : Stmt :=
  .seq (Stmt.block ztvwl) (.seq ptKey (Stmt.block [.copyN 81062 50215]))

/-- **The height vertex** of the walk vertex in register `a`. -/
def fHv (a : ℕ) : Stmt :=
  .seq (Stmt.block [.loadN 81064 81000]) (.ifLtN 81011 81064 (hvInt a) (hvChain a))

/-- The cost bound of `fHv`. -/
def hvK : ℕ := 15820
variable {E : FEnv} {c₀ c : Config}
theorem fscr_5 {r : ℕ} (h1 : 50000 ≤ r) (h2 : r < 60000) : FScr r := by
  refine Or.inr ?_
  zucvl
  zuvs
theorem pos_vtx0 (M : Model) (Q : Polygon) (e : ℕ) : M.pos Q ztjy = M.wa e := by
  show Geometry.lerp ztmbq ztmbr _ = M.wa e
  simp

/-- **The height vertex** as a run step of the search. -/
theorem fHv_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {a : ℕ} (ha1 : 80000 ≤ a) (ha2 : a < 90000) (ha62 : a ≠ 81062) (ha64 : a ≠ 81064)
    (hea : c.nreg a < E.M.W.n)
    (hset : ∀ C : Chain, E.M = chainModel C → E.M.pos zti ztegx ∈ C.set)
    (hroom : c.nreg ALLOC + hvK ≤ E.W) :
    FRS B E.P E.W c₀ (fHv a) c hvK (fun c' => c'.nreg 81062 < E.P.n ∧
      ((Qof E.P).vtx (c'.nreg 81062)).2 = (E.M.pos zti ztegx).2 ∧
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c'.nreg q = c.nreg q) := by
  zubnt

  zudrh

  zuiyp
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81000 = E.MD ∧ c'.nreg 81011 = 0 ∧
      c'.nreg 81012 = 1 ∧ c'.nreg 81020 = E.P.n := fun c' hI' =>
    ⟨by rw [hI'.hin _ by_tauto, hE.i0],
      by zuoac,
      by zuoae,
      by zuoad⟩
  obtain ⟨i0, k0, k1, pn⟩ := fx c hI
  zuki
  have hMD6 := le_trans hwf.1 hA
  have ok0 : okB E.W c.nmem [.loadN 81064 81000] c.nreg := by
    zurp
  refine (FRS.seq (K₂ := 15819) ztemq (fun c₁ hI₁ hA₁' h₁ => ?_)).mono
    by_rfl ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.loadN 81064 81000] c.nreg q := by_simp_all
  zulp
  have r64 : c₁.nreg 81064 = c.nmem E.MD := by zumwx; simp [regB, regI, upd, i0]
  have f₁ : ∀ q, q ≠ 81064 → c₁.nreg q = c.nreg q := fun q hq => by
    zutt
  zuhwj
  obtain ⟨j0, j11, j12, j20⟩ := fx c₁ hI₁
  have hfin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 →
      c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c'.nreg q = c.nreg q :=
    by grind
  have ea : ztsgl := by_grind
  zucip
  · -- a chain model: `ptKey`
    refine (FRS.ifF by_omega ?_).mono (K := 15819) by_omega ztb
    have ok : okB E.W c₁.nmem ztvwl c₁.nreg := by
      simp only [hvChainL, okB, okI]
      exact ⟨⟨fscr_5 by_norm_num by_norm_num |> Or.inl, by_omega⟩,
        Or.inl zttkg,
        ⟨Or.inl zttkg, by_omega⟩, trivial⟩
    refine FRS.seq (K₂ := 15814) ztpyj zthgu
    have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem _ c₁.nreg q := fun q => by rw [h₂]
    zukik
    have s00 : c₂.nreg 50200 = E.MD + 1 := by
      zunag; simp [hvChainL, regB, regI, upd, j0, j12]
    have s01 : c₂.nreg 50201 = c.nreg a := by
      rw [e₂, ← ea]
      simp [hvChainL, regB, regI, upd, show a ≠ 50200 by omega]
    have s02 : c₂.nreg 50202 = 0 := by_tauto
    have f₂ : ∀ q, 80000 ≤ q → c₂.nreg q = c₁.nreg q := fun q hq => by
      zunag
      zunn
      zufbo
      rcases hi with rfl | rfl | rfl <;> zvmwd <;> omega
    have hA₂ : ztbae := by
      rw [e₂, regB_other _ _ _ ztdp, hA₁]
      zufbo
      rcases hi with rfl | rfl | rfl <;> zvmwd <;> unfold ALLOC <;> omega
    -- the preconditions of `ptKey`
    have hC₂ : ChainDescAt c₂.nmem ztqkk zti H C := by_grind
    have hwf₂ : ChainWF E.P zthwb c₂.nmem ztqkk := by
      rw [m₂, s00, hA₂]; exact hwfc.2 h0
    have h0' : E.m₀ E.MD = 0 := by rw [← hag _ (by have := hE.hwf.1; omega)]; exact h0
    obtain ⟨H₀, C₀, hC₀, -⟩ : ∃ H₀ C₀, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H₀ C₀ ∧
        E.M = chainModel C₀ := by
      rcases hE.hMD with ⟨-, H₀, C₀, hC₀, hM₀⟩ | ⟨h1, -, -⟩
      · grind
      omega
    have hreg₀ := hE.hreg h0' H₀ C₀ hC₀
    obtain ⟨-, -, hEb, -⟩ := (hE.hwf.2 h0').2 H₀ C₀ hC₀
    have hH₀ : HostAt c.nmem _ H₀ := Gran.hostAt_agree' hC₀.1 hEb hag
    have e1 : c.nmem _ = E.m₀ ztcsy := hag _ (by have := hE.hwf.1; omega)
    have hregH : ∀ H', HostAt c₂.nmem (c₂.nmem ztqkk) H' → HostRegular E.P.n H' := by
      zujap
      rw [m₂, s00, e1] at hH'
      have  := NFLoc.hostAt_unique hH₀ hH'
      zumo
      rw [show (Qof E.P).n = E.P.n from shear_n _ _] at hreg₀
      omega
    have hWn : (chainModel C).W.n = E.M.W.n := by zvmzx
    have hpos : (chainModel C).pos zti ztegx ∈ C.set := by
      grind
    have hpre : PrimPre PtIn E.P E.W c₂ := ⟨hE.hG, hE.hWh, hwf₂, H, C, hC₂,
      by omega,
      by rw [s01, s02]; exact ztdjf,
      Or.inl s02, hregH⟩
    obtain ⟨c₃, k₃, ex₃, hk₃, post₃, hfr₃⟩ := ptKey_meets E.P E.W c₂ hI₂.hw hpre
      (by rw [hA₂]; unfold hvK at hroom; grind)
    replace hk₃ : k₃ ≤ 15800 := hk₃
    obtain ⟨pr, -⟩ := post₃ H C hC₂
    rw [s01, s02] at pr
    obtain ⟨-, hy, -⟩ := pr
    have hyR : |((chainModel C).pos _ ⟨c.nreg a, 0⟩).2| < C.radius :=
      lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hpos).2 C.coordBound_lt_radius
    obtain ⟨t14, -, t15, t15e⟩ : c₃.nreg 50214 = 1 ∧ True ∧ c₃.nreg 50215 < E.P.n ∧
        ((chainModel C).pos zti ztegx).2 = ((Qof E.P).vtx (c₃.nreg 50215)).2 := by
      rcases hy with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨k, -, hl, hv⟩
      · rw [hv, abs_neg, abs_of_pos C.radius_pos] at hyR; grind
      · rw [hv, abs_of_pos C.radius_pos] at hyR; grind
      grind
    have h8 := fun q h1 h2 =>
      hfr₃.1 q ztcmc
        ztu
    refine FRS.seq (K₂ := 1) (FRS.prim (Q := fun c' => c' = c₃) hB hI₂ ex₃ hfr₃ le_rfl by_omega rfl)
      ztnyr
    subst h₄
    have ok' : okB E.W c₄.nmem [.copyN 81062 50215] c₄.nreg := by
      zurp
    refine (FRS.block hB _ hI₄ ok').mono le_rfl ztqnm
    have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.copyN 81062 50215] c₄.nreg q := fun q => by
      zueyl
    have v62 : c₅.nreg 81062 = c₄.nreg 50215 := by zunkr; rfl
    refine ⟨by_omega, by_grind, hfin c₅ fun q h1 h2 h3 _ => ?_⟩
    rw [e₅, show regB c₄.nmem [.copyN 81062 50215] c₄.nreg q = c₄.nreg q by
      zundy, h8 q h1 h2, f₂ q h1]
  · -- the interior model: `iIdx bit n e`
    refine (FRS.ifT by_omega ?_).mono (K := 15819) by_omega ztb
    have ok : okB E.W c₁.nmem [.addN 81064 81000 81012, .loadN 81064 81064] c₁.nreg := by
      zudu
      exact ⟨ztzof,
        Or.inl ztec, trivial⟩
    refine FRS.seq (K₂ := 8) ztpyj zthgu |>.mono
      by_simp ztb
    have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem [.addN 81064 81000 81012, .loadN 81064 81064]
        c₁.nreg q := fun q => by rw [h₂]
    set bit := c.nmem _ with hbit'
    have b64 : c₂.nreg 81064 = bit := by zunag; simp [regB, regI, upd, j0, j12, m₁, hbit']
    have f₂ : ∀ q, q ≠ 81064 → c₂.nreg q = c₁.nreg q := fun q hq => by
      zunag; zumyf
    obtain ⟨-, l11, l12, l20⟩ := fx c₂ hI₂
    have he : c.nreg a < E.P.n := by rw [hM, interior_n] at hea; omega
    have ha' : c₂.nreg a = c.nreg a := by_grind
    -- the reversed index
    have hrev : ∀ c' : Config, FInv E.W c₀ c' → (∀ q, q ≠ 81064 → c'.nreg q = c₂.nreg q) →
        c'.nreg 81064 = bit → bit ≠ 1 →
        FRS B E.P E.W c₀ ztqqv c' 2 (fun c'' => c''.nreg 81062 < E.P.n ∧
          ((Qof E.P).vtx (c''.nreg 81062)).2 = (E.M.pos zti ztegx).2 ∧
          ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81062 → q ≠ 81064 → c''.nreg q = c.nreg q) := by
      intro c' hI' hc' _ hb1
      have okr : okB E.W c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a] c'.nreg := by
        zudu
        exact ⟨Or.inl ztec,
          Or.inl ztec, trivial⟩
      refine (FRS.block hB _ hI' okr).mono le_rfl ztgix
      have e'' : ∀ q, c''.nreg q = regB c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a]
          c'.nreg q := fun q => by rw [h'']
      have v62 : ztyyk := by
        have w20 : c'.nreg 81020 = E.P.n := by_grind
        have w12 : ztunf := by_grind
        have wa : c'.nreg a = c.nreg a := by_grind
        zupan
        unfold iIdx; rw [ite_eq_right hb1]
        simp [regB, regI, upd, ha62, w20, w12, wa]
      refine ztfjv
      · zufop
      · rw [e'', show regB c'.nmem [.subN 81062 81020 81012, .subN 81062 81062 a] c'.nreg q =
          c'.nreg q by zundy, hc' q h4, f₂ q h4, f₁ q h4]
    have hI₂' := hI₂
    by_cases hb : 1 < bit
    · exact (FRS.ifT by_omega (hrev c₂ hI₂ by_omega b64
        by_omega)).mono by_omega by_grind
    refine FRS.ifF by_omega ?_ |>.mono (K := 8) by_omega ztb
    by_cases hb0 : 0 < bit
    · zuhya
      refine FRS.ifT by_omega ?_ |>.mono (K := 6) by_omega ztb
      have okc : okB E.W c₂.nmem [.copyN 81062 a] c₂.nreg := by
        zurp
      refine (FRS.block hB _ hI₂ okc).mono by_simp ztgix
      have e'' : ∀ q, c''.nreg q = regB c₂.nmem [.copyN 81062 a] c₂.nreg q := fun q => by
        rw [h'']
      have v62 : ztyyk := by
        zupan; zumxt; rw [ha']
        zumsv
      refine ztfjv
      · zufop
      · rw [e'', show regB c₂.nmem [.copyN 81062 a] c₂.nreg q = c₂.nreg q by
          zundy, f₂ q h4, f₁ q h4]
    · exact (FRS.ifF by_omega (hrev c₂ hI₂ by_omega b64
        by_omega)).mono by_omega by_grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt)

/-- **The result registers are sound.** -/
def FWin (E : FEnv) (c : Config) : Prop :=
  c.nreg 81007 ≤ 1 ∧ (c.nreg 81007 = 1 → ∀ reg, NFRegs E.M zti E.N reg →
    (recOf ztghj).Attached E.M zti ∧
    c.nreg 81008 < (Qof E.P).n ∧
    (recOf ztghj).toSet E.M zti ∈ E.M.Adm ∧
    SplitsWell E.M ztwky ztbuw
      ((recOf ztghj).toSet E.M zti))

/-- A good candidate at the walk vertex `v` in the direction of the bit `σb`. -/
def GoodAt (E : FEnv) (reg : ℕ → Set Point) (v σb : ℕ) : Prop :=
  ∃ T, GoodCand E.M zti ztwky ztbuw ztcfs ztbem T
variable {E : FEnv} {c₀ c : Config}

/-- **A test at a good candidate sets the flag.** -/
theorem TOut.good (hE : FGood E c₀) {c' : Config} (h : TOut E c c') {reg : ℕ → Set Point}
    (hregs : NFRegs E.M zti E.N reg) (hch : (E.N.region E.r).chords ≠ [])
    (hx1 : c.nreg 81061 = 0) (hg : GoodAt E reg ztmgh zteqx) :
    c'.nreg 81007 = 1 := by
  obtain ⟨T, hx0, hxe, hσ, hT, hsec, hdom, hout, hadm, hsw⟩ := hg
  obtain ⟨-, -, hcl⟩ := h
  obtain ⟨-, hex, hcomp⟩ := hcl reg hregs
  have hxeq : (zteya : WPos) = ztegw := by rw [hx1]
  rw [hxeq] at hex hcomp
  have hp0 : E.M.param zti ztegw = 0 := rfl
  obtain ⟨h10, h11⟩ := hcomp by_tauto hch T hT hdom hout hadm hsw.1 hsw.2.1
  obtain ⟨T', hT', hstr, hposf, hfe, hfp, hadm', hA, hB, hiff⟩ := hex h10 h11
  zuclv
  have hout' : rayPt ztzth ztbahm T' ∉ E.M.D := by
    rw [← hposf]
    exact hM.trace _ hfe _ hfp.1 hfp.2.1.le
  have hdom' : ∀ t, 0 < t → t < T' →
      rayPt ztzth ztbahm t ∈ E.M.D :=
    fun t h0 h1 => (Chazelle.Chain.regionsIn_subset zttoh ztrse).1
  obtain rfl : T = T' := exit_unique hT hT' hdom hout hdom' hout'
  refine hiff.2 ?_
  have hAB : sidePt E.M.W ztmgh (E.M.param zti ztegw) ≠
      sidePt E.M.W ztfgi (E.M.param zti ztha) := by
    show E.M.pos zti ztegw ≠ E.M.pos zti ztha
    zuikm
  exact counts_of_splitsWell hM hE.hNF.1.2.1 hE.hNF.1.1 zttoh hadm hA hB hAB hsw

/-- **The test call**, with the soundness of the result registers. -/
theorem tcall_win (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hcand : c.nreg 81007 = 0 →
      CandOK E zteya ztqie zteqx)
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ ztmou c ztqxe (fun c' => TKeep c c' ∧ FWin E c' ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg 81061 = 0 → GoodAt E reg ztmgh zteqx → c'.nreg 81007 = 1)) := by
  refine (tcall_fs hE hB hBT hI hw.1 hcand hroom).mono le_rfl ztijk
  zujdg
  · zulkz
    refine ⟨hk, zticm, fun h => by_omega,
      fun reg hregs hch hx1 hg => hout.good hE hregs hch hx1 hg⟩
  · zuetx
    refine ⟨hk, ztmqo, fun _ => f1, fun _ _ _ _ _ => f1⟩
    zuemr

/-! ## Testing a walk vertex in both directions -/

/-- **Test the walk vertex in register `a`** in both directions. -/
def tVert (a : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.copyN 81060 a, .constN 81061 0]) (.seq ztvqi
    (.seq (.seq (Stmt.block [.constN 81063 0]) ztmov)
      (.seq (Stmt.block [.constN 81063 1]) ztmov)))

/-- The cost bound of `tVert`. -/
def tvK (E : FEnv) : ℕ := 2 * tK E + hvK + 4

/-- The registers `tVert` writes below the test's registers. -/
def VertW (q : ℕ) : Prop := 81060 ≤ q ∧ q ≤ 81064

/-- **Testing a walk vertex** as a run step of the search. -/
theorem tVert_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {a : ℕ}
    (hv : c.nreg a < E.M.W.n)
    (hset : ∀ C : Chain, E.M = chainModel C → E.M.pos zti ztegx ∈ C.set)
    (hroom : c.nreg ALLOC + tvK E ≤ E.W) :
    FRS B E.P E.W c₀ (tVert a E.sT) c (tvK E) (fun c' => FWin E c' ∧
      ztfji ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        ∀ σb, σb ≤ 1 → GoodAt E reg ztcux σb → c'.nreg 81007 = 1)) := by
  zucb
  zuivr
  -- the candidate vertex
  have ok1 : okB E.W c.nmem [.copyN 81060 a, .constN 81061 0] c.nreg := by
    zudu
    exact ⟨Or.inl ztwmk,
      ⟨Or.inl ztcgx, by_omega⟩, trivial⟩
  refine (FRS.seq (K₂ := 2 * tK E + hvK + 2) ztbbr
    ztiy).mono
    (by simp only [List.length_cons, List.length_nil, tvK]; omega) ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81060 a, .constN 81061 0] c.nreg q :=
    fun q => by zvnbm
  have v60 : c₁.nreg 81060 = c.nreg a := by_tauto
  have v61 : c₁.nreg 81061 = 0 := by_tauto
  have f₁ : zthpe := fun q h1 h2 => by
    zuib
  have hA₁' : ztdc := f₁ _ by_decide
    by_decide
  -- the height vertex
  refine (FRS.seq (K₂ := 2 * tK E + 2) (fHv_fs hE hB hI₁ (a := 81060) by_norm_num
    by_norm_num by_norm_num by_norm_num by_omega by_simp_all
    (by rw [hA₁']; unfold tvK at hroom; omega)) (fun c₂ hI₂ hA₂ ⟨hv2, hy2, fr2⟩ => ?_)).mono
    by_omega ztb
  have g₂ : ∀ q, 80000 ≤ q → q < 90000 → q ≠ 81060 → q ≠ 81061 → q ≠ 81062 → q ≠ 81064 →
      c₂.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => by
    grind
  have w60 : c₂.nreg 81060 = c.nreg a := by
    grind
  have w61 : c₂.nreg 81061 = 0 := by
    grind
  have hw₂ : ztsbh := by
    zumqt
    rw [g₂ 81007 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num, g₂ 81008 by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, g₂ 81009 by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num, g₂ 81010 by_norm_num by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num]
    zulzb
  have hA₂' : c₂.nreg ALLOC ≤ c.nreg ALLOC + hvK := by_omega
  rw [v60] at hy2
  -- a direction bit and a test
  have dir : ∀ (b : ℕ) (cx : Config), b ≤ 1 → FInv E.W c₀ cx → FWin E cx →
      cx.nreg 81060 = c.nreg a → cx.nreg 81061 = 0 → cx.nreg 81062 = c₂.nreg 81062 →
      cx.nreg ALLOC + tK E + 1 ≤ E.W →
      FRS B E.P E.W c₀ (.seq (Stmt.block [.constN 81063 b]) ztmou) cx (tK E + 1)
        (fun c' => FWin E c' ∧ (∀ q, 81011 ≤ q → q < 83000 → q ≠ 81063 → c'.nreg q = cx.nreg q) ∧
          (cx.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
          (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
            GoodAt E reg ztcux b → c'.nreg 81007 = 1)) := by
    intro b cx hb hIx hwx x60 x61 x62 hrx
    have okb : okB E.W cx.nmem [.constN 81063 b] cx.nreg := by
      zumzu; exact ⟨ztbaln, trivial⟩
    refine (FRS.seq (K₂ := tK E) (FRS.block hB _ hIx okb) (fun cy hIy hAy hy => ?_)).mono
      by_grind ztb
    have ey : ∀ q, cy.nreg q = regB cx.nmem [.constN 81063 b] cx.nreg q := fun q => by rw [hy]
    have y63 : cy.nreg 81063 = b := by_tauto
    have fy : ∀ q, q ≠ 81063 → cy.nreg q = cx.nreg q := fun q hq => by
      rw [ey]; zumyf
    have hwy : FWin E cy := by
      zumqt
      rw [fy 81007 by_norm_num, fy 81008 by_norm_num, fy 81009 by_norm_num,
        fy 81010 by_norm_num]
      tauto
    have hcand : CandOK E ⟨cy.nreg 81060, cy.nreg 81061⟩ (cy.nreg 81062) (cy.nreg 81063) := by
      rw [fy _ by_norm_num, fy _ by_norm_num, fy _ by_norm_num, y63, x60, x61, x62]
      exact ⟨hv, ztdjf, Or.inl rfl,
        hset, hv2, hy2, hb⟩
    refine (tcall_win hE hB hBT hIy hwy (fun _ => hcand) (by
      grind)).mono le_rfl
      (fun c' ⟨hk, hw', hm, hg⟩ => ⟨hw', fun q h1 h2 h3 => by rw [hk q h1 h2, fy q h3], fun h => hm
        by_grind, fun reg hregs hch hgd => hg reg hregs hch
          by_grind by_grind⟩)
  refine (FRS.seq (K₂ := tK E + 1)
    (dir 0 c₂ by_norm_num hI₂ hw₂ w60 w61 rfl ztnwd)
    (fun c₄ hI₄ hA₄ ⟨hw₄, fr₄, hm₄, hg₄⟩ => ?_)).mono by_omega (fun _ h => h)
  refine (dir 1 c₄ le_rfl hI₄ hw₄ by_grind
    by_grind
    by_grind
    ztnwd).mono le_rfl
    (fun c₆ ⟨hw₆, fr₆, hm₆, hg₆⟩ => ⟨hw₆, fun q h1 h2 hq => ?_, fun h => hm₆ (hm₄ ?_),
      fun reg hregs hch σb hσb hgd => ?_⟩)
  · unfold VertW at hq
    rw [fr₆ q h1 h2 by_omega, fr₄ q h1 h2 by_omega]
    exact g₂ q by_omega by_omega by_omega by_omega by_omega by_omega
  · grind
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hσb with rfl | rfl
    · grind
    grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim

/-- Test the vertex in `81071` if it is in the candidate range. -/
def vTest (sT : Stmt) : Stmt :=
  .ifLtN 81071 81021 .skip (.ifLtN 81019 81071 .skip (tVert 81071 sT))

/-- The step of the vertex: `t + 1`, `v + 1 mod n`. -/
def k0StepL : List Instr := [.addN 81072 81072 81012, .addN 81071 81071 81012]

/-- **The light piece.** -/
def kind0 (sT : Stmt) : Stmt :=
  .seq (Stmt.block [.copyN 81071 81070, .constN 81072 0])
    (.whileLtN 81072 81024 (.seq (vTest sT) (.seq ztvdk
      ztipv)))

/-- The cost bound of `kind0`. -/
def k0K (E : FEnv) : ℕ := 10 * tvK E + 114
variable {E : FEnv} {c₀ c : Config}

/-- The candidate condition of a walk vertex: in a chain model, a point of the chain. -/
def VSet (E : FEnv) (v : ℕ) : Prop :=
  ∀ C : Chain, E.M = chainModel C → E.M.pos zti ztcfs ∈ C.set
theorem FWin.congr {c' : Config} (h : FWin E c) (h7 : c'.nreg 81007 = c.nreg 81007)
    (h8 : c'.nreg 81008 = c.nreg 81008) (h9 : c'.nreg 81009 = c.nreg 81009)
    (h10 : c'.nreg 81010 = c.nreg 81010) : FWin E c' := by
  unfold FWin; rw [h7, h8, h9, h10]; exact h

/-- **Testing a vertex in the candidate range.** -/
theorem vTest_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hv : c.nreg 81071 < E.M.W.n) (hroom : c.nreg ALLOC + tvK E ≤ E.W) :
    FRS B E.P E.W c₀ ztwho c (tvK E + 4) (fun c' => FWin E c' ∧
      ztfji ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        VSet E ztvit → ∀ σb, σb ≤ 1 → GoodAt E reg ztvit σb →
          c'.nreg 81007 = 1)) := by
  have r21 : ztmuo := hI.hin _ ztbc
  have r19 : c.nreg 81019 = c₀.nreg 81019 := hI.hin _ ztbc
  by_cases h1 : c.nreg 81071 < c.nreg 81021
  · refine (FRS.ifT h1 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ => rfl, id,
      fun reg _ _ hs _ _ _ => ?_⟩)).mono by_omega (fun _ h => h)
    have := (hE.hvc _ hv hs).1
    omega
  refine (FRS.ifF h1 ?_).mono (K := tvK E + 4) by_omega ztb
  by_cases h2 : c.nreg 81019 < c.nreg 81071
  · refine (FRS.ifT h2 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ => rfl, id,
      fun reg _ _ hs _ _ _ => ?_⟩)).mono by_omega (fun _ h => h)
    have := (hE.hvc _ hv hs).2
    omega
  refine (FRS.ifF h2 ?_).mono (K := tvK E + 2) by_omega ztb
  refine (tVert_fs hE hB hBT hI hw hv (hE.hvr _ hv by_omega by_omega) hroom).mono le_rfl
    (fun c' ⟨h1', h2', h3', h4'⟩ => ⟨h1', h2', h3', fun reg hr hch _ => h4' reg hr hch⟩)
theorem mod_step {n a : ℕ} (hn : 0 < n) :
    (if a % n + 1 < n then a % n + 1 else 0) = ztdf % n := by
  have hlt := Nat.mod_lt a hn
  have e := WalkEmbed.mod_succ_mod n a 0
  zvnhg at e
  zus
  · rw [← e, Nat.mod_eq_of_lt h]
  · have : ztplk := by_omega
    simp_all

/-- **A light piece** as a run step of the search. -/
theorem kind0_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {e₀ : ℕ}
    (he : c.nreg 81070 = e₀) (he₀ : e₀ < E.M.W.n) (hroom : c.nreg ALLOC + k0K E ≤ E.W) :
    FRS B E.P E.W c₀ (kind0 E.sT) c (k0K E) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81072 →
        c'.nreg q = c.nreg q) ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        ∀ t, t < 10 → VSet E ztbaak → ∀ σb, σb ≤ 1 →
          GoodAt E reg ztbaak σb → c'.nreg 81007 = 1)) := by
  zukzt
  zucmj
  have hW10 : 10 ≤ E.W := by
    have := hE.hWh; have := hE.hG.1.1; unfold hostWords at *; omega
  have hnW : n ≤ E.W := by
    have := hI.hw.1 81017
    rwa [hI.hin _ ztbc, hE.wn] at this
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81017 = n ∧ c'.nreg 81024 = 10 ∧
      c'.nreg 81012 = 1 := fun c' hI' =>
    ⟨by zuoab,
      by rw [hI'.hin _ ztbc, hE.k10],
      by zuoae⟩
  have ok0 : okB E.W c.nmem [.copyN 81071 81070, .constN 81072 0] c.nreg := by
    zudu
    exact ⟨Or.inl ztwmk,
      ⟨Or.inl ztcgx, by_omega⟩, trivial⟩
  refine (FRS.seq (K₂ := (tvK E + 11) * 10 + 2) ztemq
    ztiy).mono
    (by simp only [List.length_cons, List.length_nil, k0K]; omega) ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.copyN 81071 81070, .constN 81072 0] c.nreg q :=
    fun q => by zvnbm
  have v71 : c₁.nreg 81071 = e₀ := by zumwx; tauto
  have v72 : c₁.nreg 81072 = 0 := by_tauto
  have f₁ : ∀ q, q ≠ 81071 → q ≠ 81072 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    zuib
  have hA₁' : ztdc := f₁ _ by_decide
    by_decide
  -- the loop
  let I : Config → Prop := fun c' => c'.nreg 81072 ≤ 10 ∧
    c'.nreg 81071 = (e₀ + c'.nreg 81072) % n ∧ FWin E c' ∧
    (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81072 → c'.nreg q = c.nreg q) ∧
    ztfn ∧
    (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
      ∀ t, t < c'.nreg 81072 → VSet E ztbaal → ∀ σb, σb ≤ 1 →
        GoodAt E reg ztbaal σb → c'.nreg 81007 = 1)
  have hI1 : ztkzz := by
    refine ⟨by_omega, by rw [v71, v72, Nat.add_zero, Nat.mod_eq_of_lt he₀], ?_,
      fun q _ _ _ h4 h5 => f₁ q h4 h5, fun h => by_simp_all,
      fun _ _ _ t ht => by_omega⟩
    exact hw.congr zthxi zthxi
      zthxi zthxi
  have hbody : ∀ c', FInv E.W c₀ c' → I c' → c'.nreg 81072 < c'.nreg 81024 →
      c'.nreg ALLOC + ztrxq ≤ E.W →
      FRS B E.P E.W c₀ (.seq ztwho (.seq ztvdk
        ztipv)) c' (tvK E + 9)
        (fun c'' => I c'' ∧ 10 - c''.nreg 81072 < 10 - c'.nreg 81072) := by
    intro c' hI' ⟨i1, i2, i3, i4, i5, i6⟩ ht hr
    obtain ⟨g17, g24, g12⟩ := fx c' hI'
    rw [g24] at ht
    have hv' : c'.nreg 81071 < n := by rw [i2]; exact Nat.mod_lt _ hn0
    refine FRS.seq (K₂ := 5) (vTest_fs hE hB hBT hI' i3 hv' by_omega)
      (fun c₂ hI₂ hA₂ ⟨j1, j2, j3, j4⟩ => ?_)
    have k71 : c₂.nreg 81071 = c'.nreg 81071 := j2 _ by_norm_num by_norm_num
      ztod
    have k72 : c₂.nreg 81072 = c'.nreg 81072 := j2 _ by_norm_num by_norm_num
      ztod
    obtain ⟨-, -, h12⟩ := fx c₂ hI₂
    have ok : okB E.W c₂.nmem k0StepL c₂.nreg := by
      simp only [k0StepL, okB, okI, regI]
      refine ⟨ztbaln,
        ⟨Or.inl ztcgx, ?_⟩, trivial⟩
      rw [upd_ne by_norm_num, upd_ne by_norm_num, k71, h12]; omega
    refine FRS.seq (K₂ := 3) (FRS.block hB _ hI₂ ok) ztcnf
    have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem k0StepL c₂.nreg q := fun q => by zunbh
    have u71 : c₃.nreg 81071 = c'.nreg 81071 + 1 := by
      zumzv; simp [k0StepL, regB, regI, upd, k71, h12]
    have u72 : c₃.nreg 81072 = c'.nreg 81072 + 1 := by
      zumzv; simp [k0StepL, regB, regI, upd, k72, h12]
    have f₃ : ∀ q, q ≠ 81071 → q ≠ 81072 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
      zumzv; simp [k0StepL, regB, regI, upd, h1, h2]
    obtain ⟨h17, -, -⟩ := fx c₃ hI₃
    -- the post-state facts, given the new vertex
    have fin : ∀ c₄ : Config, c₄.nreg 81072 = c'.nreg 81072 + 1 →
        c₄.nreg 81071 = (e₀ + (c'.nreg 81072 + 1)) % n →
        (∀ q, q ≠ 81071 → c₄.nreg q = c₃.nreg q) →
        I c₄ ∧ 10 - c₄.nreg 81072 < 10 - c'.nreg 81072 := by
      intro c₄ w72 w71 f₄
      have g : ∀ q, q ≠ 81071 → q ≠ 81072 → c₄.nreg q = c₂.nreg q := fun q h1 h2 => by
        rw [f₄ q h1, f₃ q h1 h2]
      refine ⟨⟨by_omega, by rw [w71, w72], ?_, fun q h1 h2 h3 h4 h5 => ?_, fun h => ?_,
        fun reg hr hch t htl hs σb hσb hg => ?_⟩, by_omega⟩
      · exact j1.congr zthxj zthxj
          zthxj zthxj
      · rw [g q h4 h5, j2 q h1 h2 h3, i4 q h1 h2 h3 h4 h5]
      · zumwu; omega
      · zumwu
        rw [w72] at htl
        rcases Nat.lt_succ_iff_lt_or_eq.1 htl with htl | rfl
        · exact j3 (i6 reg hr hch t htl hs σb hσb hg)
        · rw [← i2] at hs hg; exact j4 reg hr hch hs σb hσb hg
    by_cases hc : c₃.nreg 81071 < c₃.nreg 81017
    · refine (FRS.ifT hc (FRS.skip (K := 0) hI₃ (fin c₃ u72 ?_ ztcj))).mono
        by_omega ztb
      rw [u71, i2, ← Nat.add_assoc, ← mod_step hn0, ite_eq_left by_omega]
    · have okc : okB E.W c₃.nmem [.constN 81071 0] c₃.nreg := by
        zudu
        exact ⟨ztbaln, trivial⟩
      refine (FRS.ifF hc ztpym).mono by_simp ztqnl
      have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem [.constN 81071 0] c₃.nreg q := fun q => by
        zumok
      refine fin c₄ (by zunce; tauto) ?_
        (fun q hq => by zunce; zumyf)
      zunce; zumxt
      rw [← Nat.add_assoc, ← mod_step hn0, ite_eq_right by_omega]
  have hroom₁ : c₁.nreg ALLOC + (tvK E + 9 + 2) * (10 - c₁.nreg 81072) ≤ E.W := by
    rw [hA₁', v72]; unfold k0K at hroom; omega
  have k24 : c.nreg 81024 = 10 := (fx c hI).2.1
  have w24 : ∀ c', I c' → c'.nreg 81024 = 10 := fun c' hc' => by
    rw [hc'.2.2.2.1 _ by_norm_num by_norm_num ztod by_norm_num
      by_norm_num, k24]
  refine (FRS.while I (fun c' => 10 - c'.nreg 81072) ztrxq (fun c' hc' ht => ?_) hbody
    hI₁ hI1 hroom₁).mono (by rw [v72]) (fun c' ⟨hc', ht⟩ => ⟨hc'.2.2.1, hc'.2.2.2.1,
      hc'.2.2.2.2.1, fun reg hr hch t ht' => hc'.2.2.2.2.2 reg hr hch t (by
        rw [w24 c' hc'] at ht; omega)⟩)
  rw [w24 c' hc'] at ht; omega
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

/-- The setup of a key comparison. -/
def fKeySetL : List Instr := [.addN 83020 81000 81012, .loadN 83021 81000, .constN 83022 0,
  .constN 83023 1, .copyN 83000 81000]

/-- **A key comparison** of the host positions `(a, b)` and `(d, e)`. -/
def fKey (a b d e : ℕ) : Stmt := .seq (Stmt.block fKeySetL) ztjxb
theorem fKeySet_eff (m f : ℕ → ℕ) :
    regB m fKeySetL f 83020 = f 81000 + f 81012 ∧ regB m fKeySetL f 83021 = m (f 81000) ∧
      regB m fKeySetL f 83022 = 0 ∧ regB m fKeySetL f 83023 = 1 ∧
      regB m fKeySetL f 83000 = f 81000 ∧
      ∀ q, q ≠ 83000 → q ≠ 83020 → q ≠ 83021 → q ≠ 83022 → q ≠ 83023 →
        regB m fKeySetL f q = f q := by
  refine ⟨by_rfl, by_rfl,
    by rfl, by_rfl,
    by rfl, fun q h0 h1 h2 h3 h4 => regB_other m _ f ztdp⟩
  simp only [fKeySetL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> omega
variable {E : FEnv} {c₀ c : Config}

/-- The registers a key comparison writes in band `bRestore`. -/
def KeyW (q : ℕ) : Prop := q = 83000 ∨ (83020 ≤ q ∧ q ≤ 83023)

/-- **A key comparison** as a run step of the search. -/
theorem fKey_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {a b d e : ℕ} (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e)
    (hx : PosG E.M zti E.P.n ztel)
    (hy : PosG E.M zti E.P.n ztge)
    (hroom : c.nreg ALLOC + 11020 ≤ E.W) :
    FRS B E.P E.W c₀ ztqmx c 11020 (fun c' =>
      BitIs c' 50210 (E.M.key zti ztel <
        E.M.key zti ztge) ∧
      BitIs c' 50211 (E.M.key zti ztge <
        E.M.key zti ztel) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → c'.nreg q = c.nreg q) := by
  zubnt

  zudrh

  have i0 : ztuog := by rw [hI.hin _ by_tauto, hE.i0]
  zuhr
  zuivr
  have hMD6 : E.MD + 6 ≤ c.nreg ALLOC := le_trans hwf.1 hA
  have ok : okB E.W c.nmem fKeySetL c.nreg := by
    simp only [fKeySetL, okB, okI, FScr, FOut]
    grind
  refine (FRS.seq (K₂ := 11010) (FRS.block hB fKeySetL hI ok) ztbzx).mono
    by_decide ztb
  obtain ⟨s20, s21, s22, s23, s00, sfr⟩ := fKeySet_eff c.nmem c.nreg
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem fKeySetL c.nreg q := fun q => by zvnbm
  zulp
  have hA₁ : ztdc := by
    tauto
  have f₁ : ztkol := fun q hq => by
    unfold KeyW at hq
    grind
  have r20 : c₁.nreg 83020 = E.MD + 1 := by_simp_all
  have r21 : c₁.nreg 83021 = c.nmem E.MD := by_simp_all
  have r22 : ztuqn := by_simp_all
  have r23 : ztlxx := by_simp_all
  have r00 : ztuqm := by_simp_all
  have hx₁ : PosG E.M zti E.P.n ztkkf := by_simp_all
  have hy₁ : PosG E.M zti E.P.n ztkkg := by_simp_all
  rw [← f₁ a hka, ← f₁ b hkb, ← f₁ d hkd, ← f₁ e hke]
  have hfin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → c'.nreg q = c.nreg q := fun c' h q h1 h2 hq =>
    (h q h1 h2).trans (f₁ q hq)
  zucip
  · -- a chain model
    have hx' : PosOK C zti E.P.n ztkkf := by
      zvmzx at hx₁; exact ⟨hx₁.1, hx₁.2.1, hx₁.2.2 C rfl⟩
    have hy' : PosOK C zti E.P.n ztkkg := by
      zvmzx at hy₁; exact ⟨hy₁.1, hy₁.2.1, hy₁.2.2 C rfl⟩
    have hC₁ : ChainDescAt c₁.nmem ztmib zti H C := by_grind
    have hwf₁ : ChainWF E.P ztbmq c₁.nmem ztmib := by
      rw [m₁, r20, hA₁]; exact hwfc.2 h0
    obtain ⟨c', k, ex, hk, b1, b2, hf⟩ := keyCmp_exec ha hb hd he hI₁.hw hE.hG hE.hWh hwf₁ hC₁
      r22 hx' hy' (walk_le_W hE.hMD hE.hwf hE.hWh hM) by_omega
    have h8 : zthpa := fun q h1 h2 =>
      hf.1 q ztcmc
        ztu
    refine FRS.prim hB hI₁ ztcrz hf by_omega by_omega
      ⟨by_grind, by_grind, hfin c' h8⟩
  · -- the interior model
    have hn := interior_n (P := E.P)
    have hD : c₁.nreg 83000 + 1 ≤ E.W := by_omega
    have hmd : c₁.nmem ztroc = c.nmem ztcsy := by_grind
    zvmzx at hx₁ hy₁
    obtain ⟨c', k, ex, hk, b1, b2⟩ := iKey_exec (P := E.P) (a := a) (b := b) (d := d) (e := e)
      hE.hG (by have := hE.hWh; unfold hostWords at this; omega) hI₁.hw hbit hmd hD
      (by intro r hr; zvmxh at hr
          unfold InR at ha hb hd he
          omega)
      hx₁.2.1 hy₁.2.1 (by zvocr; exact hx₁.1) (by zvocr; exact hy₁.1)
    have hfr : FrameB Bik c₁ c' := exec_frameB ex ztqys
    have hf := frame_of_frameB hfr Bik_band k
    have h8 : zthpa := fun q h1 h2 =>
      hf.1 q ztcmc
        ztu
    refine FRS.prim hB hI₁ ztdrw hf by_omega
      by_omega ⟨by_grind, by_grind, hfin c' h8⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK

/-- **Host key comparison** into `r`, `r + 1`. -/
def cmpM (r a b d e : ℕ) : Stmt :=
  .seq ztqmx ztxbf

/-- The setup of a comparison in the piece's chain model. -/
def cmpAL : List Instr := [.copyN 83020 81133, .constN 83022 0]

/-- **Piece-chain key comparison** into `r`, `r + 1`. -/
def cmpA (r a b d e : ℕ) : Stmt :=
  .seq (Stmt.block cmpAL) (.seq ztjzm
    ztxbf)
variable {E : FEnv} {c₀ c : Config}

/-- The output registers of a comparison: band `bRestore`, scratch, not a key register. -/
def CmpR (r : ℕ) : Prop := 81028 ≤ r ∧ r + 1 < 83000
theorem copy2 {c₁ : Config} {r : ℕ} (hr : CmpR r) (hI₁ : FInv E.W c₀ c₁) {B : Finset ℕ}
    (hB : dBands ⊆ B) :
    FRS B E.P E.W c₀ ztxbf c₁ 2 (fun c' =>
      c'.nreg r = c₁.nreg 50210 ∧ c'.nreg ztgu = c₁.nreg 50211 ∧
      ∀ q, q ≠ r → q ≠ r + 1 → c'.nreg q = c₁.nreg q) := by
  unfold CmpR at hr
  have ok : okB E.W c₁.nmem [.copyN r 50210, .copyN ztgu 50211] c₁.nreg := by
    zudu
    exact ztbaog
  zugak
  have e' : ∀ q, c'.nreg q = regB c₁.nmem [.copyN r 50210, .copyN ztgu 50211] c₁.nreg q :=
    fun q => by zvmxl
  refine ⟨by zvmwg; zumxd, by zvmwg; simp [regB, regI, upd,
      show (50211 : ℕ) ≠ r by omega], fun q h1 h2 => by zvmwg; zunbs⟩

/-- **Host key comparison** as a run step of the search. -/
theorem cmpM_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e)
    (hx : PosG E.M zti E.P.n ztel)
    (hy : PosG E.M zti E.P.n ztge)
    (hroom : c.nreg ALLOC + 11022 ≤ E.W) :
    FRS B E.P E.W c₀ (cmpM r a b d e) c 11022 (fun c' =>
      BitIs c' r (E.M.key zti ztel <
        E.M.key zti ztge) ∧
      BitIs c' ztgu (E.M.key zti ztge <
        E.M.key zti ztel) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  refine FRS.seq (K₂ := 2) (fKey_fs hE hB hI ha hb hd he hka hkb hkd hke hx hy
    by_omega) (fun c₁ hI₁ _ ⟨b1, b2, f1⟩ => ?_)
  refine (copy2 hr hI₁ hB).mono le_rfl (fun c' ⟨v1, v2, f2⟩ => ⟨b1.of_eq v1, b2.of_eq v2,
    fun q h1 h2 h3 h4 h5 => by_simp_all⟩)

/-- **Piece-chain key comparison** as a run step of the search. -/
theorem cmpA_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztm c.nmem ztcpp)
    (hC : ChainDescAt c.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hx : PosOK Cα zti E.P.n ztel)
    (hy : PosOK Cα zti E.P.n ztge)
    (hroom : c.nreg ALLOC + 11010 ≤ E.W) :
    FRS B E.P E.W c₀ ztpae c 11010 (fun c' =>
      BitIs c' r ((chainModel Cα).key zti ztel <
        (chainModel Cα).key zti ztge) ∧
      BitIs c' ztgu ((chainModel Cα).key zti ztge <
        (chainModel Cα).key zti ztel) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  have ok : okB E.W c.nmem cmpAL c.nreg := by
    simp only [cmpAL, okB, okI]
    refine ⟨Or.inl ztwmk,
      ⟨Or.inl ztcgx, by_omega⟩, trivial⟩
  refine FRS.seq (K₂ := 11008) ztgds ztiy
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem cmpAL c.nreg q := fun q => by zvnbm
  zulp
  have r20 : c₁.nreg 83020 = c.nreg 81133 := by_tauto
  have r22 : ztuqn := by_tauto
  have f₁ : ∀ q, q ≠ 83020 → q ≠ 83022 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    zumwx; simp [cmpAL, regB, regI, upd, h1, h2]
  have hA₁' : ztdc := f₁ _ by_decide
    by_decide
  have kf : ztkol := fun q hq => by
    unfold KeyW at hq; grind
  have hx₁ : PosOK Cα zti E.P.n ztkkf := by
    simp_all
  have hy₁ : PosOK Cα zti E.P.n ztkkg := by
    simp_all
  obtain ⟨c₂, k₂, ex, hk, b1, b2, hf⟩ := keyCmp_exec ha hb hd he hI₁.hw hE.hG hE.hWh
    by_simp_all (by rw [m₁, r20]; exact hC) r22 hx₁ hy₁ hWm
    by_omega
  have h8 : ∀ q, 80000 ≤ q → q < 90000 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    hf.1 q ztcmc
      ztu
  refine FRS.seq (K₂ := 2) (FRS.prim (Q := fun c' => c' = c₂) hB hI₁ ex hf le_rfl by_omega rfl)
    ztnyq
  subst h₃
  rw [kf a hka, kf b hkb, kf d hkd, kf e hke] at b1 b2
  refine (copy2 hr hI₃ hB).mono le_rfl (fun c' ⟨v1, v2, f2⟩ => ⟨b1.of_eq v1, b2.of_eq v2,
    fun q h1 h2 h3 h4 h5 => by_grind⟩)
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {E : FEnv} {c₀ c : Config}

/-- A scratch register of the search outside the candidate and the test's registers. -/
def SReg (r : ℕ) : Prop := 81028 ≤ r ∧ r < 83000

/-- **Setting a scratch register.** -/
theorem setR_fs {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c) {r v : ℕ} (hr : SReg r)
    (hv : v ≤ E.W) :
    FRS B E.P E.W c₀ (Stmt.block [.constN r v]) c 1 (fun c' => c'.nreg r = v ∧
      ∀ q, q ≠ r → c'.nreg q = c.nreg q) := by
  unfold SReg at hr
  have ok : okB E.W c.nmem [.constN r v] c.nreg := by
    zumzu; exact ⟨⟨Or.inl ztwor, hv⟩, trivial⟩
  refine (FRS.block hB _ hI ok).mono by_simp zthi
  have e' : ∀ q, c'.nreg q = regB c.nmem [.constN r v] c.nreg q := fun q => by zvmxl
  exact ⟨by zvmwg; zumxd, fun q hq => by zvmwg; zumyf⟩

/-- The host edge and height code of an end strictly inside the stretch. -/
def endMap (s p : ℕ) : Stmt :=
  .seq (Stmt.block [.subN ztbk p 81131, .subN ztcfg 81017 81130])
    (.seq (.ifLtN ztbk ztcfg ztypw
      ztypx)
      (.seq (Stmt.block [.constN ztfp 0])
        (.ifLtN 81011 ztyd (Stmt.block [.copyN ztfp 81155]) .skip)))

/-- **The host position of an end.** -/
theorem endMap_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s p : ℕ} (hs : SReg s) (hs9 : SReg ztcfg) (_hp1 : p ≠ s + 1) (_hp9 : p ≠ s + 9)
    (hsF : ∀ q, FFix q → q ≠ s + 1 ∧ q ≠ s + 2 ∧ q ≠ s + 9) (h7 : s + 7 ≠ s + 2)
    (h71 : s + 7 ≠ s + 1) (h79 : s + 7 ≠ s + 9) (h1 : s + 1 ≠ 81130) (h9 : s + 9 ≠ 81130)
    (h55 : 81155 ≠ s + 1 ∧ 81155 ≠ s + 2 ∧ 81155 ≠ s + 9)
    (hp : c.nreg 81131 ≤ c.nreg p) (hg : c.nreg 81130 < E.M.W.n)
    (hd : c.nreg p - c.nreg 81131 < E.M.W.n) (_hb7 : c.nreg ztyd ≤ 1) :
    FRS B E.P E.W c₀ zttju c 10 (fun c' =>
      c'.nreg ztbk = ztdcr % E.M.W.n ∧
      (c.nreg ztyd = 1 → c'.nreg ztfp = c.nreg 81155) ∧
      (c.nreg ztyd = 0 → c'.nreg ztfp = 0) ∧
      ∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c.nreg q) := by
  unfold SReg at hs hs9
  zukzt
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81017 = n ∧ c'.nreg 81011 = 0 :=
    fun c' hI' => ⟨by zuoab,
      by zuoac⟩
  obtain ⟨n17, k0⟩ := fx c hI
  have h17 : s + 1 ≠ 81017 := (hsF 81017 ztbc).1.symm
  have h17' : s + 9 ≠ 81017 := (hsF 81017 ztbc).2.2.symm
  have ok : okB E.W c.nmem [.subN ztbk p 81131, .subN ztcfg 81017 81130] c.nreg := by
    zudu
    exact ztbaog
  refine FRS.seq (K₂ := 8) ztgds ztbzx
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN ztbk p 81131, .subN ztcfg 81017 81130]
      c.nreg q := fun q => by zvnbm
  have v1 : c₁.nreg ztbk = c.nreg p - c.nreg 81131 := by
    zumwx; zumxd
  have v9 : c₁.nreg ztcfg = n - c.nreg 81130 := by
    zumwx; simp [regB, regI, upd, n17, show s ≠ 81016 by omega, show s ≠ 81129 by omega]
  have f₁ : ∀ q, q ≠ s + 1 → q ≠ s + 9 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    zuib
  have w30 := f₁ 81130 ztjkn (Ne.symm h9)
  -- the host edge
  have step2 : FRS B E.P E.W c₀ (.ifLtN ztbk ztcfg ztypw
      ztypx) c₁ 3 (fun c' =>
        c'.nreg ztbk = ztdcr % n ∧
        ∀ q, q ≠ s + 1 → c'.nreg q = c₁.nreg q) := by
    by_cases hc : c₁.nreg ztbk < c₁.nreg ztcfg
    · have okc : okB E.W c₁.nmem [.addN ztbk ztbk 81130] c₁.nreg := by
        zudu
        refine ⟨⟨Or.inl ztwor, ?_⟩, trivial⟩
        have := hI₁.hw.1 81017
        grind
      refine (FRS.ifT hc (ztgdt)).mono by_simp zthi
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.addN ztbk ztbk 81130] c₁.nreg q :=
        fun q => by zvmxl
      refine ztfae
      zujn
      rw [v1, w30, Nat.mod_eq_of_lt by_omega]; omega
    · have okc : okB E.W c₁.nmem [.subN ztbk ztbk ztcfg] c₁.nreg := by
        zugzn
      refine (FRS.ifF hc (ztgdt)).mono by_simp zthi
      have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN ztbk ztbk ztcfg] c₁.nreg q :=
        fun q => by zvmxl
      refine ztfae
      zujn
      rw [v1, v9] at hc ⊢
      have e2 : c.nreg 81130 + (c.nreg p - c.nreg 81131) =
          (c.nreg p - c.nreg 81131 - ztrtw) + n := by_omega
      zuhlc
  refine FRS.seq (K₂ := 5) step2 (fun c₂ hI₂ _ ⟨u1, g₂⟩ => ?_)
  refine FRS.seq (K₂ := 4) (setR_fs hB hI₂ (r := s + 2) ztgy ztbg)
    (fun c₃ hI₃ _ ⟨u2, g₃⟩ => ?_)
  have g7 : c₃.nreg ztyd = c.nreg ztyd := by
    rw [g₃ _ h7, g₂ _ h71, f₁ _ h71 h79]
  have g11 : c₃.nreg 81011 = 0 := (fx c₃ hI₃).2
  have fin : ∀ c' : Config, (∀ q, q ≠ s + 2 → c'.nreg q = c₃.nreg q) →
      ∀ q, q ≠ s + 1 → q ≠ s + 2 → q ≠ s + 9 → c'.nreg q = c.nreg q :=
    fun c' h q h1 h2 h3 => by rw [h q h2, g₃ q h2, g₂ q h1, f₁ q h1 h3]
  by_cases hc : c₃.nreg 81011 < c₃.nreg ztyd
  · have okc : okB E.W c₃.nmem [.copyN ztfp 81155] c₃.nreg := by
      zugzn
    refine (FRS.ifT hc ztpym).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₃.nmem [.copyN ztfp 81155] c₃.nreg q :=
      fun q => by zvmxl
    have f' : ∀ q, q ≠ s + 2 → c'.nreg q = c₃.nreg q := fun q hq => by
      zubls
    refine ⟨by rw [f' _ by_omega, g₃ _ by_omega, u1], fun _ => ?_, fun h0 => by
      omega, fin c' f'⟩
    zujn
    rw [g₃ _ h55.2.1, g₂ _ h55.1, f₁ _ h55.1 h55.2.2]
  · exact (FRS.ifF hc (FRS.skip (K := 0) hI₃ ⟨by rw [g₃ _ by_omega, u1],
      fun h1 => by_omega, fun _ => u2, fin c₃ ztcj⟩)).mono
      by_omega ztb
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}
theorem sideInArc_iff' (a b x : ℝ) :
    sideInArc a b x ↔ (a < b ∧ ztnqr) ∨ ztyxr := by
  zujv

/-- `r := if [i] then [j] ∧ [k] else [j] ∨ [k]`. -/
def side3 (r i j k : ℕ) : Stmt :=
  .seq ztihr
    (.ifLtN 81011 i (.ifLtN 81011 j ztzah .skip)
      (.ifLtN 81011 j ztbpr
        ztzah))

/-- A bit routine's frame. -/
def BitFr (r : ℕ) (c c' : Config) : Prop := ∀ q, q ≠ r → c'.nreg q = c.nreg q
theorem k0_of (hE : FGood E c₀) (hI : FInv E.W c₀ c) : c.nreg 81011 = 0 := by
  zuoaa
theorem side3_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j k : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) (_hr11 : r ≠ 81011)
    {p q s : Prop} (hi : BitIs c i p) (hj : BitIs c j q) (hk : BitIs c k s) :
    FRS B E.P E.W c₀ (side3 r i j k) c 8 (fun c' =>
      BitIs c' r ztyu ∧ BitFr r c c') := by
  zucb
  refine (FRS.seq (K₂ := 7) ztxxz ztcvg).mono
    by_omega ztb
  zuxg

  have bk : BitIs c₁ k s := hk.of_eq (f₁ k ztvbo)
  have nil : ¬ ztyu →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r ztyu ∧
        BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  have one : ztyu →
      FRS B E.P E.W c₀ ztbpr c₁ 1 (fun c' =>
        BitIs c' r ztyu ∧ BitFr r c c') := fun hy =>
    (setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v hy, fun x hx => (f x hx).trans ztnzr⟩)
  have b1 : ztbvi :=
    fun h => by zvnib; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by zunkp; omega⟩
  zudwu
  · zuhfl
    refine (FRS.ifT a1 ?_).mono (K := 7) le_rfl ztb
    zubjx
    · have hq := (b1 bj).1 a2
      refine (FRS.ifT a2 ?_).mono (K := 5) by_omega ztb
      zuhrz
      · exact (FRS.ifT a3 (one (Or.inl ⟨hp, hq, (b1 bk).1 a3⟩))).mono by_omega ztb
      · exact (FRS.ifF a3 (nil (fun h => by
          grind))).mono by_omega (fun _ h => h)
    · exact (FRS.ifF a2 (nil (fun h => by
        grind))).mono by_omega (fun _ h => h)
  · zufwb
    refine (FRS.ifF a1 ?_).mono (K := 7) le_rfl ztb
    zubjx
    · exact (FRS.ifT a2 (one (Or.inr ⟨hp, Or.inl ztosj⟩))).mono by_omega
        ztb
    refine (FRS.ifF a2 ?_).mono (K := 5) le_rfl ztb
    zuhrz
    · exact (FRS.ifT a3 (one (Or.inr ⟨hp, Or.inr ((b1 bk).1 a3)⟩))).mono by_omega
        ztb
    · exact (FRS.ifF a3 (nil (fun h => by
        grind))).mono by_omega (fun _ h => h)

/-- `r := [r] ∨ (¬[i] ∧ ¬[j])`. -/
def eqor (r i j : ℕ) : Stmt := .ifLtN 81011 i .skip ztzaf
theorem eqor_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) {p q s : Prop} (hrr : BitIs c r s) (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (eqor r i j) c 5 (fun c' => BitIs c' r (s ∨ (¬ p ∧ ¬ q)) ∧ BitFr r c c') := by
  zucb
  zubgm
  have b1 : ∀ {x : ℕ} {P : Prop}, BitIs c x P → (c.nreg 81011 < c.nreg x ↔ P) :=
    fun h => by zvnib; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by zunkp; omega⟩
  by_cases a1 : c.nreg 81011 < c.nreg i
  · exact (FRS.ifT a1 (FRS.skip (K := 0) hI ⟨hrr.congr ⟨Or.inl, fun h => h.resolve_right
      (fun h' => h'.1 ((b1 hi).1 a1))⟩, fun _ _ => rfl⟩)).mono by_omega (fun _ h => h)
  zueka
  by_cases a2 : c.nreg 81011 < c.nreg j
  · exact (FRS.ifT a2 (FRS.skip (K := 0) hI ⟨hrr.congr ⟨Or.inl, fun h => h.resolve_right
      (fun h' => h'.2 ((b1 hj).1 a2))⟩, fun _ _ => rfl⟩)).mono by_omega (fun _ h => h)
  · exact (FRS.ifF a2 ((setR_fs hB hI hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v (Or.inr ⟨fun h => a1 ((b1 hi).2 h), fun h => a2 ((b1 hj).2 h)⟩), f⟩))).mono
      by_omega ztb

/-- `r := ([i] ↔ [j])`. -/
def xnorR (r i j : ℕ) : Stmt :=
  .seq ztihr
    (.ifLtN 81011 i ztzag
      ztzaf)
theorem xnorR_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (xnorR r i j) c 6 (fun c' => BitIs c' r zthjc ∧ BitFr r c c') := by
  zucb
  refine (FRS.seq (K₂ := 5) ztxxz ztcvg).mono
    by_omega ztb
  zuxg

  have b1 : ztbvi :=
    fun h => by zvnib; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by zunkp; omega⟩
  have one : zthjc → FRS B E.P E.W c₀ ztbpr c₁ 1 (fun c' =>
      BitIs c' r zthjc ∧ BitFr r c c') := fun hy =>
    (setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨BitIs.const_one v hy, fun x hx => (f x hx).trans ztnzr⟩)
  have nil : ¬ zthjc → FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r zthjc ∧
      BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  zudwu
  · zuhfl
    zuekb
    zubjx
    · exact (FRS.ifT a2 (one ⟨fun _ => (b1 bj).1 a2, fun _ => hp⟩)).mono by_omega
        ztb
    · exact (FRS.ifF a2 (nil (fun h => a2 ((b1 bj).2 (h.1 hp))))).mono by_omega ztb
  · zufwb
    zueka
    zubjx
    · exact (FRS.ifT a2 (nil (fun h => hp (h.2 ztosj)))).mono by_omega ztb
    · exact (FRS.ifF a2 (one ⟨fun h => absurd h hp, fun h => absurd ((b1 bj).2 h) a2⟩)).mono
        by_omega ztb

/-- `r := [i] ∧ [j]`. -/
def andR (r i j : ℕ) : Stmt :=
  .seq ztihr
    (.ifLtN 81011 i ztzag .skip)
theorem andR_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r i j : ℕ} (hr : SReg r) (hri : r ≠ i) (hrj : r ≠ j) {p q : Prop} (hi : BitIs c i p)
    (hj : BitIs c j q) :
    FRS B E.P E.W c₀ (andR r i j) c 6 (fun c' => BitIs c' r ztoed ∧ BitFr r c c') := by
  zucb
  refine (FRS.seq (K₂ := 5) ztxxz ztcvg).mono
    by_omega ztb
  zuxg

  have b1 : ztbvi :=
    fun h => by zvnib; exact ⟨fun h' => h.2.1 (by have := h.1; omega),
      fun h' => by zunkp; omega⟩
  have nil : ¬ ztoed → FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => BitIs c' r ztoed ∧
      BitFr r c c') := fun hn => FRS.skip hI₁ ⟨BitIs.const_zero v₁ hn, f₁⟩
  zudwu
  · zuekb
    zubjx
    · exact (FRS.ifT a2 ((setR_fs hB hI₁ hr hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
        ⟨BitIs.const_one v ⟨(b1 bi).1 a1, (b1 bj).1 a2⟩, fun x hx => (f x hx).trans
          ztnzr⟩))).mono by_omega (fun _ h => h)
    · exact (FRS.ifF a2 (nil (fun h => a2 ((b1 bj).2 h.2)))).mono by_omega ztb
  · exact (FRS.ifF a1 (nil (fun h => a1 ((b1 bi).2 h.1)))).mono by_omega ztb
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- A chain descriptor below the search's base allocator stays readable. -/
theorem chain_keep {P : Polygon} {A : ℕ} {m m' : ℕ → ℕ} {D : ℕ} {H : Host} {Cα : Chain}
    (hwf : ChainWF P A m D) (hC : ChainDescAt m D zta H Cα) (he : ∀ a, a < A → m' a = m a)
    {A' : ℕ} (hA : A ≤ A') : ChainDescAt m' D zta H Cα ∧ ChainWF P A' m' D := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H Cα hC
  zuivl
  exact ⟨ShotList.chainDescAt_copy hC hEb he by_grind,
    ShotList.chainWF_copy hwf hC he by_grind by_omega hA⟩

/-- **Piece-chain comparison** with the descriptor fixed below the base allocator. -/
theorem cmpA_fs₀ (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {r a b d e : ℕ} (hr : CmpR r) (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e)
    (hka : ¬ KeyW a) (hkb : ¬ KeyW b) (hkd : ¬ KeyW d) (hke : ¬ KeyW e) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztdq c₀.nmem ztcpp)
    (hC : ChainDescAt c₀.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hx : PosOK Cα zti E.P.n ztel)
    (hy : PosOK Cα zti E.P.n ztge)
    (hroom : c.nreg ALLOC + 11010 ≤ E.W) :
    FRS B E.P E.W c₀ ztpae c 11010 (fun c' =>
      BitIs c' r ((chainModel Cα).key zti ztel <
        (chainModel Cα).key zti ztge) ∧
      BitIs c' ztgu ((chainModel Cα).key zti ztge <
        (chainModel Cα).key zti ztel) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r → q ≠ r + 1 → c'.nreg q = c.nreg q) := by
  zufje
  exact cmpA_fs hE hB hI hr ha hb hd he hka hkb hkd hke hwf' hC' hWm hx hy hroom

/-- The side computations and the choice. -/
def sideCh : Stmt :=
  .seq (cmpA 81100 81153 81155 81154 81155) (.seq (cmpA 81102 81153 81155 81183 81011)
    (.seq (cmpA 81104 81183 81011 81154 81155) (.seq (side3 81106 81100 81102 81104)
      (.seq (cmpA 81110 81153 81155 81108 81109) (.seq (cmpA 81112 81108 81109 81154 81155)
        (.seq (side3 81107 81100 81110 81112) (.seq (eqor 81107 81110 81111)
          (.seq (xnorR 81114 81106 81107)
            (.ifLtN 81011 81114 ztoxw
              (Stmt.block [.copyN 81150 81119]))))))))))

/-- The cost bound of `sideCh`. -/
def scK : ℕ := 5 * 11010 + 40

/-- The registers `sideCh` writes. -/
def ScW (q : ℕ) : Prop := KeyW q ∨ ztelm ∨ q = 81150
theorem sideCh_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P ztdq c₀.nmem ztcpp)
    (hC : ChainDescAt c₀.nmem ztcpp zti H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hpA : PosOK Cα zti E.P.n ztkjw)
    (hpB : PosOK Cα zti E.P.n ztkjx)
    (hpU : PosOK Cα zti E.P.n ztlvo)
    (hpS : PosOK Cα zti E.P.n ztkjv)
    (hroom : c.nreg ALLOC + scK ≤ E.W) :
    FRS B E.P E.W c₀ sideCh c scK (fun c' =>
      let k := fun (x : WPos) => (chainModel Cα).key zti x
      let kA := k ztkjw
      let kB := k ztkjx
      let kU := k ztlvo
      let kS := k ztkjv
      (ztbbf → c'.nreg 81150 = c.nreg 81118) ∧
      (¬ ztbbf →
        c'.nreg 81150 = c.nreg 81119) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c.nreg q) := by
  zuddk
  zufwz
  -- the registers read
  let Rd : ℕ → Prop := fun q => q = 81108 ∨ q = 81109 ∨ q = 81118 ∨ q = 81119 ∨ q = 81133 ∨
    q = 81153 ∨ q = 81154 ∨ q = 81155 ∨ q = 81183
  have keep : ∀ (c₁ c₂ : Config) (r : ℕ), (∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r →
      q ≠ r + 1 → c₂.nreg q = c₁.nreg q) → 81100 ≤ r →
      (r + 1 ≤ 81107 ∨ (81110 ≤ r ∧ r + 1 ≤ 81114)) → ∀ q, Rd q → c₂.nreg q = c₁.nreg q := by
    intro c₁ c₂ r f h1 h2 q hq
    zujnx
    exact f q by_omega by_omega by_grind by_omega by_omega
  have keepb : ∀ (c₁ c₂ : Config) (r : ℕ), BitFr r c₁ c₂ → 81100 ≤ r → r ≤ 81114 →
      r ≠ 81108 → r ≠ 81109 → ∀ q, Rd q → c₂.nreg q = c₁.nreg q := by
    intro c₁ c₂ r f h1 h2 h3 h4 q hq
    zujnx
    exact f q by_omega
  have mA := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα _ E.P.n ⟨c'.nreg 81153, c'.nreg 81155⟩ by
      rw [h 81153 by_omega, h 81155 by_omega]; exact hpA
  have mB := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα _ E.P.n ⟨c'.nreg 81154, c'.nreg 81155⟩ by
      rw [h 81154 by_omega, h 81155 by_omega]; exact hpB
  have mU := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) (hI' : FInv E.W c₀ c') =>
    show PosOK Cα _ E.P.n ⟨c'.nreg 81183, c'.nreg 81011⟩ by
      rw [h 81183 by_omega, k0_of hE hI']; exact hpU
  have mS := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show PosOK Cα _ E.P.n ⟨c'.nreg 81108, c'.nreg 81109⟩ by
      rw [h 81108 by_omega, h 81109 by_omega]; exact hpS
  have mD := fun (c' : Config) (h : ∀ q, Rd q → c'.nreg q = c.nreg q) =>
    show c'.nreg 81133 = c.nreg 81133 from by_grind
  have hAW := hroom
  unfold scK at hAW
  -- the comparisons
  have r0 : ∀ q, Rd q → c.nreg q = c.nreg q := by_omega
  refine (FRS.seq (K₂ := 4 * 11010 + 40) (cmpA_fs₀ hE hB hI (r := 81100) ztfm
    ztwa ztwa
    ztwa ztwa
    ztmg ztmg
    ztmg ztmg hwf hC hWm
    (mA c r0) (mB c r0) by_omega) (fun c₁ hI₁ hA₁ ⟨b0, _, f₁⟩ => ?_)).mono
    by_rfl ztb
  have p1 := keep c c₁ 81100 f₁ by_norm_num by_norm_num
  refine (FRS.seq (K₂ := 3 * 11010 + 40) (cmpA_fs₀ hE hB hI₁ (r := 81102) ztfm
    ztwa ztwa
    ztwa ztwa
    ztmg ztmg
    ztmg ztmg
    (by zuomx; omega) (by zuomx; exact hC) hWm
    (mA c₁ p1) (mU c₁ p1 hI₁) by_omega) (fun c₂ hI₂ hA₂ ⟨b2, _, f₂⟩ => ?_)).mono
    by_omega ztb
  have p2 : ∀ q, Rd q → c₂.nreg q = c.nreg q := fun q hq => by
    rw [keep c₁ c₂ 81102 f₂ by_norm_num by_norm_num q hq,
      p1 q hq]
  refine (FRS.seq (K₂ := 2 * 11010 + 40) (cmpA_fs₀ hE hB hI₂ (r := 81104) ztfm
    ztwa ztwa
    ztwa ztwa
    ztmg ztmg
    ztmg ztmg
    (by zuomy; omega) (by zuomy; exact hC) hWm
    (mU c₂ p2 hI₂) (mB c₂ p2) by_omega) (fun c₃ hI₃ hA₃ ⟨b4, _, f₃⟩ => ?_)).mono
    by_omega ztb
  have p3 : ∀ q, Rd q → c₃.nreg q = c.nreg q := fun q hq => by
    rw [keep c₂ c₃ 81104 f₃ by_norm_num by_norm_num q hq,
      p2 q hq]
  -- the bits in `c₃`
  have b0₃ : BitIs c₃ 81100 _ := b0.of_eq (by
    rw [f₃ _ by_norm_num by_norm_num ztmg by_norm_num
      by_norm_num, f₂ _ by_norm_num by_norm_num ztmg
      by_norm_num by_norm_num])
  have b2₃ := b2.of_eq (f₃ _ by_norm_num by_norm_num
    ztmg by_norm_num by_norm_num)
  refine (FRS.seq (K₂ := 2 * 11010 + 32) (side3_fs hE hB hI₃ (r := 81106) ztfm
    by_norm_num by_norm_num by_norm_num by_norm_num b0₃ b2₃ b4)
    (fun c₄ hI₄ hA₄ ⟨b6, f₄⟩ => ?_)).mono by_omega (fun _ h => h)
  have p4 : ∀ q, Rd q → c₄.nreg q = c.nreg q := fun q hq => by
    rw [keepb c₃ c₄ 81106 f₄ by_norm_num by_norm_num by_norm_num by_norm_num q hq, p3 q hq]
  refine (FRS.seq (K₂ := 11010 + 32) (cmpA_fs₀ hE hB hI₄ (r := 81110) ztfm
    ztwa ztwa
    ztwa ztwa
    ztmg ztmg
    ztmg ztmg
    (by zuomz; omega) (by zuomz; exact hC) hWm
    (mA c₄ p4) (mS c₄ p4) by_omega) (fun c₅ hI₅ hA₅ ⟨b10, b11, f₅⟩ => ?_)).mono
    by_omega ztb
  have p5 : ∀ q, Rd q → c₅.nreg q = c.nreg q := fun q hq => by
    rw [keep c₄ c₅ 81110 f₅ by_norm_num by_norm_num q hq,
      p4 q hq]
  refine (FRS.seq (K₂ := 32) (cmpA_fs₀ hE hB hI₅ (r := 81112) ztfm
    ztwa ztwa
    ztwa ztwa
    ztmg ztmg
    ztmg ztmg
    (by zuona; omega) (by zuona; exact hC) hWm
    (mS c₅ p5) (mB c₅ p5) by_omega) (fun c₆ hI₆ hA₆ ⟨b12, _, f₆⟩ => ?_)).mono
    by_omega ztb
  have p6 : ∀ q, Rd q → c₆.nreg q = c.nreg q := fun q hq => by
    rw [keep c₅ c₆ 81112 f₆ by_norm_num by_norm_num q hq,
      p5 q hq]
  have g6 : ∀ q, 81100 ≤ q → q ≤ 81111 → c₆.nreg q = c₅.nreg q := fun q h1 h2 =>
    f₆ q by_omega by_omega zthyz by_omega by_omega
  have g5 : ∀ q, 81100 ≤ q → q ≤ 81107 → c₅.nreg q = c₄.nreg q := fun q h1 h2 =>
    f₅ q by_omega by_omega zthyz by_omega by_omega
  have b0₆ : BitIs c₆ 81100 _ := b0₃.of_eq (by
    rw [g6 _ by_norm_num by_norm_num, g5 _ by_norm_num by_norm_num, f₄ _ by_norm_num])
  have b10₆ := b10.of_eq ztrqz
  have b11₆ := b11.of_eq ztrqz
  refine (FRS.seq (K₂ := 19) (side3_fs hE hB hI₆ (r := 81107) ztfm
    by_norm_num by_norm_num by_norm_num by_norm_num b0₆ b10₆ b12)
    (fun c₇ hI₇ hA₇ ⟨b7, f₇⟩ => ?_)).mono by_omega (fun _ h => h)
  refine (FRS.seq (K₂ := 14) (eqor_fs hE hB hI₇ (r := 81107) ztfm b7
    (b10₆.of_eq zttkk) (b11₆.of_eq zttkk))
    (fun c₈ hI₈ hA₈ ⟨b7', f₈⟩ => ?_)).mono by_omega (fun _ h => h)
  have b6₈ : BitIs c₈ 81106 _ := b6.of_eq (by
    rw [f₈ _ by_norm_num, f₇ _ by_norm_num, g6 _ by_norm_num by_norm_num,
      g5 _ by_norm_num by_norm_num])
  refine (FRS.seq (K₂ := 3) (xnorR_fs hE hB hI₈ (r := 81114) ztfm
    by_norm_num by_norm_num b6₈ b7') (fun c₉ hI₉ hA₉ ⟨b14, f₉⟩ => ?_)).mono by_omega
    ztb
  have p9 : ∀ q, Rd q → c₉.nreg q = c.nreg q := fun q hq => by
    rw [keepb c₈ c₉ 81114 f₉ by_norm_num by_norm_num by_norm_num by_norm_num q hq,
      keepb c₇ c₈ 81107 f₈ by_norm_num by_norm_num by_norm_num by_norm_num q hq,
      keepb c₆ c₇ 81107 f₇ by_norm_num by_norm_num by_norm_num by_norm_num q hq, p6 q hq]
  -- rewrite the bits in `c`'s terms
  have z1 := k0_of hE hI₁
  have z2 := k0_of hE hI₂
  simp only [p1 81153 by_omega, p1 81155 by_omega, p1 81183 by_omega, z1] at b2
  simp only [p2 81154 by_omega, p2 81155 by_omega, p2 81183 by_omega, z2] at b4
  simp only [p4 81153 by_omega, p4 81155 by_omega, p4 81108 by_omega,
    p4 81109 by_omega] at b10 b11
  simp only [p5 81154 by_omega, p5 81155 by_omega, p5 81108 by_omega,
    p5 81109 by_omega] at b12
  -- the frame
  have frA : ∀ (c₁ c₂ : Config) (r : ℕ), (∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ r →
      q ≠ r + 1 → c₂.nreg q = c₁.nreg q) → 81100 ≤ r → r + 1 ≤ 81114 → ∀ q, 80000 ≤ q →
      q < 90000 → ¬ KeyW q → ¬ ztelm → c₂.nreg q = c₁.nreg q :=
    fun c₁ c₂ r h h1 h2 q a b hk hr => h q a b hk by_omega by_omega
  have frB : ∀ (c₁ c₂ : Config) (r : ℕ), BitFr r c₁ c₂ → 81100 ≤ r → r ≤ 81114 → ∀ q, 80000 ≤ q →
      q < 90000 → ¬ KeyW q → ¬ ztelm → c₂.nreg q = c₁.nreg q :=
    fun c₁ c₂ r h h1 h2 q _ _ _ hr => h q by_omega
  have F9 : ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → ¬ ztelm →
      c₉.nreg q = c.nreg q := fun q a b hk hr => by
    rw [frB c₈ c₉ 81114 f₉ by_norm_num by_norm_num q a b hk hr,
      frB c₇ c₈ 81107 f₈ by_norm_num by_norm_num q a b hk hr,
      frB c₆ c₇ 81107 f₇ by_norm_num by_norm_num q a b hk hr,
      frA c₅ c₆ 81112 f₆ by_norm_num by_norm_num q a b hk hr,
      frA c₄ c₅ 81110 f₅ by_norm_num by_norm_num q a b hk hr,
      frB c₃ c₄ 81106 f₄ by_norm_num by_norm_num q a b hk hr,
      frA c₂ c₃ 81104 f₃ by_norm_num by_norm_num q a b hk hr,
      frA c₁ c₂ 81102 f₂ by_norm_num by_norm_num q a b hk hr,
      frA c c₁ 81100 f₁ by_norm_num by_norm_num q a b hk hr]
  -- the decision bit
  rw [p1 81153 by_omega, p1 81155 by_omega, p1 81183 by_omega, z1,
    p2 81183 by_omega, z2, p2 81154 by_omega, p2 81155 by_omega,
    p4 81153 by_omega, p4 81155 by_omega, p4 81108 by_omega,
    p4 81109 by_omega, p5 81108 by_omega, p5 81109 by_omega,
    p5 81154 by_omega, p5 81155 by_omega] at b14
  set kA := (chainModel Cα).key zti ztkjw with hkA
  set kB := (chainModel Cα).key zti ztkjx with hkB
  set kU := (chainModel Cα).key zti ztlvo with hkU
  set kS := (chainModel Cα).key zti ztkjv with hkS
  have hY : ((kA < kB ∧ (kA < kS ∧ kS < kB)) ∨ (¬ kA < kB ∧ (kA < kS ∨ kS < kB))) ∨
      (¬ kA < kS ∧ ¬ kS < kA) ↔ (kS = kA ∨ sideInArc kA kB kS) := by
    constructor
    · zugtd
      · exact Or.inr ((sideInArc_iff' _ _ _).2 h)
      · exact Or.inl (le_antisymm ztmmr ztkbn)
    · zunp
      · right; zvmwc; simp
      · exact Or.inl ((sideInArc_iff' _ _ _).1 h)
  have hiff :=
    b14.2.trans (iff_congr (sideInArc_iff' _ _ _).symm hY)
  have k0₉ := k0_of hE hI₉
  have fin : ∀ c' : Config, (∀ q, q ≠ 81150 → c'.nreg q = c₉.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ ScW q → c'.nreg q = c.nreg q := fun c' h q a b hq => by
    rw [h q (fun e => hq ztgei), F9 q a b (fun e => hq ztccj)
      ztbapj]
  by_cases a1 : c₉.nreg 81011 < c₉.nreg 81114
  · have hb : c₉.nreg 81114 = 1 := by have := b14.1; omega
    have ok : okB E.W c₉.nmem [.copyN 81150 81118] c₉.nreg := by
      zurp
    refine (FRS.ifT a1 ztpyq).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₉.nmem [.copyN 81150 81118] c₉.nreg q := fun q => by zvmxl
    have v : c'.nreg 81150 = c.nreg 81118 := by
      zvmwg; zumxd; exact p9 81118 by_omega
    exact ⟨by_omega, (absurd (hiff.1 hb)),
      fin c' ztchy⟩
  · have hb : c₉.nreg 81114 = 0 := by_omega
    have ok : okB E.W c₉.nmem [.copyN 81150 81119] c₉.nreg := by
      zurp
    refine (FRS.ifF a1 ztpyq).mono by_simp zthi
    have e' : ∀ q, c'.nreg q = regB c₉.nmem [.copyN 81150 81119] c₉.nreg q := fun q => by zvmxl
    have v : c'.nreg 81150 = c.nreg 81119 := by
      zvmwg; zumxd; exact p9 81119 by_omega
    exact ⟨fun h => absurd (hiff.2 h) by_omega, by_omega,
      fin c' ztchy⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
variable {E : FEnv} {c₀ c : Config}

/-- **The test call with its outcome.** -/
theorem tcall_out (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hcand : c.nreg 81007 = 0 →
      CandOK E zteya ztqie zteqx)
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ ztmou c ztqxe (fun c' => TKeep c c' ∧ FWin E c' ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg 81061 = 0 → GoodAt E reg ztmgh zteqx → c'.nreg 81007 = 1) ∧
      ztlky) := by
  refine (tcall_fs hE hB hBT hI hw.1 hcand hroom).mono le_rfl
    ztijk
  zujdg
  · zulkz
    exact ⟨hk, zticm, by_simp_all,
      fun reg hregs hch hx1 hg => hout.good hE hregs hch hx1 hg, by_omega⟩
  · zuetx
    refine ⟨hk, ztmqo, by_omega, by_omega,
      by omega⟩
    zuemr

/-- The validity bit of the first test. -/
def endVal (s : ℕ) : Stmt :=
  .ifLtN 81011 ztdwa .skip (.ifLtN 81011 83010 (.ifLtN 81011 83011
    (.ifLtN 81011 ztiz ztyvi
      (.ifLtN ztjv 81021 .skip ztyvi)) .skip) .skip)
theorem endVal_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (_hs : SReg s) (hs5 : SReg ztfz) (h5 : c.nreg ztfz = 0)
    (_hd : ∀ q, FFix q → q ≠ s + 5) (_h8 : s + 8 ≠ s + 5) (_h3 : s + 3 ≠ s + 5) (_h4 : s + 4 ≠ s + 5) :
    FRS B E.P E.W c₀ ztvpy c 11 (fun c' => c'.nreg ztfz ≤ 1 ∧
      (c'.nreg ztfz = 1 ↔ (c.nreg ztdwa = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        ztxbd)) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := by
  have k0 : ztuoi := by zuoaa
  zucb
  have no : ¬ (c.nreg _ = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
      ztkpt) →
      FRS B E.P E.W c₀ .skip c 0 (fun c' => c'.nreg ztfz ≤ 1 ∧
      (c'.nreg ztfz = 1 ↔ (c.nreg ztdwa = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        ztxbd)) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI ⟨by_omega, ⟨by_simp_all, fun h => absurd h hn⟩, by_omega⟩
  have yes : (c.nreg _ = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
      ztkpt) →
      FRS B E.P E.W c₀ _ c 1 (fun c' => c'.nreg ztfz ≤ 1 ∧
      (c'.nreg _ = 1 ↔ (c.nreg ztdwa = 0 ∧ 0 < c.nreg 83010 ∧ 0 < c.nreg 83011 ∧
        ztxbd)) ∧
      ∀ q, q ≠ s + 5 → c'.nreg q = c.nreg q) := fun hy =>
    (setR_fs hB hI hs5 hW1).mono le_rfl (fun c' ⟨v, f⟩ =>
      ⟨by_omega, ⟨fun _ => hy, fun _ => v⟩, f⟩)
  by_cases a1 : c.nreg 81011 < c.nreg ztdwa
  · exact (FRS.ifT a1 ztmmo).mono by_omega by_grind
  zuhip
  by_cases a2 : c.nreg 81011 < c.nreg 83010
  · refine (FRS.ifT a2 ?_).mono (K := 9) by_omega ztb
    by_cases a3 : c.nreg 81011 < c.nreg 83011
    · refine (FRS.ifT a3 ?_).mono (K := 7) by_omega ztb
      by_cases a4 : c.nreg 81011 < c.nreg ztiz
      · exact (FRS.ifT a4 ztwib).mono by_omega
          by_grind
      refine (FRS.ifF a4 ?_).mono le_rfl ztb
      by_cases a5 : c.nreg ztjv < c.nreg 81021
      · exact (FRS.ifT a5 ztmmo).mono by_omega by_grind
      · exact (FRS.ifF a5 ztwib).mono by_omega by_grind
    · exact (FRS.ifF a3 ztmmo).mono by_omega by_grind
  · exact (FRS.ifF a2 ztmmo).mono by_omega by_grind

/-- The candidate of an end in direction `σ`, after saving the flag in `s + 8`. -/
def endCandL (s σ : ℕ) : List Instr := [.copyN ztdwa 81007, .copyN 81060 ztbk,
  .copyN 81061 ztfp, .copyN 81062 81152, .constN 81063 σ]

/-- The two tests at an end. -/
def endRun (s σ : ℕ) (sT : Stmt) : Stmt :=
  .seq (Stmt.block zttjs) (.seq ztmov
    (.seq (Stmt.block [.copyN ztjv 83012, .copyN ztiz 83013]) (.seq ztvpy
      (.seq (Stmt.block [.constN 81063 (1 - σ)]) ztmov))))

/-- The cost bound of `endRun`. -/
def erK (E : FEnv) : ℕ := 2 * tK E + 19

/-- The registers an end's tests write below the test's registers. -/
def RunW (s q : ℕ) : Prop := VertW q ∨ q = s + 3 ∨ q = s + 4 ∨ q = s + 5 ∨ q = s + 8

/-- **The two tests at an end.** -/
theorem endRun_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {s σ : ℕ}
    (hs : 81100 ≤ s ∧ s + 9 < 83000) (hσ : σ ≤ 1) (h5 : c.nreg ztfz = 0)
    (hcand : ∀ σb, σb ≤ 1 → CandOK E ztwke ztqih σb)
    (h52 : 81152 ≠ s + 8) (hroom : c.nreg ALLOC + erK E ≤ E.W) :
    FRS B E.P E.W c₀ ztrpg c (erK E) (fun c' => FWin E c' ∧
      ztcfl ∧
      ztfn ∧
      (∀ reg, NFRegs E.M zti E.N reg → (E.N.region E.r).chords ≠ [] →
        c.nreg ztfp = 0 → ∀ σb, σb ≤ 1 → GoodAt E reg ztwra σb →
          c'.nreg 81007 = 1) ∧
      c'.nreg ztfz ≤ 1 ∧ (c'.nreg ztfz = 1 → c.nreg 81007 = 0) ∧
      (c.nreg 81007 = 0 → ∃ ct ct' : Config, TOut E ct ct' ∧ ct.nreg 81060 = c.nreg ztbk ∧
        ct.nreg 81061 = c.nreg ztfp ∧ ct.nreg 81063 = σ ∧
        c'.nreg ztjv = ct'.nreg 83012 ∧ c'.nreg ztiz = ct'.nreg 83013 ∧
        (c'.nreg ztfz = 1 ↔ (ct'.nreg 83010 = 1 ∧ ct'.nreg 83011 = 1 ∧
          (0 < ct'.nreg 83013 ∨ c.nreg 81021 ≤ ct'.nreg 83012))) ∧
        ztcmv)) := by
  zubkz
  zucb
  zuki
  have wc : ∀ {c' c'' : Config}, FWin E c' → (∀ q, 81007 ≤ q → q ≤ 81010 → c''.nreg q = c'.nreg q) →
      FWin E c'' := fun hw' h => by
    zumqt
    rw [h 81007 by_norm_num by_norm_num, h 81008 by_norm_num by_norm_num,
      h 81009 by_norm_num by_norm_num, h 81010 by_norm_num by_norm_num]
    tauto
  -- the candidate
  have ok1 : okB E.W c.nmem zttjs c.nreg := by
    simp only [endCandL, okB, okI]
    exact ⟨Or.inl ztec, Or.inl ztec,
      Or.inl ztec, Or.inl ztec,
      ⟨Or.inl ztec, by_omega⟩, trivial⟩
  refine (FRS.seq (K₂ := 2 * tK E + 14) ztbbr ztiy).mono
    (by simp [endCandL, erK]; omega) ztb
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem _ c.nreg q := fun q => by zvnbm
  have u8 : c₁.nreg ztdwa = c.nreg 81007 := by
    zumwx; simp [endCandL, regB, regI, upd, show s + 8 ≠ 81060 by omega,
      show s + 8 ≠ 81061 by omega, show s + 8 ≠ 81062 by omega, show s + 8 ≠ 81063 by omega]
  have u60 : c₁.nreg 81060 = c.nreg ztbk := by
    zumwx; simp [endCandL, regB, regI, upd]
  have u61 : c₁.nreg 81061 = c.nreg ztfp := by
    zumwx; simp [endCandL, regB, regI, upd, show s + 2 ≠ 81060 by omega]
  have u62 : c₁.nreg 81062 = c.nreg 81152 := by
    zumwx; simp [endCandL, regB, regI, upd, show s ≠ 81144 by omega]
  have u63 : c₁.nreg 81063 = σ := by_tauto
  have f₁ : ∀ q, q ≠ s + 8 → ¬ VertW q → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    unfold VertW at h2
    zumwx; simp [endCandL, regB, regI, upd, h1, show q ≠ 81060 by omega,
      show q ≠ 81061 by omega, show q ≠ 81062 by omega, show q ≠ 81063 by omega]
  have fl₁ : ∀ q, 81007 ≤ q → q ≤ 81010 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    f₁ q by_omega ztod
  have hA₁' : ztdc := f₁ _ ztu
    (by unfold VertW ALLOC; omega)
  -- the first test
  refine (FRS.seq (K₂ := tK E + 14) (tcall_out hE hB hBT hI₁ (wc hw fl₁)
    ztfrh (by rw [hA₁']; unfold erK at hroom; omega))
    (fun c₂ hI₂ hA₂ ⟨k₂, w₂, m₂, g₂, o₂⟩ => ?_)).mono by_omega (fun _ h => h)
  have ok3 : okB E.W c₂.nmem [.copyN ztjv 83012, .copyN ztiz 83013] c₂.nreg := by
    zudu
    exact ⟨Or.inl ztec, Or.inl ztec, trivial⟩
  refine (FRS.seq (K₂ := tK E + 12) ztgdu ztcnf).mono
    by_grind ztb
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.copyN _ 83012, .copyN _ 83013]
      c₂.nreg q := fun q => by zunbh
  have u3 : c₃.nreg ztjv = c₂.nreg 83012 := by
    zuexl
  have u4 : c₃.nreg ztiz = c₂.nreg 83013 := by
    zumzv; simp [regB, regI, upd, show (83013 : ℕ) ≠ s + 3 by omega]
  have f₃ : ∀ q, q ≠ s + 3 → q ≠ s + 4 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    zumzv; zunbs
  have h5₃ : c₃.nreg ztfz = 0 := by
    rw [f₃ _ by_omega by_omega, k₂ _ by_omega by_omega, f₁ _ by_omega
      ztod, h5]
  refine (FRS.seq (K₂ := tK E + 1) (endVal_fs hE hB hI₃ (s := s) ztgy
    ⟨by_omega, by_omega⟩ h5₃ ztjwd by_omega by_omega
    by_omega) (fun c₄ hI₄ hA₄ ⟨v₄, b₄, f₄⟩ => ?_)).mono by_omega (fun _ h => h)
  refine (FRS.seq (K₂ := tK E) (setR_fs hB hI₄ (r := 81063) ztfm
    by_omega) (fun c₅ hI₅ hA₅ ⟨u₅, f₅⟩ => ?_)).mono by_omega (fun _ h => h)
  have g5 : ∀ q, q ≠ 81063 → q ≠ s + 5 → q ≠ s + 3 → q ≠ s + 4 →
      c₅.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 => by
    rw [f₅ q h1, f₄ q h2, f₃ q h3 h4]
  have hw₅ := wc w₂ (fun q h1 h2 => g5 q by_omega by_omega by_omega by_omega)
  have hcand₂ : c₅.nreg 81007 = 0 → CandOK E ⟨c₅.nreg 81060, c₅.nreg 81061⟩ (c₅.nreg 81062)
      (c₅.nreg 81063) := fun _ => by
    rw [u₅, g5 81060 by_norm_num by_omega by_omega by_omega,
      g5 81061 by_norm_num by_omega by_omega by_omega,
      g5 81062 by_norm_num by_omega by_omega by_omega,
      k₂ _ by_norm_num by_norm_num, k₂ _ by_norm_num by_norm_num,
      k₂ _ by_norm_num by_norm_num, u60, u61, u62]
    exact hcand _ by_omega
  have hroom₅ : c₅.nreg ALLOC + tK E ≤ E.W := by
    have := hA₁; have := hA₂; have := hA₃; have := hA₄; have := hA₅
    simp only [endCandL, List.length_cons, List.length_nil] at *
    unfold erK at hroom; omega
  refine (tcall_out hE hB hBT hI₅ hw₅ hcand₂ hroom₅).mono le_rfl
    (fun c₆ ⟨k₆, w₆, m₆, g₆, o₆⟩ => ?_)
  have back : ∀ q, 81011 ≤ q → q < 83000 → ¬ RunW s q → c₆.nreg q = c.nreg q := by
    zuetd
    unfold RunW VertW at hq
    rw [k₆ q h1 h2, g5 q by_omega by_omega by_omega by_omega, k₂ q h1 h2,
      f₁ q by_omega ztod]
  have m26 : c₂.nreg 81007 = 1 → c₆.nreg 81007 = 1 := fun h => m₆ (by
    rw [g5 _ by_norm_num by_omega by_omega by_omega]; exact h)
  have s5 : c₆.nreg ztfz = c₄.nreg ztfz := by
    rw [k₆ _ by_omega by_omega, f₅ _ by_omega]
  have s3 : c₆.nreg ztjv = c₂.nreg 83012 := by
    rw [k₆ _ by_omega by_omega, f₅ _ by_omega, f₄ _ by_omega, u3]
  have s4 : c₆.nreg ztiz = c₂.nreg 83013 := by
    rw [k₆ _ by_omega by_omega, f₅ _ by_omega, f₄ _ by_omega, u4]
  have i8 : c₃.nreg ztdwa = c.nreg 81007 := by
    rw [f₃ _ by_omega by_omega, k₂ _ by_omega by_omega, u8]
  have i21 : c₃.nreg 81021 = c.nreg 81021 := by
    rw [hI₃.hin _ ztbc, hI.hin _ ztbc]
  refine ⟨w₆, back, by_grind,
    fun reg hregs hch hc2 σb hσb hg => ?_, by_omega, fun h => ?_, fun hz => ?_⟩
  · rcases (show σb = σ ∨ σb = 1 - σ by omega) with rfl | rfl
    · exact m26 (g₂ reg hregs hch by_omega by_grind)
    · refine g₆ reg hregs hch ?_ ?_
      · rw [g5 81061 by_norm_num by_omega by_omega by_omega,
          k₂ _ by_norm_num by_norm_num, u61]; omega
      · rw [u₅, g5 81060 by_norm_num by_omega by_omega by_omega, k₂ _ by_norm_num by_norm_num, u60]; exact hg
  · grind
  · have hout := o₂ by_grind
    obtain ⟨t0, t1, -⟩ := hout
    refine ⟨c₁, c₂, by_grind, u60, u61, u63, s3,
      s4, ?_, m26⟩
    rw [s5, b₄, i8, f₃ _ by_omega by_omega, f₃ _ by_omega by_omega, u3, u4, i21]
    omega
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideInArc)
variable {E : FEnv} {c₀ c : Config}

/-- A host position the comparisons accept: in range, proper, and not a box vertex. -/
theorem posG_of_vlo (hE : FGood E c₀) (hI : FInv E.W c₀ c) {e h : ℕ} (he : e < E.M.W.n)
    (hp : ProperPos E.M zti E.P.n ztcq) (hv : 0 < h ∨ c.nreg 81021 ≤ e) :
    PosG E.M zti E.P.n ztcq := by
  refine ztkyn
  have := hE.vlo6 C hM
  rw [hI.hin _ ztbc] at hv
  grind

/-- The comparisons of the side bit. -/
def endSdC (s : ℕ) : Stmt :=
  .seq ztyvt (.seq (cmpM 81192 ztbk ztfp 81140 81141)
    (.seq (cmpM 81194 81140 81141 ztjv ztiz) (.seq (side3 ztsk 81190 81192 81194)
      (eqor ztsk 81192 81193))))

/-- **The side bit of an end.** -/
def endSd (s : ℕ) : Stmt :=
  .seq (Stmt.block [.constN ztsk 0])
    (.ifLtN 81011 ztfz (.ifLtN 81011 81141 ztmja (.ifLtN 81140 81021 .skip ztmja))
      .skip)

/-- The registers `endSd` writes. -/
def SdW (s q : ℕ) : Prop := KeyW q ∨ q = s + 6 ∨ zteln
theorem endSdC_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81150 ≤ s ∧ s + 9 < 81190)
    (hxE : PosG E.M zti E.P.n ztwke)
    (hxF : PosG E.M zti E.P.n ztwmn)
    (hxJ : PosG E.M zti E.P.n ztke)
    (hroom : c.nreg ALLOC + 33080 ≤ E.W) :
    FRS B E.P E.W c₀ ztmja c 33080 (fun c' =>
      BitIs c' ztsk (E.M.key zti ztke =
          E.M.key zti ztwke ∨
        sideInArc ztbakc
          ztbako
          ztxdp) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
  zubkz
  set kE := E.M.key zti ztwke
  set kF := E.M.key zti ztwmn
  set kJ := E.M.key zti ztke
  have nk : ∀ q, 81100 ≤ q → q < 82000 → ¬ KeyW q := fun q h1 h2 h => by unfold KeyW at h; omega
  have ir : ∀ q, 81100 ≤ q → q < 82000 → InR q := fun q h1 h2 => ztgy
  refine (FRS.seq (K₂ := 22058) (cmpM_fs hE hB hI (r := 81190) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm hxE hxF by_omega)
    (fun c₁ hI₁ hA₁ ⟨b0, b1, f₁⟩ => ?_)).mono by_omega (fun _ h => h)
  have g₁ : ∀ q, 81100 ≤ q → q < 81190 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    f₁ q by_omega by_omega (nk q h1 by_omega) by_omega by_omega
  have j₁ : ∀ q, q = 81140 ∨ q = 81141 → c₁.nreg q = c.nreg q := fun q h =>
    g₁ q by_omega by_omega
  refine (FRS.seq (K₂ := 11036) (cmpM_fs hE hB hI₁ (r := 81192) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm
    by_grind
    by_simp_all by_omega)
    (fun c₂ hI₂ hA₂ ⟨b2, b3, f₂⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [g₁ ztbk by_omega by_omega, g₁ ztfp by_omega by_omega, j₁ 81140 ztp,
    j₁ 81141 ztbt] at b2 b3
  have g₂ : ∀ q, 81100 ≤ q → q < 81190 → c₂.nreg q = c.nreg q := fun q h1 h2 => by
    grind
  refine (FRS.seq (K₂ := 14) (cmpM_fs hE hB hI₂ (r := 81194) ztfm
    ztpy ztpy ztpy
    ztpy ztnm ztnm
    ztnm ztnm
    by_grind
    by_grind by_omega)
    (fun c₃ hI₃ hA₃ ⟨b4, b5, f₃⟩ => ?_)).mono by_omega (fun _ h => h)
  rw [g₂ 81140 by_omega by_omega, g₂ 81141 by_omega by_omega,
    g₂ ztjv by_omega by_omega, g₂ ztiz by_omega by_omega] at b4 b5
  have p3 : ∀ q, 81190 ≤ q → q ≤ 81193 → c₃.nreg q = c₂.nreg q := fun q h1 h2 =>
    f₃ q by_omega by_omega zthyz by_omega by_omega
  have b0' : BitIs c₃ 81190 (kE < kF) := b0.of_eq (by
    rw [p3 _ by_norm_num by_norm_num, f₂ _ by_norm_num by_norm_num
      ztmg by_norm_num by_norm_num])
  have b2' : BitIs c₃ 81192 (kE < kJ) := b2.of_eq ztruh
  have b3' : BitIs c₃ 81193 (kJ < kE) := b3.of_eq ztruh
  refine (FRS.seq (K₂ := 5) (side3_fs hE hB hI₃ (r := s + 6) ztgy by_omega
    by_omega by_omega by_omega b0' b2' b4) (fun c₄ hI₄ hA₄ ⟨b6, f₄⟩ => ?_)).mono
    by_omega ztb
  refine (eqor_fs hE hB hI₄ (r := s + 6) ztgy b6
    (b2'.of_eq zttkj) (b3'.of_eq zttkj)).mono le_rfl
    (fun c₅ ⟨b7, f₅⟩ => ⟨b7.congr ?_, fun q h1 h2 hq => ?_⟩)
  · rw [sideInArc_iff']
    constructor
    · zugtd
      · zuhcq
      grind
    · zunp
      · grind
      · zueou
  · zugmo
    have h6 : q ≠ s + 6 := fun h => hq ztwkb
    have h9 : ¬ zteln := fun h => hq ztwxb
    rw [f₅ q h6, f₄ q h6, f₃ q h1 h2 hk by_omega by_omega,
      f₂ q h1 h2 hk by_omega by_omega, f₁ q h1 h2 hk by_omega by_omega]

/-- **The side bit of an end** as a run step (guarded by the validity bit and a check that the
target arc's start is a position the comparisons accept). -/
theorem endSd_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {s : ℕ} (hs : 81150 ≤ s ∧ s + 9 < 81190) (h5 : c.nreg ztfz ≤ 1)
    (hxE : c.nreg ztfz = 1 → PosG E.M zti E.P.n ztwke)
    (hxF : c.nreg ztfz = 1 → PosG E.M zti E.P.n ztwmn)
    (hJ : c.nreg 81140 < E.M.W.n ∧ ProperPos E.M zti E.P.n ztke)
    (hroom : c.nreg ALLOC + 33087 ≤ E.W) :
    FRS B E.P E.W c₀ ztvpx c 33087 (fun c' => c'.nreg ztsk ≤ 1 ∧
      (c.nreg ztfz = 1 → ztcef →
        (c'.nreg ztsk = 1 ↔ (E.M.key zti ztke =
          E.M.key zti ztwke ∨
        sideInArc ztbakc
          ztbako
          ztxdp))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
  zubkz
  refine (FRS.seq (K₂ := 33086) (setR_fs hB hI (r := s + 6) ztgy ztbg)
    ztesj).mono by_omega (fun _ h => h)
  zucna
  have g : ∀ q, q ≠ s + 6 → c₁.nreg q = c.nreg q := f₁
  have fin : ∀ c' : Config, (∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c₁.nreg q) →
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q :=
    fun c' h q h1 h2 h3 => by rw [h q h1 h2 h3, g q (fun e => h3 ztxgj)]
  have run : c.nreg ztfz = 1 → ztcef →
      FRS B E.P E.W c₀ ztmja c₁ 33080 (fun c' => c'.nreg ztsk ≤ 1 ∧
      (c.nreg ztfz = 1 → ztcef →
        (c'.nreg ztsk = 1 ↔ (E.M.key zti ztke =
          E.M.key zti ztwke ∨
        sideInArc ztbakc
          ztbako
          ztxdp))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := by
    intro h5' hv
    zucaz

    have r40 := g 81140 by_omega
    have r41 := g 81141 by_omega
    have hJ' : PosG E.M zti E.P.n ztke :=
      posG_of_vlo hE hI hJ.1 hJ.2 hv
    refine (endSdC_fs hE hB hI₁ ⟨by_omega, hs2⟩ by_grind
      by_grind by_grind
      by_omega).mono le_rfl
      (fun c' ⟨b, f⟩ => ⟨b.1, fun _ _ => by rw [← r1, ← r2, ← r3, ← r4, ← r40, ← r41]; exact b.2,
        fin c' f⟩)
  have skip0 : ¬ (c.nreg ztfz = 1 ∧ ztcef) →
      FRS B E.P E.W c₀ .skip c₁ 0 (fun c' => c'.nreg ztsk ≤ 1 ∧
      (c.nreg ztfz = 1 → ztcef →
        (c'.nreg ztsk = 1 ↔ (E.M.key zti ztke =
          E.M.key zti ztwke ∨
        sideInArc ztbakc
          ztbako
          ztxdp))) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ SdW s q → c'.nreg q = c.nreg q) := fun hn =>
    FRS.skip hI₁ ⟨by_omega, fun a b => absurd ztbqy hn, fin c₁ ztcnd⟩
  zukip
  have q40 := g 81140 by_omega
  have q41 := g 81141 by_omega
  have q21 : c₁.nreg 81021 = c.nreg 81021 := g 81021 by_omega
  by_cases a1 : c₁.nreg 81011 < c₁.nreg ztfz
  · have h51 : ztbacm := by_omega
    refine (FRS.ifT a1 ?_).mono (K := 33086) le_rfl ztb
    by_cases a2 : c₁.nreg 81011 < c₁.nreg 81141
    · exact (FRS.ifT a2 (run h51 ztec)).mono by_omega
        ztb
    refine (FRS.ifF a2 ?_).mono (K := 33084) by_omega ztb
    by_cases a3 : c₁.nreg 81140 < c₁.nreg 81021
    · exact (FRS.ifT a3 (skip0 (fun ⟨_, h⟩ => by
        omega))).mono by_omega (fun _ h => h)
    · exact (FRS.ifF a3 (run h51 ztbh)).mono by_omega
        ztb
  · exact (FRS.ifF a1 (skip0 (fun ⟨h, _⟩ => by_omega))).mono by_omega
      ztb
