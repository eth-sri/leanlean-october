module

public import Chazelle.Core.RestoreFRun
public import Chazelle.Core.RestoreDrvReg

/-!
# WP-E, the search on the RAM (`FindOK`), part 2: the fixed data and the test call

* `FEnv`, `FGood`: the fixed data of a run of the search (the precondition of `FindOK` at the
  start configuration `c₀`, and the contracts of the candidate test and the cutter).
* `CandOK`: the facts the test needs about a candidate (position, height vertex, direction bit).
* `tcall`: when the flag `81007` is `0`, copy the arguments to `83000 … 83009`, run the test and,
  on success, copy the chord triple to `81008 … 81010` and set the flag.
-/

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
  hOkM : ∀ P M, E.Ok P M → OkModel P M ∨ M = interiorModel (Qof P)
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.g E.A₀
  hcap : E.γ ≤ E.X.cap E.P E.m₀ E.g
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hreg : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C →
    HostRegular (Qof E.P).n H
  hsimp : E.m₀ E.MD = 0 → ∀ H C, ChainDescAt E.m₀ (E.MD + 1) (Qof E.P) H C → C.P.Simple
  hMD : ModelDescAt E.m₀ E.MD (Qof E.P) E.M
  hGM : GoodModel E.M
  hOk : E.Ok E.P E.M
  hNW : NFWithin E.m₀ E.NH E.A₀ E.N
  hNF : IsNF E.M (Qof E.P) E.N
  hdeg : E.M.DegLe (E.N.F E.M (Qof E.P)) E.d
  hsg : E.M.Semigranular (E.N.F E.M (Qof E.P)) E.γ
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
  nE : c₀.nreg 81022 = 2 * (E.P.n / 2)
  hE2 : c₀.nreg 81023 = E.P.n / 2
  wn : c₀.nreg 81017 = E.M.W.n
  k10 : c₀.nreg 81024 = 10
  hvr : ∀ v, v < E.M.W.n → c₀.nreg 81021 ≤ v → v ≤ c₀.nreg 81019 →
    ∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨v, 0⟩ ∈ C.set
  hvc : ∀ v, v < E.M.W.n →
    (∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨v, 0⟩ ∈ C.set) →
    c₀.nreg 81021 ≤ v ∧ v ≤ c₀.nreg 81019
  vlo6 : ∀ C : Chain, E.M = chainModel C → 6 ≤ c₀.nreg 81021
  ehr : ∀ e h, e < E.M.W.n → c₀.nreg 81021 ≤ e → e < c₀.nreg 81025 →
    ProperPos E.M (Qof E.P) E.P.n ⟨e, h⟩ →
    ∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) ⟨e, h⟩ ∈ C.set
  ehc : ∀ e, e < E.M.W.n → E.M.counted e → c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025

/-- **The facts the test needs about a candidate** `x`, its height vertex `hv` and the direction
bit `σb`. -/
def CandOK (E : FEnv) (x : WPos) (hv σb : ℕ) : Prop :=
  x.edge < E.M.W.n ∧ ProperPos E.M (Qof E.P) E.P.n x ∧ (x.hgt = 0 ∨ 0 < E.M.param (Qof E.P) x) ∧
    (∀ C : Chain, E.M = chainModel C → E.M.pos (Qof E.P) x ∈ C.set) ∧ hv < E.P.n ∧
    ((Qof E.P).vtx hv).2 = (E.M.pos (Qof E.P) x).2 ∧ σb ≤ 1

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
  .ifLtN 81007 81012 (.seq tArgs (.seq sT (.ifLtN 81011 83014 tWin .skip))) .skip

/-! ## The precondition of the test -/

variable {E : FEnv} {c₀ c : Config}

/-- The memory below the initial allocator is the initial memory. -/
theorem FInv.agree (hE : FGood E c₀) (hI : FInv E.W c₀ c) :
    ∀ a, a < E.A₀ → c.nmem a = E.m₀ a := fun a ha => by
  rw [hI.hm a (by rwa [hE.a0]), hE.m0]

theorem FInv.allocA (hE : FGood E c₀) (hI : FInv E.W c₀ c) : E.A₀ ≤ c.nreg ALLOC := by
  rw [← hE.a0]; exact hI.hA

/-- **The precondition of the test** in a configuration of the search whose test registers hold
the inputs and a candidate. -/
theorem test_pre (hE : FGood E c₀) (hI : FInv E.W c₀ c) (h0 : c.nreg 83000 = E.MD)
    (h1 : c.nreg 83001 = E.NH) (h2 : c.nreg 83002 = E.r) (h3 : c.nreg 83003 = E.γ)
    (h4 : c.nreg 83004 = E.g) (h9 : c.nreg 83009 = E.d)
    (hc : CandOK E ⟨c.nreg 83005, c.nreg 83006⟩ (c.nreg 83007) (c.nreg 83008)) :
    GoodEnv E.P ∧ hostWords E.P.n ≤ E.W ∧
      E.X.holds E.P c.nmem (c.nreg 83004) (c.nreg ALLOC) ∧
      c.nreg 83003 ≤ E.X.cap E.P c.nmem (c.nreg 83004) ∧
      ModelDescWF E.P (c.nreg ALLOC) c.nmem (c.nreg 83000) ∧
      (c.nmem (c.nreg 83000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 83000 + 1) (Qof E.P) H C →
        HostRegular (Qof E.P).n H) ∧
      (c.nmem (c.nreg 83000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 83000 + 1) (Qof E.P) H C →
        C.P.Simple) ∧ c.nreg 83008 ≤ 1 ∧
      ∃ M N, ModelDescAt c.nmem (c.nreg 83000) (Qof E.P) M ∧ GoodModel M ∧ E.Ok E.P M ∧
        NFWithin c.nmem (c.nreg 83001) (c.nreg ALLOC) N ∧ IsNF M (Qof E.P) N ∧
        M.DegLe (N.F M (Qof E.P)) (c.nreg 83009) ∧
        M.Semigranular (N.F M (Qof E.P)) (c.nreg 83003) ∧ c.nreg 83002 < N.nRegions ∧
        c.nreg 83005 < M.W.n ∧ ProperPos M (Qof E.P) E.P.n ⟨c.nreg 83005, c.nreg 83006⟩ ∧
        (c.nreg 83006 = 0 ∨ 0 < M.param (Qof E.P) ⟨c.nreg 83005, c.nreg 83006⟩) ∧
        (OkModel E.P M ∨ M = interiorModel (Qof E.P)) ∧
        (∀ C : Chain, M = chainModel C →
          M.pos (Qof E.P) ⟨c.nreg 83005, c.nreg 83006⟩ ∈ C.set) ∧
        c.nreg 83007 < E.P.n ∧
        ((Qof E.P).vtx (c.nreg 83007)).2 = (M.pos (Qof E.P) ⟨c.nreg 83005, c.nreg 83006⟩).2 := by
  have hag := hI.agree hE
  have hA := hI.allocA hE
  obtain ⟨hMD', hwf'⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  rw [h0, h1, h2, h3, h4, h9]
  refine ⟨hE.hG, hE.hWh, ?_, ?_, hwf'.mono hA, hregKeep hE.hwf hE.hMD hE.hreg hag,
    simpKeep hE.hwf hE.hMD hE.hsimp hag, c7, E.M, E.N, hMD', hE.hGM, hE.hOk,
    (hE.hNW.transport hag).mono hA, hE.hNF, hE.hdeg, hE.hsg, hE.hr, c1, c2, c3,
    hE.hOkM _ _ hE.hOk, c4, c5, c6⟩
  · exact E.X.mono _ _ _ _ _ hA (E.X.local_ _ _ _ _ _ (fun a ha => (hag a ha).symm) hE.hX)
  · rw [hE.hloc E.P E.m₀ c.nmem E.g E.A₀ hag hE.hX]; exact hE.hcap

/-! ## The result of a test call -/

/-- The cost bound of a test call. -/
def tK (E : FEnv) : ℕ := E.κt E.d * (E.F E.γ + 1) + 20

/-- **What a test from a clear flag gives**: the contract of the test for the candidate of `c`,
read in `c'` (valid `83010`, hit `83011`, far `83012`, `83013`; the flag `81007` is the success
bit and the triple is in `81008 … 81010`). -/
def TOut (E : FEnv) (c c' : Config) : Prop :=
  c'.nreg 83010 ≤ 1 ∧ c'.nreg 83011 ≤ 1 ∧
  ∀ reg, NFRegs E.M (Qof E.P) E.N reg →
    let x : WPos := ⟨c.nreg 81060, c.nreg 81061⟩
    let z := E.M.pos (Qof E.P) x
    let σ := dirOf (c.nreg 81063)
    let R := reg E.r
    let far : WPos := ⟨c'.nreg 83012, c'.nreg 83013⟩
    let tr := (c'.nreg 81008, c'.nreg 81009, c'.nreg 81010)
    (c'.nreg 81007 = 1 →
      (recOf tr).Attached E.M (Qof E.P) ∧ tr.1 < (Qof E.P).n ∧
      (recOf tr).toSet E.M (Qof E.P) ∈ E.M.Adm ∧
      SplitsWell E.M (E.N.F E.M (Qof E.P)) R ((recOf tr).toSet E.M (Qof E.P))) ∧
    (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
      ∃ T > (0 : ℝ), (∀ t, 0 < t → t < T → Chazelle.Visibility.rayPt z σ t ∈ R) ∧
        E.M.pos (Qof E.P) far = Chazelle.Visibility.rayPt z σ T ∧ far.edge < E.M.W.n ∧
        ProperPos E.M (Qof E.P) E.P.n far ∧
        chordOf z σ T ∈ E.M.Adm ∧
        Chazelle.Chain.SideAttach E.M.W (chordOf z σ T) x.edge (E.M.param (Qof E.P) x) ∧
        Chazelle.Chain.SideAttach E.M.W (chordOf z σ T) far.edge (E.M.param (Qof E.P) far) ∧
        (c'.nreg 81007 = 1 ↔
          CountOK E.M (E.N.F E.M (Qof E.P)) R (E.M.key (Qof E.P) x) (E.M.key (Qof E.P) far))) ∧
    (Chazelle.Chain.sideLeft E.M.W x.edge (E.M.param (Qof E.P) x)
        (Chazelle.Visibility.rayPt z σ 1) →
      (E.N.region E.r).chords ≠ [] →
      (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T → Chazelle.Visibility.rayPt z σ t ∈ E.M.D) →
        Chazelle.Visibility.rayPt z σ T ∉ E.M.D →
        chordOf z σ T ∈ E.M.Adm → chordOf z σ T ∉ E.N.F E.M (Qof E.P) →
        chordOf z σ T ∩ E.M.D ⊆ R → c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1))

/-- The registers of the search a test call keeps: band `bRestore` from `81011` below
`83000`. -/
def TKeep (c c' : Config) : Prop := ∀ q, 81011 ≤ q → q < 83000 → c'.nreg q = c.nreg q

/-! ## The test call as a run step -/

/-- The instructions of `tArgs`. -/
def tArgsL : List Instr := [.copyN 83000 81000, .copyN 83001 81001, .copyN 83002 81002,
  .copyN 83003 81003, .copyN 83004 81004, .copyN 83005 81060, .copyN 83006 81061,
  .copyN 83007 81062, .copyN 83008 81063, .copyN 83009 81005]

/-- The arguments of the test as a register effect. -/
theorem tArgs_eff (m f : ℕ → ℕ) :
    regB m tArgsL f 83000 = f 81000 ∧ regB m tArgsL f 83001 = f 81001 ∧
      regB m tArgsL f 83002 = f 81002 ∧ regB m tArgsL f 83003 = f 81003 ∧
      regB m tArgsL f 83004 = f 81004 ∧ regB m tArgsL f 83005 = f 81060 ∧
      regB m tArgsL f 83006 = f 81061 ∧ regB m tArgsL f 83007 = f 81062 ∧
      regB m tArgsL f 83008 = f 81063 ∧ regB m tArgsL f 83009 = f 81005 ∧
      ∀ q, (q < 83000 ∨ 83009 < q) → regB m tArgsL f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  all_goals try (simp [tArgsL, regB, regI, upd]; done)
  refine regB_other m _ f (fun i hi => ?_)
  simp only [tArgsL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dstI] <;> omega

/-- The instructions of `tWin`. -/
def tWinL : List Instr := [.copyN 81008 83015, .copyN 81009 83016, .copyN 81010 83017,
  .constN 81007 1]

/-- The record of a success as a register effect. -/
theorem tWin_eff (m f : ℕ → ℕ) :
    regB m tWinL f 81008 = f 83015 ∧ regB m tWinL f 81009 = f 83016 ∧
      regB m tWinL f 81010 = f 83017 ∧ regB m tWinL f 81007 = 1 ∧
      ∀ q, (q < 81007 ∨ 81010 < q) → regB m tWinL f q = f q := by
  refine ⟨?_, ?_, ?_, ?_, fun q hq => ?_⟩
  all_goals try (simp [tWinL, regB, regI, upd]; done)
  refine regB_other m _ f (fun i hi => ?_)
  simp only [tWinL, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega

theorem okB_tArgs {W : ℕ} (m f : ℕ → ℕ) : okB W m tArgsL f := by
  simp only [tArgsL, okB, okI, FScr, FOut]; norm_num

theorem okB_tWin {W : ℕ} (hW : 1 ≤ W) (m f : ℕ → ℕ) : okB W m tWinL f := by
  simp only [tWinL, okB, okI, FScr, FOut]; norm_num; omega

/-- **The test call** as a run step of the search. -/
theorem tcall_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hfl : c.nreg 81007 ≤ 1)
    (hcand : c.nreg 81007 = 0 →
      CandOK E ⟨c.nreg 81060, c.nreg 81061⟩ (c.nreg 81062) (c.nreg 81063))
    (hroom : c.nreg ALLOC + tK E ≤ E.W) :
    FRS B E.P E.W c₀ (tcall E.sT) c (tK E) (fun c' => TKeep c c' ∧ c'.nreg 81007 ≤ 1 ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1 ∧ c'.nreg 81008 = c.nreg 81008 ∧
        c'.nreg 81009 = c.nreg 81009 ∧ c'.nreg 81010 = c.nreg 81010) ∧
      (c.nreg 81007 = 0 → TOut E c c')) := by
  have fx : ∀ q, FFix q → c.nreg q = c₀.nreg q := fun q hq => hI.hin q hq
  have k0 : c.nreg 81011 = 0 := by rw [fx _ (by unfold FFix; omega), hE.k0]
  have k1 : c.nreg 81012 = 1 := by rw [fx _ (by unfold FFix; omega), hE.k1]
  have hW1 : 1 ≤ E.W := by have := hE.hWh; unfold hostWords at this; omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hfl with h0 | h1
  · -- the test runs
    have g : c.nreg 81007 < c.nreg 81012 := by rw [h0, k1]; omega
    have hc := hcand h0
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, afr⟩ := tArgs_eff c.nmem c.nreg
    have hT := hE.hT
    unfold TestOK at hT
    refine (FRS.ifT g (FRS.seq (FRS.block hB tArgsL hI (okB_tArgs _ _))
      (fun c₁ hI₁ _ h₁ => ?_))).mono (K := tArgsL.length + (E.κt E.d * (E.F E.γ + 1) + 6) + 2)
      (by simp only [tK, tArgsL, List.length_cons, List.length_nil]; omega) (fun _ h => h)
    subst h₁
    -- the registers after the arguments
    have i0 : c.nreg 81000 = E.MD := by rw [fx _ (by unfold FFix; omega), hE.i0]
    have i1 : c.nreg 81001 = E.NH := by rw [fx _ (by unfold FFix; omega), hE.i1]
    have i2 : c.nreg 81002 = E.r := by rw [fx _ (by unfold FFix; omega), hE.i2]
    have i3 : c.nreg 81003 = E.γ := by rw [fx _ (by unfold FFix; omega), hE.i3]
    have i4 : c.nreg 81004 = E.g := by rw [fx _ (by unfold FFix; omega), hE.i4]
    have i5 : c.nreg 81005 = E.d := by rw [fx _ (by unfold FFix; omega), hE.i5]
    set c₁ : Config := { c with nreg := regB c.nmem tArgsL c.nreg } with hc₁
    have r0 : c₁.nreg 83000 = E.MD := by rw [hc₁]; exact a0.trans i0
    have r1 : c₁.nreg 83001 = E.NH := by rw [hc₁]; exact a1.trans i1
    have r2 : c₁.nreg 83002 = E.r := by rw [hc₁]; exact a2.trans i2
    have r3 : c₁.nreg 83003 = E.γ := by rw [hc₁]; exact a3.trans i3
    have r4 : c₁.nreg 83004 = E.g := by rw [hc₁]; exact a4.trans i4
    have r5 : c₁.nreg 83005 = c.nreg 81060 := by rwa [hc₁]
    have r6 : c₁.nreg 83006 = c.nreg 81061 := by rwa [hc₁]
    have r7 : c₁.nreg 83007 = c.nreg 81062 := by rwa [hc₁]
    have r8 : c₁.nreg 83008 = c.nreg 81063 := by rwa [hc₁]
    have r9 : c₁.nreg 83009 = E.d := by rw [hc₁]; exact a9.trans i5
    have rfr : ∀ q, (q < 83000 ∨ 83009 < q) → c₁.nreg q = c.nreg q := fun q hq => by
      rw [hc₁]; exact afr q hq
    have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := rfr _ (by unfold ALLOC; omega)
    have hc' : CandOK E ⟨c₁.nreg 83005, c₁.nreg 83006⟩ (c₁.nreg 83007) (c₁.nreg 83008) := by
      rwa [r5, r6, r7, r8]
    have pre := test_pre hE hI₁ r0 r1 r2 r3 r4 r9 hc'
    have hcost : E.κt (c₁.nreg 83009) * (E.F (c₁.nreg 83003) + 1) =
        E.κt E.d * (E.F E.γ + 1) := by rw [r9, r3]
    refine FRS.seq ((FRS.call hT hBT hI₁ pre (by rw [hcost, hA₁]; unfold tK at hroom; omega)
      (fun c' hp q hq => hp.1 q (band8 (by unfold FFix at hq; omega) (by unfold FFix at hq; omega))
        (by unfold FFix at hq; omega))).mono (le_of_eq hcost) (fun _ h => h))
      (fun c₂ hI₂ _ hp => ?_)
    obtain ⟨⟨hkeep, b10, b11, b14, hres⟩, -, -⟩ := hp
    have z₂ : c₂.nreg 81011 = 0 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k0]
    -- the record of a success
    have hwin : FRS B E.P E.W c₀ (.ifLtN 81011 83014 tWin .skip) c₂ 6 (fun c₃ =>
        (∀ q, (q < 81007 ∨ 81010 < q) → c₃.nreg q = c₂.nreg q) ∧
        (c₃.nreg 81007 = 1 ↔ c₂.nreg 83014 = 1) ∧ c₃.nreg 81007 ≤ 1 ∧
        (c₂.nreg 83014 = 1 → c₃.nreg 81008 = c₂.nreg 83015 ∧ c₃.nreg 81009 = c₂.nreg 83016 ∧
          c₃.nreg 81010 = c₂.nreg 83017)) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 b14 with s0 | s1
      · have g' : ¬ c₂.nreg 81011 < c₂.nreg 83014 := by rw [z₂, s0]; omega
        refine (FRS.ifF g' (FRS.skip hI₂ (K := 0) (Q := fun c' => c' = c₂) rfl)).mono
          (by omega) ?_
        intro c' hc'
        rw [hc']
        have e7 : c₂.nreg 81007 = 0 := by
          rw [hkeep 81007 (band8 (by omega) (by omega)) (by omega), rfr _ (by omega), h0]
        exact ⟨fun _ _ => rfl, by rw [e7, s0], by omega, fun h => by omega⟩
      · have g' : c₂.nreg 81011 < c₂.nreg 83014 := by rw [z₂, s1]; omega
        refine (FRS.ifT g' (FRS.block hB tWinL hI₂ (okB_tWin hW1 _ _))).mono
          (by simp [tWinL]) ?_
        intro c' hc'
        rw [hc']
        obtain ⟨w8, w9, w10, w7, wfr⟩ := tWin_eff c₂.nmem c₂.nreg
        exact ⟨wfr, by simp only []; rw [w7, s1], by simp only []; rw [w7],
          fun _ => ⟨w8, w9, w10⟩⟩
    refine hwin.mono le_rfl (fun c₃ ⟨h3fr, h3s, h3le, h3t⟩ => ?_)
    have keep₂ : ∀ q, 80000 ≤ q → q < 83000 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
      hkeep q (band8 h1 (by omega)) h2
    refine ⟨fun q h1 h2 => ?_, h3le, fun h => by omega, fun _ => ?_⟩
    · rw [h3fr q (by omega), keep₂ q (by omega) h2, rfr q (by omega)]
    -- the contract of the test, for the candidate of `c`
    have e10 : c₃.nreg 83010 = c₂.nreg 83010 := h3fr _ (by omega)
    have e11 : c₃.nreg 83011 = c₂.nreg 83011 := h3fr _ (by omega)
    have e12 : c₃.nreg 83012 = c₂.nreg 83012 := h3fr _ (by omega)
    have e13 : c₃.nreg 83013 = c₂.nreg 83013 := h3fr _ (by omega)
    refine ⟨by rwa [e10], by rwa [e11], fun reg hregs => ?_⟩
    have hag := hI.agree hE
    obtain ⟨hMD', -⟩ := Gran.desc_agree' hE.hwf hE.hMD hag
    have hMD₁ : ModelDescAt c₁.nmem (c₁.nreg 83000) (Qof E.P) E.M := by rwa [r0]
    have hNA₁ : NFAt c₁.nmem (c₁.nreg 83001) E.N := by
      rw [r1]; exact NFWithin.nfAt (hE.hNW.transport hag)
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
    have g : ¬ c.nreg 81007 < c.nreg 81012 := by rw [h1, k1]; omega
    refine (FRS.ifF g (FRS.skip hI (K := 0) (Q := fun c' => c' = c) rfl)).mono (by unfold tK; omega) ?_
    rintro c' rfl
    exact ⟨fun q _ _ => rfl, hfl, fun _ => ⟨h1, rfl, rfl, rfl⟩, fun h => by omega⟩

end

end Restore

end Chazelle.Core
