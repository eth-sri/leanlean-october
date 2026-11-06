module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepEvBatch
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.DownPhaseOracleArc

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def pK2 : ℕ := sw 2480
def pK1 : ℕ := sw 2481
def pT : ℕ := sw 2482
def pS : ℕ := sw 2483
def p2 : ℕ := sw 2484
def p4 : ℕ := sw 2485
def p8 : ℕ := sw 2486
def p16 : ℕ := sw 2487
def p32 : ℕ := sw 2488
def p64 : ℕ := sw 2489
def pU : ℕ := sw 2490

/-- The head: read `K₂`, `K₁`; the table end `pT = ALLOC + 6 K₂`. -/
def prepHead : List Instr :=
  [.loadN pK2 ztbz, .loadN pK1 ztea, .copyN pT ALLOC, .addN pT pT pK2, .addN pT pT pK2,
    .addN pT pT pK2, .addN pT pT pK2, .addN pT pT pK2, .addN pT pT pK2]

/-- Zero the table, one word per iteration. -/
def zeroLoop : Stmt :=
  .whileLtN ALLOC pT (.seq ztowb ztckm)

/-- The middle: `lB`, `lC`, and the log end `pU = ALLOC + 112 (K₁ + K₂ + 1)`. -/
def prepMid : List Instr :=
  [.copyN lB ALLOC, .copyN lC K0, .addN pS pK1 pK2, .addN pS pS K1, .addN p2 pS pS,
    .addN p4 p2 p2, .addN p8 p4 p4, .addN p16 p8 p8, .addN p32 p16 p16, .addN p64 p32 p32,
    .copyN pU ALLOC, .addN pU pU p16, .addN pU pU p32, .addN pU pU p64]

/-- Raise the allocator to `pU`, one word per iteration. -/
def allocLoop : Stmt := .whileLtN ALLOC pU ztckm

/-- **The preparation.** -/
def prep : Stmt := .seq ztvfk (.seq zeroLoop (.seq ztvfl allocLoop))

/-! ## Steps -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- One word of allocation. -/
theorem allocOne_irs (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ ztckm c 1
      (fun c' => c' = { c with nreg := upd c.nreg ALLOC (c.nreg ALLOC + 1) }) := by
  zuegb
  rw [hK1] at ex
  exact IRS.ofExec hI ex le_rfl (fun r _ hr => upd_other _ _ _ hr) rfl ztcj rfl rfl
    by_simp by_simp rfl

/-- The zeroing loop. -/
theorem zeroLoop_irs (hI : IInv W c₀ c) (hK : Consts c) {T : ℕ} (hT : c.nreg pT = T)
    (hAT : c.nreg ALLOC ≤ T) (hroom : c.nreg ALLOC + 4 * ztrkj ≤ W) :
    IRS P W c₀ zeroLoop c (4 * ztrkj + 2) (fun c' =>
      c'.nreg ALLOC = T ∧ ztjn ∧
      (∀ x, c.nreg ALLOC ≤ x → x < T → c'.nmem x = 0) ∧
      ztbgf) := by
  zujq
  zudpw
  zucnb
  have nT : pT ≠ ALLOC := by_decide
  have n0 : K0 ≠ ALLOC := by_decide
  zuibh
  let I : Config → Prop := fun c' => A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ T ∧
    ztjn ∧
    (∀ x, A ≤ x → x < c'.nreg ALLOC → c'.nmem x = 0) ∧
    (∀ x, x < A → c'.nmem x = c.nmem x)
  have hpT : ∀ c', I c' → c'.nreg pT = T := fun c' hc => (hc.2.2.1 _ nT).trans hT
  have h := IRS.while (P := P) (c₀ := c₀) (a := ALLOC) (b := pT)
    (body := .seq ztowb ztckm) I
    (fun c' => T - c'.nreg ALLOC) 2
    ztpbg ?_ hI
    ⟨le_rfl, hAT, fun _ _ => rfl, fun x h1 h2 => by_omega, fun _ _ => rfl⟩ by_omega
  · refine zttlp
    grind
  · zukjd
    rw [hpT c' hc] at hlt
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    refine IRS.seq (K₁ := 1) (K₂ := 1) (IRS.store hI' hI'.hA) ?_
    zuer
    refine (allocOne_irs hI₁ by_simp_all by_grind).mono le_rfl ?_
    zugtg

    refine ⟨⟨by_omega, by_omega, fun r hr => ?_, fun x hx1 hx2 => ?_, fun x hx => ?_⟩, by_omega⟩
    · simp_all
    · rw [h3 _ n0, k0]
      by_cases hx : x = c'.nreg ALLOC
      · simp_all
      · rw [upd_other _ _ _ hx]; grind
    · zurj

/-- The allocation loop. -/
theorem allocLoop_irs (hI : IInv W c₀ c) (hK : Consts c) {U : ℕ} (hU : c.nreg pU = U)
    (hAU : c.nreg ALLOC ≤ U) (hroom : c.nreg ALLOC + 3 * ztrkk ≤ W) :
    IRS P W c₀ allocLoop c (3 * ztrkk + 2) (fun c' =>
      c'.nreg ALLOC = U ∧ ztjn ∧ c'.nmem = c.nmem) := by
  zujq
  zucnb
  have nU : pU ≠ ALLOC := by_decide
  zuibh
  let I : Config → Prop := fun c' => A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ U ∧
    ztjn ∧ c'.nmem = c.nmem
  have hpU : ∀ c', I c' → c'.nreg pU = U := fun c' hc => (hc.2.2.1 _ nU).trans hU
  have h := IRS.while (P := P) (c₀ := c₀) (a := ALLOC) (b := pU)
    (body := .instr (.addN ALLOC ALLOC K1)) I (fun c' => U - c'.nreg ALLOC) 1
    ztpbg ?_ hI
    ⟨le_rfl, hAU, fun _ _ => rfl, rfl⟩ by_omega
  · refine zttlp
    grind
  · zukjd
    rw [hpU c' hc] at hlt
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine (allocOne_irs hI' by_simp_all by_omega).mono le_rfl ?_
    zugtg

    refine ⟨⟨by_omega, by_omega, fun r hr => ?_, h4⟩, by_omega⟩
    simp_all

/-- The head. -/
theorem prepHead_irs (hI : IInv W c₀ c) {K₁ K₂ : ℕ} (h2 : c.nmem ztwrb = K₂)
    (h1 : c.nmem ztwsx = K₁) (hroom : c.nreg ALLOC + 6 * K₂ ≤ W) :
    IRS P W c₀ ztvfk c 9 (fun c' => c'.nreg pK2 = K₂ ∧ c'.nreg pK1 = K₁ ∧
      c'.nreg pT = c.nreg ALLOC + 6 * K₂ ∧
      (∀ r, r ≠ pK2 → r ≠ pK1 → r ≠ pT → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  simp only [sw, ALLOC] at h1 h2 hroom
  refine (IRS.block prepHead hI ?_).mono le_rfl ?_
  · simp [prepHead, okB, okI, regI, upd, pK2, pK1, pT, sw, ALLOC, IScr, h2]
    omega
  · zuu
    simp [prepHead, regB, regI, upd, pK2, pK1, pT, sw, ALLOC, h1, h2]
    grind

/-- The middle block. -/
theorem prepMid_irs (hI : IInv W c₀ c) (hK : Consts c) {K₁ K₂ : ℕ} (h1 : c.nreg pK1 = K₁)
    (h2 : c.nreg pK2 = K₂) (hroom : c.nreg ALLOC + 112 * ztctf ≤ W) :
    IRS P W c₀ ztvfl c 14 (fun c' => c'.nreg lB = c.nreg ALLOC ∧ c'.nreg lC = 0 ∧
      c'.nreg pU = c.nreg ALLOC + 112 * ztctf ∧
      (∀ r, r ≠ lB → r ≠ lC → (r < pS ∨ pU < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zudpw
  zucnb
  simp only [K0, K1, sw, ALLOC, pK1, pK2] at h1 h2 hroom k0 k1
  refine (IRS.block prepMid hI ?_).mono le_rfl ?_
  · simp [prepMid, okB, okI, regI, upd, pK2, pK1, pS, p2, p4, p8, p16, p32, p64, pU, lB, lC, sw,
      ALLOC, IScr, K0, K1, h1, h2, k1]
    omega
  · zuu
    simp [prepMid, regB, regI, upd, pK2, pK1, pS, p2, p4, p8, p16, p32, p64, pU, lB, lC, sw,
      ALLOC, K0, K1, h1, h2, k0, k1]
    grind
theorem nw₁' {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {J : Merge.Junction} {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂)
    (hI : IInv W c₀ c) : NFWithin c.nmem ztwsx ztm N₁ := by
  zubuy
  exact (E.hNW₁.transport zttj).mono hI.hA

/-- **Task P: the preparation.** -/
theorem prepTask : PrepTask := by
  refine ⟨prep, 400, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hAc hroom
  have hK : Consts c := E.hK.fix hI
  have h2 : ztbaox := (E.nw₂' hI).nfAt.1
  have h1 : ztbaoy := (nw₁' E hI).nfAt.1
  set K₁ := N₁.nChords with hK₁
  set K₂ := N₂.nChords with hK₂
  set t := K₁ + K₂ + 1 with ht
  zujq
  have hTB : c.nreg cTB = A := hAc.symm
  refine IRS.mono (K := 9 + ((4 * ztniq + 2) + (14 + (3 * (A + 6 * K₂ + 112 * t -
    (A + 6 * K₂)) + 2)))) ?_ by_omega (fun _ h => h)
  refine IRS.seq (prepHead_irs hI h2 h1 by_omega) ?_
  rintro c₁ hI₁ - - ⟨a2, a1, aT, afr, am⟩
  have nA : ∀ r, r = ALLOC → r ≠ pK2 ∧ r ≠ pK1 ∧ r ≠ pT := by
    rintro r rfl; decide
  have e1A : ztizl := afr _ (nA _ rfl).1 (nA _ rfl).2.1 (nA _ rfl).2.2
  have hK₁' : ztukh := E.hK.fix hI₁
  refine IRS.seq ((zeroLoop_irs hI₁ hK₁' aT by_omega by_omega).mono
    (K' := 4 * ztniq + 2) by_omega ztb) ?_
  rintro c₂ hI₂ - - ⟨z1, z2, z3, z4⟩
  rw [e1A] at z3 z4
  have hK₂' : Consts c₂ := E.hK.fix hI₂
  have nk1 : pK1 ≠ ALLOC := by_decide
  have nk2 : pK2 ≠ ALLOC := by_decide
  refine IRS.seq (prepMid_irs hI₂ hK₂' (by rw [z2 _ nk1, a1]) (by rw [z2 _ nk2, a2])
    (by rw [z1]; omega)) ?_
  rintro c₃ hI₃ - - ⟨m1, m2, m3, m4, m5⟩
  rw [z1] at m1 m3
  have e3A : c₃.nreg ALLOC = A + 6 * K₂ := by
    rw [m4 _ (by unfold lB ALLOC sw; omega) (by unfold lC ALLOC sw; omega)
      (by left; unfold pS ALLOC sw; omega), z1]
  refine (allocLoop_irs hI₃ ztjih m3 by_omega by_omega).mono by_omega ?_
  rintro c' ⟨f1, f2, f3⟩
  have nlB : lB ≠ ALLOC := by_decide
  have nlC : lC ≠ ALLOC := by_decide
  refine ⟨fun j hj => ?_, ?_, ?_, ?_, fun x hx => ?_, fun r hr hpr hra => ?_⟩
  · rw [f3, m5, hTB]; grind
  · grind
  · grind
  · grind
  · grind
  · unfold PR at hpr
    push Not at hpr
    rw [f2 r hra, m4 r hpr.1 hpr.2.1 (by unfold pS pU sw at *; omega), z2 r hra,
      afr r (by unfold pK2 sw at *; omega) (by unfold pK1 sw at *; omega)
        (by unfold pT sw at *; omega)]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
@[expose] public section
def logCap (N₁ N₂ : NF) : ℕ := 16 * ztks

/-- The offset of the current key. -/
noncomputable def keyOff (P : Polygon) (J : Merge.Junction) (c : Config) : ℝ :=
  offK P J ztwe ztbhr

/-- The label set of the current key. -/
noncomputable def curLab (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) :
    Set ztf :=
  labSet J zta N₂ ztjsi ztvjo ztbagn ztbago
    ztbagp

/-- The offsets of all possible keys (`CountTask`). -/
def keyS (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) : Set ℝ :=
  cutOffs J ztwis ∪ winOffs P J N₁

/-- The offset of stop `i`. -/
noncomputable def stopOff (P : Polygon) (J : Merge.Junction) (c : Config) (i : ℕ) : ℝ :=
  offK P J ztbjv ztbjw

/-- **The stops of stage 2** in the configuration `c` (the body of `StopOut`). -/
def StopData (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config)
    (rs ax : List ztcf) : Prop :=
  rs.length = c.nreg sC ∧ ax.length = rs.length ∧
    StopRecsAt c.nmem zthvm rs ∧ AuxRecsAt c.nmem ztmgu ax ∧
    StopsOK J ztwis ztwoy ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      zthkb) ∧
    (∀ i, i < rs.length → AuxOK P J N₂
      (stopSet J zta N₂ (rs.getD i ztip).2.2.1 (rs.getD i ztip).2.2.2.1
        (rs.getD i ztip).2.2.2.2) (ax.getD i (0, 0, 0, 0, 0))) ∧
    rs.length ≤ 4 * N₂.nChords + 8

/-- **The log so far**: `LogOK` without the condition after the last key. -/
def LogPre (J : Merge.Junction) (S₂ : Set ztf) (es : List ztwws) :
    Prop :=
  es ≠ [] ∧
  (∀ x ∈ es, x.1 < (chainModel J.whole).W.n ∧ 0 ≤ x.2.1 ∧ x.2.1 < 1 ∧
    (Lst J : ℝ) ≤ oW J ztbui) ∧
  ztxsp ∧
  es.Pairwise ztxxd ∧
  (∀ i, i + 1 < es.length →
    NoCutIn J S₂ ztbarp
      ztbarq) ∧
  ∀ x ∈ es, LabIn J S₂ x.1 x.2.1 x.2.2

/-- The word facts of the log records (as in `Out`). -/
def LogWords (P : Polygon) (J : Merge.Junction) (N₂ : NF)
    (ls : List ztck) : Prop :=
  ∀ r ∈ ls, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 4 ∧
    ztndi ∧ ztndq ∧
    ztnfj ∧ ztnge

/-- **The table up to the offset `o`**: flags `≤ 1`; a flag `1` holds an accepted position
(`CandOK`); every valid query whose chord meets `C₁` first, attached on the `C₁` part beyond the
start at an offset `≤ o`, has flag `1`. -/
def TabInv (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) (o : ℝ) : Prop :=
  ∀ j, j < 2 * N₂.nChords →
    c.nmem ztbwv ≤ 1 ∧
    (c.nmem ztbwv = 1 →
      CandOK P J ztwis ztwka ztri
        (c.nmem ztghl) (c.nmem ztghm)) ∧
    (ValidJ J zta N₂ j →
      J.whole.hitParam ztwka ztri <
        J.right.hitParam ztwka ztri →
      ∀ (p : ℕ) (t : ℝ), SideAttach (chainModel J.whole).W
          ztbams p t →
        sidePt (chainModel J.whole).W p t = rayPt ztwka ztri
          ztbanq →
        (Lst J : ℝ) < oW J ztk → oW J ztk ≤ o → c.nmem ztbwv = 1)

/-- **The invariant of the event loop** at the start of an iteration (configuration `c`, start of
the run steps `c₀`). -/
structure LoopInv (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c₀ c : Config) : Prop where
  /-- the stops of stage 2 -/
  stops : ∃ rs ax, StopData P J N₂ c rs ax
  /-- sorted, at most two stops at one offset -/
  sorted : ∀ i i', i ≤ i' → i' < c.nreg sC → stopOff P J c i ≤ stopOff P J c i'
  two : ∀ i, i + 2 < c.nreg sC → stopOff P J c i < stopOff P J c ztcnn
  /-- the layout: table at the allocator of `c₀`, then the log, then the stop arrays -/
  tab0 : c.nreg cTB = c₀.nreg ALLOC
  lay1 : c.nreg cTB + 6 * N₂.nChords ≤ c.nreg lB
  lay2 : c.nreg lB + 7 * logCap N₁ N₂ ≤ c.nreg sB
  lay3 : c.nreg lB + 7 * logCap N₁ N₂ ≤ c.nreg aB
  lay4 : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC
  lay5 : c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC
  /-- the key and its label set -/
  key : PosW P J ztwe ztbhr
  keyL : (Lst J : ℝ) ≤ keyOff P J c
  labN : c.nreg kN ≤ 4
  labR : ∀ i, i < c.nreg kN → c.nreg ztbuc < N₂.nRegions
  inv : EvInv J ztwis ztbnc (curLab P J N₂ c)
  /-- the gap regions -/
  gapN : c.nreg gN ≤ 2
  gapR : ∀ i, i < c.nreg gN → c.nreg ztcvq < N₂.nRegions
  gap : ∀ V, GapLab J ztwis V →
    ∃ i, i < c.nreg gN ∧ regOf ztj zta N₂ ztbagl = V
  /-- the stop pointer: the stops at or before the key -/
  ptr : c.nreg sP ≤ c.nreg sC
  ptrL : ∀ i, i < c.nreg sC → (i < c.nreg sP ↔ stopOff P J c i ≤ keyOff P J c)
  /-- the log so far, ending with the current key -/
  log : ∃ ls : List ztck, ls.length = c.nreg lC ∧
    LogRecsAt c.nmem ztqiv ls ∧ LogWords P J N₂ ls ∧
    LogPre J ztwis ztxxq ∧
    ls.getLast? = some (c.nreg kE, c.nreg kH, c.nreg kN, c.nreg kL, c.nreg ztdvf,
      c.nreg ztdvg, c.nreg ztdvh)
  /-- the measure: the log records and the keys left -/
  meas : c.nreg lC + (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard ≤ (keyS P J N₁ N₂).ncard + 1
  /-- the table up to the key -/
  tab : TabInv P J N₂ c ztbnc
  /-- the run state -/
  done0 : c.nreg dF = 0

/-! ## One iteration -/

/-- The reset of the best candidate: `cs` is `cw` with `bF = bN = 0`. -/
def ResetRel (cw cs : Config) : Prop :=
  cs.nmem = cw.nmem ∧ cs.nreg bF = 0 ∧ cs.nreg bN = 0 ∧
    ∀ r, r ≠ bF → r ≠ bN → cs.nreg r = cw.nreg r

/-- **The facts of one iteration** from `c` (start) through `cw` (after the window), `cs` (after
the reset), `co` (after the origins) to `c'` (after the next key). -/
def IterRel (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c cw cs co c' : Config) : Prop :=
  WinOut P J N₁ c cw ∧ c.nreg ALLOC ≤ cw.nreg ALLOC ∧ ResetRel cw cs ∧
    BatchInv P J N₂ cs
      ztwro
      zthib co ∧
    KeyOut P J co c'

/-- **Task L1 (mathematics): one iteration that does not finish** keeps the invariant and lowers
the number of keys left. -/
def StepTask : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 0 →
    LoopInv P J N₁ N₂ c₀ c' ∧
      (keyS P J N₁ N₂ ∩ Ioi ztcnt).ncard < (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard

/-- **Task L2 (mathematics): the last iteration** gives the outputs (read through `fin`) and the
size of the log. -/
def DoneTask : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 1 →
    Out P J N₂ ztjvd ∧ c'.nreg lC ≤ logCap N₁ N₂

/-! ## The start of the loop -/

/-- The registers the start may write (besides the oracle bands and the allocator). -/
def StR (r : ℕ) : Prop :=
  r = kE ∨ r = kH ∨ r = kN ∨ ztdot ∨ r = gN ∨ r = gR ∨ r = gR + 1 ∨ r = sP ∨
    r = dF ∨ r = lC ∨ ztfus ∨ ztgz ∨
    (sw 2610 ≤ r ∧ r ≤ sw 2612) ∨ ztcok

/-- **Task L0: the start of the loop**, at cost `κS0 D (TLR + 1)`: after the preparation
(`PrepOut` from `c₀`) and stage 2 (`StopOut` from `c₁` to `c`), the program `start` reaches the
invariant `LoopInv` (the start key `((gW + Lst) % n, 0)`; its label set: the labels of the
anchored stops at the start key if one exists (`evInv_anchor`, through `StartMathTask`), else the
region faced before the end of the right stretch (`StartTask`); the gap regions (`face`); the stop
pointer past the stops at the start key; the first log record), writing only `StR`, the oracle
bands, the allocator and the log record. -/
def LoopStartTask : Prop :=
  ∃ (start : Stmt) (κS0 : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c₁ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → PrepOut N₁ N₂ c₀ c₁ →
      StopOut P J N₁ N₂ c₁ c → IInv W c₀ c →
      c.nreg ALLOC + κS0 zto * ztgf ≤ W →
      IRS P W c₀ start c (κS0 zto * ztgf) (fun c' =>
        LoopInv P J N₁ N₂ c₀ c' ∧
        ztfcv ∧
        ztdww)

/-! ## The arcs of a region (mathematics) -/

/-- **Task R (mathematics): the arcs of a region**: a region record of a valid normal form of a
chain model with degree cap `D` lists at most `D + 1` arcs (`arcsPerRegion`, distinct start keys
of the arcs of one region, `ArcsOK`). -/
def RegArcsTask : Prop :=
  ∀ (C : Chain) (Q : Polygon) (N : NF) (D : ℕ), C.P.Simple → IsNF ztc Q N →
    (chainModel C).DegLe ztwjh D →
    ∀ r, r < N.nRegions → (N.region r).arcs.length ≤ D + 1
def resetL : List Instr := [.constN bF 0, .constN bN 0]

/-- **One iteration of the event loop.** -/
def iter (win key : Stmt) (orgs : Stmt → Stmt) (sh g : Stmt) : Stmt :=
  .seq win (.seq (block resetL) (.seq (orgs ztkbr) key))

/-- The cost of one origin, for at most `2 (D + 1)` gathered arcs. -/
def odK (Fg D KG : ℕ) : ℕ := orgDoK Fg (2 * ztef) KG

/-- The cost of one iteration. -/
def iterK (KW KK κO Fg D KG : ℕ) : ℕ :=
  KW + (2 + ((zteki * ztpcw + κO) + KK))
theorem orgDoK_mono {Fg K K' KG : ℕ} (h : K ≤ K') : orgDoK Fg K KG ≤ orgDoK Fg K' KG := by
  unfold orgDoK evCandK evShotK ShotList.shotCost
  simp_all
theorem regArcs_length_le {N : NF} {rs : List ℕ} {B : ℕ}
    (h : ∀ r ∈ rs, (N.region r).arcs.length ≤ B) : (regArcs N rs).length ≤ rs.length * B := by
  induction rs with
  | nil => zupch
  | cons r rs ih =>
    have h1 := h r List.mem_cons_self
    have h2 := ih fun r' hr' => h r' ztszl
    simp only [regArcs, List.flatMap_cons, List.length_append, List.length_cons] at h2 ⊢
    rw [Nat.succ_mul]
    omega
theorem regArcs_lt {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) {rs : List ℕ}
    (hrs : ∀ r ∈ rs, r < N.nRegions) : ∀ a ∈ regArcs N rs, a < N.arcs.length := by
  zuge
  unfold regArcs at ha
  zufyx
  exact (((regOf_spec hN).2.2.1.2.2.2 r zttoi a).1 har).1

/-- The registers an iteration does not write. -/
def KeepR (r : ℕ) : Prop :=
  240000 ≤ r ∧ r < 250000 ∧ ¬ WR r ∧ r ≠ bF ∧ r ≠ bN ∧ ¬ OrgR r ∧ ¬ LR r
theorem keepR_of {r : ℕ} (h : ztnga ∨ (242400 ≤ r ∧ r < 242410) ∨
    (242426 ≤ r ∧ r < 242460) ∨ (242480 ≤ r ∧ r < 243000)) : KeepR r := by
  unfold KeepR WR OrgR CandR BestR LblR LR bF bE bH bN bL oK oS sw; omega
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **One iteration of the event loop.** -/
theorem iter_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {win key g : Stmt} {orgs : Stmt → Stmt}
    {KW KK κO KG : ℕ} (hgen : GenOK P W c₀ J g KG)
    (hreg : ∀ r, r < N₁.nRegions → (N₁.region r).arcs.length ≤ c₀.nreg ztbey + 1)
    (hcount : (keyS P J N₁ N₂).ncard ≤ 4 * N₂.nChords + 2 * N₁.nChords + 9)
    (hwin : ∀ c, IInv W c₀ c → PosW P J ztwe ztbhr →
      (Lst J : ℝ) ≤ offK P J ztwe ztbhr → c.nreg ALLOC + KW ≤ W →
      IRS P W c₀ win c KW ztqdg)
    (horgs : ∀ (od : Stmt) (Kod : ℕ) (Inv : Set ℕ → Config → Prop),
      (∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c → c.nreg oK < N₂.nChords →
        c.nreg oS ≤ 1 → c.nreg ALLOC + Kod ≤ W →
        IRS P W c₀ od c Kod (fun c' => Inv ztxxm c' ∧
          ztwpx ∧
          ztvw)) →
      (∀ (O : Set ℕ) (c c' : Config), Inv O c → ztedk →
        c'.nmem = c.nmem → c'.rmem = c.rmem → c'.rreg = c.rreg → c'.output = c.output →
        Inv O c') →
      ∀ (O : Set ℕ) (c : Config), IInv W c₀ c → Inv O c →
        ztxrl →
        ztxrm →
        ztimp →
        c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
        c.nreg ALLOC + ztwqy ≤ W →
        IRS P W c₀ ztwbf c ztwqy
          ztmbh)
    (hkey : ∀ c, IInv W c₀ c →
      PosW P J ztwe ztbhr →
      ztxbh →
      ztdav →
      ztwwt →
      (∀ i i', i ≤ i' → i' < c.nreg sC →
        offK P J ztbjv ztbjw ≤ offK P J ztkfo ztkfp) →
      (∀ i, i + 2 < c.nreg sC →
        offK P J ztbjv ztbjw < offK P J ztxyb ztxyc) →
      c.nreg sP ≤ c.nreg sC → c.nreg kN ≤ 4 → c.nreg bN ≤ 4 →
      c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC → c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC →
      c₀.nreg ALLOC ≤ c.nreg lB → c.nreg lB + 7 * ztllq ≤ c.nreg ALLOC →
      c.nreg ALLOC + KK ≤ W →
      IRS P W c₀ key c KK ztlew)
    {c : Config} (hI : IInv W c₀ c) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hroom : c.nreg ALLOC + iterK KW KK κO ztwiu zto KG ≤ W) :
    IRS P W c₀ (iter win key orgs sh g) c (iterK KW KK κO ztwiu zto KG)
      ztfyf := by
  obtain ⟨rs, ax, hlen, haxl, hrecs, haux, hSok, hword, hauxok, hsize⟩ := hL.stops
  unfold iter iterK at *
  -- 1. the window
  refine IRS.seq (hwin c hI hL.key hL.keyL by_omega) ?_
  rintro cw hIw hAw hAw' hWO
  have hWO' := hWO
  obtain ⟨rsW, hrsW2, hrsWR, hgK, hgB1, hgB2, harcs, hwX1, hwE, -, hmW, hfrW⟩ := hWO
  have keepW : ∀ r, KeepR r → cw.nreg r = c.nreg r := fun r h =>
    hfrW r ztoxz h.2.2.1 (by have := h.1; unfold ALLOC; omega)
  -- 2. the reset
  refine IRS.seq (K₁ := resetL.length)
    (IRS.block resetL hIw ⟨ztkma,
      ⟨iscr_sw by_decide by_decide, by_omega⟩, trivial⟩) ?_
  rintro cs hIs hAs hAs' rfl
  have hrl : resetL.length = 2 := rfl
  set cs : Config := { cw with nreg := regB cw.nmem resetL cw.nreg } with hcsd
  have hsF : cs.nreg bF = 0 := by
    rfl
  have hsN : cs.nreg bN = 0 := by
    rfl
  have hsO : ∀ r, r ≠ bF → r ≠ bN → cs.nreg r = cw.nreg r := fun r h1 h2 =>
    regB_other _ _ _ (by
      zug
      simp only [resetL, List.mem_cons, List.not_mem_nil, or_false] at hi
      zufzx
      · exact Ne.symm h1
      · exact Ne.symm h2)
  have hRes : ResetRel cw cs := ⟨rfl, hsF, hsN, hsO⟩
  have keepS := fun r h =>
    (hsO r h.2.2.2.1 h.2.2.2.2.1).trans (keepW r h)
  have hmS : ∀ x, x < c.nreg ALLOC → cs.nmem x = c.nmem x := by_omega
  -- the window registers, kept by the reset
  have sGK : ztsfu := hsO _ by_decide by_decide
  have sGB : ztsft := hsO _ by_decide by_decide
  have sX : cs.nreg wX = cw.nreg wX := hsO _ by_decide by_decide
  have sE : cs.nreg wE = cw.nreg wE := hsO _ by_decide by_decide
  have sH : cs.nreg wH = cw.nreg wH := hsO _ by_decide by_decide
  -- kept registers
  have kTB : ztguj := keepS _ ztbeq
  have kaB : ztsfq := keepS _ ztbeq
  have ksC : ztsfr := keepS _ ztbeq
  have ksB : cs.nreg sB = c.nreg sB := keepS _ ztbeq
  have kkE : ztizg := keepS _ ztbeq
  have kkH : ztizh := keepS _ ztbeq
  have kkN : ztmuy := keepS _ ztbeq
  have kgN : ztmux := keepS _ ztbeq
  have klB : cs.nreg lB = c.nreg lB := keepS _ ztbeq
  have klC : cs.nreg lC = c.nreg lC := keepS _ ztbeq
  have ksP : ztsfs := keepS _ ztbeq
  have kkL : ∀ i, i < 4 → cs.nreg _ = c.nreg ztbuc := fun i hi =>
    keepS _ (keepR_of ztiix)
  have kgR : ∀ i, i < 2 → cs.nreg _ = c.nreg ztcvq := fun i hi =>
    keepS _ (keepR_of (by unfold gR sw; omega))
  have hAcs := hAw
  -- the layout at `cs`
  have hT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg ALLOC := by
    have := hL.lay1; have := hL.lay2; have := hL.lay4; omega
  have hWT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg wGB := by
    have := hL.lay1; have := hL.lay2; have := hL.lay4; omega
  have hauxT : cs.nreg cTB + 6 * N₂.nChords ≤ cs.nreg aB := by
    have := hL.lay1; have := hL.lay3; omega
  have hauxL : cs.nreg aB + 5 * cs.nreg sC ≤ cs.nreg ALLOC := by
    have := hL.lay5; omega
  -- the gathered arcs
  have hLlen : (regArcs N₁ rsW).length ≤ 2 * ztbaav := by
    have := regArcs_length_le
      (fun r hr => hreg r (hrsWR r hr))
    have h2 : rsW.length * ((c₀.nreg _) + 1) ≤ 2 * ztbaav := Nat.mul_le_mul_right _ hrsW2
    omega
  have hLarc := regArcs_lt E.hNF₁ hrsWR
  -- 3. the origins
  have hod : ∀ (O : Set ℕ) (c' : Config), IInv W c₀ c' →
      BatchInv P J N₂ cs (ShotList.loSet ztbw zta cs.nmem ztcpv
        ztdzq []) O c' → c'.nreg oK < N₂.nChords → c'.nreg oS ≤ 1 →
      c'.nreg ALLOC + odK ztwiu zto KG ≤ W →
      IRS P W c₀ ztkbr c' (odK ztwiu zto KG) (fun c'' =>
        BatchInv P J N₂ cs (ShotList.loSet ztbw zta cs.nmem ztcpv
          ztdzq []) (insert (2 * c'.nreg oK + c'.nreg oS) O) c'' ∧
        (∀ r, ztbcj ∨ ER r → c''.nreg r = c'.nreg r) ∧
        (∀ x, c'.nreg aB ≤ x → x < c'.nreg aB + 5 * c'.nreg sC → c''.nmem x = c'.nmem x)) := by
    intro O c' hI' hInv hk hs hroom'
    rw [sGK, hgK] at hInv ⊢
    have hmono := orgDoK_mono (Fg := F ztq) (KG := KG) hLlen
    exact (orgDo_batch E hgen hLarc by_omega
      by_omega (fun k hk' => by rw [sGB]; exact harcs k hk') hT hWT hauxT hauxL
      (by rw [kkE, kkH]; exact hL.key) O c' hI' hInv hk hs
      (by unfold odK at hroom'; omega)).mono (by unfold odK; omega) (fun _ h => h)
  have hstab : ∀ (O : Set ℕ) (c1 c2 : Config),
      BatchInv P J N₂ cs _ O c1 → (∀ r, ¬ LR r → c2.nreg r = c1.nreg r) →
      c2.nmem = c1.nmem → c2.rmem = c1.rmem → c2.rreg = c1.rreg → c2.output = c1.output →
      BatchInv P J N₂ cs (ShotList.loSet ztbw zta cs.nmem ztcpv
        ztdzq []) O c2 :=
    fun O c1 c2 h hr hm _ _ _ => batch_stable h hr hm
  have hpar : ∀ i, i < cs.nreg sC → parOf cs i ≤ N₂.nChords := fun i hi => by
    rw [ksC, ← hlen] at hi
    have hA := haux i by_omega
    have hok := (hauxok i hi).2.2.2.2.2.2.1
    unfold parOf
    rw [kaB, hmS _ (by have := hL.lay5; omega)]
    omega
  refine IRS.seq
    (horgs _ _ _ hod hstab ∅ cs hIs (batch_base hsF by_omega)
      (fun i hi => by
        rw [kkL i by_omega]
        exact hL.labR i by_omega)
      (fun i hi => by
        rw [kgR i by_omega]
        exact hL.gapR i by_omega)
      hpar hauxL by_omega) ?_
  rintro co hIo hAo hAo' hBo
  rw [Set.empty_union] at hBo
  have hBo' := hBo
  obtain ⟨hregO, hAO, A, hBA⟩ := hBo
  have keepO : ∀ r, KeepR r → co.nreg r = cs.nreg r := fun r h =>
    hregO r ztoxz h.2.2.2.2.2.1 h.2.2.2.2.2.2
      (by have := h.1; unfold ALLOC; omega)
  have keepOC := fun r h => (keepO r h).trans (keepS r h)
  have hmO :=
    fun x h1 h2 => (hBA.memT x by_omega ztjku).trans (hmS x h2)
  -- registers at `co`
  have oaB : ztsfj := keepOC _ ztbeq
  have osC : ztsfl := keepOC _ ztbeq
  have osB : ztmuw := keepOC _ ztbeq
  have okE : co.nreg kE = c.nreg kE := keepOC _ ztbeq
  have okH : co.nreg kH = c.nreg kH := keepOC _ ztbeq
  have okN : ztsfk := keepOC _ ztbeq
  have olB : ztize := keepOC _ ztbeq
  have olC : ztgui := keepOC _ ztbeq
  have osP : ztsfm := keepOC _ ztbeq
  have nW : ∀ r, (r = wX ∨ r = wE ∨ r = wH) → co.nreg r = cw.nreg r := fun r hr => by
    rw [hregO r (band_sw_not (by unfold wX wE wH sw at hr; omega))
      (by unfold OrgR CandR BestR LblR bF bE bH bN bL; unfold wX wE wH sw at hr; unfold sw; omega)
      (by unfold LR oK oS; unfold wX wE wH sw at hr; unfold sw; omega)
      (by unfold wX wE wH sw at hr; unfold ALLOC; omega)]
    exact hsO r (by unfold wX wE wH sw at hr; unfold bF sw; omega)
      (by unfold wX wE wH sw at hr; unfold bN sw; omega)
  have oX := nW _ ztp
  have oE : co.nreg wE = cw.nreg wE := nW _ by_omega
  have oH : co.nreg wH = cw.nreg wH := nW _ by_omega
  -- the stops at `co`
  have hstopM : ∀ i, i < c.nreg sC → stopE co i = stopE c i ∧ stopH co i = stopH c i := by
    zug
    have := hL.lay4; have := hL.lay1; have := hL.lay2
    zujre
    rw [osB, hmO _ by_omega by_omega, hmO _ by_omega by_omega]
    omega
  have hoff : ∀ i, i < c.nreg sC → offK P J (stopE co i) (stopH co i) = stopOff P J c i :=
    fun i hi => by zungx; rfl
  -- the room of the log
  have hroomL : co.nreg lB + 7 * (co.nreg lC + 1) ≤ co.nreg ALLOC := by
    have hm := hL.meas
    have h2 := hL.lay2; have h4 := hL.lay4
    rw [olB, olC]
    have : c.nreg lC + 1 ≤ logCap N₁ N₂ := by unfold logCap; omega
    omega
  refine (hkey co hIo (by rw [okE, okH]; exact hL.key) (fun h => by
      obtain ⟨⟨j, hj⟩, -⟩ := hBA.bAcc h
      exact (hBA.acc _ hj).2.2.2.2.2.2.2.1)
    (fun h => by rw [oE, oH]; rw [oX] at h; exact (hwE h).1)
    (fun i hi => by
      rw [osC] at hi
      zungx
      zufuv
      obtain ⟨r1, r2, -⟩ := hrecs i hi'
      unfold stopE stopH; rw [r1, r2]
      exact (hword _ (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; simp)).1)
    (fun i i' h1 h2 => by
      rw [osC] at h2; rw [hoff i by_omega, hoff i' h2]; exact hL.sorted i i' h1 h2)
    (fun i h => by
      rw [osC] at h; rw [hoff i by_omega, hoff _ h]; exact hL.two i h)
    (by rw [osP, osC]; exact hL.ptr) (by rw [okN]; exact hL.labN) hBA.fN
    (by rw [osB, osC]; have := hL.lay4; omega) by_omega
    (by rw [olB]; have := hL.lay1; have := hL.tab0; omega) hroomL by_omega).mono le_rfl ?_
  intro c' hK
  exact ⟨cw, cs, co, hWO', hAw, hRes, hBo', hK⟩
theorem iter_keep {c cw cs co c' : Config} (h : IterRel P J N₁ N₂ c cw cs co c') :
    (∀ r, KeepR r → ¬ KR r → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC := by
  obtain ⟨hWO, hAw, ⟨-, -, -, hsO⟩, ⟨hregO, hAO, -⟩, ⟨hfrK, hAK, -⟩⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfrW⟩ := hWO
  have hsA : ztfkw :=
    hsO _ by_decide by_decide
  refine ⟨fun r hr hk => ?_, by_omega⟩
  have hb := band_sw_not ⟨hr.1, hr.2.1⟩
  have hra : ztjag := by have := hr.1; unfold ALLOC; omega
  rw [hfrK r hb hk hra, hregO r hb hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hra,
    hsO r hr.2.2.2.1 hr.2.2.2.2.1, hfrW r hb hr.2.2.1 hra]

/-- The end of the loop. -/
def FinS (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c₀ c : Config) : Prop :=
  c.nreg dF = 1 ∧ RunOut P J N₁ N₂ c₀ c

/-- The measure of the loop. -/
noncomputable def μL (P : Polygon) (J : Merge.Junction) (N₁ N₂ : NF) (c : Config) : ℕ :=
  if c.nreg dF = 0 then (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard + 1 else 0

/-- **The outputs after the last iteration.** -/
theorem done_runOut {c₀ c cw cs co c' : Config} (hL : LoopInv P J N₁ N₂ c₀ c)
    (hIR : IterRel P J N₁ N₂ c cw cs co c') (hOut : Out P J N₂ ztjvd)
    (hlC : c'.nreg lC ≤ logCap N₁ N₂) : RunOut P J N₁ N₂ c₀ c' := by
  obtain ⟨hk, hA⟩ := iter_keep hIR
  have esB : ztiyz :=
    hk _ ztbeq zthub
  have esC : ztmum :=
    hk _ ztbeq zthuc
  have elB : ztgue :=
    hk _ ztbeq zthua
  have eTB : ztgud :=
    hk _ ztbeq zthtz
  obtain ⟨rs, ax, hlen, -, -, -, -, -, -, hsize⟩ := hL.stops
  have h0 := hL.tab0; have h1 := hL.lay1; have h2 := hL.lay2; have h4 := hL.lay4
  unfold logCap at h2 hlC
  refine ⟨hOut, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [esB, esC, elB, eTB] at * <;> try omega

/-- **The event loop.** -/
theorem loop_irs {W : ℕ} {c₀ : Config} {body : Stmt} {Kb : ℕ}
    (hiter : ∀ c, IInv W c₀ c → LoopInv P J N₁ N₂ c₀ c → c.nreg ALLOC + Kb ≤ W →
      IRS P W c₀ body c Kb ztfyf)
    (hstep : ∀ c cw cs co c', LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' →
      c'.nreg dF = 0 → LoopInv P J N₁ N₂ c₀ c' ∧
        (keyS P J N₁ N₂ ∩ Ioi ztcnt).ncard < (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard)
    (hdone : ∀ c cw cs co c', LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' →
      c'.nreg dF = 1 → Out P J N₂ ztjvd ∧ c'.nreg lC ≤ logCap N₁ N₂)
    (hfin : (keyS P J N₁ N₂).Finite)
    {c : Config} (hI : IInv W c₀ c) (hK1 : c.nreg K1 = 1) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hroom : c.nreg ALLOC + ztkq * ztkpl ≤ W) :
    IRS P W c₀ (.whileLtN dF K1 body) c (ztkq * ztkpl + 2)
      (fun c' => FinS P J N₁ N₂ c₀ c') := by
  have hle : ∀ c : Config, μL P J N₁ N₂ c ≤ (keyS P J N₁ N₂).ncard + 1 := fun c => by
    unfold μL; split_ifs
    · have := Set.ncard_le_ncard (Set.inter_subset_left (s := keyS P J N₁ N₂)
        (t := Ioi ztbnc)) hfin
      omega
    · omega
  have hμ : ∀ c : Config, LoopInv P J N₁ N₂ c₀ c →
      μL P J N₁ N₂ c = (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard + 1 := fun c h => by
    unfold μL; rw [ite_eq_left h.done0]
  have hw := IRS.while (P := P) (W := W) (c₀ := c₀) (a := dF) (b := K1) (body := body)
    (fun c => c.nreg K1 = 1 ∧ (LoopInv P J N₁ N₂ c₀ c ∨ FinS P J N₁ N₂ c₀ c)) (μL P J N₁ N₂) Kb
    (fun c ⟨hk, h⟩ ht => by
      zuy
      · simp_all
      · rw [hk, h.1] at ht; omega)
    (fun c hIc ⟨hk, h⟩ ht hr => by
      have hLc : LoopInv P J N₁ N₂ c₀ c := by
        zuy
        · zubh
        · rw [hk, h.1] at ht; omega
      refine (hiter c hIc hLc hr).mono le_rfl ?_
      rintro c' ⟨cw, cs, co, hIR⟩
      have hkeep := (iter_keep hIR).1
      have hk' : c'.nreg K1 = 1 := by
        rw [hkeep _ ztbeq (by unfold KR kE kH kN kL sP dF lC K1 sw; omega)]
        exact hk
      by_cases hd : c'.nreg dF = 0
      · grind
      · have hd1 : ztunh := by
          obtain ⟨-, -, -, -, hK⟩ := hIR
          obtain ⟨-, -, hnone, hsome⟩ := hK
          grind
        obtain ⟨hOut, hlC⟩ := hdone c cw cs co c' hLc hIR hd1
        refine ⟨⟨hk', Or.inr ⟨hd1, done_runOut hLc hIR hOut hlC⟩⟩, ?_⟩
        rw [hμ c hLc]
        unfold μL; simp_all)
    hI ⟨hK1, Or.inl hL⟩ (by have := Nat.mul_le_mul_left ztkq ztvvm; omega)
  refine hw.mono (by have := Nat.mul_le_mul_left ztkq ztvvm; omega) ?_
  rintro c' ⟨⟨hk, h⟩, ht⟩
  zuy
  · rw [hk, h.done0] at ht; omega
  omega
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
@[expose] public section
def iterA (D κWD κGD κO κK : ℕ) : ℕ :=
  4 * κWD + 2 + zteki * ztcrq + κO + κK

/-- The constant of the run steps. -/
def runA (D κWD κGD κO κK κP κSD κS0D : ℕ) : ℕ :=
  10 * iterA D κWD κGD κO κK + 22 + 4 * κS0D + κP + κSD
theorem odK_le {Fg D KG Z : ℕ} (hF : Fg + 1 ≤ Z) :
    odK Fg D KG ≤ ((2 * D + 3) * 500016 + 166500) * Z + KG := by
  unfold odK orgDoK evCandK evShotK ShotList.shotCost
  have h1 : 16 * Fg + 500000 ≤ 500016 * Z := by_omega
  have h2 : ztzaw * ztgbz ≤ ztzaw * (500016 * Z) :=
    Nat.mul_le_mul_left _ h1
  nlinarith
theorem iterK_le {Fg D T L KG κWD κGD κO κK Z : ℕ} (hZ : Z = Fg + L + 1) (hT : T ≤ L + 3)
    (hKG : KG = κGD * ztbbs) :
    iterK ztyti κK κO Fg D KG ≤ iterA D κWD κGD κO κK * Z := by
  zuhxw
  have hT4 : T + 1 ≤ 4 * Z := by_omega
  have hF4 : Fg + T + 1 ≤ 4 * Z := by_omega
  have hW : κWD * ztxz ≤ κWD * ztstb := Nat.mul_le_mul_left _ hT4
  have hG : KG ≤ κGD * ztstb := by rw [hKG]; exact Nat.mul_le_mul_left _ hF4
  have hO := odK_le (Fg := Fg) (D := D) (KG := KG) (Z := Z) by_omega
  have hO2 : odK Fg D KG + κO ≤ ztcrq * Z := by
    have : ztsog := Nat.le_mul_of_pos_right _ hZ1
    nlinarith
  have hO3 : zteki * ztpcw ≤
      zteki * (ztcrq * Z) :=
    Nat.mul_le_mul_left _ hO2
  have hk1 : ztsog := Nat.le_mul_of_pos_right _ hZ1
  have hk2 : κK ≤ κK * Z := Nat.le_mul_of_pos_right _ hZ1
  unfold iterK iterA
  nlinarith

/-- **The cost of the run steps.** -/
theorem run_cost {D Fg L T K' n κWD κGD κO κK κP κSD κS0D Z KG : ℕ} (hZ : Z = Fg + L + 1)
    (hT : T ≤ L + 3) (hK : 1 ≤ K') (hn : n + 1 ≤ 10 * K') (hKG : KG = κGD * ztbbs) :
    κP * K' + (κSD * K' * Z + (κS0D * ztxz +
      ((iterK ztyti κK κO Fg D KG + 2) * ztkk + 2))) ≤
      runA D κWD κGD κO κK κP κSD κS0D * K' * Z := by
  zuhxw
  have hit := iterK_le (Fg := Fg) (D := D) (T := T) (L := L) (KG := KG) (κWD := κWD) (κGD := κGD)
    (κO := κO) (κK := κK) (Z := Z) hZ hT hKG
  set A := iterA D κWD κGD κO κK with hA
  set I := iterK ztyti κK κO Fg D KG with hI
  have hKZ : 1 ≤ K' * Z := Nat.one_le_iff_ne_zero.2 zthbt
  have h1 : (I + 2) * ztkk ≤ ztpvk * ztsqt :=
    Nat.mul_le_mul by_omega hn
  have h2 : ztpvk * ztsqt + 2 ≤ (10 * A + 22) * ztjjg := by_nlinarith
  have h3 : κS0D * ztxz ≤ 4 * κS0D * ztjjg := by
    have : T + 1 ≤ 4 * ztjjg := by_nlinarith
    nlinarith
  have h4 : κP * K' ≤ κP * ztjjg := Nat.mul_le_mul_left _ by_nlinarith
  unfold runA
  grind
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
def runProg (prep start win key : Stmt) (mk2 orgs mkG : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq prep (.seq ztvzf (.seq start (.whileLtN dF K1 (iter win key orgs sh ztqtq))))
set_option maxHeartbeats 8000000 in
/-- **The run steps meet `RunTask`.** -/
theorem runTask_of (hGen : GenTask) (hStop : StopTask) (hWin : WinTask) (hOrgs : OrgsTask)
    (hKey : KeyTask) (hPrep : PrepTask) (hL0 : LoopStartTask) (hL1 : StepTask) (hL2 : DoneTask)
    (hRA : RegArcsTask) (hC : CountTask) : RunTask := by
  obtain ⟨mkG, κG, hG⟩ := hGen
  obtain ⟨mk2, κS, hS⟩ := hStop
  obtain ⟨win, κW, hW⟩ := hWin
  obtain ⟨orgs, κO, hO⟩ := hOrgs
  obtain ⟨key, κK, hK⟩ := hKey
  obtain ⟨prep, κP, hPr⟩ := hPrep
  obtain ⟨start, κS0, hSt⟩ := hL0
  refine ⟨runProg prep start win key mk2 orgs mkG,
    fun D => runA D (κW D) (κG D) κO κK κP (κS D) (κS0 D), ?_⟩
  intro sh Bs F X Ok P W c₀ J N₁ N₂ E hwb hroom
  have hI0 : ztulc := ⟨hwb, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  zubmr
  obtain ⟨hfin0, hcnt0⟩ := hC P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hfin : (keyS P J N₁ N₂).Finite := hfin0
  have hcnt : ztdap := hcnt0
  have hPl : J.left.P.Simple := E.ctx1.2.2.2.2.1
  have hreg := hRA J.left zta N₁ zto hPl E.hNF₁ E.hdeg₁
  have hT := E.hTLR
  have hsum := run_cost (D := c₀.nreg ztbey) (Fg := F ztq)
    (L := Nat.clog 2 ztks) (T := c₀.nreg TLR)
    (K' := N₁.nChords + N₂.nChords + 1) (n := (keyS P J N₁ N₂).ncard) (κWD := κW zto)
    (κGD := κG zto) (κO := κO) (κK := κK) (κP := κP) (κSD := κS zto)
    (κS0D := κS0 zto)
    (KG := κG zto * ztwit) rfl hT by_omega
    by_omega rfl
  unfold runProg
  refine IRS.mono (IRS.seq (hPr sh Bs F X Ok P W c₀ c₀ J N₁ N₂ E hI0 E.hTA.symm (by
      omega)) ?_)
    hsum ztb
  rintro c₁ hI₁ hA₁ hA₁' hPO
  refine IRS.seq (hS sh Bs F X Ok P W c₀ c₁ J N₁ N₂ E hI₁ by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' hSO
  refine IRS.seq (hSt sh Bs F X Ok P W c₀ c₁ c₂ J N₁ N₂ E hPO hSO hI₂ by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hL3, -, -⟩
  refine (loop_irs (Kb := iterK ztzoe κK κO
      ztwiu zto
      ztbaqj)
    (fun c hIc hLc hr => iter_irs E (hG sh Bs F X Ok P W c₀ J N₁ N₂ E) hreg
      hcnt
      (fun c hIc hpos hL hr => hW sh Bs F X Ok P W c₀ c J N₁ N₂ E hIc hpos hL hr)
      (hO sh Bs F X Ok P W c₀ J N₁ N₂ E)
      (fun c hIc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 =>
        hK sh Bs F X Ok P W c₀ c J N₁ N₂ E hIc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)
      hIc hLc hr)
    (fun c cw cs co c' h1 h2 h3 => hL1 sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E h1 h2 h3)
    (fun c cw cs co c' h1 h2 h3 => hL2 sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E h1 h2 h3)
    hfin hI₃ (E.hK.fix hI₃).2.1 hL3 by_omega).mono le_rfl ?_
  exact fun c' h => h.2
theorem sweepEvSpec_of (hAsm : AsmTask) (hInit : InitTask) (hGen : GenTask) (hStop : StopTask)
    (hWin : WinTask) (hOrgs : OrgsTask) (hKey : KeyTask) (hPrep : PrepTask)
    (hL0 : LoopStartTask) (hL1 : StepTask) (hL2 : DoneTask) (hRA : RegArcsTask)
    (hC : CountTask) : SweepEvSpec :=
  hAsm hInit (runTask_of hGen hStop hWin hOrgs hKey hPrep hL0 hL1 hL2 hRA hC)
theorem arcsTask : ArcsTask := by
  intro C Q N hP hN
  classical
  zudbh
  zubqs

  set F := N.F M Q with hF
  have hN' := hN
  obtain ⟨hFam, -, -, reg, hRC, -, hAO, -, -⟩ := hN
  set A := N.arcs.length with hA
  set R := N.nRegions with hR
  -- 1. the arcs by region
  have h1 : A = ∑ r ∈ Finset.range R, ((Finset.range A).filter fun j => (N.arc j).reg = r).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.range A) (t := Finset.range R)
      (f := fun j => (N.arc j).reg) (fun j hj => by
        have hj' : j < A := by_simp_all
        simpa using (hAO.1 j hj').1)
    grind
  -- 2. per region: at most `deg + 1` arcs
  have h2 : ∀ r, r < R → ((Finset.range A).filter fun j => (N.arc j).reg = r).card ≤
      M.deg F ztcz + 1 := by
    zuz
    have hU : reg r ∈ M.regions F := hRC.1 r hr
    obtain ⟨hfin, hle⟩ := arcsPerRegion M Q F hGM hFam ztcz hU
    refine le_trans ?_ hle
    zuezr
    refine Set.ncard_le_ncard_of_injOn (fun j => ztbyr)
      ztjvz (fun j hj j' hj' h => ?_) hfin
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj ⊢
      have := (hAO.1 j hj.1).2
      grind
    · simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj hj'
      have hk : M.key Q (N.arc j).s = M.key Q (N.arc j').s := congrArg Prod.fst h
      exact hAO.2.1 j j' hj.1 hj'.1 by_omega hk
  -- 3. the degrees sum to at most `2 K`
  have hsys := hM.sys F hFam.2.1 hFam.1
  have hpot := Merge.potential_le hsys hM.preconn hM.nonempty (subset_refl F) 0
  have himg : M.regions F = reg '' ((Finset.range R : Finset ℕ) : Set ℕ) := by
    zulge
    simp only [Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · intro hU; obtain ⟨r, hr, rfl⟩ := hRC.2.2 U hU; grind
    · zuewj
  have hinj : Set.InjOn reg ((Finset.range R : Finset ℕ) : Set ℕ) := fun r hr r' hr' h =>
    hRC.2.1 r r' by_grind by_grind h
  have h3 : ∑ r ∈ Finset.range R, M.deg F ztcz ≤ 2 * F.ncard := by
    have e : Merge.potential M.D 0 F = ∑ r ∈ Finset.range R, M.deg F ztcz := by
      unfold Merge.potential
      change ∑ᶠ U ∈ M.regions F, _ = _
      rw [himg, finsum_mem_image hinj, finsum_mem_coe_finset]
      rfl
    omega
  -- 4. the count
  have hK : F.ncard = N.nChords := Gran.ncard_F hN'
  have hRK : R = N.nChords + 1 := Gran.nRegions_eq hN' hM
  have h4 : ∑ r ∈ Finset.range R, ((Finset.range A).filter fun j => (N.arc j).reg = r).card ≤
      ∑ r ∈ Finset.range R, (M.deg F ztcz + 1) :=
    Finset.sum_le_sum fun r hr => h2 r ztjix
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h4
  omega
variable {P : Polygon} {m m' : ℕ → ℕ} (x : ℕ)
/-- **A well-formed model descriptor** survives a change of the memory at or above its bound. -/
theorem modelDescAt_keep' {D E E' : ℕ} {M : Model}
    (hwf : ModelDescWF P E m D) (hMD : ModelDescAt m D zta M)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D zta M ∧ ModelDescWF P E' m' D := by
  zuciq
  · obtain ⟨w', h0', hC'⟩ := ShotList.modelDesc_keep hwf h0 hC he hE
    exact ⟨Or.inl ztfwl, w'⟩
  · zucrt

    exact ⟨Or.inr ztrap,
      ⟨by_omega, fun h => by_omega⟩⟩

/-- Junction descriptors survive a change of the memory at or above the allocator. -/
theorem junction_keep {E E' b0 b1 b2 : ℕ} {H : Host}
    {J : Merge.Junction} (hJ : JunctionAt m b0 b1 b2 zta H J) (hJW : JunctionWF P E m b0 b1 b2)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    JunctionAt m' b0 b1 b2 zta H J ∧ JunctionWF P E' m' b0 b1 b2 := by
  obtain ⟨l0, l1⟩ := chainDesc_keep hJW.1 hJ.1 he hE
  obtain ⟨r0, r1⟩ := chainDesc_keep hJW.2.1 hJ.2.1 he hE
  obtain ⟨w0, w1⟩ := chainDesc_keep hJW.2.2.1 hJ.2.2 he hE
  refine ⟨⟨l0, r0, w0⟩, l1, r1, w1, fun H' hH' => ?_⟩
  have := NFLoc.hostAt_unique w0.1 hH'
  zumo
  zulyq

/-- **The stage-0 state** survives a step keeping `sw 0 … 99` and the memory below the
allocator, and not lowering the allocator. -/
theorem st0S_keep {c c' : Config} {H : Host} {J : Merge.Junction}
    (h : St0S P c H J) (hr : ∀ j, j < 100 → c'.nreg ztgc = c.nreg ztgc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    St0S P c' H J := by
  obtain ⟨h90, h91, h92, h93, hJ, hJW, d20, w20, d21, w21, h23, h24, hR, hL, h33, h34, h35, md30,
    mw30, md31, mw31⟩ := h
  have r : ∀ j, j < 100 → c'.nreg ztgc = c.nreg ztgc := hr
  obtain ⟨hJ', hJW'⟩ := junction_keep hJ hJW hm hA
  zucbg

  obtain ⟨m30, mw30'⟩ := modelDescAt_keep' mw30 md30 hm hA
  obtain ⟨m31, mw31'⟩ := modelDescAt_keep' mw31 md31 hm hA
  refine ⟨by_simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all,
    by simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all,
    by simp_all,
    fun k hk => by_grind,
    fun k hk => by_grind,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all⟩

/-! ## Arithmetic -/
theorem clog_four_mul : Nat.clog 2 (4 * x) ≤ Nat.clog 2 x + 2 := by
  zujhc
  have := Nat.le_pow_clog (by norm_num : 1 < 2) x
  omega
theorem clog_le_self' : Nat.clog 2 x ≤ x := by
  zuosp; exact Nat.lt_two_pow_self.le

/-! ## The environment -/

/-- The constant of the initialisation. -/
def κI : ℕ := 40000
set_option maxRecDepth 20000 in
/-- **The environment after the initialisation.** -/
theorem evEnv_of_init {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {J₀ : Merge.Junction} (hXl : X.CapLocal) (hBs : Bs ⊆ oracleBands)
    (hsh : ShooterOK sh Bs F X Ok) {P : Polygon} {W : ℕ} {c c₀ : Config} {k : ℕ}
    (hpre : Pre X Ok P W c) (fr : Frame ioBands c c₀ k) (R : InitRes P J₀ c c₀)
    (hk : k ≤ 31100 + 6 * Nat.clog 2 ztwkd)
    (hroom : c.nreg ALLOC + κI * ztwou ≤ W)
    {H : Host} {J : Merge.Junction} {N₁ N₂ : NF} (hJ₀ : J = J₀)
    (hpa : PreAt X Ok P c H J N₁ N₂) : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ := by
  subst hJ₀
  obtain ⟨hG, hWh, hX, hcap, -, -⟩ := hpre
  obtain ⟨hJ, hP, hOk1, hOk2, hNW1, hNW2, hNF1, hNF2, hdeg1, hdeg2, hsg1, hsg2, hst⟩ := hpa
  zuizh
  obtain ⟨-, -, -, -, -, hJW, d20, w20, d21, w21, -⟩ := hst'
  have hm : ∀ a, a < c.nreg ALLOC → c₀.nmem a = c.nmem a := R.mem
  have hA : ztsey := fr.2.2.2.2.2.1
  have hAk : c₀.nreg ALLOC ≤ c.nreg ALLOC + k := fr.2.2.2.2.2.2
  have kp : ∀ j, j < 600 → c₀.nreg ztgc = c.nreg ztgc := fun j hj =>
    R.keep _ ztxlc ztiiy
      ztce
  -- the normal forms
  zuibi

  have hK1 : c.nmem ztwb = N₁.nChords := nN1.1
  have hK2 : c.nmem ztrl = N₂.nChords := nN2.1
  have ha1 : c.nmem ztyej = N₁.arcs.length := nN1.2.1
  have ha2 : c.nmem ztyei = N₂.arcs.length := nN2.2.1
  have hA1 := arcsTask J.left zta N₁ hP hNF1
  have hA2 := arcsTask J.right zta N₂ hP hNF2
  zuiit
  rw [ha1, ha2] at hk
  have hL := R.hTLR
  rw [ha1, ha2] at hL
  have hpow : N₁.arcs.length + N₂.arcs.length + 1 ≤ 2 ^ c₀.nreg TLR := by
    zvnlm; exact Nat.le_pow_clog by_norm_num _
  have hLle := clog_le_self' ztqbc
  have hMD := R.hA
  have hTB := R.hTBR
  have hAl := R.hAl
  -- the descriptor of `C₁`
  have k20 : c₀.nreg ztiw = c.nreg ztiw := kp 20 by_norm_num
  obtain ⟨hmd, hmwf, hCD⟩ := modelDesc_of_copy (E' := c₀.nreg ALLOC) w20 d20 hMD hm R.md0
    (fun j hj => R.mdc j hj) by_omega
  have ctx20 := chainCtx_of (W := W) hG hWh hP hJ hJW d20 w20
  have ctx21 := chainCtx_of (W := W) hG hWh hP hJ hJW d21 w21
  have ctxW := chainCtx_of (W := W) (d := sw 2) hG hWh hP hJ hJW hJ.2.2 hJW.2.2.1
  have hWn : 2 * (chainModel J.whole).W.n ≤ W := walk_two_le hJW.2.2.1 hJ.2.2 hWh
  have e10 := kp 10 by_norm_num
  have e5 := kp 5 by_norm_num
  have e6 := kp 6 by_norm_num
  have e3 := kp 3 by_norm_num
  have e4 := kp 4 by_norm_num
  refine ⟨hsh, hBs, hXl, hG, hWh, hP, ?_, ?_, hOk1, hNF1, ?_, ?_, hNF2, ?_, hmd, hmwf, R.md0,
    R.hcd, ?_, ?_, ?_, R.hK, R.hO, R.hM, R.hgw, ?_, ?_, hWn, ?_, ?_, hOk2, ?_, ?_, ?_, R.htab,
    by omega, by_omega, by_omega, ?_, ?_, ?_, R.hTA⟩
  · rw [e10]; exact X.mono _ _ _ _ _ hA (X.local_ P c.nmem c₀.nmem _ _ ztfbu hX)
  · have hc := hXl P c.nmem c₀.nmem _ _ hm hX
    rw [e10, e5]
    exact hcap.trans_eq hc.symm
  · zukqx
  · zvnak; exact (hNW1.transport hm).mono hA
  · rw [e4]; exact (hNW2.transport hm).mono hA
  · obtain ⟨g1, g2, -, ⟨H', hd', hreg⟩, g5, g6⟩ := ctx20
    refine ⟨g1, g2, ?_, ⟨H, ?_, ?_⟩, g5, g6⟩
    · zupcd; exact hmwf.2 R.md0
    · zupcd; omega
    · zulyq
  · exact ctx21.transport (kp 21 by_norm_num) hm hA
  · exact ctxW.transport (kp 2 by_norm_num) hm hA
  · zupce
  · zupce; have := Nat.mul_le_mul_left κI (le_refl ztks)
    unfold κI at hroom; omega
  · refine ⟨H, ?_, st0S_keep hst (fun j hj => kp j by_omega) hm hA⟩
    zueml
    exact (junction_keep hJ hJW hm hA).1
  · zueml
    exact (junction_keep hJ hJW hm hA).2
  · zukqx
  · zukqy
  · zukqy
  · zvnak; exact (hNW1.transport hm).mono by_omega
  · rw [e4]; exact (hNW2.transport hm).mono by_omega
  · zvnlm
    calc Nat.clog 2 ztqbc
        ≤ Nat.clog 2 (4 * ztks) :=
          Nat.clog_mono_right _ by_omega
      _ ≤ Nat.clog 2 ztks + 2 := clog_four_mul _
      _ ≤ _ := by_omega

/-! ## Task I -/
theorem InitRes.keep200 {J : Merge.Junction} {c c₀ : Config}
    (R : InitRes P J c c₀) : ∀ j, j < 200 → c₀.nreg ztgc = c.nreg ztgc := fun j hj => by
  have h1 : ztujz := by unfold sw; omega
  zuglg
  exact R.keep ztgc ztsg ztiiy (Or.inl (by
    unfold sw; omega))
set_option maxRecDepth 20000 in
/-- **Task I: the initialisation** (`initE`, constant `κI = 40000`). -/
theorem initTask : InitTask := by
  refine ⟨initE, κI, fun sh Bs F X Ok hXl hBs hsh P W c hw hpre hroom => ?_⟩
  zumeo
  obtain ⟨hG, hWh, -, -, -, H₀, J₀, N₁₀, N₂₀, hJ₀, hP₀, -, -, hNW1, hNW2, hNF1, hNF2, -, -, -, -,
    hst⟩ := hpre'
  zuibi

  have hA1 := arcsTask J₀.left zta N₁₀ hP₀ hNF1
  have hA2 := arcsTask J₀.right zta N₂₀ hP₀ hNF2
  have hK1 : c.nmem ztwb = N₁₀.nChords := nN1.1
  have hK2 : c.nmem ztrl = N₂₀.nChords := nN2.1
  have ha1 : c.nmem ztyej = N₁₀.arcs.length := nN1.2.1
  have ha2 : c.nmem ztyei = N₂₀.arcs.length := nN2.2.1
  have h3 : c.nreg ztea + 1 < c.nreg ALLOC := nfWithin_lt' hNW1
  have h4 : c.nreg ztbz + 1 < c.nreg ALLOC := nfWithin_lt' hNW2
  zumes
  rw [hK1, hK2] at hroom'
  unfold κI at hroom'
  obtain ⟨c₀, k, ex, hk, fr, R⟩ := initE_exec hw hst hG hWh hP₀ h3 h4 (by
    omega)
  have hk' := hk
  rw [ha1, ha2] at hk'
  have hcl := clog_le_self' (N₁₀.arcs.length + N₂₀.arcs.length + 1)
  refine ⟨c₀, k, ex, ?_, fr, ex.wb_right, R.keep200, fun H J N₁ N₂ hpa => ?_⟩
  · rw [hK1, hK2]; unfold κI NF.nChords at *; omega
  · exact evEnv_of_init hXl hBs hsh hpre fr R hk hroom (junction_unique hpa.1 hJ₀) hpa
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
theorem list_ext_getD' {α : Type} {l l' : List α} (x : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i x = l'.getD i x) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by
    simp_all

/-- **The layout and validity determine the records**: two valid normal forms readable at the
same handle have the same chord, arc, region and sequence records. -/
theorem nf_recs_eq {m : ℕ → ℕ} {B : ℕ} {M M' : Model} {Q Q' : Polygon} {N N' : NF}
    (h : NFAt m B N) (h' : NFAt m B N') (hN : IsNF M Q N) (hN' : IsNF M' Q' N') :
    N.chords = N'.chords ∧ N.arcs = N'.arcs ∧ N.regions = N'.regions ∧ N.seq = N'.seq := by
  obtain ⟨c0, a0, r0, -, -, hc, ha, hr, hs, -⟩ := h
  obtain ⟨c0', a0', r0', -, -, hc', ha', hr', hs', -⟩ := h'
  have hA : N.arcs = N'.arcs := list_ext_getD' ztgp by_omega fun j hj => by
    zubz

  obtain ⟨-, -, -, reg, -, -, -, -, hS, -⟩ := hN
  obtain ⟨-, -, -, reg', -, -, -, -, hS', -⟩ := hN'
  have hl : N.seq.length = N.arcs.length := by rw [hS.1.length_eq, List.length_range]
  have hl' : N'.seq.length = N'.arcs.length := by rw [hS'.1.length_eq, List.length_range]
  refine ⟨list_ext_getD' ztrp by_omega fun i hi => ?_, hA,
    list_ext_getD' zthmd by_omega fun q hq => ?_,
    list_ext_getD' 0 by_omega fun t ht => by
      rw [← hs t ht, ← hs' t by_omega]⟩
  · zucl

  · zuye

    have harcs : ztkyv :=
      list_ext_getD' 0 by_omega fun t ht => by zunma
    have hchs : ztkyw :=
      list_ext_getD' 0 by_omega fun t ht => by zunmb
    zuil
variable {P : Polygon} (c : Config)
/-- **The outputs depend only on the chord, arc, region and sequence records** of the normal
form (the decomposition fields are not read). -/
theorem out_congr {J : Merge.Junction} {N N' : NF} {c : Config}
    (hc : N.chords = N'.chords) (ha : N.arcs = N'.arcs) (hr : N.regions = N'.regions)
    (hs : N.seq = N'.seq) : Out P J N c → Out P J N' c := by
  obtain ⟨c1, a, r, s, d, ro, l⟩ := N
  zudeb
  simp only at hc ha hr hs
  subst hc ha hr hs
  exact id

/-! ## The finalisation -/
set_option maxRecDepth 20000 in
theorem finCfg_val :
    (finCfg c).nreg ztcwm = c.nreg sB ∧ (finCfg c).nreg ztsn = c.nreg sC ∧
      (finCfg c).nreg ztfx = c.nreg lB ∧ (finCfg c).nreg ztex = c.nreg lC ∧
      (finCfg c).nreg ztps = c.nreg cTB ∧
      ∀ r, r ≠ sw 200 → r ≠ sw 201 → r ≠ sw 300 → r ≠ sw 301 → r ≠ sw 302 →
        (finCfg c).nreg r = c.nreg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_⟩
  all_goals simp only [finCfg, finL, regB, regI, Config.nreg_mk]
  all_goals try simp only [sB, sC, lB, lC, cTB, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other,
    Nat.reduceEqDiff, not_false_eq_true]
  zvmyk at h1 h2 h3 h4 h5
  simp_all
theorem fin_exec {W : ℕ} {c : Config} (hw : WordsBounded W c) :
    Exec P W fin c ztgiq 5 :=
  exec_regB finL hw by_trivial
theorem fin_frame : Frame ioBands c ztgiq 5 := by
  obtain ⟨-, -, -, -, -, ho⟩ := finCfg_val c
  refine frame_regs 5 (fun r hr => ho r ?_ ?_ ?_ ?_ ?_) rfl rfl rfl rfl <;> rintro rfl <;>
    exact hr (sw_io by_decide by_decide)

/-! ## Task Z -/
set_option maxRecDepth 20000 in
/-- **Task Z: the assembly.** -/
theorem asmTask : AsmTask := by
  rintro ⟨init, κI', hI⟩ ⟨run, κR, hR⟩
  refine ⟨fun sh => .seq init (.seq ztwcw fin), fun D => κI' + κR D + 5,
    fun sh Bs F X Ok hXl hBs hsh => ?_⟩
  zubgq
  zumeo
  obtain ⟨-, -, -, -, -, H₀, J₀, N₁₀, N₂₀, hpa₀⟩ := hpre'
  have hpa : PreAt X Ok P c H₀ J₀ N₁₀ N₂₀ := hpa₀
  set K := c.nmem ztwb + c.nmem ztrl + 1 with hKd
  set M := F ztbro + Nat.clog 2 K + 1 with hMd
  set D := rd c bSweep 6 with hDd
  have hM1 : ztrzw := by_omega
  have hcost : cost (fun D => κI' + κR D + 5) F P c = ztper * K * M := rfl
  zuexw
  have hIK : κI' * K ≤ κI' * K * M := Nat.le_mul_of_pos_right _ hM1
  have hRK : ztper * K * M = κI' * K * M + κR D * K * M + 5 * K * M := by_ring
  have hKM : 1 ≤ K * M := Nat.one_le_iff_ne_zero.2 zthbt
  have hKM5 : 5 ≤ 5 * K * M := by_grind
  obtain ⟨c₀, k₀, e₀, hk₀, fr₀, hw₀, hkeep, hEnv⟩ :=
    hI sh Bs F X Ok hXl hBs hsh P W c hw hpre (show c.nreg ALLOC + κI' * K ≤ W by omega)
  have hk₀' : k₀ ≤ κI' * K := hk₀
  have E := hEnv H₀ J₀ N₁₀ N₂₀ hpa
  have nN1 := hpa.2.2.2.2.1.nfAt
  have nN2 := hpa.2.2.2.2.2.1.nfAt
  have hK1 : N₁₀.nChords = c.nmem ztwb := nN1.1.symm
  have hK2 : N₂₀.nChords = c.nmem ztrl := nN2.1.symm
  have e5 : c₀.nreg ztbcb = rd c bSweep 5 := hkeep 5 by_norm_num
  have e6 : c₀.nreg ztbey = rd c bSweep 6 := hkeep 6 by_norm_num
  have hA₀ : c₀.nreg ALLOC ≤ c.nreg ALLOC + k₀ := fr₀.2.2.2.2.2.2
  have hA₀' : ztsey := fr₀.2.2.2.2.2.1
  obtain ⟨c', k₁, e₁, hk₁, hII, hIFr, hout⟩ := hR sh Bs F X Ok P W c₀ J₀ N₁₀ N₂₀ E hw₀ (by
    grind)
  rw [e5, e6, hK1, hK2] at hk₁
  have hk₁' : k₁ ≤ κR D * K * M := hk₁
  obtain ⟨hOut, s1, s2, l1, l2, t1, z1, z2⟩ := hout
  rw [hK1, hK2] at z1 z2
  rw [hK2] at t1
  obtain ⟨f200, f201, f300, f301, f302, fo⟩ := finCfg_val c'
  have hw' := e₁.wb_right
  have eTB : c'.nreg cTB = c₀.nreg cTB := hII.hin _ by_trivial
  refine ⟨finCfg c', k₀ + (k₁ + 5), .seq e₀ (.seq e₁ (fin_exec hw')), by_omega,
    ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun H J N₂ hJ hN₂ hNF₂ => ?_⟩, ?_⟩
  · rw [fo _ ztce ztce ztce
      ztce ztce, hII.hin _ ztze]
    grind
  · show c.nreg ALLOC ≤ (finCfg c').nreg ztcwm
    omega
  · show (finCfg c').nreg ztcwm + 5 * (finCfg c').nreg ztsn ≤ (finCfg c').nreg ALLOC
    rw [f200, f201, fo _ by_decide by_decide
      by_decide by_decide by_decide]
    exact s2
  · show c.nreg ALLOC ≤ (finCfg c').nreg ztfx
    omega
  · show (finCfg c').nreg ztfx + 7 * (finCfg c').nreg ztex ≤ (finCfg c').nreg ALLOC
    rw [f300, f301, fo _ by_decide by_decide
      by_decide by_decide by_decide]
    exact l2
  · show c.nreg ALLOC ≤ (finCfg c').nreg ztps
    rw [f302, eTB]; have := E.hT; omega
  · show (finCfg c').nreg ztps + 3 * ztzjq ≤ (finCfg c').nreg ALLOC
    rw [f302, fo _ by_decide by_decide
      by_decide by_decide by_decide]
    exact t1
  · show (finCfg c').nreg ztsn ≤ _
    omega
  · show (finCfg c').nreg ztex ≤ _
    omega
  · have hJJ : J₀ = J := junction_unique hpa.1 hJ
    subst hJJ
    obtain ⟨hc, ha, hr, hs⟩ := nf_recs_eq nN2 hN₂ hpa.2.2.2.2.2.2.2.1 hNF₂
    exact out_congr hc ha hr hs hOut
  · have f₁ : Frame ioBands c₀ c' k₁ := frame_of_irs hII hIFr
    exact frame_ioB ((fr₀ : Frame ioBands c c₀ k₀).trans (frame_ioB (f₁.trans (fin_frame c'))))
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
variable {n g x y : ℝ}
theorem off_eq_sub (hx0 : 0 ≤ x) (hyn : y < n) (h : off n g x ≤ off n g y) :
    off n x y = off n g y - off n g x := by
  zugir
theorem off_eq_sub' (hxn : x < n) (hy0 : 0 ≤ y) (h : off n g y < off n g x) :
    off n x y = off n g y - off n g x + n := by
  zugir
theorem sia_iff_off {n a b z : ℝ} (hab : a ≠ b) (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
    (hz0 : 0 ≤ z) (hzn : z < n) :
    sideInArc a b z ↔ 0 < off n a z ∧ off n a z < off n a b := by
  unfold sideInArc off
  grind

/-- **The closed arc after a point of it.** -/
theorem cIn_of_off {n a b x y : ℝ} (han : a < n) (hb0 : 0 ≤ b) (hbn : b < n)
    (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n) (hab : a ≠ b)
    (hx : sideInArc a b x ∨ a = x) (hpos : 0 < off n x y) (hle : off n x y ≤ off n x b) :
    CIn a b y := by
  have hxb : off n a x < off n a b := by
    rcases hx with hx | rfl
    · exact ((sia_iff_off hab han hb0 hbn hx0 hxn).1 hx).2
    · rw [off_self n a]
      grind
  have e1 := off_eq_sub hx0 hbn hxb.le
  have hay : off n a y = off n a x + off n x y := by
    zugir
  by_cases hyb : y = b
  · tauto
  · left
    rw [sia_iff_off hab han hb0 hbn hy0 hyn]
    have hax := off_nonneg hx0 han
    refine ⟨by_linarith, lt_of_le_of_ne by_linarith fun h => hyb ?_⟩
    zugis
section Gap
variable {J : Merge.Junction}
theorem win_n_eq : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n J.whole
theorem win_n₁_eq : (chainModel J.left).W.n = 2 * J.left.m + 7 := cm_n J.left
theorem win_lδ_cases : lδ J = 0 ∨ lδ J = 7 := by unfold lδ; grind
theorem win_Lst_lt : Lst J < (chainModel J.whole).W.n := by
  rw [Lst_rlen, win_n_eq]
  zucz
  have := J.one_le_m₁
  unfold rlen; grind
theorem win_gW_lt : gW J < (chainModel J.whole).W.n := by
  have := tpos_lt J.whole J.m₁
  zupcz; unfold gW; omega
theorem win_E₁_eq : E₁ J = (chainModel J.whole).W.n - Lst J + lδ J := rfl

/-- **The facts of the left gap** (case G). -/
theorem gap_facts (hP : J.P.Simple) (hδ : 0 < lδ J) :
    VNotTop J ∧ lδ J = 7 ∧ lL1 J = 2 * J.m₁ - tpos J.left J.m₁ ∧ b₁ J = 6 + tpos J.left J.m₁ ∧
      0 < tpos J.left J.m₁ ∧ tpos J.left J.m₁ < 2 * J.m₁ ∧
      Lst J + lL1 J < (chainModel J.whole).W.n ∧
      (gW J + (Lst J + lL1 J)) % (chainModel J.whole).W.n =
        6 + tpos J.whole ztbv + lL1 J ∧
      6 + tpos J.whole ztbv + lL1 J < (chainModel J.whole).W.n := by
  have hv : VNotTop J := by
    by_contra h; have := (nvt_left J hP h).2.1; omega
  zueau
  have hb : ztcfz := by
    unfold b₁; rw [ite_eq_right (fun h => (caseB_facts J h).1 hv)]
  have hlOff : ztflb := by rw [lOff_of_vnt J hv, Lst_rlen]
  have hlen : ztckb := by
    zupcc; exact rlen_add_llen J hv
  have hL := lL1_add_lL2 J
  have hA : ztxzy := by
    intro h; unfold lδ at hδ; simp_all
  have hτ := tpos_lt J.whole ztbv
  have hn := win_n_eq (J := J)
  have hlt : 6 + tpos J.whole ztbv + lL1 J < (chainModel J.whole).W.n := by
    omega
  refine ⟨hv, h7, hl1, hb, hτp, hτl, by_omega, ?_, hlt⟩
  rw [← add_assoc, ← Nat.mod_add_mod, ← hlOff, gL_eq, Nat.mod_eq_of_lt hlt]

/-- `Lst + ψ d < n` on the `C₁` part. -/
theorem Lst_ψ_lt (hP : J.P.Simple) {d : ℕ} (hd : d < E₁ J) :
    Lst J + ψ J d < (chainModel J.whole).W.n := by
  have hL := win_Lst_lt (J := J)
  rw [win_E₁_eq] at hd
  unfold ψ
  zupi
  · have := (gap_facts hP h1.1).2.2.2.2.2.2.1; omega
  · omega
  · rcases win_lδ_cases (J := J) with h | h
    · omega
    · have := (gap_facts hP by_omega).2.2.2.2.2.2.1
      omega
end Gap

/-! ## The key read in the walk of `C₁` -/
section Key
variable {J : Merge.Junction}
theorem dOf_add_mod {n g d : ℕ} (hg : g < n) (hd : d < n) : dOf n g ztxym = d :=
  add_mod_inj (dOf_lt by_omega g _) hd (add_dOf hg ztcv)

/-- The part offset `D - Lst` of the key edge `e` (as the RAM computes it). -/
noncomputable def kr (J : Merge.Junction) (e : ℕ) : ℕ :=
  dOf (chainModel J.whole).W.n ztwks e

/-- The `b₁`-offset of a part offset (beyond the gap if at or after its start). -/
noncomputable def d0Of (J : Merge.Junction) (r : ℕ) : ℕ := if lL1 J ≤ r then r + lδ J else r

/-- The `b₁`-offset of the key edge. -/
noncomputable def kd (J : Merge.Junction) (e : ℕ) : ℕ := d0Of J (kr J e)

/-- The edge of the walk of `C₁` of the key edge. -/
noncomputable def ke₁ (J : Merge.Junction) (e : ℕ) : ℕ := (b₁ J + kd J e) % (chainModel J.left).W.n
theorem win_offK_eq {P : Polygon} {e h : ℕ} (he : e < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztcq) :
    offK P J e h = (dOf (chainModel J.whole).W.n ztead e : ℝ) +
      (chainModel J.whole).param zta ztcq := by
  unfold offK
  exact off_key' win_gW_lt he hpp.1 hpp.2.1

/-- **The key in the walk of `C₁`.** -/
theorem key_map {P : Polygon} (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) :
    offK P J e h = (Lst J : ℝ) + (kr J e : ℝ) + (chainModel J.whole).param zta ztcq ∧
      kd J e < E₁ J ∧ (0 < lδ J → kd J e < lL1 J ∨ lL1 J + lδ J ≤ kd J e) ∧
      ψ J ztcvy = kr J e ∧ mEdge J ztcvy = e ∧ MValid J ztcvy ztcn ∧
      (chainModel J.left).param zta ztcjv = (chainModel J.whole).param zta ztcq ∧
      (∀ s, sidePt (chainModel J.whole).W e s = sidePt (chainModel J.left).W (ke₁ J e) s) := by
  obtain ⟨he, hpp, -⟩ := hpw
  have hg := win_gW_lt (J := J)
  have hLn := win_Lst_lt (J := J)
  zudbn
  set D := dOf n ztead e with hD
  have hDn : D < n := dOf_lt by_omega _ _
  have hoff := win_offK_eq he hpp
  rw [← hD] at hoff
  have hLD : ztull := by
    have h1 : ztlwv := by rw [hoff] at hL; linarith [hpp.2.1]
    exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast h1)
  have hr : kr J e = D - Lst J := by
    refine add_mod_inj (g := ztit % n) (dOf_lt by_omega _ _) by_omega ?_
    unfold kr
    rw [← hn, add_dOf ztcv he, Nat.mod_add_mod,
      show gW J + Lst J + zthqv = gW J + D by omega, hD, add_dOf hg he]
  have hE : kd J e < E₁ J := by
    rw [win_E₁_eq]; unfold kd d0Of; grind
  have hgap : 0 < lδ J → kd J e < lL1 J ∨ lL1 J + lδ J ≤ kd J e := by
    intro _; unfold kd d0Of; grind
  have hψ : ψ J ztcvy = kr J e := by
    unfold kd d0Of ψ; grind
  have hm : mEdge J ztcvy = e := by
    unfold mEdge; rw [hψ, hr, ← hn, show Lst J + zthqv = D by omega, hD, add_dOf hg he]
  have hv : MValid J ztcvy ztcn := by
    refine ⟨hE, fun h => ?_, fun h => ?_, by_simp_all⟩
    · omega
    omega
  refine ⟨?_, hE, hgap, hψ, hm, hv, ?_, fun s => ?_⟩
  · simp_all
  · have := param_corr hP hv by_norm_num zta h
    zvmwi at this; exact this.symm
  · have := edge_corr hP hv by_norm_num s
    zvmwi at this; tauto

/-- The key of the key position in the walk of `C₁` has `b₁`-offset `kd + t₀`. -/
theorem key₁_off {P : Polygon} (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) :
    off (chainModel J.left).W.n ztbsn ztymy =
      (kd J e : ℝ) + (chainModel J.whole).param zta ztcq := by
  obtain ⟨-, hE, -, -, -, -, hpar, -⟩ := key_map hP hpw hL
  have hpp := hpw.2.1
  zuhqn
  zubi
  zueyf
  exact off_key b₁_lt (lt_of_lt_of_le hE ztjip) hpp.1 hpp.2.1
end Key

/-! ## Monotonicity of the part offsets -/
section Mono
variable {J : Merge.Junction}

/-- Gap property of a `b₁`-offset: not inside the gap and not at its start. -/
def GapOut (J : Merge.Junction) (d : ℕ) : Prop := 0 < lδ J → d < lL1 J ∨ lL1 J + lδ J ≤ d
variable {d d' : ℕ}
theorem ψ_mono (h : d ≤ d') : ψ J d ≤ ψ J d' := by
  zudwk
theorem ψ_step (h : d < d') (hd : GapOut J d) : ψ J d + 1 ≤ ψ J d' := by
  unfold GapOut at hd; unfold ψ; grind

/-- **Beyond the key**: a valid offset whose image is beyond the image of the key lies beyond it
in the walk of `C₁`. -/
theorem lex_lt {d₀ d : ℕ} {t₀ t : ℝ} (hd₀ : GapOut J d₀)
    (hv2 : ¬ ztrv) (hv3 : ¬ ztbft)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ < 1)
    (h : (ψ J d₀ : ℝ) + t₀ < ψ J d + t) : (d₀ : ℝ) + t₀ < d + t := by
  zux

  have hdd : d ≤ d₀ := by
    have : (d : ℝ) < d₀ + 1 := by_linarith
    zulfy
  zujdo
  · grind
  · by_cases hs : 0 < lδ J ∧ d = lL1 J
    · have t0 : ztbhh := by_simp_all
      have : ψ J d ≤ ψ J d₀ := ψ_mono hlt.le
      have : (ψ J d : ℝ) ≤ ψ J d₀ := by_simp_all
      grind
    · have hg : GapOut J d := fun hδ => by
        omega
      have := ψ_step hlt hg
      have : (ψ J d : ℝ) + 1 ≤ ψ J d₀ := by exact_mod_cast this
      linarith

/-- **Up to the window end**: an offset whose image is at most the image of `dE + tE` lies at
most there in the walk of `C₁`. -/
theorem lex_le {d dE : ℕ} {t tE : ℝ} (hdE : GapOut J dE) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (htE0 : 0 ≤ tE) (htE1 : tE < 1) (h : (ψ J d : ℝ) + t ≤ ψ J dE + tE) :
    (d : ℝ) + t ≤ dE + tE := by
  zux

  have hdd : dE ≤ d := by
    have : (dE : ℝ) < d + 1 := by_linarith
    zulfy
  zujdo
  · grind
  · have := ψ_step hlt hdE
    have : (ψ J dE : ℝ) + 1 ≤ ψ J d := by exact_mod_cast this
    linarith

/-- **Up to the gap start.** -/
theorem lex_le_gap {d : ℕ} {t : ℝ} (hδ : 0 < lδ J)
    (hv2 : ¬ ztrv) (hv3 : ¬ ztbft)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (h : (ψ J d : ℝ) + t ≤ lL1 J) :
    (d : ℝ) + t ≤ lL1 J ∨ (d = lL1 J + lδ J ∧ t = 0) := by
  by_cases h1 : d < lL1 J
  · left
    have : ((d + 1 : ℕ) : ℝ) ≤ lL1 J := by exact_mod_cast h1
    grind
  · by_cases h2 : d = lL1 J
    · simp_all
    · right
      have h3 : lL1 J + lδ J ≤ d := by
        omega
      have hψ : ψ J d = d - lδ J := by
        zudwk
      rw [hψ] at h
      have h4 : lL1 J ≤ d - lδ J := by_omega
      have h5 : (lL1 J : ℝ) ≤ ((d - lδ J : ℕ) : ℝ) := by_simp_all
      have t0 : ztbhh := by_linarith
      refine ⟨?_, t0⟩
      subst t0
      have : ((d - lδ J : ℕ) : ℝ) ≤ lL1 J := by_linarith
      have : d - lδ J ≤ lL1 J := by_simp_all
      omega
end Mono

/-- **The closed arc beyond a point of it**, in offsets from a base `g`: a point `y` beyond `x`
and not beyond the end `b` (or anywhere beyond `x` if the arc wraps past `g`). -/
theorem cIn_of_U {n g a b x y : ℝ} (hg0 : 0 ≤ g) (hgn : g < n) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n) (hab : a ≠ b)
    (hx : sideInArc a b x ∨ a = x) (hxy : off n g x < off n g y)
    (hyb : off n g y ≤ off n g b ∨ off n g b < off n g x) : CIn a b y := by
  have e1 := off_eq_sub hx0 hyn hxy.le
  refine cIn_of_off han hb0 hbn hx0 hxn hy0 hyn hab hx by_linarith ?_
  rcases hyb with h | h
  · rw [e1, off_eq_sub hx0 hbn by_linarith]; linarith
  · rw [e1, off_eq_sub' hxn hb0 h]
    have := off_lt hyn hg0
    have := off_nonneg hb0 hgn
    linarith

/-! ## The arc after the key -/
section Arc
variable {C : Chain} {Q : Polygon} {N : NF}
theorem not_sia_end (a b : ℝ) : ¬ sideInArc a b b := by
  zudcn

/-- **The arc of a located key, if the key is not its end.** -/
theorem arc_of_loc {o : ℕ} {x : ℝ}
    (hne : (N.F ztc Q).Nonempty)
    (hl1 : ¬ (chainModel C).IsCut ztwjh x →
      N.F ztc Q = ∅ ∨
        sideInArc ztzcw ztzct x)
    (hl2 : (chainModel C).IsCut ztwjh x →
      OracleQ.sk ztc Q N o = x ∨ OracleQ.ek ztc Q N o = x)
    (he : OracleQ.ek ztc Q N o ≠ x) :
    sideInArc ztzcw ztzct x ∨
      OracleQ.sk ztc Q N o = x := by
  by_cases hc : (chainModel C).IsCut ztwjh x
  · simp_all
  · zuevl
    · simp_all
    simp_all

/-- **The successor arc starts at the key** if the located arc ends there. -/
theorem arc_of_loc' (hP : C.P.Simple) (hN : IsNF ztc Q N) {o : ℕ}
    (ho : o < N.arcs.length) {x : ℝ} (hne : (N.F ztc Q).Nonempty)
    (he : OracleQ.ek ztc Q N o = x) :
    OracleQ.sk ztc Q N (OracleQ.succP N.arcs.length o) = x := by
  rw [← OracleQ.ek_eq_sk_succ hN hP hne ho, he]
end Arc

/-! ## The window ends -/
section End
variable {J : Merge.Junction} {P : Polygon}
theorem win_pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge ztbyt := rfl
theorem mvalid_half {d : ℕ} (hd : d < E₁ J) (hg : GapOut J d) : MValid J d ztcn := by
  refine ⟨hd, fun h => ?_, fun h => ?_, by_simp_all⟩
  · zubya
  · zubya

/-- **The window end at an arc end** of `N₁`: its image `(mEdge dE, hE)` in the walk of `C`. -/
theorem wend_map (hP : J.P.Simple) {dE eE hE : ℕ} (hdE : dE < E₁ J) (hg : GapOut J dE)
    (heE : ztljz % (chainModel J.left).W.n = eE)
    (hpp : ProperPos ztbw zta P.n ztonk)
    (hy : |((chainModel J.left).pos zta ⟨eE, hE⟩).2| < J.left.radius) :
    PosW P J zttta hE ∧ offK P J zttta hE =
      (Lst J : ℝ) + ψ J dE + (chainModel J.left).param zta ztonk := by
  have hv := mvalid_half hdE hg
  have hpar := param_corr hP hv by_norm_num zta hE
  rw [heE] at hpar
  have hpt := edge_corr hP hv by_norm_num ((chainModel J.left).param zta ztonk)
  rw [heE] at hpt
  have hm : mEdge J dE < (chainModel J.whole).W.n := by
    unfold mEdge; exact Nat.mod_lt _ (by have := win_gW_lt (J := J); omega)
  have hpp' : ProperPos ztbm zta P.n ⟨mEdge J dE, hE⟩ := by
    rw [ProperPos, hpar]; tauto
  refine ⟨posW_of_inner hm hpp' ?_, ?_⟩
  · rw [win_pos_eq_sidePt, hpar]
    zubi
    zubil
    zulfn
  · rw [win_offK_eq hm hpp', hpar]
    unfold mEdge
    rw [dOf_add_mod win_gW_lt (Lst_ψ_lt hP hdE)]
    simp
theorem win_pred_mod {n b d e : ℕ} (hb : b < n) (hd : d < n) (h1 : 1 ≤ d) (he : zthdo % n = e)
    (he0 : e ≠ 0) : ztzvc % n + 1 = e := by
  zuhsh
  · zujhf
    zupd
  · zugty
    zuzu

/-- **The cut witness of a window end at an arc end.** -/
theorem wend_cut {dE eE : ℕ} {tE : ℝ} {G : Set ztf} (hdE : dE < E₁ J)
    (hheE : ztljz % (chainModel J.left).W.n = eE) (htE0 : 0 ≤ tE) (htE1 : tE ≤ 1)
    (hcut : (chainModel J.left).IsCut G ((eE : ℝ) + tE))
    (hg : GapOut J dE)
    (h0 : tE = 0 → 1 ≤ dE ∧ eE ≠ 0 ∧ (0 < lδ J → dE < lL1 J ∨ lL1 J + lδ J < dE))
    (hn₁ : dE < (chainModel J.left).W.n) :
    ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (Lst J : ℝ) + ψ J dE + tE = (Lst J : ℝ) + ψ J d + t ∧
      (chainModel J.left).IsCut G ztwms := by
  rcases lt_or_eq_of_le htE0 with hpos | hz
  · refine ⟨dE, tE, ⟨hdE, fun h => ?_, fun h => ?_, by_grind⟩, htE0, htE1,
      rfl, ?_⟩
    · zubya
    · zubya
    simp_all
  · obtain ⟨h1, he0, hg'⟩ := h0 hz.symm
    refine ⟨dE - 1, 1, ⟨by_omega, fun h => ?_, fun h => ?_, by_grind⟩,
      zero_le_one, le_rfl, ?_, ?_⟩
    · omega
    · omega
    · have : ψ J (dE - 1) + 1 = ψ J dE := by
        zudwk
      rw [← hz, ← this]; grind
    · rw [← hz, add_zero] at hcut
      have := win_pred_mod b₁_lt hn₁ h1 hheE he0
      zvnnr at hcut; grind

/-- **The window end at the gap start.** -/
theorem wend_gap (hP : J.P.Simple) (hδ : 0 < lδ J) :
    PosW P J (ztbalm % (chainModel J.whole).W.n) 0 ∧
      offK P J (ztbalm %
        (chainModel J.whole).W.n) 0 = (Lst J : ℝ) + lL1 J := by
  obtain ⟨-, -, -, -, -, -, hlt, heq, hlt'⟩ := gap_facts hP hδ
  rw [Nat.mod_add_mod, add_assoc, heq]
  have hpp : ProperPos ztbm zta P.n
      ⟨6 + tpos J.whole ztbv + lL1 J, 0⟩ :=
    ⟨le_refl _, by_simp, Nat.zero_le _⟩
  refine ⟨⟨hlt', hpp, by_grind⟩, ?_⟩
  rw [win_offK_eq hlt' hpp, ← heq, dOf_add_mod win_gW_lt hlt]
  simp

/-- **The two ends of the gap are the same point** (the copies of the top of `C₁`). -/
theorem gap_pt (hP : J.P.Simple) (hδ : 0 < lδ J) :
    sidePt (chainModel J.left).W ((b₁ J + ztjzy) % (chainModel J.left).W.n) 0 =
      sidePt (chainModel J.left).W ((b₁ J + lL1 J) % (chainModel J.left).W.n) 0 := by
  obtain ⟨-, h7, hl1, hb, hτp, hτl, -⟩ := gap_facts hP hδ
  have hn₁ := win_n₁_eq (J := J)
  zufd
  rw [hb, hl1, h7, hn₁]
  rw [show 6 + tpos J.left J.m₁ + ztdki = 6 + ztcsh by
      omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_simp_all,
    show 6 + tpos J.left J.m₁ + ztgyg = 2 * J.left.m + 6 by omega,
    Nat.mod_eq_of_lt by_simp_all]
  obtain ⟨a, b⟩ := sidePt_top_copies J.left
  simp_all
end End

/-! ## The gathered arcs -/
section Gath

/-- The arc list `l` is stored at `A` (normalised ends). -/
def Gath (M : Model) (Q : Polygon) (N : NF) (m : ℕ → ℕ) (A : ℕ) (l : List ℕ) : Prop :=
  ∀ k, k < l.length → ShotList.arcAt m A k = nArc M Q N ztcak
variable {M : Model}
theorem arc_mem_region {Q : Polygon} {N : NF} (hN : IsNF M Q N) {j : ℕ}
    (hj : j < N.arcs.length) : (N.arc j).reg < N.nRegions ∧ j ∈ (N.region (N.arc j).reg).arcs := by
  obtain ⟨-, -, -, reg, -, -, hA, -⟩ := hN
  have h1 := (hA.1 j hj).1
  exact ⟨h1, ((hA.2.2.2 _ h1 j).2 by_omega)⟩

/-- **A point of a gathered arc is in `loSet`.** -/
theorem mem_loSet {Q : Polygon} {N : NF} {n' : ℕ} {m : ℕ → ℕ}
    {A : ℕ} {l : List ℕ} (hg : Gath M Q N m A l) (hl : ∀ a ∈ l, a < N.arcs.length)
    (hpp : ∀ j, j < N.arcs.length → ProperPos M Q n' (N.arc j).s ∧ ProperPos M Q n' (N.arc j).e)
    {a : ℕ} (ha : a ∈ l) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hc : CIn (M.key Q (N.arc a).s) (M.key Q (N.arc a).e) ztk) :
    sidePt M.W p t ∈ ShotList.loSet M Q m A l.length [] := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
  have hkd : l.getD k 0 = l[k] := by_simp_all
  have hal := hl _ ha
  obtain ⟨hs, he⟩ := hpp _ hal
  refine ⟨p, t, hp, ht0, ht1, ztcyc, by_simp_all, rfl⟩
  rw [hg k hk, hkd]
  zujqr
  zubi
  rw [(Restore.normOf_facts hs).2.2.2.1, (Restore.normOf_facts he).2.2.2.1]
  exact hc
end Gath

/-! ## Coverage -/
section Cover
variable {J : Merge.Junction} {P : Polygon} {N₁ : NF}
theorem key₁_range {M : Model} {Q : Polygon} {n' : ℕ} {x : WPos} (hx : x.edge < M.W.n)
    (hpp : ProperPos M Q n' x) : 0 ≤ M.key Q x ∧ M.key Q x < M.W.n := by
  zuhqn
  have h1 := hpp.1; have h2 := hpp.2.1
  have : ((x.edge + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hx
  grind

/-- **Coverage by the arc after the key.** -/
theorem cover_arc (hP : J.P.Simple) (hN : IsNF ztbw zta N₁)
    {m : ℕ → ℕ} {A : ℕ} {l : List ℕ} (hg : Gath ztbw zta N₁ m A l)
    (hl : ∀ a ∈ l, a < N₁.arcs.length) {o : ℕ} (ho : o < N₁.arcs.length)
    (hol : OracleQ.sj N₁ o ∈ l) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < (chainModel J.left).W.n)
    (hab : OracleQ.sk ztbw zta N₁ o ≠ OracleQ.ek ztbw zta N₁ o)
    (hin : sideInArc (OracleQ.sk ztbw zta N₁ o)
        ztxvt x ∨
      OracleQ.sk ztbw zta N₁ o = x)
    {d : ℕ} {t : ℝ} (hd : d < E₁ J) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hlt : off (chainModel J.left).W.n ztbsn x < d + t)
    (hup : (d : ℝ) + t ≤ off (chainModel J.left).W.n ztbsn
        ztxvt ∨
      off (chainModel J.left).W.n ztbsn ztxvt <
        off (chainModel J.left).W.n ztbsn x) :
    sidePt (chainModel J.left).W ztwjw t ∈
      ShotList.loSet ztbw zta m A l.length [] := by
  set M := chainModel J.left with hM
  have hn₁ : ztbiy := by rw [hM, win_n₁_eq]; omega
  have hdn := lt_of_lt_of_le hd ztjip
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M zta (Qof P).n (N₁.arc j).s ∧
      ProperPos M zta (Qof P).n (N₁.arc j).e := fun j hj => by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, h⟩ := hN; simp_all
  obtain ⟨reg, -, -, harc⟩ := OracleQ.isArc_sj hN ho
  obtain ⟨hs0, hsn, he0, hen, -⟩ := harc
  have hp := Nat.mod_lt zthm hn₁
  have hy : off M.W.n _ ((zthm % M.W.n : ℕ) + t) = d + t :=
    off_key b₁_lt hdn ht0 ht1
  have hyr : 0 ≤ ((zthm % M.W.n : ℕ) : ℝ) + t ∧ ((zthm % M.W.n : ℕ) : ℝ) + t < M.W.n := by
    have : ((zthm % M.W.n + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hp
    grind
  have hb0 : (0 : ℝ) ≤ b₁ J := Nat.cast_nonneg _
  have hbn : (b₁ J : ℝ) < M.W.n := by exact_mod_cast b₁_lt
  refine mem_loSet hg hl hpp hol hp ht0 ht1.le ?_
  refine cIn_of_U hb0 hbn hsn he0 hen hx0 hxn hyr.1 hyr.2 hab hin by_simp_all ?_
  rw [hy]; tauto
end Cover
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
def wD : ℕ := sw 3000
def wE1 : ℕ := sw 3001
def wO : ℕ := sw 3002
def wT : ℕ := sw 3003
def wA : ℕ := sw 3004
def wR : ℕ := sw 3005
def wEE : ℕ := sw 3006
def wEH : ℕ := sw 3007
def wL : ℕ := sw 3008
def wC : ℕ := sw 3010
def wCh : ℕ := sw 3012
def wDE : ℕ := sw 3013
def wPs : ℕ := sw 3014

/-! ## Single instructions -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- One register update. -/
def win_Upd (c c' : Config) (r v : ℕ) : Prop :=
  c'.nreg r = v ∧ ztbcc ∧ c'.nmem = c.nmem
theorem win_upd_of_eq {c' : Config} {r v : ℕ} (h : c' = { c with nreg := upd c.nreg r v }) :
    win_Upd c c' r v := by
  subst h; exact ⟨by_simp, by_simp_all, rfl⟩
variable {r a b : ℕ} {J : Merge.Junction} (m f : ℕ → ℕ) {q : ℕ}
theorem win_irs_add (hI : IInv W c₀ c) (hr : IScr r) (hw : c.nreg a + c.nreg b ≤ W) :
    IRS P W c₀ ztder c 1 (fun c' => win_Upd c c' r ztqio) :=
  (IRS.reg hI hr (Exec.addN hI.hw r a b hw)).mono le_rfl fun _ h => win_upd_of_eq h
theorem win_irs_sub (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ ztgwy c 1 (fun c' => win_Upd c c' r (c.nreg a - c.nreg b)) :=
  (IRS.reg hI hr ztjin).mono le_rfl fun _ h => win_upd_of_eq h
theorem win_irs_copy {r a : ℕ} (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ ztdsf c 1 (fun c' => win_Upd c c' r ztcux) :=
  (IRS.reg hI hr zthqx).mono le_rfl fun _ h => win_upd_of_eq h
theorem win_irs_load {r a : ℕ} (hI : IInv W c₀ c) (hr : IScr r) :
    IRS P W c₀ ztowa c 1 (fun c' => win_Upd c c' r (c.nmem ztcux)) :=
  (IRS.reg hI hr ztlel).mono le_rfl fun _ h => win_upd_of_eq h
theorem win_irs_const' {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r) (hv : v ≤ W) :
    IRS P W c₀ ztcyq c 1 (fun c' => win_Upd c c' r v) :=
  (IRS.reg hI hr ztjik).mono le_rfl fun _ h => win_upd_of_eq h
theorem win_condSub_irs {dst a b : ℕ} (hI : IInv W c₀ c) (hd : IScr dst) :
    IRS P W c₀ ztlme c 3 (fun c' =>
      win_Upd c c' dst ztdhq) := by
  obtain ⟨c', k, hk, ex, v, o⟩ := condSub_exec (P := P) hI.hw dst a b
  refine (irs_of_out hI ex hk o by_simp_all).mono le_rfl ?_
  rintro _ rfl
  exact ⟨v, fun q hq => o.1 q by_simp_all, o.2.2.1⟩

/-- The reduction of `x < 2 n` modulo `n`. -/
theorem win_condSub_mod {x n : ℕ} (h : x < 2 * n) :
    ztkws = x % n := by
  zulsr
  · rw [Nat.mod_eq_of_lt h']
  · zul
theorem win_sw_ne {i j : ℕ} (h : i ≠ j) : sw i ≠ sw j := by unfold sw; omega

/-- Distinct registers. -/
macro "rne" : tactic => `(tactic| (simp only [wD, wE1, wO, wT, wA, wR, wEE, wEH, wL, wC, wCh,
  wDE, wPs, cGL, cNW, cLL, cLD, cLE, cB1, cN1, cE1, kE, kH, K0, K1, K2, K3, K4, K5, K6, wE, wH, wX,
  wGB, wGK, gL, gC, gNF, gBase, gK, ALLOC, MD₁, CD₁, TBR, TLR, sw, ne_eq]; omega))

/-! ## The program -/

/-- The key read in the walk of `C₁`: `wD := kd`, `wE1 := ke₁`. -/
def wKeyS : Stmt :=
  .seq (.instr (.addN wD kE cNW)) (.seq (.instr (.subN wD wD cGL)) (.seq (condSub wD wD cNW)
    (.seq ztifm
      (.seq (.instr (.addN wE1 cB1 wD)) (condSub wE1 wE1 cN1)))))
set_option maxHeartbeats 4000000 in
/-- **The key in the walk of `C₁`.** -/
theorem wKeyS_irs (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (he : c.nreg kE < (chainModel J.whole).W.n) (hP : J.P.Simple)
    (hWn : 2 * (chainModel J.whole).W.n ≤ W) (hkdE : kd J ztwe < E₁ J) :
    IRS P W c₀ wKeyS c 12 (fun c' => c'.nreg wD = kd J ztwe ∧
      c'.nreg wE1 = ke₁ J ztwe ∧ (∀ r, r ≠ wD → r ≠ wE1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  zuclu
  zudbn
  zubae
  zucmj
  have hn7 : 7 ≤ n := by rw [hn, win_n_eq]; omega
  have hgl : ztit % n < n := Nat.mod_lt _ hn0
  have hn₁n : n₁ ≤ n := by
    rw [hn₁, hn, win_n₁_eq, win_n_eq]; simp
  have sD : IScr wD := iscr_sw' by_norm_num by_norm_num
  have wsE : IScr wE1 := iscr_sw' by_norm_num by_norm_num
  have nDE : wE1 ≠ wD := win_sw_ne by_norm_num
  have hkr : kr J ztwe < n := dOf_lt hn0 _ _
  have hkd : kd J _ < n₁ := lt_of_lt_of_le hkdE ztjip
  unfold wKeyS
  refine IRS.seq (K₂ := 11) (win_irs_add hI sD (by rw [hM.nw]; omega)) ?_ |>.mono
    by_norm_num ztb
  zukz
  refine IRS.seq (K₂ := 10) (win_irs_sub hI₁ sD) ?_ |>.mono by_norm_num ztb
  zula
  rw [v1, o1 _ (by rne), hM.gl, hM.nw] at v2
  refine IRS.seq (K₂ := 7) (win_condSub_irs hI₂ sD) ?_ |>.mono by_norm_num ztb
  zulb
  rw [v2, o2 _ (by rne), o1 _ (by rne), hM.nw,
    win_condSub_mod by_omega] at v3
  have vr : c₃.nreg wD = kr J _ := v3
  zulis
  -- beyond the gap
  have step : IRS P W c₀ ztifm c₃ 3
      (fun c' => win_Upd c₃ c' wD (kd J ztwe)) := by
    by_cases h : c₃.nreg wD < c₃.nreg cLL
    · refine (IRS.ifT h (IRS.skip (K := 1) hI₃ ztdqf)).mono by_norm_num ztb
      rw [vr]; rw [vr, hM₃.ll] at h; unfold kd d0Of; grind
    · refine (IRS.ifF h (win_irs_add hI₃ sD ?_)).mono by_norm_num ?_
      · rw [vr, hM₃.ld]; rcases win_lδ_cases with h' | h' <;> zvmxl <;> omega
      · zubyi
        refine ztrab
        rw [a, vr, hM₃.ld]; rw [vr, hM₃.ll] at h; unfold kd d0Of; grind
  refine IRS.seq (K₂ := 4) step ?_ |>.mono by_norm_num ztb
  zucei
  have hM₄ := hM₀.fix hI₄
  refine IRS.seq (K₂ := 3) (win_irs_add hI₄ wsE (by rw [v4, hM₄.b1]; have := b₁_lt (J := J); omega)) ?_
    |>.mono by_norm_num (fun _ h => h)
  rintro c₅ hI₅ - - ⟨v5, o5, m5⟩
  rw [v4, hM₄.b1] at v5
  refine (win_condSub_irs hI₅ wsE).mono le_rfl ?_
  rintro c₆ ⟨v6, o6, m6⟩
  have hM₅ := hM₀.fix hI₅
  rw [v5, hM₅.n1, win_condSub_mod (by have := b₁_lt (J := J); omega)] at v6
  have fr : ∀ r, r ≠ wD → r ≠ wE1 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    rw [o6 r h2, o5 r h2, o4 r h1, o3 r h1, o2 r h1, o1 r h1]
  refine ⟨?_, v6, fr, by_grind⟩
  rw [o6 _ (by rne), o5 _ (by rne), v4]

/-- Load the arc at the spine position `wO`: index `wA`, region `wR`, end `wEE, wEH`. -/
def arcL : List Instr :=
  [.addN wT ztea K6, .loadN wT wT, .addN wT wT wO, .loadN wA wT,
    .addN wT ztea K4, .loadN wT wT, .addN wT wT wA, .addN wT wT wA, .addN wT wT wA,
    .addN wT wT wA, .addN wT wT wA, .loadN wR wT, .addN wT wT K3, .loadN wEE wT, .addN wT wT K1,
    .loadN wEH wT]
def arcS : Stmt := block arcL
theorem arcL_val (k6 : f K6 = 6) (k4 : f K4 = 4) (k3 : f K3 = 3) (k1 : f K1 = 1) :
    regB m arcL f wA = m ztwpk ∧
    regB m arcL f wR = m (m ztxea + 5 * m ztwpk) ∧
    regB m arcL f wEE = m (m ztxea + 5 * m ztwpk + 3) ∧
    regB m arcL f wEH = m (m ztxea + 5 * m ztwpk + 4) := by
  zucan

  simp only [arcL, regB, regI, upd, wT, wA, wR, wEE, wEH, wO, K6, K4, K3, K1, sw]
  grind
theorem arcL_other (h1 : q ≠ wT) (h2 : q ≠ wA) (h3 : q ≠ wR)
    (h4 : q ≠ wEE) (h5 : q ≠ wEH) : regB m arcL f q = f q :=
  regB_other m arcL f (fun i hi => by
    simp only [arcL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all)
theorem arcL_ok (k6 : f K6 = 6) (k4 : f K4 = 4) (k3 : f K3 = 3) (k1 : f K1 = 1)
    (hb1 : f ztea + 6 ≤ W) (hb2 : m (f ztea + 6) + f wO ≤ W)
    (hb3 : m ztxea + 5 * m ztwpk + 4 ≤ W) : okB W m arcL f := by
  zucan

  have s1 : IScr (240000 + 3003) := iscr_sw by_norm_num by_norm_num
  have s2 : IScr (240000 + 3004) := iscr_sw by_norm_num by_norm_num
  have s3 : IScr (240000 + 3005) := iscr_sw by_norm_num by_norm_num
  have s4 : IScr (240000 + 3006) := iscr_sw by_norm_num by_norm_num
  have s5 : IScr (240000 + 3007) := iscr_sw by_norm_num by_norm_num
  have hb1' : f 240003 + 6 ≤ W := hb1
  have hb2' : m ztrpj + f 243002 ≤ W := hb2
  have hb3' : m (f 240003 + 4) + 5 * m (m ztrpj + f 243002) + 4 ≤ W := hb3
  simp only [arcL, okB, okI, regI, upd, wT, wA, wR, wEE, wEH, wO, K6, K4, K3, K1, sw]
  grind

/-- **The arc at the spine position `wO`.** -/
theorem arcS_irs {M : Model} {Q : Polygon} {N : NF} (hI : IInv W c₀ c) (hK : Consts c)
    (hNF : IsNF M Q N) (hNA : NFAt c.nmem ztwsx N)
    (hB1 : c.nreg ztea + 7 ≤ W) (hB2 : c.nmem ztzks + 5 * N.arcs.length ≤ W)
    (hB3 : c.nmem ztzkt + N.arcs.length ≤ W) (ho : c.nreg wO < N.arcs.length) :
    IRS P W c₀ arcS c 16 (fun c' => c'.nreg wA = OracleQ.sj N ztcps ∧
      c'.nreg wR = (N.arc ztypo).reg ∧
      c'.nreg wEE = (N.arc ztypo).e.edge ∧
      c'.nreg wEH = (N.arc ztypo).e.hgt ∧
      (∀ q, q ≠ wT → q ≠ wA → q ≠ wR → q ≠ wEE → q ≠ wEH → c'.nreg q = c.nreg q) ∧
      c'.nmem = c.nmem) := by
  zuch
  zullh
  have hsj : c.nmem _ = OracleQ.sj N ztcps :=
    hNA.2.2.2.2.2.2.2.2.1 _ by_omega
  have hal := NFLoc.seq_lt hNF ho
  have hrec := hNA.2.2.2.2.2.2.1 _ hal
  unfold OracleQ.sj at hsj hal hrec ⊢
  have hok := arcL_ok (W := W) c.nmem c.nreg k6 k4 k3 k1 by_omega by_omega by_omega
  refine (IRS.block arcL hI hok).mono by_rfl ?_
  zuu
  obtain ⟨vA, vR, vE, vH⟩ := arcL_val c.nmem c.nreg k6 k4 k3 k1
  rw [hsj] at vA vR vE vH
  exact ⟨vA, vR.trans hrec.1, vE.trans hrec.2.2.2.1, vH.trans hrec.2.2.2.2,
    fun q h1 h2 h3 h4 h5 => arcL_other _ _ h1 h2 h3 h4 h5, rfl⟩

/-! ## The decision -/
def clipE : Stmt :=
  .seq (.instr (.addN wE cGL cLL)) (.seq ztrns
    (.seq (.instr (.constN wH 0)) ztour))
def normE : Stmt :=
  .seq ztfek
    (.seq (.instr (.addN wE cGL wPs)) (.seq ztrns
      (.seq (.instr (.copyN wH wEH)) ztour)))
def midS : Stmt := .ifLtN K0 cLD (.ifLtN wD cLL (.ifLtN wDE cLL normE clipE) normE) normE
def decS : Stmt :=
  .ifLtN K0 ztgmk ztige
    (.seq (.instr (.addN wDE wEE cN1)) (.seq (.instr (.subN wDE wDE cB1))
      (.seq (condSub wDE wDE cN1) (.ifLtN wDE cE1 midS ztige))))

/-- The registers the decision writes. -/
def DecW (q : ℕ) : Prop := q = wX ∨ q = wE ∨ q = wH ∨ q = wDE ∨ q = wPs

/-- **The outcomes of the decision.** -/
def DecOut (J : Merge.Junction) (Pw : Prop) (d₀ eE hE : ℕ) (c' : Config) : Prop :=
  (c'.nreg wX = 1 ∧ (Pw ∨ E₁ J ≤ dOf (chainModel J.left).W.n ztbsn eE)) ∨
  (c'.nreg wX = 0 ∧ ¬ Pw ∧ 0 < lδ J ∧ d₀ < lL1 J ∧ lL1 J ≤ dOf (chainModel J.left).W.n ztbsn eE ∧
    dOf (chainModel J.left).W.n ztbsn eE < E₁ J ∧
    c'.nreg wE = ztbalm % (chainModel J.whole).W.n ∧
    c'.nreg wH = 0) ∨
  (c'.nreg wX = 0 ∧ ¬ Pw ∧
    ¬ (0 < lδ J ∧ d₀ < lL1 J ∧ lL1 J ≤ dOf (chainModel J.left).W.n ztbsn eE) ∧
    dOf (chainModel J.left).W.n ztbsn eE < E₁ J ∧
    c'.nreg wE = (ztwks +
      (if dOf (chainModel J.left).W.n ztbsn eE < lL1 J + lδ J then
        dOf (chainModel J.left).W.n ztbsn eE else dOf (chainModel J.left).W.n ztbsn eE - lδ J)) %
        (chainModel J.whole).W.n ∧
    c'.nreg wH = hE)
theorem win_lL1_lt_n : lL1 J < (chainModel J.whole).W.n := by
  zupcz; have := J.one_le_m₂; have : zttd := rfl
  have := tpos_lt J.left J.m₁
  zumth
theorem win_n₁_le_n {J : Merge.Junction} : (chainModel J.left).W.n ≤ (chainModel J.whole).W.n := by
  rw [win_n₁_eq, win_n_eq]; simp
theorem decW_X (h : ¬ DecW q) : q ≠ wX := fun e => h ztccj
theorem decW_E (h : ¬ DecW q) : q ≠ wE := fun e => h ztxgj
theorem decW_H (h : ¬ DecW q) : q ≠ wH := fun e => h ztbh
theorem decW_D (h : ¬ DecW q) : q ≠ wDE := fun e => h ztbh
theorem decW_P (h : ¬ DecW q) : q ≠ wPs := fun e => h ztbh
theorem wsX : IScr wX := iscr_sw' by_norm_num by_norm_num
theorem wsE : IScr wE := iscr_sw' by_norm_num by_norm_num
theorem wsH : IScr wH := iscr_sw' by_norm_num by_norm_num
theorem wsDE : IScr wDE := iscr_sw' by_norm_num by_norm_num
theorem wsP : IScr wPs := iscr_sw' by_norm_num by_norm_num
theorem clipE_irs (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hWn : 2 * (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ clipE c 6 (fun c' =>
      c'.nreg wE = ztbalm %
        (chainModel J.whole).W.n ∧ c'.nreg wH = 0 ∧ c'.nreg wX = 0 ∧
      ztcqg ∧ c'.nmem = c.nmem) := by
  zuclu
  have hgl : ztwyn :=
    Nat.mod_lt _ (by have := win_gW_lt (J := J); omega)
  have hl := win_lL1_lt_n (J := J)
  unfold clipE
  refine IRS.seq (K₂ := 5) (win_irs_add hI wsE (by rw [hM.gl, hM.ll]; omega)) ?_ |>.mono
    by_norm_num ztb
  zukz
  refine IRS.seq (K₂ := 2) (win_condSub_irs hI₁ wsE) ?_ |>.mono by_norm_num ztb
  zula
  rw [v1, hM.gl, hM.ll, o1 _ (by rne), hM.nw, win_condSub_mod by_omega] at v2
  refine IRS.seq (K₂ := 1) (win_irs_const' hI₂ wsH ztbg) ?_ |>.mono by_norm_num ztb
  zulb
  refine (win_irs_const' hI₃ wsX ztbg).mono le_rfl ?_
  rintro c₄ ⟨v4, o4, m4⟩
  refine ⟨by rw [o4 _ (by rne), o3 _ (by rne), v2], by_grind, v4,
    fun q hq => ?_, by_simp_all⟩
  rw [o4 q ztmis, o3 q ztvoz, o2 q ztmir, o1 q ztmir]
theorem normE_irs (hI : IInv W c₀ c) (hM₀ : MapK J c₀)
    (hWn : 2 * (chainModel J.whole).W.n ≤ W) (hDE : c.nreg wDE < (chainModel J.whole).W.n) :
    IRS P W c₀ normE c 10 (fun c' =>
      c'.nreg wE = (ztwks +
        ztfyj) %
        (chainModel J.whole).W.n ∧ c'.nreg wH = c.nreg wEH ∧ c'.nreg wX = 0 ∧
      ztcqg ∧ c'.nmem = c.nmem) := by
  zuclu
  have hgl : ztwyn :=
    Nat.mod_lt _ by_omega
  unfold normE
  have step : IRS P W c₀ ztfek c 3
      (fun c' => win_Upd c c' wPs
        ztfyj) := by
    by_cases h : c.nreg wDE < c.nreg cLE
    · refine (IRS.ifT h (win_irs_copy hI wsP)).mono by_norm_num ?_
      zubyi
      rw [hM.le] at h; exact ⟨by_simp_all, b, d⟩
    · refine (IRS.ifF h (win_irs_sub hI wsP)).mono by_norm_num ?_
      zubyi
      rw [hM.le] at h; exact ⟨by rw [a, ite_eq_right h, hM.ld], b, d⟩
  refine IRS.seq (K₂ := 7) step ?_ |>.mono by_norm_num ztb
  zukz
  refine IRS.seq (K₂ := 6) (win_irs_add hI₁ wsE (by rw [v1, o1 _ (by rne), hM.gl]; grind))
    ?_ |>.mono by_norm_num ztb
  zula
  refine IRS.seq (K₂ := 3) (win_condSub_irs hI₂ wsE) ?_ |>.mono by_norm_num ztb
  zulb
  rw [v2, v1, o1 _ (by rne), hM.gl, o2 _ (by rne), o1 _ (by rne), hM.nw,
    win_condSub_mod by_grind] at v3
  refine IRS.seq (K₂ := 1) (win_irs_copy hI₃ wsH) ?_ |>.mono by_norm_num ztb
  zucei
  refine (win_irs_const' hI₄ wsX ztbg).mono le_rfl ?_
  rintro c₅ ⟨v5, o5, m5⟩
  refine ⟨by rw [o5 _ (by rne), o4 _ (by rne), v3], ?_, v5, fun q hq => ?_,
    by simp_all⟩
  · rw [o5 _ (by rne), v4, o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)]
  · rw [o5 q ztmis, o4 q ztvoz, o3 q ztmir, o2 q ztmir, o1 q (decW_P hq)]
set_option maxHeartbeats 4000000 in
/-- **The decision.** -/
theorem decS_irs (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hM₀ : MapK J c₀)
    {Pw : Prop} (hbit : BitIs c ztgmk Pw) (hEE : c.nreg wEE < (chainModel J.left).W.n)
    (hWn : 2 * (chainModel J.whole).W.n ≤ W) :
    IRS P W c₀ decS c 30 (fun c' => DecOut J Pw ztqja ztqjb ztvjy c' ∧
      ztcqg ∧ c'.nmem = c.nmem) := by
  zuyr
  zuclu
  zudpx
  have hnn := win_n₁_le_n (J := J)
  zuheq
  unfold decS
  by_cases hb1 : c.nreg K0 < c.nreg ztgmk
  · refine (IRS.ifT hb1 ztryj).mono by_norm_num ?_
    zudjp
    have hp := hbit.2.1 (by have := hbit.1; omega)
    exact ⟨Or.inl by_simp_all, fun q hq => o q ztmis, m⟩
  have hnp := fun hp => hb1 (by rw [k0, hbit.2.2 hp]; norm_num)
  refine IRS.mono (IRS.ifF hb1 ?_) le_rfl ztb
  refine IRS.seq (K₂ := 27) (win_irs_add hI wsDE (by zupcj; omega)) ?_ |>.mono by_norm_num
    ztb
  zukz
  refine IRS.seq (K₂ := 26) (win_irs_sub hI₁ wsDE) ?_ |>.mono by_norm_num ztb
  zula
  refine IRS.seq (K₂ := 23) (win_condSub_irs hI₂ wsDE) ?_ |>.mono by_norm_num ztb
  zulb
  have hM₁ := hM₀.fix hI₁
  have hM₂ := hM₀.fix hI₂
  rw [v2, v1, o1 cB1 (by rne), hM.n1, hM.b1, o2 cN1 (by rne), o1 cN1 (by rne), hM.n1,
    win_condSub_mod by_omega] at v3
  set dE := dOf (chainModel J.left).W.n ztbsn ztqjb with hdE
  have vd : c₃.nreg wDE = dE := v3
  zulis
  zulim
  have o3' : ∀ q, ¬ DecW q → c₃.nreg q = c.nreg q := fun q hq => by
    rw [o3 q ztqly, o2 q ztqly, o1 q ztqly]
  have m3' : ztckd := by_simp_all
  have hdn : dE < (chainModel J.left).W.n := dOf_lt by_omega _ _
  by_cases hb2 : c₃.nreg wDE < c₃.nreg cE1
  · zuinb
    refine IRS.mono (K := 18 + 2) (IRS.ifT ztlja ?_) by_norm_num
      ztb
    unfold midS
    have eD : c₃.nreg wD = c.nreg wD := o3' _ (by unfold DecW; rne)
    have eH : c₃.nreg wEH = c.nreg wEH := o3' _ (by unfold DecW; rne)
    have finN : ∀ c', (c'.nreg wE = (ztwks +
        (if c₃.nreg wDE < lL1 J + lδ J then c₃.nreg wDE else c₃.nreg wDE - lδ J)) %
        (chainModel J.whole).W.n ∧ c'.nreg wH = c₃.nreg wEH ∧ c'.nreg wX = 0 ∧
        (∀ q, ¬ DecW q → c'.nreg q = c₃.nreg q) ∧ c'.nmem = c₃.nmem) →
        ¬ (0 < lδ J ∧ c.nreg wD < lL1 J ∧ lL1 J ≤ dE) →
        DecOut J Pw ztqja ztqjb ztvjy c' ∧
          ztcqg ∧ c'.nmem = c.nmem := by
      rintro c' ⟨a1, a2, a3, a4, a5⟩ hn
      rw [vd] at a1
      exact ⟨Or.inr by_grind,
        fun q hq => (a4 q hq).trans zttuq, a5.trans m3'⟩
    have hDEn : c₃.nreg wDE < (chainModel J.whole).W.n := by_omega
    by_cases hδ : c₃.nreg K0 < c₃.nreg cLD
    · have hδ' : zthoc := by rw [hK₃.1, hM₃.ld] at hδ; exact hδ
      refine IRS.mono (K := 16 + 2) ztsyd by_norm_num ztb
      by_cases hd0 : c₃.nreg wD < c₃.nreg cLL
      · have hd0' : c.nreg wD < lL1 J := by rw [eD, hM₃.ll] at hd0; omega
        refine IRS.mono (K := 12 + 2) (IRS.ifT hd0 ?_) by_norm_num ztb
        by_cases hd1 : c₃.nreg wDE < c₃.nreg cLL
        · refine IRS.mono (IRS.ifT hd1 ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
            fun c' h => finN c' h ?_)) by_norm_num by_grind
          rw [vd, hM₃.ll] at hd1; omega
        · refine IRS.mono (K := 10 + 2) (IRS.ifF hd1 ((clipE_irs hI₃ hM₀ hWn).mono by_norm_num
            ?_)) by_norm_num (fun _ h => h)
          rintro c' ⟨a1, a2, a3, a4, a5⟩
          rw [vd, hM₃.ll] at hd1
          exact ⟨Or.inr by_grind,
            fun q hq => (a4 q hq).trans zttuq, a5.trans m3'⟩
      · have hd0' : ¬ c.nreg wD < lL1 J := by rw [eD, hM₃.ll] at hd0; omega
        refine IRS.mono (IRS.ifF hd0 ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
          fun c' h => finN c' h ?_)) by_norm_num by_grind
        omega
    · have hδ' : ¬ 0 < lδ J := by rw [hK₃.1, hM₃.ld] at hδ; exact hδ
      refine IRS.mono (IRS.ifF hδ ((normE_irs hI₃ hM₀ hWn hDEn).mono le_rfl
        fun c' h => finN c' h ?_)) by_norm_num by_grind
      omega
  · zuinb
    refine IRS.mono (IRS.ifF ztlja
      (win_irs_const' hI₃ wsX by_omega)) by_norm_num ?_
    zudjp
    exact ⟨Or.inl by_omega, fun q hq => (o q ztmis).trans by_grind,
      m.trans m3'⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Environment facts at a run configuration -/
theorem win_nt (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    NFWithin c.nmem ztwsx ztvjh N₁ := by
  rw [hI.hin _ ztlta,
    hI.hin _ ztddj]
  zumaw
  exact Robust.transport E.hNT₁ zthgt
theorem win_tab (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    ztug ∧ N₁.arcs.length < 2 ^ c.nreg TLR ∧
      c.nreg TBR + c.nreg TLR ≤ c₀.nreg ALLOC ∧ c.nreg TLR = c₀.nreg TLR := by
  zucro

  refine ⟨fun j hj => ?_, by rw [eL]; exact E.hbig₁, by_omega, eL⟩
  zudfr
theorem chain_vtx_abs_snd_lt (C : Chain) {p : ℕ} (h6 : 6 ≤ p) (hp : p < (chainModel C).W.n) :
    |((chainModel C).W.vtx p).2| < C.radius := by
  zuii
  zukk
  rw [cm_W, C.sideWalk_vtx_tour _ by_omega, Chain.sideTour]
  exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set ztxuz).2
    C.coordBound_lt_radius

/-- The key position in the walk of `C₁` is a vertex only on the tour. -/
theorem key6 (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h) (hL : (Lst J : ℝ) ≤ offK P J e h)
    (h0 : h = 0) : 6 ≤ ke₁ J e := by
  obtain ⟨-, -, -, -, -, -, -, hpt⟩ := key_map hP hpw hL
  have h6 := hpw.2.2 h0
  have hv := hpt 0
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero] at hv
  zulwe
  have a1 := chain_vtx_abs_snd_lt J.whole h6 hpw.1
  have a2 := Restore.chain_box_vtx_abs J.left (p := ke₁ J e) by_omega
  rw [hv, a2] at a1
  exact lt_irrefl _ a1

/-- An arc end of a nonempty family is a vertex only on the tour. -/
theorem end6 {C : Chain} (hP : C.P.Simple) {N : NF} (hNF : IsNF ztc zta N)
    (hne : (N.F ztc zta).Nonempty) {j : ℕ} (hj : j < N.arcs.length)
    (h0 : (N.arc j).e.hgt = 0) : 6 ≤ (N.arc j).e.edge := by
  have hab := (Restore.arc_abs_lt hP hNF hne hj).2
  zulwe
  have hpos : (chainModel C).pos zta (N.arc j).e = (chainModel C).W.vtx (N.arc j).e.edge := by
    have hp0 : (chainModel C).param zta (N.arc j).e = 0 := by
      unfold Model.param; zvmzn
    rw [win_pos_eq_sidePt, hp0]
    exact Chazelle.Chain.sidePt_zero _ _
  rw [hpos, Restore.chain_box_vtx_abs C by_omega] at hab
  simp_all

/-! ## Double identification of the key -/
def locS : Stmt := locJ MD₁ ztea wE1 kH wO

/-- The post of `locJ` at the key. -/
def LocPost (P : Polygon) (J : Merge.Junction) (N₁ : NF) (c c' : Config) : Prop :=
  c'.nreg wO < N₁.arcs.length ∧
    (¬ (chainModel J.left).IsCut ztwjx
        ztwon →
      N₁.F ztbw zta = ∅ ∨
        sideInArc (OracleQ.sk ztbw zta N₁ ztjrn)
          (OracleQ.ek ztbw zta N₁ ztjrn)
          ztwon) ∧
    ((chainModel J.left).IsCut ztwjx
        ztwon →
      OracleQ.sk ztbw zta N₁ ztjrn =
          (chainModel J.left).key zta ztoj ∨
        OracleQ.ek ztbw zta N₁ ztjrn =
          (chainModel J.left).key zta ztoj) ∧
    (∀ r, bandOf r ∉ oracleBands → r ≠ wO → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem
set_option maxRecDepth 20000 in
theorem locS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he : c.nreg wE1 < (chainModel J.left).W.n)
    (hpp : ProperPos ztbw zta P.n ztoj)
    (hroom : c.nreg ALLOC + ztxuq ≤ W) :
    IRS P W c₀ locS c ztxuq (LocPost P J N₁ c) := by
  obtain ⟨hmd, hmwf, -, -⟩ := E.md hI
  zujzs
  have hNA : NFAt c.nmem _ N₁ := hNT.nfAt
  obtain ⟨htab, hbig, hTB, eL⟩ := win_tab E hI
  zumcf
  have hA0 := arcs_pos hP₁ E.hNF₁
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT E.hNF₁ hA0
  zubwc
  zudni
  unfold locS
  refine (locJ_irs hI E.hG E.hWh
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide⟩ hmd hmwf hP₁ hNA E.hNF₁
    he hpp htab hbig by_omega by_omega by_omega by_omega
    by_simp_all).mono (by rw [eL]) ?_
  rintro c' ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, fun r hr hro => ?_, h6⟩
  grind

/-! ## The comparison of the key with an arc end -/
def cmpS : Stmt := callOff CD₁ wE1 kH wEE wEH cB1 wC

/-- The registers `callOff` may write. -/
def BcO (o : ℕ) (r : ℕ) : Bool :=
  Bprim r || decide ztqt || decide zttxz || decide ztqvd
theorem callOff_wr (dsc ex hx ey hy g o : ℕ) : SignK.wr ztuwq ztmhh = true := by
  have hoff : SignK.wr ztuwq offCmp = true :=
    wr_mono wr_offCmp (fun r h => by simp [BcO, h])
  simp [callOff, callP, cps, block, SignK.wr, SignK.wrOK, BcO, hoff]

/-- The `b₁`-offset of a position of the walk of `C₁`. -/
noncomputable def U₁ (P : Polygon) (J : Merge.Junction) (x : WPos) : ℝ :=
  off (chainModel J.left).W.n ztbsn ((chainModel J.left).key zta x)
set_option maxRecDepth 20000 in
theorem cmpS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he : c.nreg wE1 < (chainModel J.left).W.n) (hee : c.nreg wEE < (chainModel J.left).W.n)
    (hpx : ProperPos ztbw zta P.n ztoj)
    (hpy : ProperPos ztbw zta P.n ztgop)
    (h6x : c.nreg kH = 0 → 6 ≤ c.nreg wE1) (h6y : c.nreg wEH = 0 → 6 ≤ c.nreg wEE)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ cmpS c 11008 (fun c' =>
      BitIs c' wC (U₁ P J ztoj < U₁ P J ztgop) ∧
      BitIs c' ztgmk (U₁ P J ztgop < U₁ P J ztoj) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ wC → r ≠ sw 3011 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  have hctx := E.ctx1' hI
  have hM := E.hM.fix hI
  have hg : c.nreg cB1 < (chainModel J.left).W.n := by rw [hM.b1]; exact b₁_lt
  unfold cmpS
  refine (IRS.addFrameB (callOff_wr _ _ _ _ _ _ _) (callOff_irs hI hctx
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide⟩ he hee hg hpx hpy h6x h6y hroom)).mono
    le_rfl ?_
  rintro c' ⟨⟨b1, b2, k, -, -⟩, hf⟩
  rw [hM.b1] at b1 b2
  have hA : ztble := hf.1 _ by_rfl
  refine ⟨b1, b2, fun r hr h1 h2 => ?_, hf.2.2.1, hA⟩
  zujtu
  · simp_all
  · exact k r hr h1 h2 hra

/-! ## The arc after the key -/

/-- The arc registers hold the arc at spine position `o`. -/
def ArcRegs (N : NF) (c : Config) (o : ℕ) : Prop :=
  c.nreg wA = OracleQ.sj N o ∧ c.nreg wR = (N.arc ztnnr).reg ∧
    c.nreg wEE = (N.arc ztnnr).e.edge ∧ c.nreg wEH = (N.arc ztnnr).e.hgt
def swS : Stmt :=
  .seq (.instr (.addN wT ztea K1)) (.seq (.instr (.loadN wL wT)) (.seq (.instr (.addN wO wO K1))
    (.seq ztipw arcS)))
def eqS : Stmt := .ifLtN K0 wC .skip (.ifLtN K0 ztgmk .skip swS)

/-- The registers of the arc step. -/
def ArcW (q : ℕ) : Prop := q = wT ∨ q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH ∨ q = wL ∨ q = wO
set_option maxHeartbeats 4000000 in
theorem eqS_irs {M : Model} {Q : Polygon} {N : NF} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hNF : IsNF M Q N) (hNA : NFAt c.nmem ztwsx N)
    (hB1 : c.nreg ztea + 7 ≤ W) (hB2 : c.nmem ztzks + 5 * N.arcs.length ≤ W)
    (hB3 : c.nmem ztzkt + N.arcs.length ≤ W) (ho : c.nreg wO < N.arcs.length)
    {p1 p2 : Prop} (hb1 : BitIs c wC p1) (hb2 : BitIs c ztgmk p2) (har : ArcRegs N c ztcps) :
    IRS P W c₀ eqS c 30 (fun c' =>
      (p1 ∨ p2 → c'.nreg wO = c.nreg wO) ∧
      (¬ p1 → ¬ p2 → c'.nreg wO = OracleQ.succP N.arcs.length ztcps) ∧
      ArcRegs N c' ztjrn ∧ (∀ q, ¬ ArcW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zuyr
  zudpx
  unfold eqS
  by_cases h1 : c.nreg K0 < c.nreg wC
  · have hp := hb1.2.1 (by have := hb1.1; omega)
    refine (IRS.ifT h1 ztsyf).mono le_rfl ztb
  have hn1 := fun hp => h1 (by rw [k0, hb1.2.2 hp]; norm_num)
  refine IRS.mono ztfnr le_rfl ztb
  by_cases h2 : c.nreg K0 < c.nreg ztgmk
  · have hp := hb2.2.1 (by have := hb2.1; omega)
    exact (IRS.ifT h2 ztsyf).mono le_rfl ztb
  have hn2 := fun hp => h2 (by rw [k0, hb2.2.2 hp]; norm_num)
  refine IRS.mono ztsya le_rfl ztb
  have sT : IScr wT := iscr_sw' by_norm_num by_norm_num
  have sL : IScr wL := iscr_sw' by_norm_num by_norm_num
  have sO : IScr wO := iscr_sw' by_norm_num by_norm_num
  unfold swS
  refine IRS.seq (K₂ := 25) (win_irs_add hI sT (by rw [hK.2.1]; omega)) ?_ |>.mono by_norm_num
    ztb
  zukz
  refine IRS.seq (K₂ := 24) (win_irs_load hI₁ sL) ?_ |>.mono by_norm_num ztb
  zula
  rw [v1, m1, hK.2.1, hNA.2.1] at v2
  refine IRS.seq (K₂ := 23) (win_irs_add hI₂ sO (by
    rw [o2 _ (by rne), o1 _ (by rne), (hK₀.fix hI₂).2.1]; omega)) ?_ |>.mono by_norm_num
    ztb
  zulb
  rw [o2 _ (by rne), o1 _ (by rne), (hK₀.fix hI₂).2.1] at v3
  have hsucc : IRS P W c₀ ztipw c₃ 3
      (fun c' => win_Upd c₃ c' wO (OracleQ.succP N.arcs.length ztcps)) := by
    by_cases h : c₃.nreg wO < c₃.nreg wL
    · refine (IRS.ifT h (IRS.skip (K := 1) hI₃ ztdqf)).mono
        by_norm_num ztb
      rw [o3 wL (by rne), v2, v3] at h
      zunrr; unfold OracleQ.succP; simp_all
    · refine (IRS.ifF h (win_irs_const' hI₃ sO (Nat.zero_le W))).mono by_norm_num ?_
      zubyi
      refine ztrab
      rw [o3 wL (by rne), v2, v3] at h
      rw [a]; unfold OracleQ.succP; simp_all
  refine IRS.seq (K₂ := 16) hsucc ?_ |>.mono by_norm_num ztb
  zucei
  have hm4 : zteid := by_simp_all
  have e3 : ztzqa := by
    rw [o4 _ (by rne), o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)]
  have hs := OracleQ.succP_lt ho
  refine (arcS_irs hI₄ ztqpk hNF by_simp_all by_omega
    by_simp_all by_simp_all by_omega).mono
    le_rfl ?_
  zuecf
  have eo : c'.nreg wO = OracleQ.succP N.arcs.length ztcps := by
    rw [a5 _ (by rne) (by rne) (by rne) (by rne) (by rne), v4]
  refine ⟨by_grind, by_omega, ?_, fun q hq => ?_, by_grind⟩
  · rw [eo]; rw [v4] at a1 a2 a3 a4; trivial
  · unfold ArcW at hq
    grind

/-! ## The gather of the region -/

/-- Store `wR` at the allocator, raising it by one. -/
def win_put1 : Stmt := block [.storeN ALLOC wR, .addN ALLOC ALLOC K1]
theorem win_put1_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ win_put1 c 2 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      ztjn ∧
      c'.nmem = upd c.nmem ztm (c.nreg wR)) := by
  zubgn
  zubod
  zukfh
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 243005, .addN 9999 9999 240611]) c c' k ∧
      k = 2 ∧ c'.nreg 9999 = c.nreg 9999 + 1 ∧ ztedh ∧
      c'.nmem = upd c.nmem zterc (c.nreg 243005) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    simp_all
  zupp
  refine IRS.ofExec hI ex by_omega ztgjo h4 ztts h5 h6
    by_grind by_grind
    ⟨h1, h2, h3⟩
  zugul
  zubcl

  zuby
  grind
def gatherS : Stmt :=
  .seq (.instr (.copyN gL ALLOC)) (.seq (.instr (.constN gC 1)) (.seq (.instr (.copyN gNF ztea))
    (.seq win_put1 (.seq (gather CD₁) (.seq (.instr (.copyN wGB gBase)) (.instr (.copyN wGK gK)))))))

/-- The registers the gather tail writes (besides the oracle bands and the allocator). -/
def GathW (q : ℕ) : Prop := GSet q ∨ q = gL ∨ q = gC ∨ q = gNF ∨ q = wGB ∨ q = wGK
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem gatherS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hR : c.nreg wR < N₁.nRegions)
    (hroom : c.nreg ALLOC + ztmki ≤ W) :
    IRS P W c₀ gatherS c ztmki (fun c' =>
      c.nreg ALLOC ≤ c'.nreg wGB ∧ c'.nreg wGK = (regArcs N₁ [c.nreg wR]).length ∧
      c'.nreg wGB + 4 * (regArcs N₁ [c.nreg wR]).length ≤ c'.nreg ALLOC ∧
      Gath ztbw zta N₁ c'.nmem zthug (regArcs N₁ [c.nreg wR]) ∧
      zth ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ GathW r → r ≠ ALLOC → c'.nreg r = c.nreg r)) := by
  zuiw
  have sL : IScr gL := iscr_sw' by_norm_num by_norm_num
  have sC : IScr gC := iscr_sw' by_norm_num by_norm_num
  have sN : IScr gNF := iscr_sw' by_norm_num by_norm_num
  have sB : IScr wGB := iscr_sw' by_norm_num by_norm_num
  have sK : IScr wGK := iscr_sw' by_norm_num by_norm_num
  zubwc
  set R := c.nreg wR with hRd
  unfold gatherS
  refine IRS.seq (K₂ := gatherK N₁ [R] + 9) (win_irs_copy hI sL) ?_ |>.mono by_omega ztb
  zukz
  refine IRS.seq (K₂ := gatherK N₁ [R] + 8) (win_irs_const' hI₁ sC by_omega) ?_ |>.mono by_omega
    ztb
  zula
  refine IRS.seq (K₂ := gatherK N₁ [R] + 7) (win_irs_copy hI₂ sN) ?_ |>.mono by_omega ztb
  zulb
  have a3 : ztcke := by
    rw [o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)]
  refine IRS.seq (K₂ := gatherK N₁ [R] + 5) (win_put1_irs hI₃ ztjih by_omega) ?_ |>.mono
    by_omega ztb
  rintro c₄ hI₄ - - ⟨a4, o4, m4⟩
  have r3 : c₃.nreg wR = R := by rw [o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)]
  rw [a3, r3] at m4
  rw [a3] at a4
  have l4 : c₄.nreg gL = c.nreg ALLOC := by
    rw [o4 _ (by rne), o3 _ (by rne), o2 _ (by rne), v1]
  have c4 : c₄.nreg gC = 1 := by rw [o4 _ (by rne), o3 _ (by rne), v2]
  have n4 : c₄.nreg gNF = c₀.nreg ztea := by
    rw [o4 _ (by rne), v3, o2 _ (by rne), o1 _ (by rne)]
    zugkg
  have hNW : NFWithin c₄.nmem _ _ N₁ :=
    E.hNW₁.transport hI₄.hm
  zumcf
  refine IRS.seq (K₂ := 2) (gather_irs (rs := [R]) hI₄ E.hK (E.ctx1' hI₄)
    ⟨by_decide, by_decide, by unfold GSet CD₁ sw; omega⟩
    hP₁ E.hNF₁ hNW n4 hI₄.hA by_simp_all
    by_simp_all
    by_simp_all by_omega by_omega) ?_ |>.mono by_omega
    ztb
  rintro c₅ hI₅ - - ⟨⟨g1, g2, g3, g4, g5, g6, -⟩, -⟩
  refine IRS.seq (K₂ := 1) (win_irs_copy hI₅ sB) ?_ |>.mono le_rfl ztb
  rintro c₆ hI₆ - - ⟨v6, o6, m6⟩
  refine (win_irs_copy hI₆ sK).mono le_rfl ?_
  rintro c₇ ⟨v7, o7, m7⟩
  have e7B : c₇.nreg wGB = c.nreg ALLOC + 1 := by rw [o7 _ (by rne), v6, g1, a4]
  have e7A : c₇.nreg ALLOC = c.nreg ALLOC + 1 + 4 * (regArcs N₁ [R]).length := by
    rw [o7 _ (by rne), o6 _ (by rne), g3, a4]
  refine ⟨by_omega, by rw [v7, o6 _ (by rne), g2], by_omega, fun k hk => ?_, fun a ha => ?_,
    fun r hr hg hra => ?_⟩
  · grind
  · rw [m7, m6, g5 a by_omega, m4, upd_other _ _ _ by_omega, m3, m2, m1]
  · have hG := fun h => hg zteg
    rw [o7 r ztxgt,
      o6 r ztxgt, g6 r hr hG hra,
      o4 r hra, o3 r ztxgt,
      o2 r ztxgt, o1 r (fun h => hg ztwkb)]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem wr_sw {i : ℕ} (h1 : 3000 ≤ i) (h2 : i < 6000) : WR ztcdy :=
  Or.inr (Or.inr ztcbm)
theorem ne_of_wr {r q : ℕ} (hr : ¬ WR r) (hq : WR q) : r ≠ q := by_grind
theorem wr_wX : WR wX := Or.inr ztbaew
theorem wr_wE : WR wE := Or.inr ztwos
theorem wr_wH : WR wH := Or.inr ztwos
theorem win_off_inj {n g x y : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n)
    (h : off n g x = off n g y) : x = y := by
  zugis

/-! ## The body: the arc after the key and the decision -/
def neS : Stmt := .seq cmpS (.seq eqS (.seq cmpS decS))
def bodyS : Stmt := .ifLtN K0 wCh neS ztige

/-- The post of the body. -/
def BodyPost (P : Polygon) (J : Merge.Junction) (N₁ : NF) (x₀ : ℝ) (u₀ : WPos) (d₀ : ℕ)
    (c c' : Config) : Prop :=
  ∃ o', o' < N₁.arcs.length ∧ ArcRegs N₁ c' o' ∧
    ((N₁.F ztbw zta).Nonempty →
      (sideInArc ztzcv
          ztzcs x₀ ∨
        OracleQ.sk ztbw zta N₁ o' = x₀) ∧
      DecOut J (U₁ P J (N₁.arc ztdfy).e < U₁ P J u₀) d₀
        (N₁.arc ztdfy).e.edge (N₁.arc ztdfy).e.hgt c') ∧
    (N₁.F ztbw zta = ∅ → c'.nreg wX = 1) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ WR r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem
variable {M : Model} {Q : Polygon}
theorem win_F_nonempty_iff {N : NF} :
    (N.F M Q).Nonempty ↔ 0 < N.chords.length := by
  constructor
  · rintro ⟨x, r, hr, -⟩
    grind
  · zuq
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos h
    exact ⟨_, r, hr, rfl⟩
theorem win_F_empty_iff {N : NF} :
    N.F M Q = ∅ ↔ N.chords.length = 0 := by
  rw [← Set.not_nonempty_iff_eq_empty, win_F_nonempty_iff]; omega
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The body.** -/
theorem bodyS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he1 : c.nreg wE1 < (chainModel J.left).W.n)
    (hpx : ProperPos ztbw zta P.n ztoj)
    (h6x : c.nreg kH = 0 → 6 ≤ c.nreg wE1)
    (ho : c.nreg wO < N₁.arcs.length) (har : ArcRegs N₁ c ztcps)
    (hl1 : ¬ (chainModel J.left).IsCut ztwjx
        ztwon →
      N₁.F ztbw zta = ∅ ∨
        sideInArc (OracleQ.sk ztbw zta N₁ ztcps)
          (OracleQ.ek ztbw zta N₁ ztcps)
          ztwon)
    (hl2 : (chainModel J.left).IsCut ztwjx
        ztwon →
      OracleQ.sk ztbw zta N₁ ztcps =
          (chainModel J.left).key zta ztoj ∨
        OracleQ.ek ztbw zta N₁ ztcps =
          (chainModel J.left).key zta ztoj)
    (hch : c.nreg wCh = N₁.chords.length) (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ bodyS c 22100 (BodyPost P J N₁
      ztwon ztoj
      ztqja c) := by
  zujmp
  set x₀ := M.key zta ztoj with hx₀
  zuiw
  zudpw
  zucwa

  zuc
  unfold bodyS
  by_cases hne : c.nreg K0 < c.nreg wCh
  swap
  · -- the empty family
    have hemp : N₁.F M zta = ∅ := by rw [win_F_empty_iff]; omega
    refine (IRS.ifF hne ztryj).mono by_norm_num ?_
    zudjp
    refine ⟨c.nreg wO, ho, ?_, fun h => absurd hemp h.ne_empty, fun _ => v,
      fun r _ hr => o r (ne_of_wr hr wr_wX), m⟩
    obtain ⟨a1, a2, a3, a4⟩ := har
    exact ⟨by rw [o _ (by rne), a1], by rw [o _ (by rne), a2], by rw [o _ (by rne), a3],
      by rw [o _ (by rne), a4]⟩
  have hFne : ztziw := by rw [win_F_nonempty_iff]; omega
  refine IRS.mono (K := 22098 + 2) (IRS.ifT hne ?_) le_rfl ztb
  -- facts on arcs
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M zta P.n (N₁.arc j).e ∧
      (N₁.arc j).e.edge < M.W.n ∧ ((N₁.arc j).e.hgt = 0 → 6 ≤ (N₁.arc j).e.edge) := by
    zun
    obtain ⟨-, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP₁ hNF hj
    exact ⟨hpe, hee, end6 hP₁ hNF hFne hj⟩
  zujzs
  have hNA : NFAt c.nmem ztwsx N₁ := hNT.nfAt
  zucvt

  obtain ⟨-, -, hTB, -⟩ := win_tab E hI
  zubwc
  zudni
  zufub
  set o := c.nreg wO with hod
  have hsj : OracleQ.sj N₁ o < N₁.arcs.length := NFLoc.seq_lt hNF ho
  obtain ⟨hr1, hr2, hr3, hr4⟩ := har
  obtain ⟨hpe, hee, he6⟩ := hpp _ hsj
  have hxr := key₁_range (Q := Qof P) he1 hpx
  -- 1. compare with the end of the located arc
  refine IRS.seq (K₂ := 11082) (cmpS_irs E hI he1 by_simp_all hpx
    by_simp_all h6x by_omega by_omega) ?_ |>.mono
    by_norm_num ztb
  rintro c₁ hI₁ - - ⟨b1, b2, k1, m1, a1⟩
  have k1' : ∀ r, ¬ WR r → bandOf r ∉ oracleBands → c₁.nreg r = c.nreg r := fun r hr hb =>
    k1 r hb (ne_of_wr hr (wr_sw (i := 3010) by_norm_num by_norm_num))
      (ne_of_wr hr (wr_sw (i := 3011) by_norm_num by_norm_num))
  have e1 : ∀ q, q = wO ∨ q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH ∨ q = wE1 ∨ q = kH ∨ q = wD ∨
      q = sw 3 → c₁.nreg q = c.nreg q := by
    zuco
    have hq' : zthod := by
      rcases hq with h | h | h | h | h | h | h | h | h <;> subst h <;>
        simp only [sw, wO, wA, wR, wEE, wEH, wE1, kH, wD, wC] <;> omega
    exact k1 q zttuh hq'.2.2.1 hq'.2.2.2
  have hEo : (ztgop : WPos) = (N₁.arc ztjkv).e := by
    rw [hr3, hr4]
  rw [hEo] at b1 b2
  -- 2. the successor if the key is the end
  zubke
  refine IRS.seq (K₂ := 11050) (eqS_irs hI₁ E.hK hNF by_grind
    by_grind by_grind
    by_grind by_grind b1 b2
    (by rw [e1 _ by_simp]; exact ⟨by_grind,
      by grind, by_grind,
      by grind⟩)) ?_ |>.mono by_norm_num (fun _ h => h)
  rintro c₂ hI₂ - - ⟨q1, q2, har2, k2, m2⟩
  set o' := c₂.nreg wO with ho'd
  have nA : ∀ q, ztgrt → ¬ ArcW q := by
    intro q hq; rcases hq with h | h | h | h <;> subst h <;>
      simp only [ArcW, wT, wA, wR, wEE, wEH, wL, wO, wE1, kH, wD, sw] <;> omega
  have e2 : ∀ q, ztgrt → c₂.nreg q = c.nreg q := fun q hq => by
    grind
  have eo1 : c₁.nreg wO = o := e1 _ by_simp
  rw [eo1] at q1 q2
  have hU : ∀ y : WPos, y.edge < M.W.n → ProperPos M zta P.n y →
      U₁ P J y = U₁ P J ztoj → M.key zta y = x₀ := by
    intro y hy hpy h
    have := key₁_range (Q := Qof P) hy hpy
    exact win_off_inj this.1 this.2 hxr.1 hxr.2 h
  have hsel : o' < N₁.arcs.length ∧
      (sideInArc ztzcu ztwzo x₀ ∨
        OracleQ.sk M zta N₁ o' = x₀) := by
    by_cases hp : U₁ P J ztoj < U₁ P J (N₁.arc ztjkv).e ∨
        U₁ P J (N₁.arc ztjkv).e < U₁ P J ztoj
    · rw [q1 hp]
      refine ⟨ho, arc_of_loc hFne hl1 hl2 fun h => ?_⟩
      have : U₁ P J (N₁.arc ztjkv).e = U₁ P J ztoj := by
        unfold U₁; exact congrArg _ h
      grind
    · push Not at hp
      rw [q2 (not_lt.2 hp.1) (not_lt.2 hp.2)]
      have heq := hU _ hee hpe (le_antisymm hp.1 hp.2)
      exact ⟨OracleQ.succP_lt ho, Or.inr (arc_of_loc' hP₁ hNF ho hFne heq)⟩
  obtain ⟨ho', hin⟩ := hsel
  obtain ⟨hr1', hr2', hr3', hr4'⟩ := har2
  have hsj' : OracleQ.sj N₁ o' < N₁.arcs.length := NFLoc.seq_lt hNF ho'
  obtain ⟨hpe', hee', he6'⟩ := hpp _ hsj'
  have a2 : ztbae := by
    rw [k2 _ (by simp only [ArcW, wT, wA, wR, wEE, wEH, wL, wO, ALLOC, sw]; omega), a1]
  have eE1 := e2 wE1 by_simp
  have ekH := e2 kH by_simp
  -- 3. compare with the end of the arc after the key
  refine IRS.seq (K₂ := 32) (cmpS_irs E hI₂ by_grind by_grind
    by_grind (by zuoow; omega) by_omega
    by_omega by_omega) ?_ |>.mono by_norm_num (fun _ h => h)
  rintro c₃ hI₃ - - ⟨b1', b2', k3, m3, a3⟩
  have hEo' : (⟨c₂.nreg wEE, c₂.nreg wEH⟩ : WPos) = (N₁.arc ztdfy).e := by
    zuoow
  rw [hEo', eE1, ekH] at b2'
  have e3 : ∀ q, (q = wD ∨ q = wEE ∨ q = wEH ∨ q = wA ∨ q = wR) → c₃.nreg q = c₂.nreg q := by
    zuco
    have hq' : zthod := by
      rcases hq with h | h | h | h | h <;> subst h <;>
        simp only [sw, wEE, wEH, wD, wC, wA, wR] <;> omega
    exact k3 q zttuh hq'.2.2.1 hq'.2.2.2
  -- 4. the decision
  refine (decS_irs hI₃ E.hK E.hM b2' (by rw [e3 wEE by_simp, hr3']; omega) E.hWn).mono
    by_norm_num ?_
  rintro c₄ ⟨hdec, k4, m4⟩
  rw [e3 wD by_simp, e2 wD by_simp, e3 wEE by_simp, hr3', e3 wEH by_simp, hr4'] at hdec
  have nD : ∀ q, (q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH) → ¬ DecW q := by
    intro q hq; rcases hq with h | h | h | h <;> subst h <;>
      simp only [DecW, wX, wE, wH, wDE, wPs, wA, wR, wEE, wEH, sw] <;> omega
  refine ⟨o', ho', ztfh, fun _ => ⟨hin, hdec⟩, fun h => absurd h hFne.ne_empty,
    fun r hr hw => ?_, by_grind⟩
  · rw [k4 _ ztkbf, e3 _ by_simp, hr1']
  · rw [k4 _ ztkbf, e3 _ by_simp, hr2']
  · rw [k4 _ ztkbf, e3 _ by_simp, hr3']
  · rw [k4 _ ztkbf, e3 _ by_simp, hr4']
  · have hnD : ¬ DecW r := by
      rintro (h | h | h | h | h) <;> subst h <;> apply hw
      · exact wr_wX
      · exact wr_wE
      · exact wr_wH
      · zulzy
      · zulzy
    have hnA : ¬ ArcW r := by
      rintro (h | h | h | h | h | h | h) <;> subst h <;> exact hw (wr_sw by_norm_num by_norm_num)
    rw [k4 r hnD, k3 r hr (ne_of_wr hw (wr_sw (i := 3010) by_norm_num by_norm_num))
      (ne_of_wr hw (wr_sw (i := 3011) by_norm_num by_norm_num)), k2 r hnA, k1' r hw hr]
