module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.UpPhase15
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.OracleQueryExec

namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SignK
open BuildNF (codeLe)
open SortL (seg)
@[expose] public section
def lvRegA : Stmt := block [.copyN 215000 210005, .copyN 215001 211010, .copyN 215002 211008]

/-- The arguments of the region procedure. -/
def lvRegB : Stmt :=
  block [.copyN 219200 215010, .copyN 219201 215012, .copyN 219202 211002, .copyN 219203 211004,
    .copyN 219204 211006, .copyN 219205 230001]

/-- The arguments of the extraction. -/
def lvRegC : Stmt :=
  block [.copyN 217000 210005, .copyN 217001 211010, .copyN 217002 211008,
    .copyN 217003 215010, .copyN 217004 215012, .copyN 217005 219210, .copyN 217006 219211]

/-- The table entry, the total, the next region. -/
def lvRegD : Stmt :=
  block [.addN 211020 211010 211010, .addN 211020 211020 211010, .addN 211020 211020 211009,
    .storeN 211020 217010, .addN 211020 211020 211014, .storeN 211020 217011,
    .addN 211020 211020 211014, .storeN 211020 217012,
    .addN 211012 211012 217011, .addN 211010 211010 211014]

/-- The largest length. -/
def lvRegE : Stmt := .ifLtN 211013 217011 (.instr (.copyN 211013 217011)) .skip

/-- **The body of the region loop.** -/
def lvBody (sH sR sX : Stmt) : Stmt :=
  .seq lvRegA (.seq sH (.seq lvRegB (.seq sR (.seq lvRegC (.seq sX (.seq lvRegE lvRegD))))))

/-- **The region loop.** -/
def lvLoop (sH sR sX : Stmt) : Stmt := .whileLtN 211010 211011 ztlqz

/-! ## The facts of a region -/

/-- The registers the region loop keeps. -/
def LvFixed (q : ℕ) : Prop :=
  (210000 ≤ q ∧ q ≤ 210005) ∨ (211000 ≤ q ∧ q ≤ 211009) ∨ (211014 ≤ q ∧ q ≤ 211017) ∨
    q = 230000 ∨ q = 230001

/-- **The math facts of a finished region** (the hypothesis of `LevelMathSpec`). -/
noncomputable def RegOK (P : Polygon) (L : List zte) (E : List ℕ) (reg : ℕ → Set Point)
    (γ₀ r : ℕ) (C : Chain) (NR : NF) (γR : ℕ) (Lx : List zte) : Prop :=
  open Classical in
  C.P = (regHost ztwkl (Qof P).n
      ztbaja r).poly (Qof P) ∧
    C.s = 0 ∧ C.m + 1 = C.P.n ∧
    IsCanonicalNF ztc zta NR γR regCap ∧ γ₀ ≤ γR ∧ γR ≤ γ₀ + 128 ∧
    {x | ∃ y ∈ Lx, x = (recOf y).toSet ztwiq zta} =
      Extract.kept ztcz ztxki ∧
    (Lx.map fun y => (recOf y).toSet ztwiq zta).Nodup ∧
    ztbaji ∧
    ∀ q, q < 2 * Lx.length →
      ∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
        OnArcKey zta ztbaja j ztdui

/-- **The memory facts of a finished region**: its table entry at `T + 3 r` (triples, length,
buckets), the triples and the buckets at or above `B`, below `A`. -/
def RegMem (m : ℕ → ℕ) (A T B : ℕ) (Q : Polygon) (N : NF) (r : ℕ) (Lx : List zte) :
    Prop :=
  m ztnpr = Lx.length ∧ B ≤ m ztjnb ∧ m ztjnb + 3 * Lx.length ≤ A ∧
    ChordListAt m (m ztjnb) Lx ∧ B ≤ m zteoi ∧
    m zteoi + 2 * Lx.length ≤ A ∧
    ∀ q, q < 2 * Lx.length → m (m zteoi + q) = keyBkt Q N ztdui

/-- The memory facts of a region survive a change of the memory at or above `A` outside the
table, and a larger bound. -/
theorem RegMem.transport {m m' : ℕ → ℕ} {A A' T B : ℕ} {Q : Polygon} {N : NF} {r : ℕ}
    {Lx : List zte} (h : RegMem m A T B Q N r Lx) (hTB : T + 3 * r + 3 ≤ B)
    (hm : ∀ a, (a < A ∧ (a < B → T + 3 * r ≤ a ∧ a < T + 3 * r + 3)) → m' a = m a)
    (hA : A ≤ A') : RegMem m' A' T B Q N r Lx := by
  zumt
  have e0 : ztskj := hm _ ⟨by_omega, fun _ => ⟨le_rfl, by_omega⟩⟩
  have e1 : m' _ = m ztnpr := hm _ by_omega
  have e2 : m' _ = m zteoi := hm _ by_omega
  refine ⟨by_omega, by_omega, by_omega, ?_, by_omega,
    by omega, fun q hq => ?_⟩
  · zujhv
    exact clAt_congr h4 by_grind
  grind

/-- A host description below `A` is robust. -/
theorem hostAt_robust {m : ℕ → ℕ} {B A : ℕ} {H : Host} (h : HostAt m B H)
    (hA : B + 3 * H.length + 1 ≤ A) : Robust A m (fun m => HostAt m B H) := by
  zubxa
  obtain ⟨h0, hi⟩ := h
  refine ⟨by_grind, fun i hi' => ?_⟩
  have := hi i hi'
  revert this
  rcases H.getD i _ with ⟨a, ℓ⟩ | ⟨⟨j⟩ | ⟨e, hh⟩⟩ <;> simp only <;> intro hh' <;>
    · grind

/-! ## Counted loops with the allocator -/
section loops
variable {P : Polygon} {W : ℕ}

/-- **A counted loop whose iterations allocate at most their steps.** -/
theorem forLoopA {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c → ∃ c' k, Exec P W body c c' k ∧ Inv ztl c' ∧ k ≤ Kb ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W ztfmn c c' k ∧ Inv N c' ∧ k ≤ ztkq * zthbl + 2 ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  induction hn : N - j generalizing j c with
  | zero =>
    zubaq

    zucq
    exact ⟨c, 2, .whileLtN_false by_omega hw, hc, by_omega, by_omega⟩
  | succ t ih =>
    zucq
    zufvj
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁, hA₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂, hA₂⟩ := ih hI₁ by_omega by_omega
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true by_omega e₁ e₂, hI', ?_, by_omega⟩
    zuewu
end loops

/-! ## The context and the invariant -/

/-- **The context of the region loop**: the configuration `c₁` after `lvPar`, the state
`(L, E)` of `Inv(λ)` and the region correspondence `reg` of `N = buildNF I Q L E`. -/
structure LvCtx (O : OracleIface) (P : Polygon) (W : ℕ) (c₁ : Config) (L : List zte)
    (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ) : Prop where
  good : GoodEnv P
  w3 : P.n + 3 ≤ W
  wh : hostWords P.n ≤ W
  setup : Robust ztfhb c₁.nmem
    (fun m => SetupAt m (c₁.nreg ztcpu) P.n ztfhb)
  holds : (gradeCtx O).holds P c₁.nmem ztyjb ztfhb
  cap : P.n - 1 ≤ (gradeCtx O).cap P c₁.nmem ztyjb
  h16 : 16 ≤ lam
  hlp : lam ≤ topGrade P.n
  hL : L ≠ []
  ok : ChordTriplesOK ztwiq zta L
  perm : E.Perm ztct
  sort : E.Pairwise ztbajl
  deg : (interiorModel zta).DegLe
    ztbajd 4
  wt : (interiorModel zta).Semigranular
    ztbajd
    ztxuo
  regs : Restore.NFRegs ztwiq zta
    ztbaja reg
  nf : NFWithin c₁.nmem (c₁.nreg 210005) ztfhb
    ztbaja
  r00 : c₁.nreg 210000 = lam
  r02 : c₁.nreg 211002 = nextLvl lam
  r04 : c₁.nreg 211004 = 2 ^ nextLvl lam
  r06 : c₁.nreg 211006 = 3 * 2 ^ ztwqe
  r07 : c₁.nreg 211007 = 2 ^ ztwnz
  r08 : c₁.nreg 211008 ≤ 1
  r08' : c₁.nreg 211008 = 1 ↔ Mountain.LeftInside zta
  r09 : c₁.nreg 211009 + 3 * ztkr = c₁.nreg ALLOC
  r14 : c₁.nreg 211014 = 1
  big : 3 * 2 ^ ztwqe + 129 ≤ P.n - 1
  big2 : 2 ^ ztwnz ≤ P.n - 1
  md : Robust ztfhb c₁.nmem
    (fun m => ModelDescAt m ztqkf zta ztwiq)
  mdA : c₁.nreg 210001 + 6 ≤ c₁.nreg 211009
  r03 : c₁.nreg 210003 = L.length
  lA : c₁.nreg 210002 + 3 * L.length ≤ c₁.nreg 211009
  lmem : Robust ztfhb c₁.nmem (fun m => ChordListAt m (c₁.nreg 210002) L)
  eA : c₁.nreg 210004 + 2 * L.length ≤ c₁.nreg 211009
  emem : Robust ztfhb c₁.nmem (fun m => seg m (c₁.nreg 210004) ztpu = E)

/-- **The environment** at every configuration that keeps the core registers and the memory
below the table, with the allocator at or above the table. -/
theorem LvCtx.envD {O : OracleIface} {P : Polygon} {W : ℕ} {c₁ : Config} {L : List zte}
    {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ} (h : LvCtx O P W c₁ L E reg lam) {c : Config}
    (h0 : c.nreg ztcpu = c₁.nreg ztcpu) (h1 : c.nreg ztbzv = c₁.nreg ztbzv)
    (hm : ∀ a, a < c₁.nreg 211009 → c.nmem a = c₁.nmem a) (hA : c₁.nreg 211009 ≤ c.nreg ALLOC) :
    EnvD ztsy P W c := by
  refine ⟨h.good, h.w3, h.wh, ?_, ?_, ?_⟩
  · zvmzn; exact setup_transport h.setup hm hA
  · zuwv
    exact (gradeCtx O).mono P _ _ _ _ hA
      ((gradeCtx O).local_ P c₁.nmem c.nmem _ _ by_simp_all h.holds)
  · rw [h1, gradeCtx_capLocal O P c₁.nmem c.nmem _ _ hm h.holds]; exact h.cap

/-- **The invariant of the region loop** after `j` regions (`Kb` bounds the steps of one
iteration). -/
def LvInv (_O : OracleIface) (P : Polygon) (W : ℕ) (c₁ : Config) (L : List zte)
    (E : List ℕ) (reg : ℕ → Set Point) (Kb j : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 211010 = j ∧ c.nreg 211011 = L.length + 1 ∧
    (∀ q, LvFixed q → c.nreg q = c₁.nreg q) ∧
    (∀ a, a < c₁.nreg 211009 → c.nmem a = c₁.nmem a) ∧
    (∀ a, a < c₁.nreg 211009 → c.rmem a = c₁.rmem a) ∧
    (∀ q, bandOf q ∉ drvBands → q ≠ ALLOC → c.nreg q = c₁.nreg q) ∧
    (∀ q, bandOf q ∉ drvBands → c.rreg q = c₁.rreg q) ∧ c.output = c₁.output ∧
    c₁.nreg ALLOC ≤ c.nreg ALLOC ∧ c.nreg ALLOC ≤ c₁.nreg ALLOC + j * Kb ∧
    ∃ (C : ℕ → Chain) (NR : ℕ → NF) (γR : ℕ → ℕ) (Lx : ℕ → List zte),
      c.nreg 211012 = ((List.range j).flatMap Lx).length ∧
      (∀ r, r < j → (Lx r).length ≤ c.nreg 211013) ∧
      (c.nreg 211013 = 0 ∨ ∃ r, r < j ∧ c.nreg 211013 = (Lx r).length) ∧
      ∀ r, r < j → RegOK P L E reg ztvmp r ztdyi ztvab ztwid ztdyq ∧
        RegMem c.nmem ztm ztfhb ztbmq zta
          ztbaja r ztdyq
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine
@[expose] public section
def HostMeets (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDownDrv}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 215002 ≤ 1 ∧
      ztxks ∧
      ∃ (L : List zte) (E : List ℕ), L ≠ [] ∧
        ChordTriplesOK ztwiq zta L ∧ E.Perm ztct ∧
        E.Pairwise ztbajk ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) 4 ∧
        NFWithin c.nmem ztghd ztm
          ztbaja ∧
        c.nreg 215001 < (BuildNF.buildNF ztwiq zta L E).nRegions)
    (fun P c c' =>
      ztbff ∧
      ∀ (L : List zte) (E : List ℕ), L ≠ [] →
        ChordTriplesOK ztwiq zta L → E.Perm ztct →
        E.Pairwise ztbajk →
        NFAt c.nmem ztghd ztbaja →
        let H := regHost ztzei (Qof P).n
          ztbaja ztdzj
        c.nreg ALLOC ≤ c'.nreg 215010 ∧ c'.nreg 215010 + 3 * H.length + 1 ≤ c'.nreg ALLOC ∧
          HostAt c'.nmem ztmfe H ∧ c'.nreg 215011 = H.length ∧
          c'.nreg 215012 = (H.pts (Qof P).n).length)
    ztqne
theorem hostMeets_of (h : HostRamSpec) : ∃ s κ, HostMeets s κ := h

/-- The `Meets` statement of `RegionSpec` for one program. -/
def RegMeets (O : OracleIface) (s : Stmt) (κ : ℕ) : Prop :=
  Meets s drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztdzl ztm ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem ztdzl ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran ztdzk ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta ztdzk ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem ztdzl ∧
      ∃ H : Host, Robust ztm c.nmem ztfbx ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly zta).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (fun P c c' =>
      ztbfg ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P ztdo c'.nmem ztfgh ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem ztqhv H → C.P = H.poly zta →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust ztdo c'.nmem
          (fun m => m ztfgh = 0 ∧
            ChainDescAt m ztcyy zta H C ∧
            m ztcyy = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem ztmfg ztdo N ∧
          IsCanonicalNF ztc zta N ztmfh regCap)
    ztbanw
theorem regMeets_of {O : OracleIface} (h : RegionSpec O) : ∃ s κ, RegMeets O s κ := h

/-- The `Meets` statement of `ExtractRamSpec` for one program. -/
def ExtMeets (s : Stmt) (κ : ℕ) : Prop :=
  Meets s {bDownDrv, bSign, bLocate, bBuild, bSort}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ c.nreg 217002 ≤ 1 ∧
      ztxkt ∧
      ∃ (L : List zte) (E : List ℕ) (C : Chain) (NR : NF), L ≠ [] ∧
        ChordTriplesOK ztwiq zta L ∧ E.Perm ztct ∧
        E.Pairwise ztbajk ∧
        (interiorModel zta).DegLe
          ((BuildNF.buildNF ztwiq zta L E).F ztwiq
            zta) 4 ∧
        NFWithin c.nmem zthup ztm
          ztbaja ∧
        c.nreg 217001 < (BuildNF.buildNF ztwiq zta L E).nRegions ∧
        Robust ztm c.nmem (fun m => HostAt m ztmga
          (regHost ztgm (Qof P).n
            ztbaja ztos)) ∧
        c.nreg 217003 + 3 * (regHost ztgm (Qof P).n
            ztbaja ztos).length + 1 ≤
          c.nreg ALLOC ∧
        c.nreg 217004 = ((regHost ztgm (Qof P).n
          ztbaja ztos).pts
            (Qof P).n).length ∧
        C.P = (regHost ztgm (Qof P).n
          ztbaja ztos).poly (Qof P) ∧
        C.s = 0 ∧ C.m + 1 = C.P.n ∧
        ModelDescWF P ztm c.nmem ztghe ∧
        Robust ztm c.nmem (fun m => ModelDescAt m ztghe zta
          ztc) ∧
        Robust ztm c.nmem (fun m => ChainDescAt m ztlkt zta
          (regHost ztgm (Qof P).n
            ztbaja ztos) C) ∧
        NFWithin c.nmem ztchk ztm NR ∧ IsNF ztc zta NR)
    (fun P c c' =>
      ztcbj ∧
      ∀ (L : List zte) (E : List ℕ) (C : Chain) (NR : NF) (reg : ℕ → Set Point),
        L ≠ [] → ChordTriplesOK ztwiq zta L →
        E.Perm ztct →
        E.Pairwise ztbajk →
        NFAt c.nmem zthup ztbaja →
        Restore.NFRegs ztwiq zta
          ztbaja reg →
        C.P = (regHost ztgm (Qof P).n
          ztbaja ztos).poly (Qof P) →
        C.s = 0 → C.m + 1 = C.P.n → NFAt c.nmem ztchk NR →
        IsNF ztc zta NR →
        ∃ Lx : List zte,
          c.nreg ALLOC ≤ c'.nreg 217010 ∧ c'.nreg 217010 + 3 * Lx.length ≤ c'.nreg ALLOC ∧
          c.nreg ALLOC ≤ c'.nreg 217012 ∧ c'.nreg 217012 + 2 * Lx.length ≤ c'.nreg ALLOC ∧
          c'.nreg 217011 = Lx.length ∧ ChordListAt c'.nmem ztqha Lx ∧
          {x | ∃ y ∈ Lx, x = (recOf y).toSet ztwiq zta} =
            Extract.kept ztbaio ztxki ∧
          (Lx.map fun y => (recOf y).toSet ztwiq zta).Nodup ∧
          ztbaji ∧
          ∀ q, q < 2 * Lx.length →
            c'.nmem ztlkg = keyBkt zta
              ztbaja ztdui ∧
            ∃ j ∈ ((BuildNF.buildNF ztwiq zta L E).region
                ztos).arcs,
              OnArcKey zta ztbaja j
                ztdui)
    ztbanv
theorem extMeets_of (h : ExtractRamSpec) : ∃ s κ, ExtMeets s κ := h
open Machine.Stmt Programs SignK BuildRam
section exec
variable {P : Polygon} {W : ℕ}
def BregA (r : ℕ) : Bool := decide (215000 ≤ r ∧ r ≤ 215002)
theorem wr_lvRegA : wr BregA lvRegA = true := by_decide
def BregB (r : ℕ) : Bool := decide (219200 ≤ r ∧ r ≤ 219205)
theorem wr_lvRegB : wr BregB lvRegB = true := by_decide
def BregC (r : ℕ) : Bool := decide (217000 ≤ r ∧ r ≤ 217006)
theorem wr_lvRegC : wr BregC lvRegC = true := by_decide
def BregE (r : ℕ) : Bool := decide (r = 211013)
theorem wr_lvRegE : wr BregE lvRegE = true := by_decide
def BregD (r : ℕ) : Bool := decide (r = 211020 ∨ r = 211012 ∨ r = 211010)
theorem wrM_lvRegD : wrM BregD lvRegD = true := by_decide
variable (c : Config)
theorem lvRegA_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegA c c' k ∧ k = 3 ∧ c'.nreg 215000 = c.nreg 210005 ∧
      c'.nreg 215001 = c.nreg 211010 ∧ c'.nreg 215002 = c.nreg 211008 := by
  unfold lvRegA
  exec_block
  simp
theorem lvRegB_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegB c c' k ∧ k = 6 ∧ c'.nreg 219200 = c.nreg 215010 ∧
      c'.nreg 219201 = c.nreg 215012 ∧ c'.nreg 219202 = c.nreg 211002 ∧
      c'.nreg 219203 = c.nreg 211004 ∧ c'.nreg 219204 = c.nreg 211006 ∧
      c'.nreg 219205 = c.nreg 230001 := by
  unfold lvRegB
  exec_block
  simp
theorem lvRegC_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegC c c' k ∧ k = 7 ∧ c'.nreg 217000 = c.nreg 210005 ∧
      c'.nreg 217001 = c.nreg 211010 ∧ c'.nreg 217002 = c.nreg 211008 ∧
      c'.nreg 217003 = c.nreg 215010 ∧ c'.nreg 217004 = c.nreg 215012 ∧
      c'.nreg 217005 = c.nreg 219210 ∧ c'.nreg 217006 = c.nreg 219211 := by
  unfold lvRegC
  exec_block
  simp
theorem lvRegE_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W lvRegE c c' k ∧ k ≤ 3 ∧
      c'.nreg 211013 = max ztqhr (c.nreg 217011) := by
  unfold lvRegE
  by_cases h : c.nreg 211013 < c.nreg 217011
  · have e := Exec.copyN (P := P) hw 211013 217011
    refine ⟨_, _, .ifLtN_true h e, by_omega, ?_⟩
    zudbz
  · exact ⟨_, _, .ifLtN_false h ztjd, by_omega, by_omega⟩
theorem lvRegD_exec (hw : WordsBounded W c) {T j p ℓ b tot : ℕ}
    (h09 : c.nreg 211009 = T) (h10 : c.nreg 211010 = j) (h14 : c.nreg 211014 = 1)
    (h17 : c.nreg 217010 = p) (h11 : c.nreg 217011 = ℓ) (h12 : c.nreg 217012 = b)
    (ht : c.nreg 211012 = tot) (hW1 : T + 3 * j + 2 ≤ W) (hW2 : tot + ℓ ≤ W) (hW3 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lvRegD c c' k ∧ k = 10 ∧ c'.nreg 211012 = tot + ℓ ∧
      c'.nreg 211010 = j + 1 ∧ c'.nmem ztctp = p ∧ c'.nmem zteog = ℓ ∧
      c'.nmem zteoh = b ∧
      (∀ a, ztgez → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have wp := hw.1 217010
  have wl := hw.1 217011
  have wb := hw.1 217012
  unfold lvRegD
  exec_block
  all_goals try (config_simp; (try simp only [h09, h10, h14, h17, h11, h12, ht]); omega)
  refine ztfwv
  · simp_all
  · simp_all
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; grind
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; grind
  · config_simp; simp only [h09, h10, h14, h17, h11, h12, Machine.upd_apply]; grind
  · intro a ha; config_simp; simp only [h09, h10, h14, Machine.upd_apply]
    grind
  · config_simp
  · config_simp
  simp
end exec

/-! ## Arithmetic of the level -/
theorem gradeGran_le_nat (g : ℕ) : gradeGran g ≤ 1201 * 2 ^ Cost.ceilBeta g := by
  zulhg
  exact_mod_cast h

/-- The targets of the region procedure. -/
theorem g0_facts (μ : ℕ) :
    2 * gradeGran μ ≤ 3 * 2 ^ ztblx ∧ 128 ≤ 3 * 2 ^ ztblx ∧
      3 * 2 ^ ztblx ≤ 4096 * 2 ^ Cost.ceilBeta μ := by
  have h := gradeGran_le_nat μ
  grind

/-- The merge grade is served by the up-phase data. -/
theorem mu_le_grades {n x lam : ℕ} (hcap : n - 1 ≤ 2 ^ ztoka) (h16 : 16 ≤ lam)
    (hlp : lam ≤ topGrade n) : nextLvl lam ≤ x := by
  have h1 := nextLvl_lt h16
  have h2 : topGrade n ≤ x - 1 := Nat.clog_le_of_le_pow hcap
  omega

/-- The chain of a host with at least three points. -/
noncomputable def hostChainOf (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length) : Chain :=
  ⟨H.poly Q, 0, (H.pts Q.n).length - 1, by_omega,
    by zuodx; omega⟩
variable (Q : Polygon) (H : Host) (h : 3 ≤ (H.pts Q.n).length)
theorem hostChainOf_P :
    (hostChainOf Q H h).P = H.poly Q := rfl
theorem hostChainOf_s :
    (hostChainOf Q H h).s = 0 := rfl
theorem hostChainOf_m :
    (hostChainOf Q H h).m + 1 = (hostChainOf Q H h).P.n := by
  show (H.pts Q.n).length - 1 + 1 = (H.poly Q).n
  zuodx; omega

/-- **The chords of a region map** (Lemma 2.3). -/
theorem nch_le {Q : Polygon} {C : Chain} (hP : C.P.Simple) {N : NF} {γ γ₀ μ : ℕ}
    (hc : IsCanonicalNF ztc Q N γ regCap) (hγ : γ₀ ≤ γ)
    (hm : C.m + 1 ≤ 10 * 2 ^ μ + 8) (hγ₀ : γ₀ = 3 * 2 ^ ztblx) :
    N.chords.length ≤ lvNch μ := by
  obtain ⟨hNF, hdeg, hgran, -⟩ := hc
  have h23 := DownMath.lemma23_chain hP hNF.1 hdeg hgran
  rw [Gran.ncard_F hNF] at h23
  have h2 : N.nChords * ztbfd ≤ N.nChords * ztgj := Nat.mul_le_mul_left _ by_omega
  have h3 : 140 * ztevh * ztyw ≤ 140 * ztevh * ztdey :=
    Nat.mul_le_mul_left _ by_omega
  unfold lvNch
  rw [← hγ₀, Nat.le_div_iff_mul_le by_omega]
  exact le_trans h2 (le_trans h23 h3)
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}
theorem nRegions_bnf {M : Model} {Q : Polygon} {L : List zte} {E : List ℕ} :
    (BuildNF.buildNF M Q L E).nRegions = L.length + 1 := by
  zudvx
open Classical in
/-- **The host RAM of region `j`.** -/
theorem callH {sH : Stmt} {κH : ℕ} (hH : HostMeets sH κH) (c : Config) (hw : WordsBounded W c)
    {L : List zte} {E : List ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hL : L ≠ [])
    (hok : ChordTriplesOK ztwiq zta L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztbajl)
    (hdeg : (interiorModel zta).DegLe
      ztbajd 4)
    (hnf : NFWithin c.nmem ztghd ztm
      ztbaja)
    (hli : c.nreg 215002 ≤ 1) (hli' : c.nreg 215002 = 1 ↔ Mountain.LeftInside zta)
    {j : ℕ} (hj0 : c.nreg 215001 = j) (hj : j < L.length + 1)
    (hroom : c.nreg ALLOC + κH ≤ W) :
    ∃ c' k, Exec P W sH c c' k ∧ k ≤ κH ∧ Frame {bDownDrv} c c' k ∧
      ztbff ∧
      c.nreg ALLOC ≤ c'.nreg 215010 ∧
      c'.nreg 215010 + 3 * (regHost ztwkl (Qof P).n
        ztbaja j).length + 1 ≤ c'.nreg ALLOC ∧
      HostAt c'.nmem ztmfe (regHost ztwkl (Qof P).n
        ztbaja j) ∧
      c'.nreg 215012 = ((regHost ztwkl (Qof P).n
        ztbaja j).pts (Qof P).n).length := by
  obtain ⟨c', k, ex, hk, ⟨hkeep, hpost⟩, hfr⟩ := hH P W c hw
    ⟨hG, hWh, hli, hli', L, E, hL, hok, hperm, hsort, hdeg, hnf,
      by zuojk; exact hj⟩ hroom
  have hdec : decide ztfqe = decide ztzce :=
    decide_eq_decide.mpr hli'
  obtain ⟨h1, h2, h3, -, h5⟩ := hpost L E hL hok hperm hsort hnf.nfAt
  rw [hdec, hj0] at h2 h3 h5
  exact ⟨c', k, ex, hk, hfr, hkeep, h1, h2, h3, h5⟩

/-- **The region procedure of region `j`.** -/
theorem callR {O : OracleIface} {sR : Stmt} {κR : ℕ} (hR : RegMeets O sR κR) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {HB μ γ₀ g : ℕ} {H : Host}
    (h00 : c.nreg 219200 = HB) (h01 : c.nreg 219201 = (H.pts (Qof P).n).length)
    (h02 : c.nreg 219202 = μ) (h03 : c.nreg 219203 = 2 ^ μ) (h04 : c.nreg 219204 = γ₀)
    (h05 : c.nreg 219205 = g)
    (hX : (gradeCtx O).holds P c.nmem g ztm) (h7 : 7 ≤ μ) (hμg : μ ≤ c.nmem g)
    (hg0 : 2 * gradeGran μ ≤ γ₀) (hg1 : 128 ≤ γ₀) (hg2 : γ₀ ≤ 4096 * 2 ^ Cost.ceilBeta μ)
    (hcap : γ₀ + 129 ≤ (gradeCtx O).cap P c.nmem g)
    (hHA : Robust ztm c.nmem ztesn)
    (hHB : HB + 3 * H.length + 1 ≤ c.nreg ALLOC) (h20 : H.length ≤ 20)
    (hwf : HostWF (Qof P).n H) (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly zta).Simple)
    (h3 : 3 ≤ (H.pts (Qof P).n).length) (hrun : ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * 2 ^ μ)
    (hroom : c.nreg ALLOC + κR * ztud ≤ W) :
    ∃ c' k, Exec P W sR c c' k ∧ k ≤ κR * ztud ∧ Frame drvBands c c' k ∧
      ztbfg ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      γ₀ ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ γ₀ + 128 ∧
      ModelDescWF P ztdo c'.nmem ztfgh ∧
      Robust ztdo c'.nmem
          (fun m => m ztfgh = 0 ∧
            ChainDescAt m ztcyy zta H ztyfc ∧
            m ztcyy = HB) ∧
        ∃ N, NFWithin c'.nmem ztmfg ztdo N ∧
          IsCanonicalNF (chainModel ztyfc) zta N ztmfh
            regCap := by
  obtain ⟨c', k, ex, hk, ⟨hkeep, a10, a11, a12, a12', hwfd, hpost⟩, hfr⟩ := hR P W c hw
    ⟨hG, hWh, by_simp_all, by_omega, by_simp_all,
      by simp_all, by_simp_all, by_omega,
      by simp_all, by_simp_all,
      H, by_simp_all, by_omega, h20, hwf, hreg, hsimp, h01,
      by omega, by_grind⟩
    by_simp_all
  have hk' : k ≤ κR * ztud := by
    grind
  obtain ⟨hrob, N, hN, hc⟩ := hpost H ztyfc (by rw [h00]; exact hHA.holds)
    rfl rfl (hostChainOf_m _ _ h3)
  grind
open Classical in
/-- **The extraction of region `j`.** -/
theorem callX {sX : Stmt} {κX : ℕ} (hX : ExtMeets sX κX) (c : Config) (hw : WordsBounded W c)
    {L : List zte} {E : List ℕ} {reg : ℕ → Set Point} (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hL : L ≠ [])
    (hok : ChordTriplesOK ztwiq zta L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztbajl)
    (hdeg : (interiorModel zta).DegLe
      ztbajd 4)
    (hregs : Restore.NFRegs ztwiq zta
      ztbaja reg)
    (hnf : NFWithin c.nmem zthup ztm
      ztbaja)
    (hli : c.nreg 217002 ≤ 1) (hli' : c.nreg 217002 = 1 ↔ Mountain.LeftInside zta)
    {j HB MD : ℕ} (hj0 : c.nreg 217001 = j) (hj : j < L.length + 1)
    (h03 : c.nreg 217003 = HB) (h05 : c.nreg 217005 = MD)
    (hHA : Robust ztm c.nmem (fun m => HostAt m HB
      (regHost ztwkl (Qof P).n
        ztbaja j)))
    (hHB : HB + 3 * (regHost ztwkl (Qof P).n
        ztbaja j).length + 1 ≤ c.nreg ALLOC)
    (h04 : c.nreg 217004 = ((regHost ztwkl (Qof P).n
        ztbaja j).pts (Qof P).n).length)
    {C : Chain} (hCP : C.P = (regHost ztwkl (Qof P).n
        ztbaja j).poly (Qof P))
    (hCs : C.s = 0) (hCm : C.m + 1 = C.P.n)
    (hmwf : ModelDescWF P ztm c.nmem MD)
    (hmd : Robust ztm c.nmem (fun m => m MD = 0 ∧
      ChainDescAt m ztki zta (regHost ztwkl (Qof P).n
        ztbaja j) C ∧ m (MD + 1) = HB))
    {NR : NF} (hNR : NFWithin c.nmem ztchk ztm NR)
    (hNRi : IsNF ztc zta NR)
    (hroom : c.nreg ALLOC + κX * ztnni ≤ W) :
    ∃ c' k, Exec P W sX c c' k ∧ k ≤ κX * ztnni ∧
      Frame {bDownDrv, bSign, bLocate, bBuild, bSort} c c' k ∧
      ztcbj ∧
      ∃ Lx : List zte,
          c.nreg ALLOC ≤ c'.nreg 217010 ∧ c'.nreg 217010 + 3 * Lx.length ≤ c'.nreg ALLOC ∧
          c.nreg ALLOC ≤ c'.nreg 217012 ∧ c'.nreg 217012 + 2 * Lx.length ≤ c'.nreg ALLOC ∧
          c'.nreg 217011 = Lx.length ∧ ChordListAt c'.nmem ztqha Lx ∧
          {x | ∃ y ∈ Lx, x = (recOf y).toSet ztwiq zta} =
            Extract.kept (reg j) ztxki ∧
          (Lx.map fun y => (recOf y).toSet ztwiq zta).Nodup ∧
          ztbaji ∧
          ∀ q, q < 2 * Lx.length →
            c'.nmem ztlkg = keyBkt zta
              ztbaja ztdui ∧
            ∃ j' ∈ ((BuildNF.buildNF ztwiq zta L E).region j).arcs,
              OnArcKey zta ztbaja j'
                ztdui := by
  have hdec : decide ztlks = decide ztzce :=
    decide_eq_decide.mpr hli'
  have hmdA : Robust ztm c.nmem (fun m => ModelDescAt m MD zta ztc) :=
    fun m' hm' => Or.inl ⟨(hmd m' hm').1, _, C, (hmd m' hm').2.1, rfl⟩
  have hcd : Robust ztm c.nmem (fun m => ChainDescAt m ztki zta
      (regHost ztwkl (Qof P).n
        ztbaja j) C) :=
    fun m' hm' => (hmd m' hm').2.1
  have hNR0 : ztyyl := hNR.nfAt.1
  obtain ⟨c', k, ex, hk, ⟨hkeep, hpost⟩, hfr⟩ := hX P W c hw
    ⟨hG, hWh, hli, hli', L, E, C, NR, hL, hok, hperm, hsort, hdeg, hnf,
      by zuojk; exact hj, by_simp_all,
      by simp_all, by_simp_all,
      by simp_all, hCs, hCm, by_simp_all, by_simp_all,
      by simp_all, hNR, hNRi⟩
    by_simp_all
  have hk' : k ≤ κX * ztnni := by
    have : k ≤ κX * ztxdv := hk
    rwa [hNR0] at this
  obtain ⟨Lx, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩ := hpost L E C NR reg hL hok hperm hsort
    hnf.nfAt hregs (by rw [hdec, hj0]; omega) hCs hCm hNR.nfAt hNRi
  rw [hj0] at x7 x10
  exact ⟨c', k, ex, hk', hfr, hkeep, Lx, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10⟩
theorem len_le_of_kept {α : Type*} {Lx : List α} {f : α → Set Point}
    {S F : Set ztf} (hS : {x | ∃ y ∈ Lx, x = f y} = S) (hnd : (Lx.map f).Nodup)
    (hSF : S ⊆ F) (hF : F.Finite) : Lx.length ≤ F.ncard := by
  classical
  have e : {x | ∃ y ∈ Lx, x = f y} = ((Lx.map f).toFinset : Set ztf) := by
    ext x; simp [eq_comm]
  have h1 : ({x | ∃ y ∈ Lx, x = f y} : Set ztf).ncard = Lx.length := by
    rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← h1, hS]
  exact Set.ncard_le_ncard hSF hF

/-- **The kept list of a region is short** (Lemma 2.3). -/
theorem regOK_len {P : Polygon} {L : List zte} {E : List ℕ} {reg : ℕ → Set Point}
    {r μ : ℕ} {C : Chain} {NR : NF} {γR : ℕ} {Lx : List zte}
    (h : RegOK P L E reg (3 * 2 ^ ztblx) r C NR γR Lx) (hP : C.P.Simple)
    (hm : C.m + 1 ≤ 10 * 2 ^ μ + 8) : Lx.length ≤ lvNch μ := by
  obtain ⟨-, -, -, hc, hγ, -, hk, hnd, -, -⟩ := h
  have h1 := nch_le hP hc hγ hm rfl
  have hF : (NR.F ztc zta).Finite := hc.1.1.1
  have h2 := len_le_of_kept hk hnd ztdoj hF
  rw [Gran.ncard_F hc.1] at h2
  exact h2.trans h1
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}
open Classical in
set_option maxHeartbeats 8000000 in
/-- **One iteration of the region loop.** -/
theorem lvBody_exec {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hH : HostMeets sH κH) (hR : RegMeets O sR κR) (hX : ExtMeets sX κX)
    (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    {c₁ : Config} {L : List zte} {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ}
    (ctx : LvCtx O P W c₁ L E reg lam) {Kb : ℕ}
    (hKb : 30 + κH + κR * ztwuz + κX * ztxoh +
      lvNch ztmc ≤ Kb)
    (hroom : c₁.nreg ALLOC + ztkr * Kb ≤ W)
    {j : ℕ} {c : Config} (hj : j < L.length + 1) (hinv : LvInv O P W c₁ L E reg Kb j c) :
    ∃ c' k, Exec P W ztlqz c c' k ∧ LvInv O P W c₁ L E reg Kb ztl c' ∧
      k ≤ Kb ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, h10, h11, hfix, hmem, hrmem, hoth, hroth, hout, hA1, hA2, C, NR, γR, Lx, htot, hMx,
    hM0, hdat⟩ := hinv
  set Q := Qof P with hQ
  zugyi
  set T := c₁.nreg 211009 with hT
  set A₁ := c₁.nreg ALLOC with hA₁
  set μ := nextLvl lam with hμ
  set γ₀ := 3 * 2 ^ ztblx with hγ₀
  have hT9 := ctx.r09
  have fx := hfix
  have f05 := fx 210005 ztbzn
  have f02 := fx 211002 ztbzn
  have f04 := fx 211004 ztbzn
  have f06 := fx 211006 ztbzn
  have f08 := fx 211008 ztbzn
  have f09 := fx 211009 ztbzn
  have f14 := fx 211014 ztbzn
  have f31 := fx 230001 ztbzn
  have f30 := fx 230000 ztbzn
  have hjr : j < N.nRegions := by rw [nRegions_bnf]; exact hj
  have hjK : ztl * Kb ≤ ztkr * Kb := Nat.mul_le_mul_right _ by_omega
  have hjK' : ztl * Kb = j * Kb + Kb := by_ring
  -- the math of region `j`
  obtain ⟨hHwf, hHreg, hHsimp, -, -, -, -⟩ :=
    hR1 P L E reg j ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs hjr
  have hsz := (hLM P L E reg lam ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.wt
    ctx.regs).1
  obtain ⟨hH20, hrun, hpt3, hpt10⟩ := hsz j hjr
  set H := regHost ztbahl Q.n N j with hHdef
  -- A: the arguments of the host RAM
  obtain ⟨cA, kA, eA, hkA, a00, a01, a02⟩ := lvRegA_exec (P := P) c hw
  have gA := exec_frameB eA wr_lvRegA
  have hwA := eA.wb_right
  have AA : cA.nreg ALLOC = c.nreg ALLOC := gA.1 _ by_decide
  have hnfA : NFWithin cA.nmem (cA.nreg 215000) (cA.nreg ALLOC) N := by
    rw [a00, f05, gA.2.2.1, AA]
    exact (ctx.nf.transport hmem).mono by_omega
  -- H: the host
  obtain ⟨cH, kH, eH, hkH, frH, keepH, b10, b10', hHA, b12⟩ := callH hH cA hwA ctx.good ctx.wh
    ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg hnfA (by zuojl; exact ctx.r08)
    (by zuojl; exact ctx.r08') by_omega hj by_omega
  have hwH := eH.wb_right
  have AH := frH.2.2.2.2.2.2
  have AH' := frH.2.2.2.2.2.1
  set HB := cH.nreg 215010 with hHB
  -- B: the arguments of the region procedure
  obtain ⟨cB, kB, eB, hkB, d00, d01, d02, d03, d04, d05⟩ := lvRegB_exec (P := P) cH hwH
  have gB := exec_frameB eB wr_lvRegB
  have hwB := eB.wb_right
  have AB : cB.nreg ALLOC = cH.nreg ALLOC := gB.1 _ by_decide
  have kHq :=
    fun q hq hr => (keepH q hq hr).trans (gA.1 q (by
      zunka; omega))
  have core :=
    fun q hq hA => (frH.1 q hq hA).trans (gA.1 q (by
      zuggw
      zunka; omega))
  have mB : ∀ a, a < c.nreg ALLOC → cB.nmem a = c.nmem a := fun a ha => by
    rw [gB.2.2.1, frH.2.2.1 a by_omega, gA.2.2.1]
  have envB : EnvD _ P W cB := ctx.envD
    (by rw [show coreReg 0 = 230000 from rfl, gB.1 _ by_decide, core _ by_decide by_decide]
        omega)
    (by rw [show coreReg 1 = 230001 from rfl, gB.1 _ by_decide, core _ by_decide by_decide]
        omega)
    (fun a ha => (mB a by_omega).trans ztoaw) by_omega
  have g31 : cB.nreg 219205 = c₁.nreg ztbzv := by
    rw [d05, core _ by_decide by_decide]; exact f31
  have hXB : (gradeCtx O).holds P cB.nmem ztyjb ztvkr := by
    have := envB.2.2.2.2.1
    rwa [gB.1 _ by_decide, core _ by_decide by_decide, show coreReg 1 = 230001 from rfl,
      f31] at this
  have hcapB : P.n - 1 ≤ (gradeCtx O).cap P cB.nmem ztyjb := by
    have := envB.2.2.2.2.2
    rwa [gB.1 _ by_decide, core _ by_decide by_decide, show coreReg 1 = 230001 from rfl,
      f31] at this
  have hHrob : Robust ztvkr cB.nmem ztesn := by
    rw [AB, gB.2.2.1]; exact hostAt_robust hHA b10'
  have hjKb : c.nreg ALLOC + Kb ≤ W := by
    omega
  have hroomR : cB.nreg ALLOC + κR * ztud ≤ W := by
    omega
  -- R: the region procedure
  obtain ⟨cR, kR, eR, hkR, frR, keepR, e10, e11, e12, e12', hmwf, hmd, NRj, hNRj, hcj⟩ :=
    callR hR cB hwB ctx.good ctx.wh (HB := HB) (H := H) d00 (by rw [d01, b12])
      (by rw [d02, kHq _ by_decide by_decide, f02]; exact ctx.r02)
      (by rw [d03, kHq _ by_decide by_decide, f04]; exact ctx.r04)
      (by rw [d04, kHq _ by_decide by_decide, f06]; exact ctx.r06) g31 hXB
      (by have := nextLvl_lt ctx.h16; unfold nextLvl at this ⊢; omega)
      (mu_le_grades hcapB ctx.h16 ctx.hlp) (g0_facts μ).1 (g0_facts μ).2.1 (g0_facts μ).2.2
      (le_trans ctx.big hcapB) hHrob (by rw [AB]; omega) hH20 hHwf hHreg hHsimp hpt3
      hrun hroomR
  have hwR := eR.wb_right
  have hkR' : kR ≤ κR * ztud := hkR
  have AR := frR.2.2.2.2.2.2
  have AR' := frR.2.2.2.2.2.1
  have kRq := fun q hq hr hb => (keepR q hq hr).trans (gB.1 q (by
        simp only [BregB, decide_eq_false_iff_not]; omega))
  -- C: the arguments of the extraction
  obtain ⟨cC, kC, eC, hkC, x00, x01, x02, x03, x04, x05, x06⟩ := lvRegC_exec (P := P) cR hwR
  have gC := exec_frameB eC wr_lvRegC
  have hwC := eC.wb_right
  have AC : cC.nreg ALLOC = cR.nreg ALLOC := gC.1 _ by_decide
  have mC : ∀ a, a < c.nreg ALLOC → cC.nmem a = c.nmem a := fun a ha => by
    rw [gC.2.2.1, frR.2.2.1 a by_omega, mB a ha]
  have hnfC : NFWithin cC.nmem (cC.nreg 217000) ztvks N := by
    rw [x00, kRq _ by_decide by_decide by_decide, kHq _ by_decide by_decide, f05]
    exact ((ctx.nf.transport fun a ha => (mC a by_omega).trans ztoaw).mono by_omega)
  have hHrobC : Robust ztvks cC.nmem ztesn := by
    rw [AC, gC.2.2.1]; exact hHrob.frame frR
  have hpt : (hostChainOf Q H hpt3).m + 1 ≤ 10 * 2 ^ μ + 8 := by
    rw [hostChainOf_m]; show (H.poly Q).n ≤ _; zuodx; omega
  have hnch := nch_le hHsimp hcj e12 hpt rfl
  have hroomX : cC.nreg ALLOC + κX * zttao ≤ W := by
    have e1 : cC.nreg ALLOC ≤ c.nreg ALLOC + κH + κR * ztud := by
      omega
    have e2 : κX * zttao ≤ κX * zthyt :=
      Nat.mul_le_mul_left _ by_omega
    omega
  -- X: the extraction
  obtain ⟨cX, kX, eX, hkX, frX, keepX, Lj, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ :=
    callX hX cC hwC ctx.good ctx.wh ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs hnfC
      (by zunfb
          exact ctx.r08)
      (by zunfb
          exact ctx.r08')
      (by rw [x01, kRq _ by_decide by_decide by_decide, kHq _ by_decide by_decide, h10])
      hj (by rw [x03, kRq _ by_decide by_decide by_decide]) x05 hHrobC
      by_omega (by rw [x04, kRq _ by_decide by_decide by_decide]; omega)
      (hostChainOf_P _ _ hpt3) (hostChainOf_s _ _ hpt3) (hostChainOf_m _ _ hpt3)
      ztlgm ztlgm
      (by rw [x06, AC, gC.2.2.1]; omega) hcj.1 hroomX
  have hwX := eX.wb_right
  have AX := frX.2.2.2.2.2.2
  have AX' := frX.2.2.2.2.2.1
  have kXq : ∀ q, bandOf q = bDownDrv → q < 215000 → cX.nreg q = c.nreg q := fun q hq hr => by
    rw [keepX q hq by_omega, gC.1 q ztfbs,
      kRq q hq by_omega by_omega, kHq q hq by_omega]
  -- the length of the new kept list
  have hLj : Lj.length ≤ lvNch μ := by
    have h2 := len_le_of_kept y7 y8 ztdoj hcj.1.1.1
    rw [Gran.ncard_F hcj.1] at h2
    exact h2.trans hnch
  have hlen_r : ∀ r, r < j → (Lx r).length ≤ lvNch μ := by
    zuz
    have hrr : ztsll := by_omega
    obtain ⟨hok_r, -⟩ := hdat r hr
    have hok_r' := hok_r
    obtain ⟨hCP, -, hCm, -⟩ := hok_r'
    have simp_r := (hR1 P L E reg r ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs
      hrr).2.2.1
    have sz := (hsz r hrr).2.2.2
    rw [ctx.r06] at hok_r
    refine regOK_len hok_r (by zuody; omega) ?_
    rw [hCm, hCP, DownMath.host_poly_n]; exact sz
  have htot_le : ((List.range j).flatMap Lx).length ≤ j * lvNch μ := by
    zugtt
    have := List.sum_le_length_nsmul _ _
      (fun x hx => by
        zufyz
        exact hlen_r r (List.mem_range.1 hr))
    zujpk
  -- E: the largest length
  obtain ⟨cE, kE, eE, hkE, z13⟩ := lvRegE_exec (P := P) cX hwX
  have gE := exec_frameB eE wr_lvRegE
  have hwE := eE.wb_right
  have kEq := fun q hq => gE.1 q (by
    zuodz; exact hq)
  -- D: the table entry
  have hNK1 : ztl * lvNch μ ≤ ztl * Kb := Nat.mul_le_mul_left _ by_omega
  have hjm : ztl * lvNch μ = j * lvNch μ + lvNch μ := by_ring
  obtain ⟨cD, kD, eD, hkD, w12, w10, wp, wl, wb, wm, wrr, wrm, wout⟩ :=
    lvRegD_exec (P := P) cE hwE (T := T) (j := j) (ℓ := Lj.length)
      (tot := ((List.range j).flatMap Lx).length)
      ztdma
      ztdma
      (by rw [kEq _ by_decide, kXq _ by_decide by_decide, f14]; exact ctx.r14)
      zttqn (by rw [kEq _ by_decide]; exact y5) zttqn
      ztdma
      by_omega by_omega by_omega
  have gD := exec_frameM eD wrM_lvRegD
  have hwD := eD.wb_right
  have kDq : ∀ q, q ≠ 211020 → q ≠ 211012 → q ≠ 211010 → cD.nreg q = cE.nreg q := fun q h1 h2 h3 =>
    gD.1 q (by simp only [BregD, decide_eq_false_iff_not]; omega)
  have AD : cD.nreg ALLOC = cX.nreg ALLOC := by
    rw [kDq _ by_decide by_decide by_decide, kEq _ by_decide]
  -- the memory
  have hmD : ∀ a, a < c.nreg ALLOC → ztgez →
      cD.nmem a = c.nmem a := fun a ha hb => by
    rw [wm a hb, gE.2.2.1, frX.2.2.1 a by_omega, mC a ha]
  -- the registers outside the driver's bands
  have hob : ∀ q, bandOf q ∉ drvBands → q ≠ ALLOC → cD.nreg q = c.nreg q := by
    intro q hq hA
    zuglj
    have hr : ztppm := by
      zughh
    rw [kDq q by_omega by_omega by_omega, kEq q by_omega,
      frX.1 q (fun h => hq (by
        zulgo
        exact this h)) hA,
      gC.1 q ztfbs,
      frR.1 q hq hA, gB.1 q ztkuy,
      core q ztmeh hA]
  have hrob : ∀ q, bandOf q ∉ drvBands → cD.rreg q = c.rreg q := by
    zuco
    zuglj
    have hr : ztppm := by
      zughh
    rw [wrr, gE.2.1 q (by zuodz; omega),
      frX.2.1 q (fun h => hq (by
        zulgo
        exact this h)),
      gC.2.1 q ztfbs,
      frR.2.1 q hq, gB.2.1 q ztkuy,
      frH.2.1 q ztmeh,
      gA.2.1 q (by zunka; omega)]
  have hrm : ∀ a, a < c.nreg ALLOC → cD.rmem a = c.rmem a := fun a ha => by
    rw [wrm, gE.2.2.2.1, frX.2.2.2.1 a by_omega, gC.2.2.2.1, frR.2.2.2.1 a by_omega,
      gB.2.2.2.1, frH.2.2.2.1 a by_omega, gA.2.2.2.1]
  have hoD : cD.output = c.output := by
    rw [wout, gE.2.2.2.2, frX.2.2.2.2.1, gC.2.2.2.2, frR.2.2.2.2.1, gB.2.2.2.2, frH.2.2.2.2.1,
      gA.2.2.2.2]
  have kFix : ∀ q, bandOf q = bDownDrv → q < 215000 → q ≠ 211020 → q ≠ 211012 → q ≠ 211010 →
      q ≠ 211013 → cD.nreg q = c.nreg q := fun q hq hr h1 h2 h3 h4 => by
    rw [kDq q h1 h2 h3, kEq q h4, kXq q hq hr]
  -- the cost
  have ex : Exec P W ztlqz c cD _ :=
    .seq eA (.seq eH (.seq eB (.seq eR (.seq eC (.seq eX (.seq eE eD))))))
  have hkX' : kX ≤ κX * zthyt :=
    hkX.trans ztdfv
  refine ⟨cD, _, ex, ?_, by_omega, by_omega⟩
  have hb21 : ∀ q, (210000 ≤ q ∧ q < 215000) → bandOf q = bDownDrv := fun q hq => by
    zvmxo; omega
  refine ⟨hwD, w10, ?_, ?_, fun a ha => by rw [hmD a by_omega by_omega]; exact hmem a ha,
    fun a ha => by rw [hrm a by_omega]; exact hrmem a ha,
    fun q hq hA => by rw [hob q hq hA]; exact hoth q hq hA,
    fun q hq => by rw [hrob q hq]; exact hroth q hq, by rw [hoD]; omega, by_omega,
    by rw [hjK'] at hjK; omega, ?_⟩
  · rw [kFix _ by_decide by_decide by_decide by_decide by_decide by_decide]; omega
  · zuco
    zubwm
    unfold LvFixed at hq'
    rcases hq' with h | h | h | h | h
    · zubmf

    · zubmf

    · zubmf

    · zufpw
    · zufpw
  · have m13 : cD.nreg 211013 = max ztqhr Lj.length := by
      rw [kDq _ by_decide by_decide by_decide, z13, y5, kXq _ by_decide by_decide]
    have hTj : T + 3 * j + 3 ≤ A₁ := by_omega
    refine ⟨fun r => if r = j then hostChainOf Q H hpt3 else C r,
      fun r => if r = j then NRj else NR r, fun r => if r = j then cR.nreg 219212 else γR r,
      fun r => if r = j then Lj else Lx r, ?_, ?_, ?_, ?_⟩
    · have e1 : (List.range j).flatMap (fun r => if r = j then Lj else Lx r) =
          (List.range j).flatMap Lx :=
        List.flatMap_congr (fun r hr => by
          simp only [show r ≠ j by have := List.mem_range.1 hr; omega, ↓reduceIte])
      rw [w12, List.range_succ, List.flatMap_append, List.length_append, e1,
        List.flatMap_singleton]
      simp
    · zuz
      zumon
      zujse
      · zumzf; omega
      · zumzf; have := hMx r by_omega; omega
    · zumon
      rcases hM0 with h0 | ⟨r, hr, hr'⟩
      · by_cases hl : Lj.length = 0
        · omega
        · right; exact ztioj
      · right
        by_cases hl : Lj.length ≤ c.nreg 211013
        · exact ⟨r, by_omega, by simp only [show r ≠ j by omega, ↓reduceIte]; omega⟩
        · exact ztioj
    · zuz
      zujse
      · zubst
        zubvh
        refine ⟨⟨hostChainOf_P _ _ hpt3, hostChainOf_s _ _ hpt3, hostChainOf_m _ _ hpt3, hcj,
          by rw [ctx.r06]; omega, by rw [ctx.r06]; omega, y7, y8, y9,
          fun q hq => (y10 q hq).2⟩, ?_⟩
        have pA : c.nreg ALLOC ≤ cX.nreg 217010 := by_omega
        have bA : c.nreg ALLOC ≤ cX.nreg 217012 := by_omega
        refine ⟨wl, by zuowb; omega, by rw [wp, AD]; exact y2, ?_, by rw [wb]; omega,
          by rw [wb, AD]; exact y4, fun q hq => ?_⟩
        · zuowb
          exact clAt_congr y6 fun x hx1 hx2 => by rw [wm x by_omega, gE.2.2.1]
        · rw [wb, wm _ by_omega, gE.2.2.1]
          exact (y10 q hq).1
      · zumzf
        obtain ⟨h1, h2⟩ := hdat r by_omega
        refine ⟨h1, h2.transport by_omega ztts by_omega⟩
        obtain ⟨ha1, ha2⟩ := ha
        refine hmD a ha1 ?_
        by_cases hA : a < A₁
        · have := ha2 hA; left; omega
        omega

/-- **The region loop.** -/
theorem lvLoop_exec {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hH : HostMeets sH κH) (hR : RegMeets O sR κR) (hX : ExtMeets sX κX)
    (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    {c₁ : Config} {L : List zte} {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ}
    (ctx : LvCtx O P W c₁ L E reg lam) {Kb : ℕ}
    (hKb : 30 + κH + κR * ztwuz + κX * ztxoh +
      lvNch ztmc ≤ Kb)
    (hroom : c₁.nreg ALLOC + ztkr * Kb ≤ W)
    {c : Config} (hinv0 : LvInv O P W c₁ L E reg Kb 0 c) :
    ∃ c' k, Exec P W ztlra c c' k ∧ LvInv O P W c₁ L E reg Kb ztkr c' ∧
      k ≤ ztkq * ztkr + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, ex, hI, hk, hA⟩ := forLoopA (P := P) (W := W) (ir := 211010) (nr := 211011)
    (fun j c => LvInv O P W c₁ L E reg Kb j c) Kb ztkr
    ztywd
    (fun j c hj h => lvBody_exec hH hR hX hR1 hLM ctx hKb hroom hj h) hinv0 ztbg
  exact ⟨c', k, ex, hI, by_omega, hA⟩
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
@[expose] public section
open Machine

/-- **The count bound of the levels**: `A = 2^(regCap+4)` (the restoration rounds),
`B = 1120 (regCap + 2)` (`LevelMathSpec` (4)). -/
def lvCnt : ℕ → ℕ := DownMath.cnt ztnfk ztzso

/-- **The contract of the tail of a level (D12).** -/
def LvTailSpec (O : OracleIface) : Prop :=
  ∃ (sT : Stmt) (κ : ℕ), ∀ (Kb : ℕ) (P : Polygon) (W : ℕ) (c₁ c : Config)
    (L : List zte) (E : List ℕ) (reg : ℕ → Set Point) (lam : ℕ),
    LvCtx O P W c₁ L E reg lam →
    L.length * 2 ^ Cost.ceilBeta lam ≤ lvCnt lam * ztfmt →
    LvInv O P W c₁ L E reg Kb ztkr c →
    c.nreg ALLOC + κ * ztkr * ztwuz ≤ W →
    ∃ c' k, Exec P W sT c c' k ∧ k ≤ κ * ztkr * ztwuz ∧
      Frame drvBands c c' k ∧ c'.nreg 210000 = lam ∧ InvAt lvCnt P c' ztmc
end
end DrvR
namespace DrvG
open Machine Machine.Stmt DrvR
@[expose] public section
def rgInit0 : Stmt := block [.copyN 219000 219200, .copyN 219002 219203]

/-- The padding after the leaf table. -/
def rgPad : Stmt :=
  .seq (block [.copyN 219250 219003, .constN 219251 1])
    ztipx

/-- The constants and the loop state. -/
def rgInit1 : Stmt := block [
  .constN 219140 0, .constN 219141 1, .constN 219142 2, .constN 219143 3, .constN 219144 4,
  .constN 219145 5, .constN 219146 6,
  .copyN 219100 219200, .copyN 219101 219201, .constN 219103 130, .copyN 219104 219205,
  .loadN 219107 219200,
  .constN 219230 1, .constN 219231 3, .constN 219220 0, .constN 219221 0, .constN 219222 0,
  .subN 219223 219201 219230, .copyN 219224 219003, .addN 9999 9999 219231]

/-- The arguments of `PieceSpec`. -/
def pcArgs : Stmt := block [
  .copyN 218000 219200, .copyN 218001 219240, .copyN 218002 219241, .copyN 218003 219242,
  .copyN 218004 219243, .copyN 218005 219202, .constN 218006 130, .copyN 218007 219204,
  .copyN 218008 219205]

/-- The first piece becomes the accumulated chain. -/
def pcFirst : Stmt := block [
  .copyN 219110 218010, .copyN 219111 218011, .copyN 219112 219241, .copyN 219113 219204,
  .constN 219222 1]

/-- A later piece is merged into the accumulated chain. -/
def pcNext (sM : Stmt) : Stmt :=
  .seq zthtd ztvzb

/-- **One piece** (arguments in `219240 … 219243`). -/
def pcS (sp sM : Stmt) : Stmt := .seq pcArgs (.seq sp (.ifLtN 219222 219230 pcFirst (pcNext sM)))

/-- Load the current leaf. -/
def lfLoad : Stmt := block [
  .loadN 219226 219224, .addN 219229 219224 219230, .loadN 219227 219229,
  .addN 219229 219229 219230, .loadN 219228 219229]

/-- The connector before the current leaf (if `pos < s`). -/
def conS (sp sM : Stmt) : Stmt :=
  .ifLtN 219221 219226
    (.seq (block [.copyN 219240 219221, .subN 219241 219226 219221, .constN 219242 0,
      .constN 219243 0]) (pcS sp sM)) .skip

/-- The current leaf. -/
def lfS (sp sM : Stmt) : Stmt :=
  .seq (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1,
    .copyN 219243 219228]) (pcS sp sM)

/-- Advance past the current leaf. -/
def lfAdv : Stmt :=
  block [.addN 219221 219226 219227, .addN 219220 219220 219230, .addN 219224 219224 219231]

/-- One leaf (and the connector before it). -/
def lfBody (sp sM : Stmt) : Stmt := .seq lfLoad (.seq zttia (.seq (lfS sp sM) lfAdv))

/-- **The leaf loop.** -/
def lfLoop (sp sM : Stmt) : Stmt := .whileLtN 219220 219004 zttsh

/-- The last connector (if `pos < M`). -/
def finCon (sp sM : Stmt) : Stmt :=
  .ifLtN 219221 219223
    (.seq (block [.copyN 219240 219221, .subN 219241 219223 219221, .constN 219242 0,
      .constN 219243 0]) (pcS sp sM)) .skip

/-- The outputs. -/
def rgOut : Stmt := block [.copyN 219210 219110, .copyN 219211 219111, .copyN 219212 219113]

/-- **The region procedure.** -/
def rgS (sp sM : Stmt) : Stmt :=
  .seq rgInit0 (.seq plS (.seq rgPad (.seq rgInit1 (.seq zttsi
    (.seq zttkb rgOut)))))
open Programs BuildRam
def PcMeets (O : OracleIface) (sp : Stmt) (κ : ℕ) : Prop :=
  Meets sp drvBands
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztcuu ztm ∧
      4 ≤ c.nreg 218006 ∧ 1 ≤ c.nreg 218002 ∧ c.nreg 218003 ≤ 1 ∧
      ∃ H : Host, Robust ztm c.nmem ztfbw ∧
        c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC ∧
        H.length ≤ 64 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly zta).Simple ∧
        c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length ∧
        (c.nreg 218003 = 1 →
          c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧ c.nreg 218005 ≤ c.nmem ztcuu ∧
          c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
          2 * gradeGran ztmgb ≤ c.nreg 218007 ∧
          ∀ k, k ≤ c.nreg 218002 →
            (H.pts (Qof P).n).getD zthuq ztga = .vtx zthur) ∧
        ztghf)
    (fun P c c' =>
      ztexc ∧
      c.nreg ALLOC ≤ c'.nreg 218010 ∧ c.nreg ALLOC ≤ c'.nreg 218011 ∧
      ModelDescWF P ztdo c'.nmem ztmff ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem ztjrx H → C.P = H.poly zta →
        C.s = c.nreg 218001 → C.m = c.nreg 218002 →
        Robust ztdo c'.nmem
          (fun m => m ztmff = 0 ∧
            ChainDescAt m zthud zta H C ∧
            m zthud = c.nreg 218000) ∧
        ∃ N, NFWithin c'.nmem ztqhb ztdo N ∧
          IsCanonicalNF ztc zta N zthus ztvia)
    ztyqj
theorem pieceSpec_iff (O : OracleIface) : PieceSpec O ↔ ∃ sp κ, PcMeets O sp κ := Iff.rfl

/-- **The frame of a register block** of band `bDownDrv`. -/
theorem frame_band {B : ℕ → Bool} (hB : ∀ q, B q = true → bandOf q = bDownDrv) {c c' : Config}
    (hf : FrameM B c c') (hm : c'.nmem = c.nmem) (k : ℕ) : Frame drvBands c c' k := by
  have hA : ztble := hf.1 ALLOC (by
    cases h : B ALLOC
    · rfl
    · have := hB _ h; tauto)
  refine ⟨fun r hr _ => hf.1 r ?_, fun r hr => hf.2.1 r ?_, fun a _ => by zvmwi,
    fun a _ => by zuode, hf.2.2.2, by_omega, by_omega⟩ <;>
  · cases h : B r
    · rfl
    · exact absurd (hB r h ▸ bDownDrv_mem_drvBands) hr
section exec
variable {P : Polygon} {W : ℕ}

/-- The arguments of a piece. -/
theorem pcArgs_exec (d : Config) (hw : WordsBounded W d) (hW : 130 ≤ W) :
    ∃ d' k, Exec P W pcArgs d d' k ∧ k = 9 ∧ d'.nreg 218000 = d.nreg 219200 ∧
      d'.nreg 218001 = d.nreg 219240 ∧ d'.nreg 218002 = d.nreg 219241 ∧
      d'.nreg 218003 = d.nreg 219242 ∧ d'.nreg 218004 = d.nreg 219243 ∧
      d'.nreg 218005 = d.nreg 219202 ∧ d'.nreg 218006 = 130 ∧ d'.nreg 218007 = d.nreg 219204 ∧
      d'.nreg 218008 = d.nreg 219205 ∧ d'.nmem = d.nmem ∧
      FrameM (fun q => decide (218000 ≤ q ∧ q ≤ 218008)) d d' := by
  obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩ : ∃ d' k,
      Exec P W pcArgs d d' k ∧ k = 9 ∧ d'.nreg 218000 = d.nreg 219200 ∧
      d'.nreg 218001 = d.nreg 219240 ∧ d'.nreg 218002 = d.nreg 219241 ∧
      d'.nreg 218003 = d.nreg 219242 ∧ d'.nreg 218004 = d.nreg 219243 ∧
      d'.nreg 218005 = d.nreg 219202 ∧ d'.nreg 218006 = 130 ∧ d'.nreg 218007 = d.nreg 219204 ∧
      d'.nreg 218008 = d.nreg 219205 ∧ d'.nmem = d.nmem := by
    unfold pcArgs
    exec_block
    · zugkh
    simp
  exact ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, exec_frameM ex by_decide⟩

/-- **One call of the piece procedure.** -/
theorem pcCall_exec {O : OracleIface} {sp : Stmt} {κP : ℕ} (hsp : PcMeets O sp κP)
    (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config) (hw : WordsBounded W d)
    {H : Host} {HB s m kind a μ γ g : ℕ}
    (h00 : d.nreg 219200 = HB) (h40 : d.nreg 219240 = s) (h41 : d.nreg 219241 = m)
    (h42 : d.nreg 219242 = kind) (h43 : d.nreg 219243 = a) (h02 : d.nreg 219202 = μ)
    (h04 : d.nreg 219204 = γ) (h05 : d.nreg 219205 = g)
    (hX : (gradeCtx O).holds P d.nmem g zthwh)
    (hH : Robust zthwh d.nmem (fun mm => HostAt mm HB H))
    (hHB : HB + 3 * H.length + 4 ≤ d.nreg ALLOC) (hHl : H.length ≤ 64)
    (hwf : HostWF (Qof P).n H) (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly zta).Simple)
    (hsm : s + m + 1 ≤ (H.pts (Qof P).n).length) (hm1 : 1 ≤ m) (hk : kind ≤ 1)
    (hleaf : kind = 1 → m ≤ 2 ^ μ ∧ μ ≤ d.nmem g ∧ a + m + 1 ≤ (Qof P).n ∧
      2 * gradeGran μ ≤ γ ∧
      ∀ k, k ≤ m → (H.pts (Qof P).n).getD ztnj ztga = .vtx ztbzd)
    (hcon : kind = 0 → m ≤ 64 ∧ 2 * m ≤ γ)
    (hroom : d.nreg ALLOC + κP * ztud ≤ W) :
    ∃ d' k, Exec P W (.seq pcArgs sp) d d' k ∧ k ≤ 9 + κP * ztud ∧
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 219000 ≤ q) → d'.nreg q = d.nreg q) ∧
      d.nreg ALLOC ≤ d'.nreg 218010 ∧ d.nreg ALLOC ≤ d'.nreg 218011 ∧
      ModelDescWF P ztqkz d'.nmem ztvoh ∧
      (∀ C : Chain, C.P = H.poly zta → C.s = s → C.m = m →
        Robust ztqkz d'.nmem
          (fun mm => mm ztvoh = 0 ∧
            ChainDescAt mm ztroh zta H C ∧ mm ztroh = HB) ∧
        ∃ N, NFWithin d'.nmem (d'.nreg 218011) ztqkz N ∧
          IsCanonicalNF ztc zta N γ 130) ∧
      Frame drvBands d d' k := by
  have hW130 : 130 ≤ W := by have : ztfdq := rfl; have := hG.1.1; omega
  obtain ⟨d₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, a7, a8, m₁, f₁⟩ :=
    pcArgs_exec (P := P) d hw hW130
  have hA₁ : ztsib := f₁.1 ALLOC by_decide
  have fr₁ : Frame drvBands d d₁ k₁ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₁ m₁ k₁
  have hHA : HostAt d.nmem HB H := hH.holds
  have hpre : _ := hsp P W d₁ e₁.wb_right ⟨hG, hWn, by_simp_all,
    by omega, by_omega, by_omega, H,
    by simp_all, by_omega, hHl, hwf, hreg, hsimp,
    by omega,
    fun h1 => by
      grind,
    fun h0 => by
      omega⟩ by_simp_all
  obtain ⟨d', k₂, e₂, hk₂, ⟨q1, q2, q3, q4, q5⟩, fr₂⟩ := hpre
  zuira
  rw [a5, h02] at hk₂
  refine ⟨d', k₁ + k₂, .seq e₁ e₂, by_omega, fun q hq hq' => ?_, by_omega,
    by omega, q4, fun C hP hs hm => ?_, by
      have := fr₁.trans fr₂; grind⟩
  · rw [q1 q hq hq', f₁.1 q by_grind]
  grind
end exec
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
theorem Robust.imp {A : ℕ} {m : ℕ → ℕ} {Φ Ψ : ztjx → Prop} (h : Robust A m Φ)
    (hi : ∀ m', Φ m' → Ψ m') : Robust A m Ψ := fun m' hm' => hi m' (h m' hm')
theorem fullDegLe_mono {M : Model} {Q : Polygon} {D D' : ℕ} (h : M.FullDegLe Q D) (hD : D ≤ D') :
    M.FullDegLe Q D' := fun F hF => Model.DegLe.mono _ (h F hF) hD

/-- The capacity of the up-phase data is at most `2 n`. -/
theorem gradeCtx_cap_le {O : OracleIface} {P : Polygon} {m : ℕ → ℕ} {g A : ℕ} (hn : 1 ≤ P.n)
    (h : (gradeCtx O).holds P m g A) : (gradeCtx O).cap P m g ≤ 2 * P.n := by
  have h1 : m g ≤ topGrade P.n + 1 := h.holds.1
  show 2 ^ ztlrf ≤ 2 * P.n
  have h2 : 2 ^ ztlrf ≤ 2 ^ topGrade P.n := Nat.pow_le_pow_right by_norm_num by_omega
  refine h2.trans ?_
  zuhrf
  rcases Nat.lt_or_ge ztch 2 with h3 | h3
  · have : Nat.clog 2 ztch = 0 := Nat.clog_of_right_le_one by_omega 2
    grind
  · have h4 := Nat.pow_pred_clog_lt_self (b := 2) by_norm_num (show 1 < P.n - 1 by omega)
    have h5 : 1 ≤ Nat.clog 2 ztch := Nat.clog_pos by_norm_num by_omega
    have e : 2 ^ Nat.clog 2 ztch = 2 * 2 ^ (Nat.clog 2 ztch).pred := by
      rw [← pow_succ', Nat.pred_eq_sub_one, Nat.sub_add_cancel h5]
    omega

/-- **The data of a run of the region procedure.** -/
structure RData where
  /-- The host. -/
  H : Host
  /-- Its handle. -/
  HB : ℕ
  /-- Its number of points. -/
  NP : ℕ
  /-- The merge grade. -/
  μ : ℕ
  /-- The granularity of the pieces. -/
  γ₀ : ℕ
  /-- The handle of the up-phase data. -/
  g : ℕ
  /-- The memory after the setup. -/
  m₁ : ℕ → ℕ
  /-- The allocator after the setup. -/
  A₁ : ℕ
  /-- The leaf table. -/
  T : ℕ

/-- The leaves of the host. -/
noncomputable def RData.leaves (P : Polygon) (R : RData) : List zte :=
  hostLeaves (Qof P).n (2 ^ R.μ) 0 R.H

/-- **The static facts** of a run of the region procedure. -/
structure RFacts (O : OracleIface) (P : Polygon) (W : ℕ) (R : RData) : Prop where
  hG : GoodEnv P
  hWn : hostWords P.n ≤ W
  hHA : Robust R.A₁ R.m₁ ztnzh
  hHB : R.HB + 3 * R.H.length + 4 ≤ R.A₁
  hHl : R.H.length ≤ 20
  hwf : HostWF (Qof P).n R.H
  hreg : HostRegular (Qof P).n R.H
  hsimp : (R.H.poly zta).Simple
  hNP : R.NP = (R.H.pts (Qof P).n).length
  hNP3 : 3 ≤ R.NP
  hruns : ∀ a ℓ, HostItem.run a ℓ ∈ R.H → ℓ ≤ 2 * 2 ^ R.μ
  hμ7 : 7 ≤ R.μ
  hμg : R.μ ≤ R.m₁ R.g
  hg0 : 2 * gradeGran R.μ ≤ R.γ₀
  h128 : 128 ≤ R.γ₀
  hg1 : R.γ₀ ≤ 4096 * 2 ^ Cost.ceilBeta R.μ
  hcap : R.γ₀ + 129 ≤ (gradeCtx O).cap P R.m₁ R.g
  hX : (gradeCtx O).holds P R.m₁ R.g R.A₁
  hT : ChordListAt R.m₁ R.T ztvcx
  hTA : R.T + 3 * (R.leaves P).length ≤ R.A₁
  hγW : R.γ₀ + 129 ≤ W

/-- **The registers of the region procedure** and the memory below `A₁`. -/
structure REnv (R : RData) (d : Config) : Prop where
  r200 : d.nreg 219200 = R.HB
  r201 : d.nreg 219201 = R.NP
  r202 : d.nreg 219202 = R.μ
  r204 : d.nreg 219204 = R.γ₀
  r205 : d.nreg 219205 = R.g
  r230 : d.nreg 219230 = 1
  r231 : d.nreg 219231 = 3
  r223 : d.nreg 219223 = R.NP - 1
  r003 : d.nreg 219003 = R.T
  mg : MgConst d
  r100 : d.nreg 219100 = R.HB
  r101 : d.nreg 219101 = R.NP
  r103 : d.nreg 219103 = 130
  r104 : d.nreg 219104 = R.g
  r107 : d.nreg 219107 = R.H.length
  low : ∀ a, a < R.A₁ → d.nmem a = R.m₁ a
  alloc : R.A₁ ≤ d.nreg ALLOC

/-- The registers `REnv` reads (all of band `bDownDrv`, outside `218000 … 218999`, `219110 …
219139` and `219240 … 219243`). -/
def envRegs : List ℕ :=
  [219200, 219201, 219202, 219204, 219205, 219230, 219231, 219223, 219003, 219140, 219141,
    219142, 219143, 219144, 219145, 219146, 219100, 219101, 219103, 219104, 219107]
theorem envRegs_band : ∀ q ∈ envRegs, bandOf q = bDownDrv ∧ 219000 ≤ q ∧
    (q < 219110 ∨ 219139 < q) ∧ q ≠ 219222 := by_decide
theorem envRegs_band2 : ∀ q ∈ envRegs, q ≠ 219220 ∧ q ≠ 219221 ∧ q ≠ 219222 ∧
    (q < 219224 ∨ 219229 < q) ∧ (q < 219240 ∨ 219251 < q) := by_decide

/-- The environment survives a step keeping its registers and the memory below `A₁`. -/
theorem REnv.keep {R : RData} {d d' : Config} (h : REnv R d)
    (hr : ∀ q ∈ envRegs, d'.nreg q = d.nreg q) (hm : ∀ a, a < R.A₁ → d'.nmem a = d.nmem a)
    (hA : d.nreg ALLOC ≤ d'.nreg ALLOC) : REnv R d' := by
  have e : ∀ q, q ∈ envRegs → d'.nreg q = d.nreg q := hr
  exact ⟨by rw [e _ by_decide, h.r200], by rw [e _ by_decide, h.r201],
    by rw [e _ by_decide, h.r202], by rw [e _ by_decide, h.r204],
    by rw [e _ by_decide, h.r205], by rw [e _ by_decide, h.r230],
    by rw [e _ by_decide, h.r231], by rw [e _ by_decide, h.r223],
    by rw [e _ by_decide, h.r003],
    ⟨by rw [e _ by_decide, h.mg.r40], by rw [e _ by_decide, h.mg.r41],
      by rw [e _ by_decide, h.mg.r42], by rw [e _ by_decide, h.mg.r43],
      by rw [e _ by_decide, h.mg.r44], by rw [e _ by_decide, h.mg.r45],
      by rw [e _ by_decide, h.mg.r46]⟩,
    by rw [e _ by_decide, h.r100], by rw [e _ by_decide, h.r101],
    by rw [e _ by_decide, h.r103], by rw [e _ by_decide, h.r104],
    by rw [e _ by_decide, h.r107], fun a ha => by rw [hm a ha, h.low a ha],
    le_trans h.alloc hA⟩
section facts
variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}
theorem REnv.mem_eq {d : Config} (h : REnv R d) : ∀ a, a < R.A₁ → R.m₁ a = d.nmem a :=
  fun a ha => (h.low a ha).symm
theorem REnv.hostAt (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    Robust zthwh d.nmem ztnzh :=
  (hF.hHA.transport h.low).mono h.alloc
theorem REnv.holds (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    (gradeCtx O).holds P d.nmem R.g zthwh :=
  (gradeCtx O).mono P _ _ _ _ h.alloc ((gradeCtx O).local_ P _ _ _ _ h.mem_eq hF.hX)
theorem REnv.cap (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    (gradeCtx O).cap P d.nmem R.g = (gradeCtx O).cap P R.m₁ R.g :=
  gradeCtx_capLocal O P _ _ _ _ h.low hF.hX
theorem REnv.grades (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    d.nmem R.g = R.m₁ R.g :=
  h.low _ (gradeRaw_handle_lt (O := O) hF.hX)
theorem REnv.table (hF : RFacts O P W R) {d : Config} (h : REnv R d) :
    ChordListAt d.nmem R.T ztvcx := by
  zug
  obtain ⟨a1, a2, a3⟩ := hF.hT i hi
  have := hF.hTA
  zusk
  · zunol; exact a1
  · zunol; exact a2
  · zunol; exact a3
end facts

/-- **The accumulated chain** `⟨H.poly Q, 0, pos⟩`: descriptor, normal form, granularity `γ`. -/
structure AccOK (P : Polygon) (R : RData) (d : Config) (pos γ : ℕ) : Prop where
  r22 : d.nreg 219222 = 1
  r12 : d.nreg 219112 = pos
  r13 : d.nreg 219113 = γ
  dA : d.nreg 219110 + 6 ≤ d.nreg ALLOC
  lo1 : R.A₁ ≤ d.nreg 219110
  lo2 : R.A₁ ≤ d.nreg 219111
  desc : ∀ C : Chain, C.P = R.H.poly zta → C.s = 0 → C.m = pos →
    Robust zthwh d.nmem (fun m => m (d.nreg 219110) = 0 ∧
      m ztrol = R.HB ∧ ChainDescAt m ztrol zta R.H C) ∧
    ∃ N, NFWithin d.nmem (d.nreg 219111) zthwh N ∧
      IsCanonicalNF ztc zta N γ 130

/-- The accumulated chain survives a frame keeping its registers. -/
theorem AccOK.keep {P : Polygon} {R : RData} {d d' : Config} {pos γ : ℕ} {B : Finset ℕ} {k : ℕ}
    (h : AccOK P R d pos γ) (hf : Frame B d d' k)
    (hr : ∀ q, q = 219110 ∨ q = 219111 ∨ q = 219112 ∨ q = 219113 ∨ q = 219222 →
      d'.nreg q = d.nreg q) : AccOK P R d' pos γ := by
  have r10 := hr 219110 by_simp
  have r11 := hr 219111 by_simp
  refine ⟨by rw [hr _ by_simp, h.r22], by rw [hr _ by_simp, h.r12],
    by rw [hr _ by_simp, h.r13], by zuovf; have := hf.2.2.2.2.2.1; have := h.dA; omega,
    by zuovf; exact h.lo1, by rw [r11]; exact h.lo2, fun C hP hs hm => ?_⟩
  obtain ⟨h1, N, h2, h3⟩ := h.desc C hP hs hm
  rw [r10, r11]
  exact ⟨h1.frame hf, N, h2.frame hf, h3⟩
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
theorem exec_seq_inv {P : Polygon} {W : ℕ} {s t : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W ztfmm c c' k) :
    ∃ c₁ k₁ k₂, Exec P W s c c₁ k₁ ∧ Exec P W t c₁ c' k₂ ∧ k = k₁ + k₂ := by
  cases h with
  | seq e₁ e₂ => exact by_grind

/-- The number of points of a host whose runs have at most `2 C` edges. -/
theorem pts_length_le_runs (n C : ℕ) : ∀ H : Host, zthlu →
    (H.pts n).length ≤ H.length * (2 * C + 1)
  | [], _ => by_positivity
  | .pt x :: H, h => by
    rw [DownMath.pts_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := pts_length_le_runs n C H by_grind
    zuodo; omega
  | .run a ℓ :: H, h => by
    rw [DownMath.pts_cons, List.length_append, List.length_cons, Nat.succ_mul,
      DownMath.run_pts_length]
    have := pts_length_le_runs n C H by_grind
    grind

/-- The chord count of a `γ`-canonical normal form (cap `130`) of a chain (Lemma 2.3). -/
theorem chords_le {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hc : IsCanonicalNF ztc Q N γ 130) :
    N.chords.length * ztgj ≤ 18480 * ztyw := by
  have h := DownMath.lemma23_chain hP hc.1.1 hc.2.1 hc.2.2.1
  rw [Gran.ncard_F hc.1] at h
  tauto

/-- The cost bound of one piece. -/
def pcB (κP κM κs L : ℕ) : ℕ := 9 + κP * ztgt + 1570 + mcK κM κs * L
section exec
variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}
set_option maxHeartbeats 4000000 in
/-- **One piece**: computed, then merged into the accumulated chain (or becoming it). -/
theorem pcS_exec {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ}
    (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ ztjjo ztjjp cutGran ztsy OkModel)
    (hF : RFacts O P W R) (d : Config) (hw : WordsBounded W d) (hE : REnv R d)
    {s m kind a γ : ℕ}
    (h40 : d.nreg 219240 = s) (h41 : d.nreg 219241 = m) (h42 : d.nreg 219242 = kind)
    (h43 : d.nreg 219243 = a)
    (hacc : (d.nreg 219222 = 0 ∧ s = 0 ∧ γ = R.γ₀) ∨ (0 < s ∧ AccOK P R d s γ))
    (hγ : R.γ₀ ≤ γ) (hγ' : γ ≤ R.γ₀ + 127)
    (hm1 : 1 ≤ m) (hsm : s + m + 1 ≤ R.NP) (hk : kind ≤ 1)
    (hleaf : kind = 1 → m ≤ 2 ^ R.μ ∧ a + m + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ m → (R.H.pts (Qof P).n).getD ztnj ztga = .vtx ztbzd)
    (hcon : kind = 0 → m ≤ 64)
    (hjun : 0 < s → ∃ H₁ a' ℓ H₂ k, R.H = H₁ ++ HostItem.run a' ℓ :: H₂ ∧ 1 ≤ k ∧ k < ℓ ∧
      s = (H₁.pts (Qof P).n).length + k)
    (hroom : d.nreg ALLOC + pcB κP ztddr κs ztgks ≤ W) :
    ∃ d' k, Exec P W (pcS sp sM) d d' k ∧ k ≤ pcB κP ztddr κs ztgks ∧
      REnv R d' ∧ AccOK P R d' ztbnl (if s = 0 then R.γ₀ else γ + 1) ∧
      (∀ q, bandOf q = bDownDrv →
        (q < 218000 ∨ (219000 ≤ q ∧ q < 219110) ∨ (219139 < q ∧ q ≠ 219222)) →
        d'.nreg q = d.nreg q) ∧
      Frame drvBands d d' k := by
  zuc
  zumeh
  have hNPn : (R.H.poly zta).n = R.NP := by rw [DownMath.host_poly_n, hF.hNP]
  have hW1 : 1579 ≤ W := by unfold pcB at hroom; omega
  -- the piece
  obtain ⟨d₁, k₁, e₁, hk₁, q1, q2, q3, q4, q5, fr₁⟩ := pcCall_exec (P := P) hsp hF.hG hF.hWn d hw
    (H := R.H) hE.r200 h40 h41 h42 h43 hE.r202 hE.r204 hE.r205 (hE.holds hF) (hE.hostAt hF)
    (by have := hF.hHB; have := hE.alloc; omega) (by have := hF.hHl; omega) hF.hwf hF.hreg
    hF.hsimp (by rw [← hF.hNP]; omega) hm1 hk
    (fun h1 => by
      obtain ⟨b1, b2, b3⟩ := hleaf h1
      exact ⟨b1, by rw [hE.grades hF]; exact hF.hμg, b2, hF.hg0, b3⟩)
    (fun h0 => ⟨hcon h0, by have := hcon h0; have := hF.h128; omega⟩)
    (by unfold pcB at hroom; omega)
  obtain ⟨d₀, k₀, k₀', e₀, e₀', hk₀⟩ := exec_seq_inv e₁
  have keep1 : ∀ q ∈ envRegs, d₁.nreg q = d.nreg q := by
    zuco
    obtain ⟨b1, b2, -, -⟩ := envRegs_band q hq
    grind
  have E₁ := hE.keep keep1
    (fun a ha => fr₁.2.2.1 a (by have := hE.alloc; omega)) fr₁.2.2.2.2.2.1
  zuka
  have r22 : d₁.nreg 219222 = d.nreg 219222 := q1 _ by_rfl by_omega
  have r41 : d₁.nreg 219241 = m := by rw [q1 _ by_rfl by_omega, h41]
  rcases hacc with ⟨f0, hs0, hγ0⟩ | ⟨hs, A⟩
  · -- the first piece
    subst hs0 hγ0
    obtain ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂, g₂⟩ : ∃ d₂ k₂, Exec P W pcFirst d₁ d₂ k₂ ∧
        k₂ = 5 ∧ d₂.nreg 219110 = d₁.nreg 218010 ∧ d₂.nreg 219111 = d₁.nreg 218011 ∧
        d₂.nreg 219112 = m ∧ d₂.nreg 219113 = R.γ₀ ∧ d₂.nreg 219222 = 1 ∧ d₂.nmem = d₁.nmem ∧
        FrameM (fun q => decide (219110 ≤ q ∧ q ≤ 219113) || decide (q = 219222)) d₁ d₂ := by
      obtain ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂⟩ : ∃ d₂ k₂,
          Exec P W pcFirst d₁ d₂ k₂ ∧ k₂ = 5 ∧ d₂.nreg 219110 = d₁.nreg 218010 ∧
          d₂.nreg 219111 = d₁.nreg 218011 ∧ d₂.nreg 219112 = m ∧ d₂.nreg 219113 = R.γ₀ ∧
          d₂.nreg 219222 = 1 ∧ d₂.nmem = d₁.nmem := by
        unfold pcFirst
        exec_block
        · omega
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
        · omega
        · exact E₁.r204
      exact ⟨d₂, k₂, e₂, hk₂, v10, v11, v12, v13, v22, m₂, exec_frameM e₂ by_decide⟩
    have fr₂ := frame_band (fun q hq => by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hq; zvmxo; omega)
      g₂ m₂ k₂
    have hA₂ := fr₂.2.2.2.2.2.1.antisymm' (by
      have := fr₂.2.2.2.2.2.2; have := g₂.1 ALLOC by_decide; omega)
    refine ⟨d₂, k₀ + (k₀' + ztcaj), .seq e₀ (.seq e₀' (.ifLtN_true (by
      rw [r22, f0, E₁.r230]; omega) e₂)), by unfold pcB; omega, E₁.keep (fun q hq => g₂.1 q (by
      obtain ⟨-, -, b3, b4⟩ := envRegs_band q hq
      grind))
      by_grind by_omega, ?_, fun q hq hq' => ?_, ?_⟩
    · simp only [↓reduceIte, Nat.zero_add]
      refine ⟨v22, v12, v13, by rw [v10, hA₂]; exact q4.1, by rw [v10]; have := hE.alloc; omega,
        by zuovj; have := hE.alloc; omega, fun C hP hs hm => ?_⟩
      grind
    · rw [g₂.1 q by_grind]
      grind
    · have := fr₁.trans fr₂
      zubpw

  · -- a later piece: the merge
    have r22' : d₁.nreg 219222 = 1 := by rw [r22, A.r22]
    obtain ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂, g₂⟩ : ∃ d₂ k₂, Exec P W
        _ d₁ d₂ k₂ ∧
        k₂ = 3 ∧ d₂.nreg 219114 = d₁.nreg 218010 ∧ d₂.nreg 219115 = d₁.nreg 218011 ∧
        d₂.nreg 219116 = m ∧ d₂.nmem = d₁.nmem ∧
        FrameM (fun q => decide (219114 ≤ q ∧ q ≤ 219116)) d₁ d₂ := by
      obtain ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂⟩ : ∃ d₂ k₂, Exec P W
          zthtd d₁ d₂ k₂ ∧
          k₂ = 3 ∧ d₂.nreg 219114 = d₁.nreg 218010 ∧ d₂.nreg 219115 = d₁.nreg 218011 ∧
          d₂.nreg 219116 = m ∧ d₂.nmem = d₁.nmem := by
        exec_block
        refine ztdqw <;> config_simp
        omega
      exact ⟨d₂, k₂, e₂, hk₂, v14, v15, v16, m₂, exec_frameM e₂ by_decide⟩
    have fr₂ := frame_band (fun q hq => by
      zvmwo at hq; zvmxo; omega) g₂ m₂ k₂
    have hA₂ := g₂.1 ALLOC by_decide
    have E₂ := E₁.keep (fun q hq => g₂.1 q (by
      obtain ⟨-, -, b3, -⟩ := envRegs_band q hq
      grind)) by_grind by_omega
    have A₂ := (A.keep fr₁ fun q hq => q1 q (by
      rcases hq with h | h | h | h | h <;> subst h <;> simp [bandOf, bDownDrv])
      by_omega).keep fr₂ fun q hq => g₂.1 q (by
        grind)
    -- the two chains
    let C1 : Chain := ⟨R.H.poly zta, 0, s, hs, by_omega⟩
    let C2 : Chain := ⟨R.H.poly zta, s, m, hm1, by_omega⟩
    have hlen : ztpiz := by
      grind
    obtain ⟨hd1R, N1, hN1, hc1⟩ := A₂.desc C1 rfl rfl rfl
    obtain ⟨hd2R, N2, hN2, hc2⟩ := q5 C2 rfl rfl rfl
    -- the junction and the degree
    have hDH : ztxpn := (goodShear_epsOf hF.hG.2).2.1
    have hgen : SharedGeneric (L41.jOf C1 C2 hlen) := by
      obtain ⟨H₁, a', ℓ, H₂, k, eH, hk1, hkl, hsk⟩ := hjun hs
      refine DownMath.sharedGeneric_run by_omega hDH (H₁ := H₁) (H₂ := H₂) (a := a') ?_ hk1 hkl ?_
      · show R.H.poly _ = _; rw [eH]
      · show ztsqm % (R.H.poly _).n = _
        rw [hNPn, Nat.zero_add, Nat.mod_eq_of_lt by_omega]; omega
    have hfd : (chainModel (L41.jOf C1 C2 hlen).whole).FullDegLe zta 130 := by
      have h1 := fullDegLe_host (C := (L41.jOf C1 C2 hlen).whole) hF.hsimp
        (host_ncard_le zta hDH R.H) zta
      exact fullDegLe_mono h1 (by have := hF.hHl; omega)
    -- the cost of the merge
    have hx := chords_le hF.hsimp hc1
    have hy := chords_le hF.hsimp hc2
    have hMb : s + m ≤ 20 * ztgyc := by
      have h1 := pts_length_le_runs (Qof P).n _ R.H hF.hruns
      have h2 : R.H.length * ztgyc ≤ 20 * ztgyc :=
        Nat.mul_le_mul_right _ hF.hHl
      have := hF.hNP
      omega
    have hmc := mcost_le ztddr κs (x := N1.chords.length) (y := N2.chords.length) hF.hμ7 hF.hg0
      hF.hg1 (show γ ≤ R.γ₀ + 128 by omega) hMb
      (by
        have h1 : N1.chords.length * (R.γ₀ + 1) ≤ N1.chords.length * ztgj :=
          Nat.mul_le_mul_left _ by_omega
        grind)
      (by
        grind)
    have hmc' : mgCostV κ _ _ cutGran 130 N1.chords.length
        N2.chords.length γ _ ≤ mcK _ κs * lemma41Nat R.μ := hmc
    have hγW : R.γ₀ ≤ W := by have := hw.1 219204; rw [hE.r204] at this; omega
    -- the merge step
    obtain ⟨d₃, k₃, e₃, hk₃, w10, w11, w12, w13, wA, wR, -, ⟨N, wN, wc⟩, wq, fr₃⟩ :=
      mgStep_exec hM ztgjv hF.hG hF.hWn d₂ e₂.wb_right E₂.mg
        E₂.r100 E₂.r101 E₂.r103 E₂.r104 E₂.r107 A₂.r12 A₂.r13 v16 (E₂.hostAt hF)
        (by have := hF.hHl; omega) (hQn ▸ hF.hwf) hF.hreg hF.hsimp
        (by have := hF.hHB; have := E₂.alloc; omega) (by zvnof; exact hF.hNP)
        (Robust.imp hd1R by_grind)
        (by rw [v14, hA₂, m₂]; exact Robust.imp hd2R by_grind)
        A₂.dA (by rw [v14, hA₂]; exact q4.1) rfl rfl rfl rfl hlen hN1
        by_grind hc1 hc2 ztbhw hγ hgen hfd by_norm_num
        (E₂.holds hF) (by rw [E₂.cap hF]; have := hF.hcap; unfold fuseLoss; omega)
        (by have := hF.hγW; omega)
        (by
          have := fr₁.2.2.2.2.2.2
          rw [hA₂]; unfold pcB at hroom; omega)
    refine ⟨d₃, k₀ + (k₀' + (zttl + 2)), .seq e₀ (.seq e₀' (.ifLtN_false (by
      rw [r22', E₁.r230]; omega) (.seq e₂ e₃))), by have := hF.hHl; unfold pcB; omega,
      E₂.keep (fun q hq => wq q (envRegs_band q hq).1 (by
        obtain ⟨-, -, b3, -⟩ := envRegs_band q hq; omega)) (fun a ha => fr₃.2.2.1 a (by
          have := E₂.alloc; omega)) fr₃.2.2.2.2.2.1, ?_, fun q hq hq' => ?_, ?_⟩
    · zufa
      refine ⟨by rw [wq _ by_rfl by_omega, A₂.r22], w12, w13,
        by omega, by zuovk; have := E₂.alloc; omega,
        by have := E₂.alloc; omega, fun C hP hs' hm' => ?_⟩
      have hC : C = (L41.jOf C1 C2 hlen).whole := L41.chain_eq hP hs' hm'
      subst hC
      zuovk
      grind
    · rw [wq q hq by_omega, g₂.1 q by_grind]
      grind
    · have := (fr₁.trans fr₂).trans (fr₃.mono mgBands_subset ztbhw)
      rw [Finset.union_self, Finset.union_self] at this
      exact this.mono ztbhw by_omega
end exec
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
theorem frame_refl (B : Finset ℕ) (c : Config) (k : ℕ) : Frame B c c k :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_refl _, by_omega⟩

/-- **A counted loop with frames.** -/
theorem forLoopF {P : Polygon} {W : ℕ} {ir nr : ℕ} {body : Stmt} {B : Finset ℕ}
    (Inv : ℕ → Config → Prop) (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv ztl c' ∧ k ≤ Kb ∧ Frame B c c' k)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W ztfmn c c' k ∧ Inv N c' ∧
      k ≤ ztkq * zthbl + 2 ∧ Frame B c c' k := by
  induction hn : N - j generalizing j c with
  | zero =>
    zubaq

    zucq
    exact ⟨c, 2, .whileLtN_false by_omega hw, hc, by_omega, frame_refl B c 2⟩
  | succ t ih =>
    zucq
    zufvj
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁, f₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂, f₂⟩ := ih hI₁ by_omega by_omega
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true by_omega e₁ e₂, hI', ?_, ?_⟩
    · grind
    · have := f₁.trans f₂
      zubpw

/-- **A junction**: the host point `s` is strictly inside a run item. -/
def JunOK (n : ℕ) (H : Host) (s : ℕ) : Prop :=
  ∃ H₁ a ℓ H₂ k, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧ 1 ≤ k ∧ k < ℓ ∧ s = (H₁.pts n).length + k

/-- **The facts about a leaf.** -/
theorem leaf_facts {n C : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) {H : Host} (hwf : HostWF n H)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ hostLeaves n C 0 H) :
    1 ≤ x.1 ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + x.2.1 + 1 ≤ n ∧
      x.1 + x.2.1 + 1 ≤ (H.pts n).length ∧
      (∀ k, k ≤ x.2.1 → (H.pts n).getD (x.1 + k) ztga = .vtx (x.2.2 + k)) ∧
      JunOK n H x.1 ∧ JunOK n H ztbui := by
  obtain ⟨H₁, a, ℓ, H₂, rfl, h1, h2, h3, h4, h5, h6⟩ := mem_hostLeaves hC hn H 0 hwf x hx
  rw [Nat.zero_add] at h1 h2 h6
  have hlen := DownMath.pts_append_run_length n H₁ H₂ a ℓ
  refine ⟨by_omega, h3, h4, h5, by_omega, fun k hk => ?_,
    ⟨H₁, a, ℓ, H₂, x.1 - (H₁.pts n).length, rfl, by_omega, by_omega, by_omega⟩,
    ⟨H₁, a, ℓ, H₂, x.1 + x.2.1 - (H₁.pts n).length, rfl, by_omega, by_omega, by_omega⟩⟩
  have e := DownMath.pts_append_run n H₁ H₂ a ℓ (k := x.1 - (H₁.pts n).length + k) by_omega
  rw [show (H₁.pts n).length + ztluo = x.1 + k by omega] at e
  rw [e, h6]
  zucr
  rw [show a + ztluo = a + (x.1 - (H₁.pts n).length) + k by omega,
    Nat.add_mod, Nat.mod_eq_of_lt (show k < n by omega)]
  zudgs
structure LInv (P : Polygon) (W : ℕ) (R : RData) (V : ℕ → ℕ) (Lb Rb i : ℕ) (e : Config) :
    Prop where
  wb : WordsBounded W e
  keep : ∀ q, bandOf q = bDownDrv → zthjk → e.nreg q = V q
  r20 : e.nreg 219220 = i
  r04 : e.nreg 219004 = (R.leaves P).length
  env : REnv R e
  r24 : e.nreg 219224 = R.T + 3 * i
  il : i ≤ (R.leaves P).length
  room : e.nreg ALLOC + ztgvp * Lb + Rb ≤ W
  st : ∃ pos γ, e.nreg 219221 = pos ∧ GapsLe 64 ((R.leaves P).drop i) pos ztnoi ∧
    ((i = 0 ∧ pos = 0 ∧ e.nreg 219222 = 0) ∨
      (0 < i ∧ 0 < pos ∧ AccOK P R e pos γ ∧ R.γ₀ ≤ γ ∧ γ + 1 ≤ R.γ₀ + 2 * i ∧
        JunOK (Qof P).n R.H pos))

/-- The budget of one iteration. -/
def lfB (pc : ℕ) : ℕ := 2 * pc + 30
theorem leaves_length_le {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}
    (hF : RFacts O P W R) : (R.leaves P).length ≤ 60 := by
  have := hostLeaves_length_le (n := (Qof P).n) (C := 2 ^ R.μ) Nat.one_le_two_pow R.H 0 hF.hruns
  have := hF.hHl
  unfold RData.leaves; omega
section exec
variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}
variable {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ}
set_option maxHeartbeats 8000000 in
/-- **One iteration of the leaf loop.** -/
theorem lfBody_exec (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ ztjjo ztjjp cutGran ztsy OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Rb i : ℕ} (e : Config) (hi : i < (R.leaves P).length)
    (hI : LInv P W R V ztxhb Rb i e) :
    ∃ e' k, Exec P W zttsh e e' k ∧
      LInv P W R V ztxhb Rb ztg e' ∧
      k ≤ lfB ztsh ∧ Frame drvBands e e' k := by
  zugyt
  set x := (R.leaves P).getD i ztt with hx
  have hxL : x ∈ R.leaves P := by_simp_all
  zuc
  zumeh
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := leaf_facts (n := (Qof P).n) (C := 2 ^ R.μ)
    Nat.one_le_two_pow by_omega hF.hwf hxL
  have hNP := hF.hNP
  zulic
  zugnc
  have hpcL : ztgvp * lfB pc ≥ lfB pc := by
    have : 1 ≤ (R.leaves P).length - i := by_omega
    nlinarith
  zuejd
  have hdrop : (R.leaves P).drop i = x :: (R.leaves P).drop ztg := by
    simp_all
  rw [hdrop] at hgap
  obtain ⟨g1, g2, g3⟩ := hgap
  zumao
  have hT := E.table hF
  obtain ⟨t1, t2, t3⟩ := hT i hi
  rw [← hx] at t1 t2 t3
  have t3' : e.nmem (R.T + 3 * i + 1 + 1) = x.2.2 := t3
  have hTA := hF.hTA
  have hAW : e.nreg ALLOC ≤ W := by_omega
  have hTW : R.T + 3 * (R.leaves P).length ≤ W := by have := E.alloc; omega
  -- load the leaf
  obtain ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁, f₁⟩ : ∃ e₁ k₁, Exec P W lfLoad e e₁ k₁ ∧ k₁ = 5 ∧
      e₁.nreg 219226 = x.1 ∧ e₁.nreg 219227 = x.2.1 ∧ e₁.nreg 219228 = x.2.2 ∧ e₁.nmem = e.nmem ∧
      FrameM (fun q => decide (219226 ≤ q ∧ q ≤ 219229)) e e₁ := by
    obtain ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁⟩ : ∃ e₁ k₁, Exec P W lfLoad e e₁ k₁ ∧ k₁ = 5 ∧
        e₁.nreg 219226 = x.1 ∧ e₁.nreg 219227 = x.2.1 ∧ e₁.nreg 219228 = x.2.2 ∧
        e₁.nmem = e.nmem := by
      zudpm
      unfold lfLoad
      exec_block
      all_goals try (config_simp; (try simp only [hI.r24, E.r230]); omega)
    exact ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁, exec_frameM ex₁ by_decide⟩
  have fr₁ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₁ m₁ k₁
  zujza
  have E₁ := E.keep (fun q hq => f₁.1 q (by
    obtain ⟨-, -, -, b4, -⟩ := envRegs_band2 q hq
    grind)) by_grind by_omega
  have u₁ : ∀ q, (q < 219226 ∨ 219229 < q) → e₁.nreg q = e.nreg q := fun q hq => f₁.1 q (by
    grind)
  have hw₁ := ex₁.wb_right
  have p₁ : e₁.nreg 219221 = pos := by_grind
  -- the connector
  obtain ⟨e₃, k₃, γ₁, ex₃, hk₃, hw₃, E₃, A₃, hγ₁, hγ₁', u₃, o₃, fr₃⟩ : ∃ e₃ k₃ γ₁,
      Exec P W zttia e₁ e₃ k₃ ∧ k₃ ≤ pc + 10 ∧ WordsBounded W e₃ ∧ REnv R e₃ ∧
      AccOK P R e₃ x.1 γ₁ ∧ R.γ₀ ≤ γ₁ ∧ γ₁ ≤ R.γ₀ + 2 * i ∧
      (∀ q, q = 219004 ∨ q = 219220 ∨ q = 219221 ∨ q = 219224 ∨ q = 219226 ∨ q = 219227 ∨
        q = 219228 → e₃.nreg q = e₁.nreg q) ∧
      (∀ q, bandOf q = bDownDrv → zthjk → e₃.nreg q = e₁.nreg q) ∧
      Frame drvBands e₁ e₃ k₃ := by
    by_cases hlt : pos < x.1
    · obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, f₂⟩ : ∃ e₂ k₂, Exec P W
          _ e₁ e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
          e₂.nreg 219241 = x.1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
          e₂.nmem = e₁.nmem ∧ FrameM ztdun e₁ e₂ := by
        obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂⟩ : ∃ e₂ k₂, Exec P W
            (block [.copyN 219240 219221, .subN 219241 219226 219221, .constN 219242 0,
              .constN 219243 0]) e₁ e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
            e₂.nreg 219241 = x.1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
            e₂.nmem = e₁.nmem := by
          exec_block
          all_goals try (config_simp; (try zuodm); omega)
          refine ztcby <;> config_simp <;> zuodm
        exact ztfdg
      have fr₂ := frame_band (fun q hq => by
        zvmwo at hq; zvmxo; omega) f₂ m₂ k₂
      zujzb
      have E₂ := E₁.keep (fun q hq => f₂.1 q (by
        zubgu
        grind)) by_grind by_omega
      have u₂ : ∀ q, zthjl → e₂.nreg q = e₁.nreg q := fun q hq => f₂.1 q (by
        grind)
      have hacc : ztxsc ∨
          ztyak := by
        zuctk
        · grind
        · zumkz
          zufa
          exact (A.keep fr₁ by_grind).keep fr₂ by_grind
      have hγb : R.γ₀ ≤ ztbkq ∧
          ztbkq + 1 ≤ R.γ₀ + 2 * i + 1 := by
        grind
      obtain ⟨e₃, k₃, ex₃, hk₃, E₃, A₃, u₃, fr₃⟩ := pcS_exec hsp hM hF e₂
        ex₂.wb_right E₂ w40 w41 w42 w43 hacc hγb.1 by_omega by_omega
        by_omega by_omega by_omega
        by_grind
        (fun hp => by
          zucbr
          · omega
          · exact hj)
        (by have h1 : ztidx := rfl; omega)
      refine ⟨e₃, k₂ + k₃ + 1, if pos = 0 then R.γ₀ else γ + 1, .ifLtN_true (by
        omega) (.seq ex₂ ex₃), by_omega, ex₃.wb_right, E₃,
        by rw [show pos + (x.1 - pos) = x.1 by omega] at A₃; split_ifs at A₃ ⊢ <;> exact A₃,
        ?_, ?_, fun q hq => ?_, fun q hq hq' => ?_, ?_⟩
      · zuwd
      · rcases hst with ⟨hi0, hp0, -⟩ | ⟨-, hp0, -, -, h2, -⟩
        · grind
        · zujkg
      · rw [u₃ q (by simp only [bandOf, bDownDrv]; omega) by_omega, u₂ q by_omega]
      · rw [u₃ q hq by_omega, u₂ q by_omega]
      · have := fr₂.trans fr₃
        zubpw

    · have heq : pos = x.1 := by_omega
      zucbs
      · omega
      refine ⟨e₁, 0 + 2, γ, .ifLtN_false by_omega ztekd, by_omega, hw₁,
        E₁, by zvnbo; exact A.keep fr₁ by_grind, h1, by_omega,
        by omega, by_omega, ?_⟩
      exact frame_refl _ _ _
  have hA₃ := fr₃.2.2.2.2.2.2
  have p26 : e₃.nreg 219226 = x.1 := by_grind
  have p27 : e₃.nreg 219227 = x.2.1 := by_grind
  have p28 : e₃.nreg 219228 = x.2.2 := by_grind
  -- the leaf
  obtain ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄, f₄⟩ : ∃ e₄ k₄, Exec P W
      (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1, .copyN 219243 219228])
      e₃ e₄ k₄ ∧ k₄ = 4 ∧ e₄.nreg 219240 = x.1 ∧ e₄.nreg 219241 = x.2.1 ∧ e₄.nreg 219242 = 1 ∧
      e₄.nreg 219243 = x.2.2 ∧ e₄.nmem = e₃.nmem ∧
      FrameM ztdun e₃ e₄ := by
    obtain ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄⟩ : ∃ e₄ k₄, Exec P W
        (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1,
          .copyN 219243 219228]) e₃ e₄ k₄ ∧ k₄ = 4 ∧ e₄.nreg 219240 = x.1 ∧
        e₄.nreg 219241 = x.2.1 ∧ e₄.nreg 219242 = 1 ∧ e₄.nreg 219243 = x.2.2 ∧
        e₄.nmem = e₃.nmem := by
      have hw := hw₃
      exec_block
      all_goals try (config_simp; (try zunvd); omega)
      refine ztcby <;> config_simp <;> zunvd
    exact ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄, exec_frameM ex₄ by_decide⟩
  have fr₄ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₄ m₄ k₄
  have hA₄ := f₄.1 ALLOC by_decide
  have E₄ := E₃.keep (fun q hq => f₄.1 q (by
    zubgu
    grind)) by_grind by_omega
  have u₄ : ∀ q, zthjl → e₄.nreg q = e₃.nreg q := fun q hq => f₄.1 q (by
    grind)
  have A₄ := A₃.keep fr₄ fun q hq => u₄ q by_omega
  obtain ⟨e₅, k₅, ex₅, hk₅, E₅, A₅, u₅, fr₅⟩ := pcS_exec (P := P) (W := W) hsp hM hF e₄
    ex₄.wb_right E₄ w40 w41 w42 w43 (Or.inr ⟨by_omega, A₄⟩) hγ₁ by_omega x2
    by_omega by_omega (fun _ => ⟨x3, x4, x6⟩) (fun h => absurd h by_norm_num)
    (fun _ => x7)
    (by have h1 : ztidx := rfl; omega)
  zvmyd at A₅
  have hA₅ := fr₅.2.2.2.2.2.2
  have hw₅ := ex₅.wb_right
  have s26 : e₅.nreg 219226 = x.1 := by
    rw [u₅ _ by_rfl by_omega, u₄ _ by_omega, p26]
  have s27 : e₅.nreg 219227 = x.2.1 := by
    rw [u₅ _ by_rfl by_omega, u₄ _ by_omega, p27]
  have s20 : e₅.nreg 219220 = i := by
    rw [u₅ _ by_rfl by_omega, u₄ _ by_omega, u₃ _ by_simp,
      u₁ _ by_omega, hI.r20]
  have s24 : e₅.nreg 219224 = R.T + 3 * i := by
    rw [u₅ _ by_rfl by_omega, u₄ _ by_omega, u₃ _ by_simp,
      u₁ _ by_omega, hI.r24]
  have s04 : e₅.nreg 219004 = (R.leaves P).length := by
    rw [u₅ _ by_rfl by_omega, u₄ _ by_omega, u₃ _ by_simp,
      u₁ _ by_omega, hI.r04]
  have hNPW : R.NP ≤ W := by have := hw₅.1 219201; rw [E₅.r201] at this; omega
  -- advance
  obtain ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆, f₆⟩ : ∃ e₆ k₆, Exec P W lfAdv e₅ e₆ k₆ ∧ k₆ = 3 ∧
      e₆.nreg 219221 = x.1 + x.2.1 ∧ e₆.nreg 219220 = i + 1 ∧ e₆.nreg 219224 = R.T + 3 * ztg ∧
      e₆.nmem = e₅.nmem ∧
      FrameM (fun q => decide (q = 219220 ∨ q = 219221 ∨ q = 219224)) e₅ e₆ := by
    obtain ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆⟩ : ∃ e₆ k₆, Exec P W lfAdv e₅ e₆ k₆ ∧ k₆ = 3 ∧
        e₆.nreg 219221 = x.1 + x.2.1 ∧ e₆.nreg 219220 = i + 1 ∧
        e₆.nreg 219224 = R.T + 3 * ztg ∧ e₆.nmem = e₅.nmem := by
      have hw := hw₅
      unfold lfAdv
      exec_block
      all_goals try (config_simp; (try zunhm); omega)
      refine ztdqw <;> config_simp <;>
        zunhm; ring
    exact ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆, exec_frameM ex₆ by_decide⟩
  have fr₆ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₆ m₆ k₆
  have hA₆ := f₆.1 ALLOC by_decide
  have E₆ := E₅.keep (fun q hq => f₆.1 q (by
    obtain ⟨b1, b2, -, b4, -⟩ := envRegs_band2 q hq
    grind)) by_grind by_omega
  have A₆ : AccOK P R e₆ _ _ := A₅.keep fr₆ fun q hq => f₆.1 q (by
    zvnan; omega)
  refine ⟨e₆, k₁ + (k₃ + (ztjzr + k₆)), .seq ex₁ (.seq ex₃ (.seq (.seq ex₄ ex₅) ex₆)),
    ⟨ex₆.wb_right, fun q hq hq' => ?_, y20, by rw [f₆.1 _ by_decide, s04], E₆, y24, by_omega,
      ?_,
      x.1 + x.2.1, γ₁ + 1, y21, g3, by_grind⟩,
    by unfold lfB; omega, ?_⟩
  · rw [f₆.1 q ztmz,
      u₅ q hq by_omega, u₄ q by_omega, o₃ q hq hq', u₁ q by_omega]
    exact hI.keep q hq hq'
  · have h1 : ztidx := rfl
    have e1 : ztgvp * lfB pc =
        ((R.leaves P).length - ztg) * lfB pc + lfB pc := by
      rw [show (R.leaves P).length - i = (R.leaves P).length - ztg + 1 by omega, Nat.succ_mul]
    have := fr₁.2.2.2.2.2.2
    omega
  · have := (((fr₁.trans fr₃).trans fr₄).trans fr₅).trans fr₆
    grind

/-- **The leaf loop.** -/
theorem lfLoop_exec (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ ztjjo ztjjp cutGran ztsy OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Rb : ℕ} (e : Config)
    (hI : LInv P W R V ztxhb Rb 0 e) :
    ∃ e' k, Exec P W zttsi e e' k ∧
      LInv P W R V ztxhb Rb (R.leaves P).length e' ∧
      k ≤ ztzmt * (R.leaves P).length + 2 ∧
      Frame drvBands e e' k := by
  obtain ⟨e', k, ex, hI', hk, fr⟩ := forLoopF (P := P) (W := W) (ir := 219220) (nr := 219004)
    (B := drvBands) (LInv P W R V ztxhb Rb)
    ztxhb (R.leaves P).length
    (fun j c h => ⟨h.wb, h.r20, h.r04⟩)
    (fun j c hj h => lfBody_exec hsp hM hF c hj h) hI ztbg
  exact ⟨e', k, ex, hI', by_omega, fr⟩
set_option maxHeartbeats 4000000 in
/-- **The last connector.** -/
theorem finCon_exec (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ ztjjo ztjjp cutGran ztsy OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Lb : ℕ} (e : Config)
    (hI : LInv P W R V Lb ztyrl (R.leaves P).length e) :
    ∃ e' k γ, Exec P W zttkb e e' k ∧ k ≤ pcB κP ztddr κs ztgks + 6 ∧
      WordsBounded W e' ∧ REnv R e' ∧ AccOK P R e' ztnoi γ ∧ R.γ₀ ≤ γ ∧
      γ ≤ R.γ₀ + 2 * (R.leaves P).length ∧
      (∀ q, bandOf q = bDownDrv → zthjk → e'.nreg q = e.nreg q) ∧
      Frame drvBands e e' k := by
  zugyt
  zumao
  zudpm
  have hNP3 := hF.hNP3
  zugnc
  zuejd
  rw [List.drop_length] at hgap
  obtain ⟨g1, g2⟩ := hgap
  by_cases hlt : pos < R.NP - 1
  · obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, f₂⟩ : ∃ e₂ k₂, Exec P W
        _ e e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
        e₂.nreg 219241 = R.NP - 1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
        e₂.nmem = e.nmem ∧ FrameM ztdun e e₂ := by
      obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂⟩ : ∃ e₂ k₂, Exec P W
          (block [.copyN 219240 219221, .subN 219241 219223 219221, .constN 219242 0,
            .constN 219243 0]) e e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
          e₂.nreg 219241 = R.NP - 1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
          e₂.nmem = e.nmem := by
        exec_block
        all_goals try (config_simp; (try zuodn); omega)
        refine ztcby <;> config_simp <;> zuodn
      exact ztfdg
    have fr₂ := frame_band (fun q hq => by
      zvmwo at hq; zvmxo; omega) f₂ m₂ k₂
    zujzb
    have E₂ := E.keep (fun q hq => f₂.1 q (by
      zubgu
      grind)) by_simp_all by_omega
    have u₂ : ∀ q, zthjl → e₂.nreg q = e.nreg q := fun q hq => f₂.1 q (by
      grind)
    have hacc : ztxsc ∨
        ztyak := by
      zuctk
      · simp_all
      · zumkz
        zufa
        exact A.keep fr₂ by_simp_all
    zulic
    have hγb : R.γ₀ ≤ ztbkq ∧
        ztbkq + 1 ≤ R.γ₀ + 2 * (R.leaves P).length + 1 := by
      grind
    obtain ⟨e₃, k₃, ex₃, hk₃, E₃, A₃, u₃, fr₃⟩ := pcS_exec hsp hM hF e₂
      ex₂.wb_right E₂ w40 w41 w42 w43 hacc hγb.1 by_omega by_omega by_omega by_omega
      by_omega by_grind
      (fun hp => by
        zucbr
        · omega
        tauto)
      by_omega
    refine ⟨e₃, k₂ + k₃ + 1, if pos = 0 then R.γ₀ else γ + 1, .ifLtN_true (by
      zuojd; omega) (.seq ex₂ ex₃), by_omega, ex₃.wb_right, E₃,
      by grind,
      ?_, ?_, fun q hq hq' => by_grind, ?_⟩
    · grind
    · grind
    · have := fr₂.trans fr₃
      zubpw

  · have heq : pos = R.NP - 1 := by_omega
    zucbs
    · omega
    refine ⟨e, 0 + 2, γ, .ifLtN_false (by zuojd; omega) ztjd, by_omega, hw,
      E, by_simp_all, h1, by_omega, by_omega, frame_refl _ _ _⟩
end exec
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
theorem rgInit0_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W rgInit0 c c' k ∧ k = 2 ∧ c'.nreg 219000 = c.nreg 219200 ∧
      c'.nreg 219002 = c.nreg 219203 ∧ c'.nmem = c.nmem ∧
      FrameM (fun q => decide ztofe) c c' ∧ c'.rreg = c.rreg := by
  obtain ⟨c', k, ex, hk, h1, h2, hm⟩ : ∃ c' k, Exec P W rgInit0 c c' k ∧ k = 2 ∧
      c'.nreg 219000 = c.nreg 219200 ∧ c'.nreg 219002 = c.nreg 219203 ∧ c'.nmem = c.nmem := by
    unfold rgInit0
    exec_block
    simp
  exact ⟨c', k, ex, hk, h1, h2, hm, exec_frameM ex by_decide,
    funext fun r => exec_frameM2 ex (BN := fun q => decide ztofe)
      (BR := fun _ => false) by_decide r rfl⟩

/-- **The padding loop** runs exactly `3 (r9999 - r219250) + 2` steps. -/
theorem rgPadLoop_exec : ∀ (m : ℕ) (c : Config), WordsBounded W c → c.nreg 219251 = 1 →
    c.nreg 219250 ≤ c.nreg 9999 → c.nreg 9999 - c.nreg 219250 = m →
    Exec P W ztipx c
      { c with nreg := upd c.nreg 219250 (c.nreg 9999) } (3 * m + 2)
  | 0, c, hw, _, hle, hd => by
    have h : c.nreg 219250 = c.nreg 9999 := by_omega
    refine ztgvg
    zuezs
  | m + 1, c, hw, h51, hle, hd => by
    have e := Exec.addN (P := P) hw 219250 219250 219251 (by zuovg; have := hw.1 9999; omega)
    have h1 : ztfcp 219251 = 1 := by
      simp_all
    have h2 : ztfcp 9999 = c.nreg 9999 :=
      upd_other _ _ _ by_decide
    have h3 : ztfcp 219250 = c.nreg 219250 + 1 := by
      simp_all
    have e' := rgPadLoop_exec m _ e.wb_right h1 by_grind
      by_grind
    refine ((Exec.whileLtN_true by_omega ztztl e').cast
      by_ring).cast_end ?_
    simp

/-- **The padding**: exactly `3 (r9999 - r219003) + 4` steps. -/
theorem rgPad_exec (hw : WordsBounded W c) (hs : c.nreg 219003 ≤ c.nreg 9999)
    (hW : 1 ≤ W) :
    ∃ c', Exec P W rgPad c c' (3 * (c.nreg 9999 - c.nreg 219003) + 4) ∧
      (∀ r, r ≠ 219250 → r ≠ 219251 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₁ := Exec.copyN (P := P) hw 219250 219003
  have e₂ := Exec.constN (P := P) e₁.wb_right 219251 1 hW
  have a50 : ztecx 219250 = c.nreg 219003 := by
    simp
  have a51 : ztecx 219251 = 1 := upd_same _ _ _
  have aA : ztecx 9999 = c.nreg 9999 := by
    simp
  have e₃ := rgPadLoop_exec (P := P) _ _ e₂.wb_right a51 by_simp_all
    rfl
  refine ⟨_, (Exec.seq (Exec.seq e₁ (Exec.seq e₂ ztdyc)) e₃).cast
    by_grind, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp_all

/-- The registers `rgInit1` writes. -/
def Bi1 (q : ℕ) : Bool :=
  decide (219140 ≤ q ∧ q ≤ 219146) || decide (219100 ≤ q ∧ q ≤ 219107) ||
    decide (219220 ≤ q ∧ q ≤ 219231) || decide zttwz
set_option maxHeartbeats 1000000 in
theorem rgInit1_exec (hw : WordsBounded W c) {HB NP T Hl : ℕ}
    (h00 : c.nreg 219200 = HB) (h01 : c.nreg 219201 = NP) (h03 : c.nreg 219003 = T)
    (hHl : c.nmem HB = Hl) (hW : c.nreg 9999 + 130 ≤ W) :
    ∃ c' k, Exec P W rgInit1 c c' k ∧ k = 20 ∧ MgConst c' ∧ c'.nreg 219100 = HB ∧
      c'.nreg 219101 = NP ∧ c'.nreg 219103 = 130 ∧ c'.nreg 219104 = c.nreg 219205 ∧
      c'.nreg 219107 = Hl ∧ c'.nreg 219230 = 1 ∧ c'.nreg 219231 = 3 ∧ c'.nreg 219220 = 0 ∧
      c'.nreg 219221 = 0 ∧ c'.nreg 219222 = 0 ∧ c'.nreg 219223 = NP - 1 ∧ c'.nreg 219224 = T ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nmem = c.nmem ∧ FrameM Bi1 c c' ∧ c'.rreg = c.rreg := by
  obtain ⟨c', k, ex, hk, h40, h41, h42, h43, h44, h45, h46, a00, a01, a03, a04, a07, a30, a31,
      a20, a21, a22, a23, a24, aA, hm⟩ : ∃ c' k, Exec P W rgInit1 c c' k ∧ k = 20 ∧
      c'.nreg 219140 = 0 ∧ c'.nreg 219141 = 1 ∧ c'.nreg 219142 = 2 ∧ c'.nreg 219143 = 3 ∧
      c'.nreg 219144 = 4 ∧ c'.nreg 219145 = 5 ∧ c'.nreg 219146 = 6 ∧ c'.nreg 219100 = HB ∧
      c'.nreg 219101 = NP ∧ c'.nreg 219103 = 130 ∧ c'.nreg 219104 = c.nreg 219205 ∧
      c'.nreg 219107 = Hl ∧ c'.nreg 219230 = 1 ∧ c'.nreg 219231 = 3 ∧ c'.nreg 219220 = 0 ∧
      c'.nreg 219221 = 0 ∧ c'.nreg 219222 = 0 ∧ c'.nreg 219223 = NP - 1 ∧ c'.nreg 219224 = T ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nmem = c.nmem := by
    unfold rgInit1
    exec_block
    all_goals try (config_simp; (try zunom); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      rfl⟩ <;> config_simp <;> (try zunom)
  exact ⟨c', k, ex, hk, ⟨h40, h41, h42, h43, h44, h45, h46⟩, a00, a01, a03, a04, a07, a30, a31,
    a20, a21, a22, a23, a24, aA, hm, exec_frameM ex by_decide,
    funext fun r => exec_frameM2 ex (BN := Bi1) (BR := fun _ => false) by_decide r rfl⟩
end exec
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace DrvG
open Machine Machine.Stmt Programs BuildRam DrvR
@[expose] public section
def rgK (κP κM κs : ℕ) : ℕ := 121 * κP + 121 * mcK κM κs + 200000
theorem lfB_def (pc : ℕ) : lfB pc = 2 * pc + 30 := rfl
section exec
variable {O : OracleIface} {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **The region procedure, one run.** -/
theorem rgS_run {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ} (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ ztjjo ztjjp cutGran ztsy OkModel)
    (c : Config) (hw : WordsBounded W c)
    (hPre : GoodEnv P ∧ hostWords P.n ≤ W ∧
      (gradeCtx O).holds P c.nmem ztdzl ztm ∧
      7 ≤ c.nreg 219202 ∧ c.nreg 219202 ≤ c.nmem ztdzl ∧
      c.nreg 219203 = 2 ^ c.nreg 219202 ∧
      2 * gradeGran ztdzk ≤ c.nreg 219204 ∧ 128 ≤ c.nreg 219204 ∧
      c.nreg 219204 ≤ 4096 * 2 ^ Cost.ceilBeta ztdzk ∧
      c.nreg 219204 + 129 ≤ (gradeCtx O).cap P c.nmem ztdzl ∧
      ∃ H : Host, Robust ztm c.nmem ztfbx ∧
        c.nreg 219200 + 3 * H.length + 1 ≤ c.nreg ALLOC ∧
        H.length ≤ 20 ∧ HostWF (Qof P).n H ∧ HostRegular (Qof P).n H ∧
        (H.poly zta).Simple ∧
        c.nreg 219201 = (H.pts (Qof P).n).length ∧ 3 ≤ c.nreg 219201 ∧
        ∀ a ℓ, HostItem.run a ℓ ∈ H → ℓ ≤ 2 * c.nreg 219203)
    (hroom : c.nreg ALLOC + rgK κP ztddr κs * ztxog ≤ W) :
    ∃ c' k, Exec P W (rgS sp sM) c c' k ∧
      k ≤ rgK κP ztddr κs * ztxog ∧
      (ztbfg ∧
      c.nreg ALLOC ≤ c'.nreg 219210 ∧ c.nreg ALLOC ≤ c'.nreg 219211 ∧
      c.nreg 219204 ≤ c'.nreg 219212 ∧ c'.nreg 219212 ≤ c.nreg 219204 + 128 ∧
      ModelDescWF P ztdo c'.nmem ztfgh ∧
      ∀ (H : Host) (C : Chain), HostAt c.nmem ztqhv H → C.P = H.poly zta →
        C.s = 0 → C.m + 1 = C.P.n →
        Robust ztdo c'.nmem
          (fun m => m ztfgh = 0 ∧
            ChainDescAt m ztcyy zta H C ∧
            m ztcyy = c.nreg 219200) ∧
        ∃ N, NFWithin c'.nmem ztmfg ztdo N ∧
          IsCanonicalNF ztc zta N ztmfh regCap) ∧
      Frame drvBands c c' k := by
  obtain ⟨hG, hWn, hX0, hμ7, hμg0, hC, hg0, h128, hg1, hcap0, H, hHA0, hHB0, hHl, hwf, hreg,
    hsimp, hNP, hNP3, hruns⟩ := hPre
  zuhp
  zuiag
  zucgu
  zufut
  set μ := c.nreg 219202 with hμ
  set L := lemma41Nat μ with hLdef
  set pc := pcB κP ztddr κs L with hpc
  have hrgK : 121 * pc + 5000 ≤ rgK κP ztddr κs * ztgt := by
    unfold rgK; rw [hpc]; unfold pcB
    grind
  have hHA0' : HostAt c.nmem _ H := hHA0.holds
  have hwfP : HostWF P.n H := by_simp_all
  have hK60 : (hostLeaves P.n ztjfm 0 H).length ≤ 60 := by
    have := hostLeaves_length_le (n := P.n) (C := 2 ^ μ) Nat.one_le_two_pow H 0
      by_grind
    omega
  have hptsW : (Host.pts P.n H).length + 2 * P.n + 1 ≤ W := by
    have := Host.pts_length_le hwfP
    have : H.length * P.n ≤ 20 * P.n := Nat.mul_le_mul_right _ hHl
    omega
  -- the planner's arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a02, m₁, f₁, rr₁⟩ := rgInit0_exec (P := P) c hw
  zuka
  zujza
  have g₁ : ∀ q, q ≠ 219000 → q ≠ 219002 → c₁.nreg q = c.nreg q := fun q h1 h2 => f₁.1 q (by
    simp_all)
  -- the leaf table
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, t03, t04, tA, tT, tlow, tK, tB, rr₂, rm₂, ro₂⟩ :=
    plS_exec (C := 2 ^ μ) Nat.one_le_two_pow hn3 c₁ hw₁ (H := H) a00 by_omega
      by_simp_all hwfP by_omega
      by_omega hptsW
  set K := (hostLeaves P.n ztjfm 0 H).length with hK
  have t9 : c₂.nreg 9999 = c.nreg ALLOC + 3 * K := by_grind
  have g₂ : ∀ q, (q < 219001 ∨ 219029 < q) → q ≠ 9999 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    tB q (by simp only [Bpl, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- the padding
  obtain ⟨c₃, e₃, g₃, rr₃, m₃, rm₃, ro₃⟩ := rgPad_exec (P := P) c₂ hw₂ by_omega
    by_omega
  zuboe
  have t9₃ : c₃.nreg 9999 = c.nreg ALLOC + 3 * K := by_grind
  have hk₃ : 3 * (c₂.nreg 9999 - c₂.nreg 219003) + 4 = 9 * K + 4 := by_omega
  have g₀₃ : ∀ q, (q < 219000 ∨ (219029 < q ∧ q ≠ 219250 ∧ q ≠ 219251)) → q ≠ 9999 →
      c₃.nreg q = c.nreg q := fun q h1 h2 => by
    rw [g₃ q by_omega by_omega, g₂ q by_omega h2, g₁ q by_omega by_omega]
  have hm₃ : ztblg := fun a ha => by
    grind
  -- the constants and the loop state
  obtain ⟨c₄, k₄, e₄, hk₄, mg₄, b100, b101, b103, b104, b107, b230, b231, b220, b221, b222, b223,
      b224, b9, hm₄, f₄, rr₄⟩ := rgInit1_exec (P := P) c₃ hw₃ (HB := c.nreg 219200)
    (NP := c.nreg 219201) (T := c.nreg ALLOC) (Hl := H.length)
    ztrrb ztrrb by_grind
    (by rw [hm₃ _ by_omega]; exact hHA0'.1) by_omega
  zubwq
  zudna
  have g₀₄ : ∀ q, (q < 219000 ∨ (219029 < q ∧ q < 219100) ∨ (219107 < q ∧ q < 219140) ∨
      (219146 < q ∧ q < 219220) ∨ (219231 < q ∧ q ≠ 219250 ∧ q ≠ 219251)) → q ≠ 9999 →
      c₄.nreg q = c.nreg q := fun q h1 h2 => by
    rw [g₄ q (by zunve; omega),
      g₀₃ q by_omega h2]
  have hA₄ : c₄.nreg ALLOC = c.nreg ALLOC + 3 * K + 3 := by
    grind
  have hT₄ : c₄.nreg 219003 = c.nreg ALLOC := by
    rw [g₄ _ by_decide, g₃ _ by_decide by_decide, t03, hA₁]
  have hK₄ : c₄.nreg 219004 = K := by
    rw [g₄ _ by_decide, g₃ _ by_decide by_decide, t04]
  have hm₄' : ztjbc := fun a ha => by
    grind
  -- the data of the run
  let R : RData := ⟨H, c.nreg 219200, c.nreg 219201, μ, c.nreg 219204, c.nreg 219205, c₄.nmem,
    c₄.nreg ALLOC, c.nreg ALLOC⟩
  have hleaves : R.leaves P = hostLeaves P.n ztjfm 0 H := by
    show hostLeaves (Qof P).n ztjfm 0 H = _; zuovh
  have hglt := gradeRaw_handle_lt hX0
  have hF : RFacts O P W R := by
    refine ⟨hG, hWn, (hHA0.transport hm₄').mono by_grind,
      by grind, hHl, hwf, hreg, hsimp, hNP,
      hNP3,
      fun a ℓ hm => by have := hruns a ℓ hm; grind, hμ7,
      by grind, hg0, h128, hg1,
      by show _ ≤ (gradeCtx O).cap P c₄.nmem ztdzl
         rw [gradeCtx_capLocal O P c.nmem c₄.nmem _ _ hm₄' hX0]; omega,
      ((gradeCtx O).local_ P _ _ _ _ by_grind hX0 |> (gradeCtx O).mono P _ _ _
        _ by_grind), ?_, ?_, ?_⟩
    · grind
    · grind
    · have := gradeCtx_cap_le by_omega hX0
      grind
  have hRl : (R.leaves P).length = K := by_grind
  have E₄ : REnv R c₄ := ⟨g₀₄ _ by_omega by_decide, g₀₄ _ by_omega by_decide,
    g₀₄ _ by_omega by_decide, g₀₄ _ by_omega by_decide, g₀₄ _ by_omega by_decide,
    b230, b231, b223, hT₄, mg₄, b100, b101, b103, by rw [b104, g₀₃ _ by_omega by_decide],
    b107, by_grind, le_refl _⟩
  have hgap : GapsLe 64 ((R.leaves P).drop 0) 0 ztnoi := by
    rw [List.drop_zero]
    have := hostLeaves_gaps (C := 2 ^ μ) Nat.one_le_two_pow by_omega hwf hHl
      (degCount_le_one hsimp) by_omega
    grind
  have hKL : K * lfB pc ≤ 60 * lfB pc := Nat.mul_le_mul_right _ hK60
  have I₄ : LInv P W R c.nreg ztxhb
      ztyrl 0 c₄ := by
    refine ⟨hw₄, fun q hq hq' => g₀₄ q by_omega
      (by zvmxo at hq; omega), b220, by_omega, E₄,
      by omega, Nat.zero_le _, ?_, 0, R.γ₀, b221, hgap, by_omega⟩
    show c₄.nreg ALLOC + ((R.leaves P).length - 0) * lfB pc + (pc + 2) ≤ W
    rw [hRl, hA₄, Nat.sub_zero]
    rw [lfB_def] at hKL ⊢
    have := hrgK
    omega
  -- the leaf loop and the last connector
  obtain ⟨c₅, k₅, e₅, I₅, hk₅, fr₅⟩ := lfLoop_exec hsp hM hF c₄ I₄
  obtain ⟨c₆, k₆, γf, e₆, hk₆, hw₆, E₆, A₆, hγf, hγf', o₆, fr₆⟩ := finCon_exec hsp hM hF c₅ I₅
  -- the outputs
  obtain ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇, f₇⟩ : ∃ c₇ k₇, Exec P W rgOut c₆ c₇ k₇ ∧ k₇ = 3 ∧
      c₇.nreg 219210 = c₆.nreg 219110 ∧ c₇.nreg 219211 = c₆.nreg 219111 ∧
      c₇.nreg 219212 = c₆.nreg 219113 ∧ c₇.nmem = c₆.nmem ∧
      FrameM (fun q => decide (219210 ≤ q ∧ q ≤ 219212)) c₆ c₇ := by
    obtain ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇⟩ : ∃ c₇ k₇, Exec P W rgOut c₆ c₇ k₇ ∧ k₇ = 3 ∧
        c₇.nreg 219210 = c₆.nreg 219110 ∧ c₇.nreg 219211 = c₆.nreg 219111 ∧
        c₇.nreg 219212 = c₆.nreg 219113 ∧ c₇.nmem = c₆.nmem := by
      have hw := hw₆
      unfold rgOut
      exec_block
      simp
    exact ⟨c₇, k₇, e₇, hk₇, z10, z11, z12, m₇, exec_frameM e₇ by_decide⟩
  -- the frames
  have Fr₁ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₁ m₁ k₁
  have Fr₂₃ : Frame drvBands c₁ c₃ (k₂ + ztjfp) := by
    refine ⟨fun r hr hrA => ?_, by_grind, fun a ha => ?_,
      by grind, by_grind, ?_, ?_⟩
    · zucwf

      rw [g₃ r by_omega by_omega, g₂ r by_omega hrA]
    · rw [m₃, tlow a ha]
    · grind
    grind
  have Fr₄ : Frame drvBands c₃ c₄ k₄ := by
    refine ⟨fun r hr hrA => g₄ r ?_, by_grind, by_grind,
      fun a ha => by rw [f₄.2.2.1], f₄.2.2.2, ?_, ?_⟩
    · zucwf

      zunve
      refine ⟨ztgy, ?_⟩
      omega
    · grind
    grind
  have Fr₇ := frame_band (fun q hq => by
    zvmwo at hq; zvmxo; omega) f₇ m₇ k₇
  have Fr := ((((Fr₁.trans Fr₂₃).trans Fr₄).trans fr₅).trans fr₆).trans Fr₇
  simp only [Finset.union_self] at Fr
  -- the cost
  have hk₅' : ztzmt * (R.leaves P).length ≤
      (lfB pc + 2) * 60 := by zuovi; exact Nat.mul_le_mul_left _ hK60
  have hcost : k₁ + (k₂ + (ztjfp + ztber)) ≤
      rgK κP ztddr κs * ztgt := by
    rw [hk₃]
    have e1 : pcB κP _ κs ztgks = pc := rfl
    have e2 : lfB (pcB κP _ κs ztgks) = 2 * pc + 30 := rfl
    zvnlz at hk₅' hk₅
    omega
  have hA₇ := f₇.1 ALLOC by_decide
  have hNPn : (H.poly zta).n = c.nreg 219201 := by rw [DownMath.host_poly_n, hNP]
  refine ⟨c₇, _, .seq e₁ ztfc, hcost,
    ⟨fun q hq hq' => ?_, ?_, ?_, ?_, ?_, ?_, fun H' C hH' hP hs hm => ?_⟩,
    by grind⟩
  · rw [f₇.1 q by_grind,
      o₆ q hq hq']
    exact I₅.keep q hq hq'
  · rw [z10]; have := A₆.lo1; grind
  · rw [z11]; have := A₆.lo2; grind
  · zuoje; omega
  · zuoje; grind
  · -- the model descriptor
    have hC1 : 1 ≤ c.nreg 219201 - 1 := by_omega
    let C : Chain := ⟨H.poly zta, 0, c.nreg 219201 - 1, hC1, by_omega⟩
    obtain ⟨hdR, N, hN, hc⟩ := A₆.desc C rfl rfl rfl
    obtain ⟨d0, d1, d2⟩ := hdR.holds
    have hHA6 : HostAt c₆.nmem _ H := (E₆.hostAt hF).holds
    refine ⟨by rw [z10, hA₇]; exact A₆.dA, fun _ => ?_⟩
    rw [z10, hA₇, m₇]
    exact DrvR.chainWF_host hHA6 by_omega hwfP
      (by have := E₆.alloc; grind) d2 d1
      (by have := A₆.dA; omega) by_grind
  · -- the chain and its normal form
    have hHH := NFLoc.hostAt_unique hH' hHA0'
    zular
    have hmC : C.m = c.nreg 219201 - 1 := by_grind
    obtain ⟨hdR, N, hN, hc⟩ := A₆.desc C hP hs hmC
    rw [z10, z11, z12, hA₇, m₇, A₆.r13]
    exact ⟨Robust.imp hdR by_grind, N, hN, hc⟩
end exec

/-- **D5: the region procedure.** -/
theorem regionSpec {O : OracleIface} (hM : MergeSpec) (hSC : ShootCutSpec O) (hPc : PieceSpec O) :
    RegionSpec O := by
  obtain ⟨sp, κP, hsp⟩ := (pieceSpec_iff O).1 hPc
  zuejl
  obtain ⟨mk, κ, hmk⟩ := L41.mergeMeets_of hM
  have hMM : L41.MergeMeets _ κ _ _ cutGran _
      OkModel :=
    hmk sh cu oracleBands oracleBands _ _ cutGran _ OkModel
      ztgjv ztqcs by_grind (L41.scF_mono κs)
      (L41.scG_mono κs) L41.cutGran_mono ztibe ztibe hsh hcu
  refine ⟨rgS sp ztdvk, rgK κP ztddr κs, ?_⟩
  zujar
  exact rgS_run hsp hMM c hw hPre hroom
end
end DrvG
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideE)

/-- **The chain of the input vertices `a, …, a + m`** of `Q`. -/
def subChain (Q : Polygon) (a m : ℕ) (hm1 : 1 ≤ m) (hm : m + 1 ≤ Q.n) : Chain :=
  ⟨Q, a, m, hm1, hm⟩
variable {Q : Polygon} {a m : ℕ} {hm1 : 1 ≤ m} {hm : m + 1 ≤ Q.n}
theorem subChain_vertex (k : ℕ) : (subChain Q a m hm1 hm).vertex k = Q.vtx (ztbzd % Q.n) := rfl

/-- **The chain model of a chain of the geometry polygon is served by the oracles.** -/
theorem okModel_sub {P : Polygon} (hG : GoodEnv P) {hm' : m + 1 ≤ (Qof P).n} :
    OkModel P (chainModel (subChain zta a m hm1 hm')) := by
  zuc
  zudos
  refine ⟨Host.whole P.n, subChain zta a m hm1 hm', by zuojy,
    by zvmxg; exact L41.hostRegular_whole hn, ?_, ?_, rfl⟩
  · have := L41.poly_whole zta by_omega; zvmxg at this; tauto
  · exact (shearInvariance ztbhs P).1 hG.1

/-- The start of the interior walk's pass along the chain. -/
noncomputable def uStart (Q : Polygon) (a m : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then a % Q.n else Q.n - 1 - ztfox % Q.n

/-- The tour position of the chain from which the interior walk reads it. -/
noncomputable def jStart (Q : Polygon) (m : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then 0 else m

/-- Reversed indices: `n - 1 - ((n - 1 - r + d) mod n) = (r + n - d) mod n`. -/
theorem rev_idx {n r d : ℕ} (hr : r < n) (hd : d < n) :
    n - 1 - ((n - 1 - r + d) % n) = ztquz % n := by
  rcases Nat.lt_or_ge d ztgu with h | h
  · rw [Nat.mod_eq_of_lt (by omega : n - 1 - r + d < n),
      show r + n - d = ztofg + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    omega
  · rw [show n - 1 - r + d = (d - r - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt by_omega]
    omega

/-- `(a + (m - d)) mod n = ((a + m) mod n + n - d) mod n` for `d ≤ m`, `d < n`. -/
theorem sub_idx {n a m d : ℕ} (hn : 0 < n) (hd : d ≤ m) (hdn : d < n) :
    (a + ztkao) % n = (ztfox % n + n - d) % n := by
  have h1 := Nat.div_add_mod ztfox n
  have hr : ztfox % n < n := Nat.mod_lt _ hn
  generalize ztfox / n = q at h1
  generalize ztfox % n = r at h1 hr ⊢
  rcases Nat.lt_or_ge r d with h | h
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := by
      zujdc
      · grind
      simp_all
    have e2 : n * (q' + 1) = n * q' + n := by_rfl
    have e : a + ztkao = ztquz + n * q' := by_omega
    simp_all
  · have e : a + ztkao = ztofg + n * q := by_omega
    rw [e, Nat.add_mul_mod_self_left, show r + n - d = ztofg + n by omega, Nat.add_mod_right]

/-- **The interior walk visits the tour of the chain.** -/
theorem iw_tour (hQn : 1 ≤ Q.n) {d : ℕ} (hd : d ≤ m) :
    (interiorWalk Q).vtx ((uStart Q a m + d) % (interiorWalk Q).n) =
      WalkEmbed.tourV ztpeg (jStart Q m) d := by
  have hn : ztcfx := Trans.iw_n
  zubdb
  unfold uStart jStart
  zucla
  · zuckr
    rw [ShootCut.tourV_up _ hd, Trans.iw_vtx_left hL, subChain_vertex, Nat.mod_add_mod]
  · zuckr
    have e : WalkEmbed.tourV ztpeg m d =
        (subChain Q a m hm1 hm).vertex ztkao := ShootCut.tourV_down _ hd
    rw [e, Trans.iw_vtx_right hL ztcv, subChain_vertex]
    zucr
    rw [rev_idx ztcv by_omega, sub_idx by_omega hd by_omega]
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

/-! ## Point sets by offsets -/

/-- The points of the walk `W` at offsets in `[x, y]` from its vertex `g`. -/
def oset (W : Polygon) (g : ℕ) (x y : ℝ) : Set Point :=
  {z | ∃ d : ℕ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x ≤ d + t ∧ (d : ℝ) + t ≤ y ∧
    z = lerp (W.vtx ztwnv) (W.vtx ((g + d + 1) % W.n)) t}
variable (W : Polygon) (g : ℕ)
theorem oset_union {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    oset W g x y ∪ oset W g y z = oset W g x z := by
  zumah
  · rintro (⟨d, t, h0, h1, h2, h3, rfl⟩ | ⟨d, t, h0, h1, h2, h3, rfl⟩)
    · exact ⟨d, t, h0, h1, h2, by_linarith, rfl⟩
    · exact ztioh
  · zufh
    by_cases h : (d : ℝ) + t ≤ y
    · exact Or.inl ⟨d, t, h0, h1, h2, h, rfl⟩
    · exact Or.inr ztioh
theorem oset_mono {x y x' y' : ℝ} (hx : x' ≤ x) (hy : y ≤ y') :
    oset W g x y ⊆ oset W g x' y' := by
  rintro _ ⟨d, t, h0, h1, h2, h3, rfl⟩
  exact ⟨d, t, h0, h1, by_linarith, by_linarith, rfl⟩

/-- **Agreeing stretches have the same point sets.** -/
theorem oset_congr {W W' : Polygon} {g g' L : ℕ} (hA : WalkEmbed.Agree W W' g g' L) {x y : ℝ}
    (hy : y ≤ L) : oset W g x y = oset W' g' x y := by
  have key : ∀ {V V' : Polygon} {h h' : ℕ}, WalkEmbed.Agree V V' h h' L →
      oset V h x y ⊆ oset V' h' x y := by
    intro V V' h h' hA' p hp
    obtain ⟨d, t, h0, h1, h2, h3, rfl⟩ := hp
    have hd : d ≤ L := by
      zujvv

    rcases h0.lt_or_eq with ht | rfl
    · have hd' : ztsht := by
        grind
      refine ⟨d, t, h0, h1, h2, h3, ?_⟩
      rw [hA' d hd, show h + d + 1 = h + ztet by ring, show h' + d + 1 = h' + ztet by ring,
        hA' _ hd']
    · refine ⟨d, 0, le_rfl, zero_le_one, h2, h3, ?_⟩
      simp only [lerp_zero]
      tauto
  exact Subset.antisymm (key hA) (key fun d hd => (hA d hd).symm)

/-- Shifting the base vertex by `k` steps. -/
theorem oset_shift (g k : ℕ) {x y : ℝ} (hx : 0 ≤ x) :
    oset W g (k + x) (k + y) = oset W (g + k) x y := by
  zumah
  · zufh
    by_cases hdk : k ≤ d
    · have e : ((d - k : ℕ) : ℝ) = d - k := Nat.cast_sub hdk
      refine ⟨d - k, t, h0, h1, by_grind, by_grind, ?_⟩
      simp_all
    · have hdk' : (d : ℝ) + 1 ≤ k := by exact_mod_cast by_simp_all
      zucmr
      zukgx
      have hdk1 : d + 1 = k := by
        have : (k : ℝ) ≤ d + 1 := by_linarith
        have : k ≤ d + 1 := by exact_mod_cast this
        omega
      have hk' : (k : ℝ) = d + 1 := by_grind
      refine ⟨0, 0, le_rfl, zero_le_one, by_simp_all, by_simp_all, ?_⟩
      rw [ht, lerp_one, lerp_zero, Nat.add_assoc, hdk1, Nat.add_zero]
  · zufh
    refine ⟨k + d, t, h0, h1, by_grind, by_grind, ?_⟩
    grind

/-! ## Point sets of key intervals -/

/-- **An unwrapped key interval from a walk vertex** is an `oset`. -/
theorem wset_eq_oset (M : Model) {g : ℕ} (hg : g < M.W.n) {x y : ℝ} (hx : 0 ≤ x) :
    ShootCut.wset M ztmyw ((g : ℝ) + y) = oset M.W g x y := by
  zuiy
  zumaj
  · zudc
    set K : ℤ := (p : ℤ) - j * M.W.n - g with hK
    have hKr : (K : ℝ) = X - g - t := by rw [hK]; push_cast; linarith
    have hK1 : (-1 : ℝ) ≤ K := by_grind
    have hK1' : -1 ≤ K := by exact_mod_cast hK1
    rcases (show K = -1 ∨ 0 ≤ K by omega) with hKe | hKe
    · have hr : (K : ℝ) = -1 := by exact_mod_cast hKe
      zucmr
      zukgx
      refine ⟨0, 0, le_rfl, zero_le_one, by_simp_all, by_grind, ?_⟩
      have hgz : (g : ℤ) = ((p + 1 : ℕ) : ℤ) + (-j) * M.W.n := by
        grind
      have hgp : g = ztr % M.W.n := by
        have h1 : ((g % M.W.n : ℕ) : ℤ) = ((ztr % M.W.n : ℕ) : ℤ) := by
          rw [Int.natCast_mod, Int.natCast_mod, hgz, Int.add_mul_emod_self_right]
        rw [← Nat.mod_eq_of_lt hg]
        omega
      rw [ht, lerp_one, lerp_zero, Nat.add_zero, Nat.mod_eq_of_lt hg, hgp]
      rfl
    · lift K to ℕ using hKe with d hd
      have hdz : ((g + d : ℕ) : ℤ) = (p : ℤ) + (-j) * M.W.n := by_grind
      have hKr' : (d : ℝ) = X - g - t := by_omega
      have hgd : ztbe % M.W.n = p := by
        have h1 : ((ztbe % M.W.n : ℕ) : ℤ) = ((p % M.W.n : ℕ) : ℤ) := by
          simp_all
        rw [← Nat.mod_eq_of_lt hp]
        omega
      refine ⟨d, t, h0, h1, by_grind, by_grind, ?_⟩
      rw [hgd, show g + d + 1 = ztbe + 1 by ring, ← Nat.mod_add_mod, hgd]
      rfl
  · zufh
    refine ⟨ztbe % M.W.n, t, Nat.mod_lt _ hn, h0, h1, ⟨g + d + t, by_linarith, by_linarith,
      -((ztbe / M.W.n : ℕ) : ℤ), ?_⟩, ?_⟩
    · have e := Nat.mod_add_div ztbe M.W.n
      have e' : ((ztbe % M.W.n : ℕ) : ℝ) + M.W.n * (ztbe / M.W.n : ℕ) = g + d := by
        exact_mod_cast e
      simp only [Int.cast_neg, Int.cast_natCast]
      linarith
    · zujqa
      simp

/-- **The point set of a closed cyclic key interval** starting inside the walk edge `u` (key
`u + t₁`, `0 ≤ t₁ < 1`) is the `oset` of offsets `[t₁, t₁ + len]`. -/
theorem arcSet_eq_oset (M : Model) {u : ℕ} (hu : u < M.W.n) {t₁ b : ℝ} (ht0 : 0 ≤ t₁)
    (ht1 : t₁ < 1) (hb : 0 ≤ b) (hbn : b < M.W.n) :
    M.arcSet zteji b = oset M.W u t₁ (t₁ + ShootCut.len M.W.n zteji b) := by
  have hun : (u : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hu
  rw [ShootCut.arcSet_eq_wset M by_positivity by_linarith hb hbn, ← wset_eq_oset M hu ht0]
  zucr
  unfold ShootCut.len
  grind

/-- **The unwrapped length** of the key interval from `u + t₁` to `(u + e) mod n + t₂`, for an
end at offset `e + t₂` within one lap. -/
theorem len_key {n u e : ℕ} (hu : u < n) {t₁ t₂ : ℝ} (ht1 : t₁ < 1) (ht2 : 0 ≤ t₂)
    (hlt : t₁ < e + t₂) (hlap : (e : ℝ) + t₂ ≤ t₁ + n) :
    ShootCut.len n zteji ((ztfuy % n : ℕ) + t₂) = e + t₂ - t₁ := by
  unfold ShootCut.len
  by_cases h : u + e < n
  · zukp
    grind
  · have hen : e ≤ n := by
      have : (e : ℝ) < n + 1 := by_linarith
      have : e < n + 1 := by exact_mod_cast this
      omega
    have hm : ztfuy % n = u + e - n := by
      zul
    zucjq
    have e1 : ((u + e - n : ℕ) : ℝ) = u + e - n := by
      simp_all
    grind

/-! ## Positions at the same offset -/
theorem wa_mod (M : Model) (g d : ℕ) : M.wa ztwje = M.W.vtx ztwje := rfl
theorem wb_mod (M : Model) (g d : ℕ) :
    M.wb ztwje = M.W.vtx (ztzvu % M.W.n) := by
  zumrf
  grind

/-- Positions at the same offset of agreeing stretches have the same parameter. -/
theorem param_agree {M M' : Model} {g g' L : ℕ} (hA : WalkEmbed.Agree M.W M'.W g g' L)
    (Q : Polygon) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.param Q ztwvk = M'.param Q ztxia := by
  zufde
  zubi
  rw [wb_mod, wb_mod, wa_mod, wa_mod, hA d hd.le, hA _ hd]

/-- Positions at the same offset of agreeing stretches have the same point. -/
theorem pos_agree {M M' : Model} {g g' L : ℕ} (hA : WalkEmbed.Agree M.W M'.W g g' L)
    (Q : Polygon) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.pos Q ztwvk = M'.pos Q ztxia := by
  zueew
  zubi
  rw [param_agree hA Q hd h, wb_mod, wb_mod, wa_mod, wa_mod, hA d hd.le, hA _ hd]

/-- The parameter of a vertex position (height code `0`) is `0`. -/
theorem param_zero (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ztjy = 0 := rfl

/-! ## Weights by offsets -/
theorem keyCeil_le {e : ℕ} {f : ℝ} : e ≤ keyCeil e f := by
  zufdj

/-- **The weight of a key interval by offsets.**  If the counted walk edges are `[lo, hi)`,
`hi ≤ n`, the key interval from `u + t₁` (`lo ≤ u`) to `(u + e) mod n + t₂` (within one lap, and
not wrapping past `hi` when `lo > 0`) meets `⌈e + t₂⌉` counted edges. -/
theorem arcWt_off (M : Model) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → ztceo) (hhi : hi ≤ M.W.n) {u e : ℕ}
    (hu : u < M.W.n) (hlo : lo ≤ u) {t₁ t₂ : ℝ} (ht0 : 0 ≤ t₁) (ht1 : t₁ < 1) (ht2 : 0 ≤ t₂)
    (ht21 : t₂ < 1) (hlt : t₁ < e + t₂)
    (hwrap : (lo = 0 ∧ hi = M.W.n ∧ keyCeil e t₂ ≤ M.W.n) ∨ (u + keyCeil e t₂ ≤ hi ∧ hi < M.W.n)) :
    M.arcWt zteji ((ztfuy % M.W.n : ℕ) + t₂) = keyCeil e t₂ := by
  zuiy
  rw [M.arcWt_closed hc hhi by_simp_all by_simp_all]
  have hke : keyCeil (ztfuy % M.W.n) t₂ = ztfuy % M.W.n + (keyCeil e t₂ - e) := by
    zufdj
  have hk1 : keyCeil e t₂ ≤ e + 1 := by unfold keyCeil; grind
  have hk0 : e ≤ keyCeil e t₂ := keyCeil_le
  have hkp : keyCeil e t₂ = e → t₂ = 0 := by
    zumtf
  unfold arcWtNat
  rcases hwrap with ⟨rfl, rfl, hkn⟩ | hwrap
  · by_cases h : u + e < M.W.n
    · zvnnm at hke ⊢
      grind
    · have hm : ztfuy % M.W.n = u + e - M.W.n := by
        zul
      zvmwi at hke ⊢
      have e1 : ((u + e - M.W.n : ℕ) : ℝ) = u + e - M.W.n := by
        simp_all
      have hnot : ¬ ((u : ℝ) + t₁ < ((u + e - M.W.n : ℕ) : ℝ) + t₂) := by
        zukd
        intro hlt'
        -- then `n < e + t₂ - t₁ + …`: the key would lie beyond one lap
        have : (M.W.n : ℝ) + t₁ < e + t₂ := by_linarith
        have hkr : (keyCeil e t₂ : ℝ) ≤ M.W.n := by exact_mod_cast hkn
        rcases Nat.lt_or_ge e (keyCeil e t₂) with h2 | h2
        · have : (e : ℝ) + 1 ≤ M.W.n := by
            have : e + 1 ≤ M.W.n := by_omega
            zufc
          linarith
        grind
      grind
  · obtain ⟨hwrap, hhn⟩ := hwrap
    have hue : u + e < M.W.n := by_omega
    rw [Nat.mod_eq_of_lt hue] at hke ⊢
    rw [ite_eq_left by_grind, hke]
    omega
