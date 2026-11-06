module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.DownPhaseDrvXRamH
public import Chazelle.Core.SweepIoHoles

section
set_option hygiene false
local macro "zqrh" : tactic => `(tactic| (intro x hx hk; have hkey : (chainModel C).key _ x = x.edge + (chainModel C).param (Qof P) x := rfl))
local macro "zqri" : tactic => `(tactic| (have e1 : ztwc := hk1; have s1 : IScr (240000 + 1015) := iscr_sw by_norm_num by_norm_num))
local macro "zqrj" : tactic => `(tactic| (have e1 : ztlyg := hK1₄; have e2 : c₄.nreg 241005 = pre.length := by rw [← w2]; tauto))
local macro "zqrk" : tactic => `(tactic| rw [upd_other _ _ _ by_decide, k2 _ by_decide])
local macro "zqrl" : tactic => `(tactic| simp only [regB, regI, upd, gK, gT, K1, sw])
local macro "zqrm" : tactic => `(tactic| obtain ⟨-, -, -, hgN', -, -⟩ := hg)
set_option hygiene true

/-!
# The sweep RAM (WP-D), answers: gathering the arcs of a list of regions

The shot wrapper reads the arcs to shoot at from a contiguous array of four-word records.
`gather` copies there, at the allocator on entry, the arcs of the regions listed in memory
(`gL`, `gC` entries) of the normal form at `gNF`, each end normalised (`normS`): the record `k`
holds the normalised ends of the `k`-th arc of `regArcs N rs` (the arc lists of the regions,
concatenated).  The allocator ends `4` words per arc higher.

Also: `IRS.whileP` (a loop with a potential), `put4` (four stores at the allocator).
-/
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## A loop with a potential -/

/-- **A loop with a potential** `Φ`: an iteration of cost at most `K` lowers the potential by at
least `K + 2`. -/
theorem IRS.whileP {a b : ℕ} {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hbody : ∀ c, IInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Φ c ≤ W →
      ∃ K, IRS P W c₀ body c K (fun c' => I c' ∧ Φ c' + K + 2 ≤ Φ c))
    (hI : IInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + Φ c ≤ W) :
    IRS P W c₀ ztpx c (Φ c + 2) ztcpy := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · obtain ⟨K, c₁, k₁, e₁, hk₁, hI₁, hfr₁, hc₁, hΦ₁⟩ := hbody c hI hc ht hroom
      zumbm
      have hroom₁ : c₁.nreg ALLOC + Φ c₁ ≤ W := by_omega
      obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := ih ztgnc by_omega hI₁ hc₁ hroom₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, by_omega, hI',
        (hfr₁.trans hfr₂).mono by_omega, hq⟩
    · exact ztfwb

/-! ## Registers of the gather -/

/-- Inputs: the normal form handle, the address and length of the region list, the chain
descriptor register (a register number, read by `normS`). -/
def gNF : ℕ := sw 1000
def gL : ℕ := sw 1001
def gC : ℕ := sw 1002
/-- Outputs: the base of the arc array and the number of arcs. -/
def gBase : ℕ := sw 1004
def gK : ℕ := sw 1005
/-- Working registers. -/
def gI : ℕ := sw 1006
def gR : ℕ := sw 1007
def gT : ℕ := sw 1008
def gN : ℕ := sw 1009
def gLs : ℕ := sw 1010
def gA4 : ℕ := sw 1011
def gR5 : ℕ := sw 1012
def gL7 : ℕ := sw 1013
def gA : ℕ := sw 1014
def gX : ℕ := sw 1015
def gS : ℕ := sw 1016
def gS1 : ℕ := sw 1017
def gE : ℕ := sw 1018
def gE1 : ℕ := sw 1019
def gO : ℕ := sw 1020

/-- The registers the gather writes (outside the oracle bands). -/
def GSet (r : ℕ) : Prop := sw 1004 ≤ r ∧ r ≤ sw 1021

/-! ## Four stores at the allocator -/

/-- Store `gS, gS1, gE, gE1` at the allocator, raising it by four. -/
def put4 : Stmt :=
  block [.storeN ALLOC gS, .addN ALLOC ALLOC K1, .storeN ALLOC gS1, .addN ALLOC ALLOC K1,
    .storeN ALLOC gE, .addN ALLOC ALLOC K1, .storeN ALLOC gE1, .addN ALLOC ALLOC K1]

/-- The memory after `put4`. -/
def mem4 (m : ℕ → ℕ) (A v0 v1 v2 v3 : ℕ) : ℕ → ℕ :=
  upd ztyfu zttf v3
theorem put4_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 4 ≤ W) :
    IRS P W c₀ put4 c 8 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      ztjn ∧
      c'.nmem = mem4 c.nmem ztm (c.nreg gS) (c.nreg gS1) (c.nreg gE) (c.nreg gE1) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  zubgn
  zubod
  zukfi
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 241016, .addN 9999 9999 240611,
      .storeN 9999 241017, .addN 9999 9999 240611, .storeN 9999 241018, .addN 9999 9999 240611,
      .storeN 9999 241019, .addN 9999 9999 240611]) c c' k ∧ k = 8 ∧
      c'.nreg 9999 = c.nreg 9999 + 4 ∧
      ztedh ∧
      c'.nmem = mem4 c.nmem zterc (c.nreg 241016) (c.nreg 241017) (c.nreg 241018)
        (c.nreg 241019) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    · simp_all
    · simp_all
    · config_simp
      simp only [k1, mem4]
  zupp
  refine IRS.ofExec hI ex by_omega ztgjo h4 ztts h5 h6
    by_grind by_grind
    ⟨h1, h2, h3, h4, h5, h6⟩
  zugul
  zubcl

  unfold mem4
  zuby
  grind

/-! ## Exact frames from write sets -/

/-- **A write set gives an exact frame**: registers outside `B`, the memories and the output are
kept. -/
theorem IRS.addFrameB {s : Stmt} {B : ℕ → Bool} {K : ℕ} {Q : Config → Prop}
    (hs : SignK.wr B s = true) (h : IRS P W c₀ s c K Q) :
    IRS P W c₀ s c K (fun c' => Q c' ∧ SignK.FrameB B c c') := by
  obtain ⟨c', k, ex, hk, hI', hfr, hq⟩ := h
  exact ⟨c', k, ex, hk, hI', hfr, hq, SignK.exec_frameB ex hs⟩

/-- The registers `normS` may write. -/
def BnS (ph o : ℕ) (r : ℕ) : Bool :=
  Bprim r || decide ztqt || decide (r = ph) || decide zttxz ||
    decide ztqvd
theorem normS_wr (dsc pe ph o : ℕ) : SignK.wr ztsvt ztglb = true := by
  have hoff : SignK.wr ztsvt offCmp = true :=
    wr_mono wr_offCmp (fun r h => by simp [BnS, h])
  simp [normS, normBox, callOff, callP, cps, block, SignK.wr, SignK.wrOK, BnS, hoff]

/-- `normS` keeps the allocator and the memory. -/
theorem normS_exact {dsc pe ph o : ℕ} {Q : Config → Prop} {K : ℕ}
    (h : IRS P W c₀ ztglb c K Q) (ho : 240000 ≤ ph ∧ 240000 ≤ o) :
    IRS P W c₀ ztglb c K (fun c' => Q c' ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nmem = c.nmem) := by
  refine (IRS.addFrameB (normS_wr dsc pe ph o) h).mono le_rfl ?_
  rintro c' ⟨hq, hf⟩
  refine ⟨hq, hf.1 _ ?_, hf.2.2.1⟩
  unfold BnS Bprim ALLOC
  grind

/-! ## The arcs of a list of regions -/

/-- The arcs of a list of regions, in order. -/
def regArcs (N : NF) (rs : List ℕ) : List ℕ := rs.flatMap fun r => (N.region r).arcs

/-- The normalised ends of an arc. -/
noncomputable def nArc (M : Model) (Q : Polygon) (N : NF) (a : ℕ) : WPos × WPos :=
  (Restore.normOf M Q (N.arc a).s, Restore.normOf M Q (N.arc a).e)
variable (N : NF) (m f : ℕ → ℕ) {q : ℕ} {l : List ℕ} {dsc : ℕ}
theorem regArcs_take_succ (rs : List ℕ) {i : ℕ} (hi : i < rs.length) :
    regArcs N (rs.take ztg) = regArcs N ztked ++ (N.region ztdvy).arcs := by
  unfold regArcs
  rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hi]
  simp_all

/-- **The ends of an arc** of a valid normal form of a chain model: proper positions on walk
edges, inside the height band of the box unless on a horizontal box edge. -/
theorem arc_end_facts {C : Chain} (hP : C.P.Simple) {N : NF}
    (hNF : IsNF ztc zta N) {a : ℕ} (ha : a < N.arcs.length) :
    (ProperPos ztc zta P.n (N.arc a).s ∧ (N.arc a).s.edge < (chainModel C).W.n ∧
      ((N.arc a).s.edge < 6 → (N.arc a).s.edge ≠ 0 → (N.arc a).s.edge ≠ 2 →
        (N.arc a).s.edge ≠ 4 → |((chainModel C).pos zta (N.arc a).s).2| < C.radius)) ∧
    (ProperPos ztc zta P.n (N.arc a).e ∧ (N.arc a).e.edge < (chainModel C).W.n ∧
      ((N.arc a).e.edge < 6 → (N.arc a).e.edge ≠ 0 → (N.arc a).e.edge ≠ 2 →
        (N.arc a).e.edge ≠ 4 → |((chainModel C).pos zta (N.arc a).e).2| < C.radius)) := by
  zuc
  zugls
  obtain ⟨hFam, -, -, reg, -, -, hArcs, -, -, -, hpp⟩ := hNF'
  obtain ⟨hps, hpe⟩ := hpp a ha
  zuexu
  obtain ⟨-, harc⟩ := hArcs.1 a ha
  obtain ⟨hs0, hsn, he0, hen, hcase, -⟩ := harc
  have hedge : ∀ x : WPos, ProperPos ztc zta P.n x →
      (chainModel C).key zta x < (chainModel C).W.n → x.edge < (chainModel C).W.n := by
    zqrh
    have : ((x.edge : ℕ) : ℝ) < (chainModel C).W.n := by zungt
    simp_all
  have hzero : ∀ x : WPos, ProperPos ztc zta P.n x →
      (chainModel C).key zta x = 0 → x.edge = 0 := by
    zqrh
    have : ((x.edge : ℕ) : ℝ) ≤ 0 := by zungt
    simp_all
  rcases (N.F ztc zta).eq_empty_or_nonempty with hF | hF
  · rcases hcase with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1, h2⟩
    · simp_all
    simp_all
  · have hab := Restore.arc_abs_lt hP hNF hF ha
    simp_all

/-! ## The machine -/

/-- Read the arc at place `gT` of the current region and its ends. -/
def gRead : List Instr :=
  [.addN gX gLs gT, .loadN gA gX, .addN gX gA gA, .addN gX gX gX, .addN gX gX gA,
    .addN gX gA4 gX, .addN gX gX K1, .loadN gS gX, .addN gX gX K1, .loadN gS1 gX,
    .addN gX gX K1, .loadN gE gX, .addN gX gX K1, .loadN gE1 gX]

/-- One arc: read, normalise both ends, store, advance. -/
def gArc (dsc : ℕ) : Stmt :=
  .seq (block gRead) (.seq (normS dsc gS gS1 gO) (.seq (normS dsc gE gE1 gO)
    (.seq put4 (block [.addN gK gK K1, .addN gT gT K1]))))

/-- The cost of one arc. -/
def arcK : ℕ := 22060

/-- The head of a region: its arc count and arc list. -/
def gRegHead : List Instr :=
  [.addN gX gL gI, .loadN gR gX, .addN gX gR gR, .addN gX gX gX, .addN gX gX gR,
    .addN gX gR5 gX, .loadN gN gX, .addN gX gX K1, .loadN gLs gX]

/-- One region. -/
def gReg (dsc : ℕ) : Stmt :=
  .seq (block gRegHead) (.seq ztifl
    (.seq (.instr (.constN gT 0)) (.seq (.whileLtN gT gN ztvrd) (block [.addN gI gI K1]))))

/-- The cost of a region with `na` arcs. -/
def regK (na : ℕ) : ℕ := 20 + ztnrh * na

/-- The head of the gather. -/
def gHead : List Instr :=
  [.copyN gBase ALLOC, .constN gK 0, .constN gI 0, .addN gX gNF K4, .loadN gA4 gX,
    .addN gX gNF K5, .loadN gR5 gX, .addN gX gX K2, .loadN gL7 gX]

/-- **The gather.** -/
def gather (dsc : ℕ) : Stmt := .seq (block gHead) (.whileLtN gI gC ztvrf)

/-! ## Invariants -/

/-- The state of the gather after the records of `pre` (relative to the entry `cS`). -/
def GW (M : Model) (Q : Polygon) (N : NF) (cS c : Config) (pre : List ℕ) : Prop :=
  c.nreg gBase = cS.nreg ALLOC ∧ c.nreg gK = pre.length ∧
    c.nreg ALLOC = cS.nreg ALLOC + 4 * pre.length ∧
    (∀ k, k < pre.length →
      ShotList.arcAt c.nmem ztvkv k = nArc M Q N (pre.getD k 0)) ∧
    ztimo ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ GSet r → r ≠ ALLOC → c.nreg r = cS.nreg r) ∧
    c.nreg gA4 = cS.nmem (cS.nreg gNF + 4) ∧ c.nreg gR5 = cS.nmem ztrmw ∧
    c.nreg gL7 = cS.nmem ztrmx

/-- The state inside region `i` of the list. -/
def GIn (M : Model) (Q : Polygon) (N : NF) (cS : Config) (rs : List ℕ) (i : ℕ) (c : Config) :
    Prop :=
  GW M Q N cS c (regArcs N ztked ++ (N.region ztdvy).arcs.take (c.nreg gT)) ∧
    c.nreg gI = i ∧ c.nreg gR = rs.getD i 0 ∧
    c.nreg gN = (N.region ztdvy).arcs.length ∧
    (0 < (N.region ztdvy).arcs.length → c.nreg gLs = cS.nmem ztrmx +
      cS.nmem (cS.nmem ztrmw + 5 * rs.getD i 0 + 1)) ∧
    c.nreg gT ≤ (N.region ztdvy).arcs.length

/-! ## The register effect of the blocks -/
theorem gRead_val (hk1 : f K1 = 1) :
    regB m gRead f gS = m (f gA4 + 5 * m ztery + 1) ∧
    regB m gRead f gS1 = m (f gA4 + 5 * m ztery + 2) ∧
    regB m gRead f gE = m (f gA4 + 5 * m ztery + 3) ∧
    regB m gRead f gE1 = m (f gA4 + 5 * m ztery + 4) := by
  zubx
  simp only [gRead, regB, regI, upd, gX, gLs, gT, gA, gA4, gS, gS1, gE, gE1, K1, sw]
  grind
theorem gRead_other (h1 : q ≠ gX) (h2 : q ≠ gA) (h3 : q ≠ gS)
    (h4 : q ≠ gS1) (h5 : q ≠ gE) (h6 : q ≠ gE1) : regB m gRead f q = f q :=
  regB_other m gRead f (fun i hi => by
    simp only [gRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all)
theorem gRead_ok (hk1 : f K1 = 1) (hb : f gLs + f gT ≤ W)
    (hb2 : f gA4 + 5 * m ztery + 4 ≤ W) : okB W m gRead f := by
  zqri
  have s2 : IScr (240000 + 1014) := iscr_sw by_norm_num by_norm_num
  have s3 : IScr (240000 + 1016) := iscr_sw by_norm_num by_norm_num
  have s4 : IScr (240000 + 1017) := iscr_sw by_norm_num by_norm_num
  have s5 : IScr (240000 + 1018) := iscr_sw by_norm_num by_norm_num
  have s6 : IScr (240000 + 1019) := iscr_sw by_norm_num by_norm_num
  have hb' : f 241010 + f 241008 ≤ W := hb
  have hb2' : f 241011 + 5 * m (f 241010 + f 241008) + 4 ≤ W := hb2
  simp only [gRead, okB, okI, regI, upd, gX, gLs, gT, gA, gA4, gS, gS1, gE, gE1, K1, sw]
  grind
theorem getD_append_left {l l' : List ℕ} {n d : ℕ} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  grind
theorem getD_append_last {a d : ℕ} : (l ++ [a]).getD l.length d = a := by
  simp

/-! ## One arc -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One arc of the gather.** -/
theorem gArc_irs {C : Chain} {N : NF} {B E : ℕ} {cS : Config} {rs : List ℕ} {i : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hNW : NFWithin cS.nmem B E N) (hBS : cS.nreg gNF = B) (hE : E ≤ cS.nreg ALLOC)
    (hri : rs.getD i 0 < N.nRegions)
    (hin : GIn ztc zta N cS rs i c) (ht : c.nreg gT < c.nreg gN)
    (hroom : c.nreg ALLOC + arcK ≤ W) :
    IRS P W c₀ ztvrd c arcK (fun c' => GIn ztc zta N cS rs i c' ∧
      c'.nreg gT = c.nreg gT + 1 ∧ ChainCtx P W c' dsc C) := by
  zuus
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩, hgI, hgR, hgN, hgLs, hgT⟩ := hin
  set r := rs.getD i 0 with hr
  set t := c.nreg gT with htd
  set pre := regArcs N ztked ++ (N.region r).arcs.take t with hpre
  zukgg
  set a := (N.region r).arcs.getD t 0 with had
  have ham : a ∈ (N.region r).arcs := by
    grind
  have ha : a < N.arcs.length := by
    zucsf
    exact ((hArcs.2.2.2 r hri a).1 ham).1
  -- the memory of the normal form
  zujyy
  zuclz

  obtain ⟨b1, -, b3, b4, b5, -⟩ := Restore.nf_bounds hNWc
  have hgNF : c.nreg gNF = B := by
    rw [w6 gNF ztmr
      (fun h => by unfold GSet gNF sw at h; omega) by_decide, hBS]
  have m4 : cS.nmem _ = c.nmem ztow := (w5 _ by_omega).symm
  zuchc

  have hreg := (hNA.2.2.2.2.2.2.2.1 r hri)
  have mr1 : cS.nmem _ = c.nmem ztwrs :=
    (w5 _ by_grind).symm
  have vLs : c.nreg gLs = c.nmem ztlw + c.nmem ztwrs := by
    grind
  have vA4 : c.nreg gA4 = c.nmem ztow := by_grind
  have hblt := b5 r hri t htl
  have hat : c.nmem (c.nreg gLs + c.nreg gT) = a := by
    grind
  have harec := hNA.2.2.2.2.2.2.1 a ha
  have hab := b3 a ha
  obtain ⟨⟨hps, hse, hsy⟩, ⟨hpe, hee, hey⟩⟩ := arc_end_facts hP hNF ha
  -- the read block
  have hok : okB W c.nmem gRead c.nreg := gRead_ok _ _ hK₀.2.1 by_omega
    by_omega
  refine IRS.mono (K := gRead.length + (11015 + (11015 + (8 + 2)))) (IRS.seq (IRS.block gRead hI hok)
    ?_) by_decide (fun _ h => h)
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem gRead c.nreg } with hc₁
  obtain ⟨r1s, r1s1, r1e, r1e1⟩ := gRead_val c.nmem c.nreg hK₀.2.1
  rw [hat, vA4] at r1s r1s1 r1e r1e1
  have v1s : c₁.nreg gS = (N.arc a).s.edge := by_grind
  have v1s1 : c₁.nreg gS1 = (N.arc a).s.hgt := by_grind
  have v1e : c₁.nreg gE = (N.arc a).e.edge := by_grind
  have v1e1 : c₁.nreg gE1 = (N.arc a).e.hgt := by_grind
  have k1' : ∀ q, q ≠ gX → q ≠ gA → q ≠ gS → q ≠ gS1 → q ≠ gE → q ≠ gE1 →
      c₁.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => gRead_other _ _ h1 h2 h3 h4 h5 h6
  have k1 : ztkok := fun q hq =>
    gRead_other _ _ ztwpt
      ztwpt ztwpt
      ztwpt ztwpt
      ztwpt
  zukdw
  have hA1 : ztdc := k1 _ ztnvg
  have hctx₁ := hctx.transport (k1 _ hd.2.2) by_grind hA1.ge
  -- normalise the start
  have hy1 : c₁.nreg gS < 6 → c₁.nreg gS ≠ 0 → c₁.nreg gS ≠ 2 → c₁.nreg gS ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₁.nreg gS, c₁.nreg gS1⟩).2| < C.radius := by
    zuimy
  refine IRS.seq (normS_exact (normS_irs hI₁
    ztqph hctx₁ ⟨hd.1, hd.2.1, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    by_omega ztliv hy1
    (by zvnhf; unfold arcK at hroom; omega)) ⟨by_decide, by_decide⟩) ?_
  zucja
  have hctx₂ := hctx₁.transport
    (k2 _ zttug ztxwr
      ztxwr
      ztxwr ztu)
    by_grind hA2.ge
  have v2e : c₂.nreg gE = (N.arc a).e.edge := by
    rw [k2 _ ztmr
      by_decide by_decide by_decide
      by_decide, v1e]
  have v2e1 : c₂.nreg gE1 = (N.arc a).e.hgt := by
    rw [k2 _ ztmr
      by_decide by_decide
      by_decide by_decide, v1e1]
  -- normalise the end
  have hy2 : c₂.nreg gE < 6 → c₂.nreg gE ≠ 0 → c₂.nreg gE ≠ 2 → c₂.nreg gE ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₂.nreg gE, c₂.nreg gE1⟩).2| < C.radius := by
    zuimz
  refine IRS.seq (normS_exact (normS_irs hI₂
    ztqpi hctx₂ ⟨hd.1, hd.2.1, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    by_omega ztlix hy2
    (by zuooy; unfold arcK at hroom; omega)) ⟨by_decide, by_decide⟩) ?_
  zucjb
  have v3s : c₃.nreg gS = c₂.nreg gS := k3 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide
  have v3s1 : c₃.nreg gS1 = c₂.nreg gS1 := k3 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide
  have ns : (ztrca : WPos) = Restore.normOf ztc zta (N.arc a).s := by
    zudvj

    have := (Restore.normOf_facts hps).2.1
    rcases hn : Restore.normOf _ _ (N.arc a).s with ⟨e', h'⟩
    grind
  have ne' : (ztrbz : WPos) = Restore.normOf ztc zta (N.arc a).e := by
    zufoa

    have := (Restore.normOf_facts hpe).2.1
    rcases hn : Restore.normOf _ _ (N.arc a).e with ⟨e', h'⟩
    grind
  zuffx

  -- store the record
  refine IRS.seq (put4_irs hI₃ ztvtj (by zupdb; unfold arcK at hroom; omega)) ?_
  zudfl
  -- advance
  have k4K : c₄.nreg gK = c.nreg gK := by
    rw [k4 _ by_decide,
      k3 _ ztmr
        by_decide by_decide by_decide
        by_decide,
      k2 _ ztmr
        by_decide by_decide by_decide
        by_decide,
      k1' _ by_decide by_decide
        by_decide by_decide
        by_decide by_decide]
  -- the frame from `c` to `c₄`
  have k14 : ∀ q, bandOf q ∉ oracleBands → q ≠ gX → q ≠ gA → q ≠ gS → q ≠ gS1 → q ≠ gE →
      q ≠ gE1 → q ≠ gO → q ≠ gO + 1 → q ≠ ALLOC → c₄.nreg q = c.nreg q := by
    intro q hq h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [k4 _ h9, k3 _ hq h6 h7 h8 h9, k2 _ hq h4 h7 h8 h9, k1' _ h1 h2 h3 h4 h5 h6]
  zujyx
  have k4T : c₄.nreg gT = t := k14 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide by_decide
    by_decide by_decide by_decide
    by_decide
  zuhwy
  have hpl : pre.length + 1 ≤ W := by
    omega
  have htW : ztmwv := by
    omega
  have hok5 : okB W c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg := by
    zqrj
    zujxi
    simp only [okB, okI, regI, upd, gK, gT, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_false, e1, e2, e3]
    exact ⟨⟨iscr_sw by_norm_num by_norm_num, hpl⟩, ⟨iscr_sw by_norm_num by_norm_num, htW⟩,
      trivial⟩
  zuevs

  have r5 : ∀ q, q ≠ gK → q ≠ gT → regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg q =
      c₄.nreg q := fun q h1 h2 => regB_other _ _ _ (fun i hi => by
        zuvx
        rcases hi with rfl | rfl <;> zvmwd <;> intro h <;> subst h <;> simp_all)
  have v5K : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg gK = pre.length + 1 := by
    zqrj
    zqrl
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e2]
  have v5T : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg gT = t + 1 := by
    have e1 : ztlyg := hK1₄
    zujxi
    zqrl
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e3]
  -- the frame from `c` to `c₅`
  have k15 : ∀ q, bandOf q ∉ oracleBands → ¬ GSet q → q ≠ ALLOC →
      regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg q = c.nreg q := by
    zulnh
    have ne : ∀ g, GSet g → q ≠ g := by_grind
    rw [r5 q ztcwa ztcwa,
      k14 q hq ztcwa ztcwa
        ztcwa ztcwa
        ztcwa ztcwa
        ztcwa ztcwa hqa]
  have kk :=
    fun g hg h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
      (r5 g h1 h2).trans (k14 g hg h3 h4 h5 h6 h7 h8 h9 h10 h11)
  have nob : ∀ j, 1000 ≤ j → j ≤ 1021 → bandOf ztgc ∉ oracleBands := fun j h1 h2 =>
    not_oracle_sw ztce ztce
  have hpre' : regArcs N ztked ++ (N.region r).arcs.take ztbx = pre ++ [a] := by
    rw [hpre, List.take_add_one, List.getElem?_eq_getElem htl, List.append_assoc]
    simp only [Option.toList_some]
    rw [had, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
  have hA5 : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg ALLOC = c.nreg ALLOC + 4 := by
    rw [r5 _ by_decide by_decide, hA4']
  have hmem5 : c₄.nmem = mem4 c.nmem (cS.nreg ALLOC + 4 * pre.length) ztvnl ztvnm
      ztvnj ztvnk := by rw [hm4, hm3', hA3', w3]
  have hT5 : ({ c₄ with nreg := regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg } :
      Config).nreg gT = t + 1 := v5T
  have hpre'' : regArcs N _ ++ (N.region ztdvy).arcs.take _ =
      pre ++ [a] := hpre'
  unfold GIn GW
  rw [hT5, hpre'']
  refine ⟨⟨ztbfh, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show regB _ _ _ gBase = _
    rw [kk gBase (nob 1004 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, w1]
  · show regB _ _ _ gK = _
    rw [v5K]
    simp
  · show regB _ _ _ ALLOC = _
    rw [hA5, w3]
    simp; ring
  · zugf
    show ShotList.arcAt c₄.nmem _ k = _
    zuduh

    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rcases Nat.lt_or_ge k pre.length with hl | hg
    · rw [Restore.arcAt_upd4 hl, w4 k hl, getD_append_left hl]
    · have hk' : k = pre.length := by_omega
      zujpq
      rw [Restore.arcAt_upd4_new, getD_append_last]
      zujqr
      rw [← ns, ← ne']
  · intro a' ha'
    show c₄.nmem a' = _
    zuduh

    zuby
    rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, w5 a' ha']
  · zulnh
    show regB _ _ _ q = _
    rw [k15 q hq hg hqa, w6 q hq hg hqa]
  · show regB _ _ _ gA4 = _
    rw [kk gA4 (nob 1011 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, w7]
  · show regB _ _ _ gR5 = _
    rw [kk gR5 (nob 1012 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, w8]
  · show regB _ _ _ gL7 = _
    rw [kk gL7 (nob 1013 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, w9]
  · show regB _ _ _ gI = _
    rw [kk gI (nob 1006 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, hgI]
  · show regB _ _ _ gR = _
    rw [kk gR (nob 1007 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, hgR]
  · show regB _ _ _ gN = _
    rw [kk gN (nob 1009 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, hgN]
  · zulmx
    show regB _ _ _ gLs = _
    rw [kk gLs (nob 1010 by_norm_num by_norm_num) by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide]
    exact hgLs hpos
  · exact htl
  · rfl
  · refine hctx.transport (k15 _ zttug hd.2.2 ztu)
      (fun a' ha' => ?_) (by show c.nreg ALLOC ≤ regB _ _ _ ALLOC; omega)
    show c₄.nmem a' = _
    rw [hm4, hm3', hA3']
    unfold mem4
    zuby
    zunjd

/-- The working registers of the gather (not the outputs and not the bases). -/
def GFree (q : ℕ) : Prop :=
  q = gI ∨ q = gR ∨ q = gT ∨ q = gN ∨ q = gLs ∨ q = gA ∨ q = gX ∨ q = gS ∨ q = gS1 ∨ q = gE ∨
    q = gE1 ∨ q = gO ∨ q = gO + 1
theorem gfree_gset (h : GFree q) : GSet q := by
  unfold GFree at h; unfold GSet
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [gI, gR, gT, gN, gLs, gA, gX, gS, gS1, gE, gE1, gO, sw]

/-- The written state survives a step that keeps the memory and the registers outside the
working registers. -/
theorem GW.step {M : Model} {Q : Polygon} {N : NF} {cS c c' : Config} {pre : List ℕ}
    (h : GW M Q N cS c pre) (hm : c'.nmem = c.nmem) (hr : ∀ q, ¬ GFree q → c'.nreg q = c.nreg q) :
    GW M Q N cS c' pre := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := h
  have nf : ∀ q, (q = gBase ∨ q = gK ∨ q = ALLOC ∨ q = gA4 ∨ q = gR5 ∨ q = gL7) → ¬ GFree q := by
    intro q hq hf
    unfold GFree at hf
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gI, gR, gT, gN, gLs, gA, gX, gS, gS1, gE, gE1, gO, gBase, gK, ALLOC, gA4, gR5, gL7,
        sw] at hf
  refine ⟨by_simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, fun q hq hg hqa => ?_,
    by simp_all, by_simp_all,
    by simp_all⟩
  rw [hr q (fun hf => hg (gfree_gset hf)), w6 q hq hg hqa]

/-! ## One region -/
theorem gRegHead_val (hk1 : f K1 = 1) :
    regB m gRegHead f gR = m ztgin ∧
    regB m gRegHead f gN = m (f gR5 + 5 * m ztgin) ∧
    regB m gRegHead f gLs = m (f gR5 + 5 * m ztgin + 1) := by
  zubx
  simp only [gRegHead, regB, regI, upd, gX, gL, gI, gR, gR5, gN, gLs, K1, sw]
  grind
theorem gRegHead_other (h1 : q ≠ gX) (h2 : q ≠ gR) (h3 : q ≠ gN)
    (h4 : q ≠ gLs) : regB m gRegHead f q = f q :=
  regB_other m gRegHead f (fun i hi => by
    simp only [gRegHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      intro h <;> subst h <;> simp_all)
theorem gRegHead_ok (hk1 : f K1 = 1) (hb : f gL + f gI ≤ W)
    (hb2 : f gR5 + 5 * m ztgin + 1 ≤ W) : okB W m gRegHead f := by
  zqri
  have s2 : IScr (240000 + 1007) := iscr_sw by_norm_num by_norm_num
  have s3 : IScr (240000 + 1009) := iscr_sw by_norm_num by_norm_num
  have s4 : IScr (240000 + 1010) := iscr_sw by_norm_num by_norm_num
  have hb' : f 241001 + f 241006 ≤ W := hb
  have hb2' : f 241012 + 5 * m (f 241001 + f 241006) + 1 ≤ W := hb2
  simp only [gRegHead, okB, okI, regI, upd, gX, gL, gI, gR, gR5, gN, gLs, K1, sw]
  grind
theorem getD_mem_of_lt {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp_all
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One region of the gather.** -/
theorem gReg_irs {C : Chain} {N : NF} {B E : ℕ} {cS : Config} {rs : List ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hNW : NFWithin cS.nmem B E N) (hBS : cS.nreg gNF = B) (hE : E ≤ cS.nreg ALLOC)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hL : ∀ j, j < rs.length → cS.nmem (cS.nreg gL + j) = rs.getD j 0)
    (hLA : cS.nreg gL + rs.length ≤ cS.nreg ALLOC)
    (hgo : GW ztc zta N cS c (regArcs N (rs.take (c.nreg gI))))
    (hctx : ChainCtx P W c dsc C) (hi : c.nreg gI < rs.length)
    (hroom : c.nreg ALLOC + regK ztipd ≤ W) :
    IRS P W c₀ ztvrf c (regK ztipd)
      (fun c' => GW ztc zta N cS c' ztfui ∧
        c'.nreg gI = c.nreg gI + 1 ∧ ChainCtx P W c' dsc C) := by
  zuus
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hgo
  set i := c.nreg gI with hid
  set r := rs.getD i 0 with hrd
  have hr : ztsll := by_simp_all
  set na := (N.region r).arcs.length with hna
  zujyy
  zuclz

  obtain ⟨b1, -, -, b4, b5, -⟩ := Restore.nf_bounds hNWc
  have nob : ∀ q, ¬ GSet q → 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands :=
    fun q _ h1 h2 => not_oracle_sw h1 h2
  have hgL := w6 gL (not_oracle_sw by_decide
    by_decide) (fun h => by unfold GSet gL sw at h; omega)
    by_decide
  have hmL : c.nmem (c.nreg gL + i) = r := by
    grind
  zuchc

  have vR5 : c.nreg gR5 = c.nmem zter := by_grind
  have hreg := hNA.2.2.2.2.2.2.2.1 r hr
  have hb4 := b4 r hr
  have hLW : c.nreg gL + i ≤ W := by
    omega
  -- the head of the region
  have hok : okB W c.nmem gRegHead c.nreg := gRegHead_ok _ _ hK₀.2.1 hLW
    by_grind
  refine IRS.mono (K := gRegHead.length + (3 + (1 + (ztnrh * na + 2 + 1))))
    (IRS.seq (IRS.block gRegHead hI hok) ?_) (by simp [gRegHead, regK]; omega) ztb
  zufg
  obtain ⟨v1R, v1N, v1Ls⟩ := gRegHead_val c.nmem c.nreg hK₀.2.1
  rw [hmL] at v1R
  rw [hmL, vR5] at v1N v1Ls
  rw [hreg.1] at v1N
  have k1 : ∀ q, q ≠ gX → q ≠ gR → q ≠ gN → q ≠ gLs →
      regB c.nmem gRegHead c.nreg q = c.nreg q := fun q h1 h2 h3 h4 =>
    gRegHead_other _ _ h1 h2 h3 h4
  set c₁ : Config := { c with nreg := regB c.nmem gRegHead c.nreg } with hc₁
  have hA1 : ztdc := k1 ALLOC by_decide
    by_decide by_decide by_decide
  -- the list start
  have step2 : IRS P W c₀ ztifl c₁ 3
      (fun c' => c'.nmem = c₁.nmem ∧ (∀ q, q ≠ gLs → c'.nreg q = c₁.nreg q) ∧
        (0 < na → c'.nreg gLs = c.nmem ztlw + c.nmem ztwrs)) := by
    zuibb
    by_cases hp : 0 < na
    · have hlt : c₁.nreg K0 < c₁.nreg gN := by
        grind
      have hL7 : c₁.nreg gL7 = c.nmem ztlw := by
        rw [show c₁.nreg gL7 = c.nreg gL7 from k1 gL7 by_decide
          by_decide by_decide by_decide,
          w9, hBS, m7]
      have hb := b5 r hr 0 hp
      refine (IRS.ifT hlt (IRS.reg hI₁ (iscr_sw by_decide
        by_decide) (Exec.addN hI₁.hw gLs gLs gL7 ?_))).mono by_omega ?_
      · grind
      · zuu
        refine ⟨rfl, fun q hq => by simp only; rw [upd_other _ _ _ hq],
          fun _ => ?_⟩
        zufb
        grind
    · have hlt : ¬ c₁.nreg K0 < c₁.nreg gN := by_grind
      exact (IRS.ifF hlt (IRS.skip (K := 1) hI₁ ⟨rfl, by_omega, by_omega⟩)).mono
        by_omega ztb
  refine IRS.seq step2 ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hm2, k2, v2Ls⟩
  have hfr : ∀ g, GFree g → dsc ≠ g := fun g hg h => hd.2.2 (by zvmwc; exact gfree_gset hg)
  -- the arc place
  refine IRS.seq (IRS.reg hI₂ ztbua
    (Exec.constN hI₂.hw gT 0 ztbg)) ?_
  zubup
  have k3 : ∀ q, q ≠ gT → q ≠ gLs → q ≠ gX → q ≠ gR → q ≠ gN →
      ztegk q = c.nreg q := by
    intro q h1 h2 h3 h4 h5
    rw [upd_other _ _ _ h1, k2 q h2]
    grind
  have v3R : ztegk gR = r := by
    zqrk
    omega
  have v3N : ztegk gN = na := by
    zqrk
    omega
  have v3I : ztegk gI = i := k3 _ by_decide
    by_decide by_decide by_decide
    by_decide
  have hm3 := hm2
  have hGW3 : GW ztc zta N cS { c₂ with nreg := upd c₂.nreg gT 0 }
      (regArcs N ztked ++ (N.region r).arcs.take 0) := by
    rw [List.take_zero, List.append_nil]
    refine GW.step ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ hm3 zteso
    simp only [GFree, not_or] at hq
    exact k3 q hq.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2.2.1 hq.2.1 hq.2.2.2.1
  have hctx₃ : ChainCtx P W { c₂ with nreg := upd c₂.nreg gT 0 } dsc C :=
    hctx.transport (k3 _ (hfr gT ztdmf) (hfr gLs ztdmf)
      (hfr gX ztdmf) (hfr gR ztdmf) (hfr gN ztdmf))
      by_grind
      by_omega
  have hIn3 : GIn ztc zta N cS rs i { c₂ with nreg := upd c₂.nreg gT 0 } := by
    refine ⟨by_tauto, v3I, v3R, v3N,
      fun hp => ?_, by_simp⟩
    zubi
    rw [← hrd] at hp ⊢
    rw [upd_other _ _ _ by_decide, v2Ls hp, hBS, m7, m5,
      ← w5 _ by_omega]
  -- the arcs
  refine IRS.seq (IRS.while (fun c' => GIn _ _ N cS rs i c' ∧
      ChainCtx P W c' dsc C) (fun c' => na - c'.nreg gT) arcK
    (fun c' ⟨hg, _⟩ hlt => by
      zqrm
      grind)
    (fun c' hI' ⟨hg, hc'⟩ hlt hr' => (gArc_irs hI' hK hc' hd hP hNF hNW hBS hE by_omega hg hlt
      hr').mono le_rfl (fun c'' ⟨hg', ht', hc''⟩ => ⟨by_grind, by
        zqrm
        grind⟩))
    hI₃ by_grind (by
      show ztegk ALLOC + ztnrh * (na - ztegk gT) ≤ W
      rw [upd_same, Nat.sub_zero, upd_other _ _ _ by_decide,
        k2 _ by_decide, hA1]
      unfold regK at hroom; omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨hIn4, hctx₄⟩, hnlt⟩
  obtain ⟨hGW4, hgI4, hgR4, hgN4, -, hgT4⟩ := hIn4
  have hT4 : c₄.nreg gT = (N.region ztdvy).arcs.length := by
    omega
  rw [hT4, List.take_length, ← regArcs_take_succ N rs hi] at hGW4
  -- advance the region index
  have hiW : c₄.nreg gI + c₄.nreg K1 ≤ W := by
    zunuf; omega
  have hok6 : okB W c₄.nmem [.addN gI gI K1] c₄.nreg :=
    ⟨⟨iscr_sw by_decide by_decide, hiW⟩, trivial⟩
  refine (IRS.block _ hI₄ hok6).mono by_simp ?_
  rintro c₅ rfl
  zudlp
  zunuf
  refine ⟨GW.step hGW4 rfl (fun q hq => upd_other _ _ _ (fun h => hq (by simp [h, GFree]))), rfl,
    hctx₄.transport (upd_other _ _ _ (hfr gI ztdmf)) by_grind
      by_rfl⟩

/-! ## The gather -/

/-- The cost of the gather of a list of regions. -/
def gatherK (N : NF) (rs : List ℕ) : ℕ :=
  11 + (rs.map fun r => regK (N.region r).arcs.length + 2).sum

/-- The potential of the region loop. -/
def gPot (N : NF) (rs : List ℕ) (i : ℕ) : ℕ :=
  ((rs.drop i).map fun r => regK (N.region r).arcs.length + 2).sum
theorem gPot_succ (rs : List ℕ) {i : ℕ} (hi : i < rs.length) :
    gPot N rs i = regK (N.region ztdvy).arcs.length + 2 + gPot N rs ztg := by
  unfold gPot
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.sum_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
theorem gHead_val :
    regB m gHead f gBase = f ALLOC ∧ regB m gHead f gK = 0 ∧ regB m gHead f gI = 0 ∧
    regB m gHead f gA4 = m (f gNF + f K4) ∧ regB m gHead f gR5 = m (f gNF + f K5) ∧
    regB m gHead f gL7 = m (f gNF + f K5 + f K2) := by
  tauto
theorem gHead_other (h : ¬ GSet q) : regB m gHead f q = f q :=
  regB_other m gHead f (fun i hi => by
    simp only [gHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      intro he <;> subst he <;> apply h <;>
      simp [GSet, gX, gBase, gK, gI, gA4, gR5, gL7, sw])
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gather**: the normalised arcs of the listed regions, in order, at the allocator. -/
theorem gather_irs {C : Chain} {N : NF} {B E : ℕ} {rs : List ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hNW : NFWithin c.nmem B E N) (hB : c.nreg gNF = B) (hE : E ≤ c.nreg ALLOC)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hL : ∀ j, j < rs.length → c.nmem (c.nreg gL + j) = rs.getD j 0)
    (hLA : c.nreg gL + rs.length ≤ c.nreg ALLOC) (hC : c.nreg gC = rs.length)
    (hroom : c.nreg ALLOC + gatherK N rs ≤ W) :
    IRS P W c₀ (gather dsc) c (gatherK N rs)
      (fun c' => GW ztc zta N c c' (regArcs N rs) ∧ ChainCtx P W c' dsc C) := by
  zuus
  zudet
  zuhhh
  have hBW : B + 7 ≤ W := by_omega
  have hok : okB W c.nmem gHead c.nreg := by
    have e4 : ztlxs := k4
    have e5 : c.nreg 240614 = 5 := k5
    have e2 : ztunw := k2
    have eB : c.nreg 241000 = B := hB
    have s : ztfu := fun j h1 h2 =>
      iscr_sw by_omega by_omega
    simp only [gHead, okB, okI, regI, upd, gX, gNF, gBase, gK, gI, gA4, gR5, gL7, K4, K5, K2,
      ALLOC, sw]
    grind
  refine IRS.mono (K := gHead.length + (gPot N rs 0 + 2)) (IRS.seq (IRS.block gHead hI hok) ?_)
    (by simp [gHead, gatherK, gPot]; omega) ztb
  zufg
  obtain ⟨vB, vK, vI, vA4, vR5, vL7⟩ := gHead_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem gHead c.nreg } with hc₁
  have ko : ztkok := fun q hq => gHead_other _ _ hq
  have hA1 : ztdc := ko _ ztnvg
  have hGW1 : GW ztc zta N c c₁ (regArcs N (rs.take (c₁.nreg gI))) := by
    rw [show c₁.nreg gI = 0 from vI, List.take_zero]
    refine ⟨vB, vK, by_rfl, fun k hk => by_tauto,
      by simp_all, by_simp_all, ?_, ?_, ?_⟩
    · simp_all
    · simp_all
    simp_all
  have hctx₁ : ChainCtx P W c₁ dsc C := hctx.transport by_simp_all by_simp_all hA1.ge
  have hgC : ∀ c', GW ztc zta N c c' ztfui →
      c'.nreg gC = rs.length := fun c' hg => by
    rw [hg.2.2.2.2.2.1 gC ztmr
      (by unfold GSet gC sw; omega) by_decide, hC]
  refine (IRS.whileP (fun c' => GW ztc zta N c c' ztfui ∧
      c'.nreg gI ≤ rs.length ∧ ChainCtx P W c' dsc C) (fun c' => gPot N rs (c'.nreg gI))
    (fun c' hI' ⟨hg, hle, hc'⟩ hlt hr' => ?_) hI₁ ⟨hGW1, by
      simp_all, hctx₁⟩
    (by rw [hA1, show c₁.nreg gI = 0 from vI]; unfold gatherK at hroom; unfold gPot; grind)).mono le_rfl ?_
  · rw [hgC c' hg] at hlt
    refine ⟨regK (N.region _).arcs.length,
      (gReg_irs hI' hK hd hP hNF hNW hB hE hrs hL hLA hg hc' hlt (by
        rw [gPot_succ N rs hlt] at hr'; omega)).mono le_rfl ?_⟩
    rintro c'' ⟨hg'', hi'', hc''⟩
    zulos
    rw [hi'', gPot_succ N rs hlt]
    omega
  grind
end
end SweepIo
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqzq" : tactic => `(tactic| (refine ⟨by_omega, by_grind, fun h1 => ?_⟩
                                          obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 by_omega))
local macro "zqzr" : tactic => `(tactic| (rintro c' ⟨hL', hk', ha', hm'⟩
                                          exact ⟨hL', finish c' hk' ha' hm'⟩))
local macro "zqzs" : tactic => `(tactic| (obtain ⟨f1, f2, f3⟩ := hacc1
                                          have a0 : c₂.nreg A = c₁.nreg A := by simpa using a2 0 by_norm_num))
local macro "zqzt" : tactic => `(tactic| rw [a2 1 by_norm_num, a2 2 by_norm_num, a2 3 by_norm_num])
local macro "zqzu" : tactic => `(tactic| (have hs : ztgbb := by zungf; apply dirOf_eq_neg; omega))
set_option hygiene true

/-!
# The sweep RAM (WP-D), answers: the candidate accumulator

Every answer is the earliest of a few candidate points on the query ray (`Sweep` candidate
principle, `SweepIoAns.whole_firstHit_of_mem`).  The accumulator at a register block `A`
(`A … A + 12`) keeps the earliest candidate offered so far: a flag (`A`), its walk position
(`A + 1`, `A + 2`) in the chain model with tag `A + 3` (`Mod tag`), and its abscissa record
(`A + 4 … A + 7`).  `offer` computes the abscissa record of a new candidate (`absKey`, into
`A + 8 … A + 11`) and keeps the earlier one along the ray (`absCmp`, bit in `A + 12`).

`AccOK … L c`: the flag is `1` iff some candidate was offered (`L` the set of their ray
parameters), and then the kept candidate has the least parameter.
-/
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The accumulator state**: `L` is the set of the ray parameters of the offered candidates. -/
def AccOK (P : Polygon) (A : ℕ) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (σ : ℝ) (L : Set ℝ)
    (c : Config) : Prop :=
  c.nreg A ≤ 1 ∧ (c.nreg A = 0 → L = ∅) ∧
    (c.nreg A = 1 → ∃ τ ∈ L, (∀ τ' ∈ L, τ ≤ τ') ∧ c.nreg zttf ≤ 2 ∧
      ProperPos ztbasn zta P.n ztxhv ∧
      c.nreg ztbo < (chainModel ztwuj).W.n ∧
      (chainModel ztwuj).pos zta ztxhv =
        rayPt z σ τ ∧
      AbsRec P c ztckz (rayPt z σ τ).1 R₀)

/-- Take the candidate: copy its position, tag and record, set the flag. -/
def takeL (A e h t : ℕ) : List Instr :=
  [.copyN ztbo e, .copyN ztbcl h, .copyN zttf t, .copyN ztckz ztcla,
    .copyN ztgzp ztnir, .copyN ztjgk ztjgi, .copyN ztgzq ztnic, .constN A 1]

/-- **Offer the candidate** at the position `(e, h)` of the chain model of the descriptor `dsc`
(tag register `t`), for the direction code in `dR`. -/
def offer (A dsc e h t dR : ℕ) : Stmt :=
  .seq (callAbs dsc e h ztcla)
    (.ifLtN A K1 ztbafs
      (.ifLtN dR K1
        ztbara
        (.ifLtN K1 dR
          ztbara
          (.seq (callAbsCmp ztcla ztckz ztiq) ztwwv))))

/-- The cost of an offer. -/
def offerK : ℕ := 17000

/-- The empty accumulator. -/
theorem accOK_init (A : ℕ) (Mod : ℕ → Chain) (R₀ : ℝ) (z : Point) (σ : ℝ) {c : Config}
    (h : c.nreg A = 0) : AccOK P A Mod R₀ z σ ∅ c :=
  ⟨by_omega, by_simp_all, by_simp_all⟩

/-- The register effect of `takeL`. -/
theorem takeL_val (m f : ℕ → ℕ) {A e h t : ℕ} (_he : e < A ∨ A + 12 < e) (hh : h < A ∨ A + 12 < h)
    (ht : t < A ∨ A + 12 < t) :
    regB m ztxs f A = 1 ∧ regB m ztxs f ztbo = f e ∧
    regB m ztxs f ztbcl = f h ∧ regB m ztxs f zttf = f t ∧
    regB m ztxs f ztckz = f ztcla ∧ regB m ztxs f ztgzp = f ztnir ∧
    regB m ztxs f ztjgk = f ztjgi ∧ regB m ztxs f ztgzq = f ztnic ∧
    (∀ q, (q < A ∨ A + 7 < q) → regB m ztxs f q = f q) := by
  simp only [takeL, regB, regI, upd]
  refine ⟨by_simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · simp
  · grind
  · grind
  · simp
  · simp
  · simp
  · simp
  grind

/-- **Taking a candidate** that precedes every offered one. -/
theorem take_irs {A e h t : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {σ : ℝ} {L : Set ℝ}
    {τ : ℝ} (hI : IInv W c₀ c) (hW1 : 1 ≤ W) (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hout : ztfra ∧ ztfse ∧ ztfux)
    (hmin : ∀ τ' ∈ L, τ ≤ τ') (htag : c.nreg t ≤ 2)
    (he : c.nreg e < (chainModel ztbhn).W.n)
    (hpp : ProperPos ztzec zta P.n ztkv)
    (hpos : (chainModel ztbhn).pos zta ztkv = rayPt z σ τ)
    (hrec : AbsRec P c ztcla (rayPt z σ τ).1 R₀) :
    IRS P W c₀ ztbafs c 8 (fun c' =>
      AccOK P A Mod R₀ z σ ztobq c' ∧ (∀ r, ztlsc → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have sc : ∀ j, j ≤ 7 → IScr ztbya := fun j hj => iscr_sw by_omega by_omega
  have hok : okB W c.nmem ztxs c.nreg := by
    zuhqb
    exact ⟨by_simp_all, by_simp_all, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, by_simp_all,
      ⟨by simpa using sc 0 by_norm_num, hW1⟩, trivial⟩
  zugsj
  zuu
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, vo⟩ := takeL_val c.nmem c.nreg hout.1 hout.2.1 hout.2.2
  unfold AccOK
  zubi
  refine ⟨⟨by zuouw, fun h0 => by_omega, fun _ => ⟨τ, Set.mem_insert _ _,
    fun τ' hτ' => ?_, by_omega, by_simp_all,
    by simp_all, by_simp_all, ?_⟩⟩, vo, trivial⟩
  · grind
  · zujex
    · omega
    · omega
    · omega
    omega

/-- An abscissa record determines its abscissa. -/
theorem absRec_val {r : ℕ} {x x' R : ℝ} (h : AbsRec P c r x R) (h' : AbsRec P c r x' R) :
    x = x' := by
  obtain ⟨-, h⟩ := h
  obtain ⟨-, h'⟩ := h'
  rcases h with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, -, s, hs, -, he⟩ <;>
    rcases h' with ⟨k', hx'⟩ | ⟨k', hx'⟩ | ⟨k', -, s', hs', -, he'⟩ <;>
    first | omega | (rw [hx, hx']) | skip
  rw [← he, ← he', SignK.symPtIn_unique hs hs']
variable {d : ℕ} (C : Chain) (Q : Polygon) {n : ℕ} {x : WPos}
theorem dirOf_eq_one (h : d = 1) : dirOf d = 1 := by zungv
theorem dirOf_eq_neg (h : d ≠ 1) : dirOf d = -1 := by zungv
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **An offer**: the accumulator keeps the earliest candidate. -/
theorem offer_irs {A dsc e h t dR : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {L : Set ℝ}
    {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hregs : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ e ∧ e < 250000 ∧ 240000 ≤ h ∧
      h < 250000 ∧ 240000 ≤ t ∧ t < 250000 ∧ 240000 ≤ dR ∧ dR < 250000)
    (hout : ztlna ∧ ztfra ∧ ztfse ∧
      ztfux ∧ ztlmy)
    (hacc : AccOK P A Mod R₀ z ztcvc L c)
    (htag : c.nreg t ≤ 2) (hctx : ChainCtx P W c dsc ztbhn)
    (hR : (Mod ztjsm).radius = R₀)
    (he : c.nreg e < (chainModel ztbhn).W.n)
    (hpp : ProperPos ztzec zta P.n ztkv)
    (hpos : (chainModel ztbhn).pos zta ztkv =
      rayPt z ztcvc τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + offerK ≤ W) :
    IRS P W c₀ ztcoa c offerK (fun c' =>
      AccOK P A Mod R₀ z ztcvc ztobq c' ∧
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuus
  zudk
  zujng
  zusw
  -- the record of the candidate
  refine IRS.mono (K := 16707 + (17000 - 16707)) (IRS.seq (callAbs_irs hI hctx by_omega by_omega he hpp by_simp_all
      ztnvz) ?_) by_rfl (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨hrec₁, k1, hal₁, hm₁⟩
  rw [hpos, hR] at hrec₁
  have k1' : ∀ r, bandOf r ∉ oracleBands → ztkdg → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := by_omega
  have nob : ztiej := fun r h1 h2 =>
    not_oracle_sw h1 h2
  have keep : ∀ r, 240000 ≤ r → r < 250000 → ztkdg →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 =>
    k1' r by_grind h3 ztu
  have e1 := keep e hregs.2.2.1 hregs.2.2.2.1 by_omega
  have h1 := keep h hregs.2.2.2.2.1 hregs.2.2.2.2.2.1 by_omega
  have t1 := keep t hregs.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.1 by_omega
  have d1 := keep dR hregs.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2 by_omega
  have a1 : ∀ j, j ≤ 7 → c₁.nreg _ = c.nreg ztbya := fun j hj =>
    keep _ by_omega by_omega by_omega
  zujwl
  zuibf
  zuibd
  -- the final frame of a take
  have fin_take : ∀ c' : Config, (∀ r, ztlsc → c'.nreg r = c₁.nreg r) →
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC →
        c'.nreg r = c.nreg r) := fun c' hk r hr1 hr2 hr3 => by
    zuoov; grind
  by_cases hf : c₁.nreg A < c₁.nreg K1
  · -- the accumulator is empty: take
    have hf0 : c.nreg A = 0 := by_omega
    have hL := hacc.2.1 hf0
    refine (IRS.ifT hf (take_irs (L := L) (Mod := Mod) hI₁ hW1 hA by_omega
      by_grind by_omega by_grind
      by_grind by_grind hrec₁)).mono by_omega ?_
    zuhjl
    have hAc : ztsef := hk _ ztu
    refine ⟨hacc', fin_take c' hk, by_omega, fun a ha => by_grind⟩
  · -- compare with the kept candidate
    have hf1 : ztuom := by
      rw [k1₁, a0] at hf; have := hacc.1; omega
    obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := hacc.2.2 hf1
    have hrecA₁ : AbsRec P c₁ _ (rayPt z σ τa).1 R₀ :=
      absRec_transport hrecA (a1 4 by_norm_num) by_grind
        by_grind
        by_grind
    -- the comparison step for either order
    have cmp : ∀ (a b : ℕ), (a = A + 4 ∧ b = A + 8 ∨ a = A + 8 ∧ b = A + 4) →
        (∀ x₁ x₂ : ℝ, AbsRec P c₁ a x₁ R₀ → AbsRec P c₁ b x₂ R₀ → zthlf) →
        IRS P W c₀ (.seq (callAbsCmp a b ztiq)
          ztwwv) c₁ (269 + 10)
          (fun c' => AccOK P A Mod R₀ z σ ztobq c' ∧
            (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC →
              c'.nreg r = c.nreg r) ∧
            c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
      intro a b hab hiff
      have hxa : AbsRec P c₁ a (if a = A + 4 then (rayPt z σ τa).1 else (rayPt z σ τ).1) R₀ := by
        rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · grind
        grind
      have hxb : AbsRec P c₁ b (if b = A + 4 then (rayPt z σ τa).1 else (rayPt z σ τ).1) R₀ := by
        rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · grind
        grind
      refine IRS.seq (callAbsCmp_irs hI₁ hG hW3 by_omega by_omega hxa hxb
        ztnvz) ?_
      rintro c₂ hI₂ hA₂ hA₂' ⟨hbit, k2, hal₂, hm₂⟩
      have hb' := (hiff _ _ hxa hxb)
      have k2' := k2
      have keep2 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ A + 12 → c₂.nreg r = c₁.nreg r :=
        fun r h1 h2 h3 => k2' r by_grind h3 ztu
      zudzv
      by_cases hc : c₂.nreg K0 < c₂.nreg ztiq
      · -- take
        zukxb
        have hlt := hb'.1 (hbit.2.1 (by have := hbit.1; omega))
        refine (IRS.ifT by_omega (take_irs hI₂ hW1 hA
          ⟨hout.2.1, hout.2.2.1, hout.2.2.2.1⟩ (fun τ' hτ' => (hlt.trans_le (hmin τ' hτ')).le)
          (by rw [keep2 t by_omega by_omega by_omega, t1]; omega)
          (by rw [keep2 t by_omega by_omega by_omega, keep2 e by_omega by_omega by_omega,
            t1, e1]; exact he)
          (by rw [keep2 t by_omega by_omega by_omega, keep2 e by_omega by_omega by_omega,
            keep2 h by_omega by_omega by_omega, t1, e1, h1]; omega)
          (by rw [keep2 t by_omega by_omega by_omega, keep2 e by_omega by_omega by_omega,
            keep2 h by_omega by_omega by_omega, t1, e1, h1, hpos])
          (absRec_transport hrec₁ (keep2 _ by_omega by_omega by_omega)
            (by rw [show A + 8 + 1 = A + 9 by omega]; exact keep2 _ by_omega by_omega by_omega)
            (by rw [show A + 8 + 2 = A + 10 by omega]; exact keep2 _ by_omega by_omega by_omega)
            (by rw [show A + 8 + 3 = A + 11 by omega]; exact keep2 _ by_omega by_omega by_omega))))
          |>.mono by_omega ?_
        zuhjl
        refine ⟨hacc', fun r hr1 hr2 hr3 => ?_, ?_, fun a ha => ?_⟩
        · rw [hk r by_omega, k2' r hr1 by_omega hr3]; grind
        · rw [hk ALLOC ztu]; omega
        · rw [hm, hm₂ a by_omega]; exact hm₁ a ha
      · -- keep
        zukxb
        have hge := fun h' => by
          have := (hbit.2.2 (hb'.2 h')); omega
        refine (IRS.ifF by_omega (IRS.skip (K := 8) hI₂ ?_)).mono by_omega
          ztb
        refine ⟨⟨?_, fun h0 => ?_, fun _ => ⟨τa, Set.mem_insert_of_mem _ hτa, fun τ' hτ' => ?_, ?_⟩⟩,
          fun r hr1 hr2 hr3 => ?_, hal₁.trans hal₂, fun a ha => by rw [hm₂ a by_omega]; exact hm₁ a ha⟩
        · rw [keep2 A by_omega by_omega by_omega, a0]; omega
        · rw [keep2 A by_omega by_omega by_omega, a0, hf1] at h0; omega
        · rcases hτ' with rfl | hτ'
          · grind
          · exact hmin τ' hτ'
        · have r1 : c₂.nreg ztbo = c.nreg ztbo := by
            zunci; exact a1 1 by_norm_num
          have r2 : c₂.nreg ztbcl = c.nreg ztbcl := by
            zunci; exact a1 2 by_norm_num
          have r3 : c₂.nreg zttf = c.nreg zttf := by
            zunci; exact a1 3 by_norm_num
          rw [r1, r2, r3]
          refine ⟨htagA, hppA, heA, hposA, absRec_transport hrecA ?_ ?_ ?_ ?_⟩
          · zunci; exact a1 4 by_norm_num
          · rw [keep2 _ by_omega by_omega by_omega, show A + 4 + 1 = A + 5 by omega]
            exact a1 5 by_norm_num
          · rw [keep2 _ by_omega by_omega by_omega, show A + 4 + 2 = A + 6 by omega]
            exact a1 6 by_norm_num
          · rw [keep2 _ by_omega by_omega by_omega, show A + 4 + 3 = A + 7 by omega]
            exact a1 7 by_norm_num
        · rw [k2' r hr1 by_omega hr3]; grind
    -- the direction
    have hfneg : σ = -1 → ∀ x₁ x₂ : ℝ, AbsRec P c₁ ztckz x₁ R₀ → AbsRec P c₁ ztcla x₂ R₀ →
        zthlf := by
      zukjj
      have e₁ := absRec_val h₁ hrecA₁
      have e₂ := absRec_val h₂ hrec₁
      zunni; constructor <;> intro h <;> linarith
    have hfpos : σ = 1 → ∀ x₁ x₂ : ℝ, AbsRec P c₁ ztcla x₁ R₀ → AbsRec P c₁ ztckz x₂ R₀ →
        zthlf := by
      zukjj
      have e₁ := absRec_val h₁ hrec₁
      have e₂ := absRec_val h₂ hrecA₁
      zunni; simp
    refine (IRS.ifF hf ?_).mono (K := 269 + 10 + 4 + 2) by_omega ztb
    by_cases hd0 : c₁.nreg dR < c₁.nreg K1
    · zqzu
      exact (IRS.ifT hd0 ztmhk).mono by_omega by_grind
    · refine (IRS.ifF hd0 ?_).mono (K := 269 + 10 + 4) by_omega ztb
      by_cases hd1 : c₁.nreg K1 < c₁.nreg dR
      · zqzu
        exact IRS.ifT hd1 ztmhk
      · have hs : ztgbc := by zungf; apply dirOf_eq_one; omega
        exact IRS.ifF hd1 (cmp _ _ by_omega (hfpos hs))

/-! ## Filtered offers -/

/-- A point of the chain or of the boundary of its box. -/
def OnCB (C : Chain) (x : Point) : Prop :=
  x ∈ C.set ∨ |x.1| = C.radius ∨ |x.2| = C.radius

/-- **A walk position off the open slit** is a point of the chain or of the box boundary. -/
theorem walk_pos_good
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos ztc Q n x) (h5 : x.edge ≠ 5)
    (hs : x.edge = 2 * C.m + 6 → (chainModel C).param Q x = 0) :
    OnCB C ztte := by
  zuet
  have hpos : (chainModel C).pos Q x = sidePt ztcs x.edge
      _ := rfl
  zudbq
  zubo
  obtain ⟨b0, b1, b2, b3, b4, -, -⟩ := C.sidePt_box C.sideBeta t
  rcases (by omega : x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨
    6 ≤ x.edge) with h | h | h | h | h | h
  · zuewc
  · zuewc
  · zuewc
  · zuewc
  · zuewc
  · left
    zueyg
    exact C.sideWalk_tour_pt_mem C.sideBeta by_omega by_grind hp.1 hp.2.1

/-- **A filtered offer**: the position `(e, h)` is normalised in place (bits at `o`); positions on
the slit edge `5` and on the slit edge `2m + 6` with a positive parameter are dropped (they are
above the top of the chain); the others are offered.  `nR` holds the walk length `2m + 7`. -/
def offerF (A dsc e h t dR nR o : ℕ) : Stmt :=
  .seq (normS dsc e h o)
    (.ifLtN e K5 ztcoa
      (.ifLtN K5 e
        (.seq (.instr (.addN o e K1))
          (.ifLtN o nR ztcoa
            (.ifLtN nR o ztcoa
              (.ifLtN K0 h .skip ztcoa))))
        .skip))

/-- The cost of a filtered offer. -/
def offerFK : ℕ := 11015 + offerK + 20

/-- Points of the slit edges with a positive parameter are above the top. -/
theorem slit_above
    (hp : ProperPos ztc Q n x)
    (h : x.edge = 5 ∨ (x.edge = 2 * C.m + 6 ∧ 0 < (chainModel C).param Q x)) :
    C.top.2 < ((chainModel C).pos Q x).2 := by
  have hpos : (chainModel C).pos Q x = sidePt ztcs x.edge
      _ := rfl
  zudbq
  zumcm
  obtain ⟨-, -, -, -, -, b5, b6⟩ := C.sidePt_box C.sideBeta t
  rcases h with h | ⟨h, ht⟩
  · zuobz; simp only
    have : ztzoj := mul_pos (by zuoxq) by_linarith
    nlinarith
  simp_all
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **A filtered offer.** -/
theorem offerF_irs {A dsc e h t dR nR o : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point}
    {L : Set ℝ} {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hA : 240700 ≤ A ∧ A + 12 < 250000)
    (hregs : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240700 ≤ e ∧ e < 250000 ∧ 240700 ≤ h ∧
      h < 250000 ∧ 240000 ≤ t ∧ t < 250000 ∧ 240000 ≤ dR ∧ dR < 250000 ∧ 240000 ≤ nR ∧
      nR < 250000 ∧ 240700 ≤ o ∧ o + 1 < 250000)
    (hdist : e ≠ h ∧ o ≠ e ∧ o ≠ h ∧ o + 1 ≠ e ∧ o + 1 ≠ h ∧ o ≠ t ∧ o ≠ dR ∧ o ≠ nR ∧
      h ≠ t ∧ h ≠ dR ∧ h ≠ nR ∧ o ≠ dsc ∧ h ≠ dsc ∧ o + 1 ≠ t ∧ o + 1 ≠ dR ∧ o + 1 ≠ nR ∧
      o + 1 ≠ dsc)
    (hout : ztlna ∧ ztfra ∧ ztfse ∧
      ztfux ∧ ztlmy ∧ (o + 1 < A ∨ A + 12 < o))
    (hacc : AccOK P A Mod R₀ z ztcvc L c)
    (htag : c.nreg t ≤ 2) (hctx : ChainCtx P W c dsc ztbhn)
    (hR : (Mod ztjsm).radius = R₀) (hn : c.nreg nR = 2 * (Mod ztjsm).m + 7)
    (he : c.nreg e < (chainModel ztbhn).W.n)
    (hpp : ProperPos ztzec zta P.n ztkv)
    (hpos : (chainModel ztbhn).pos zta ztkv =
      rayPt z ztcvc τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + offerFK ≤ W) :
    IRS P W c₀ (offerF A dsc e h t dR nR o) c offerFK (fun c' =>
      (∃ L', AccOK P A Mod R₀ z ztcvc L' c' ∧
        (L' = L ∨ (L' = insert τ L ∧ OnCB ztbhn (rayPt z ztcvc τ))) ∧
        (z.2 ≤ (Mod ztjsm).top.2 → L' = insert τ L)) ∧
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zujng
  set C := Mod ztjsm with hCdef
  have nob : ztiej := fun r h1 h2 =>
    not_oracle_sw h1 h2
  -- normalise
  refine IRS.seq (K₂ := offerK + 20) (normS_exact (normS_irs
    hI ztvti hctx by_omega
    by_simp_all he hpp
    by_simp_all (by unfold offerFK at hroom; omega))
    by_omega) ?_ |>.mono by_rfl (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨n1e, n1h, k1, -, -⟩, hal1, hm1⟩
  have keep1 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ h → r ≠ o → r ≠ o + 1 →
      c₁.nreg r = c.nreg r := by_grind
  have t1 := keep1 t hregs.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.1 (Ne.symm hdist.2.2.2.2.2.2.2.2.1)
    ztvax (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have d1 := keep1 dR hregs.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2.1
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.1) ztvay
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have nR1 := keep1 nR hregs.2.2.2.2.2.2.2.2.2.2.1 hregs.2.2.2.2.2.2.2.2.2.2.2.1
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.1) ztvaz
    (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have ds1 := keep1 dsc hregs.1 hregs.2.1 (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.1)
    ztvba (Ne.symm hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
  have a1 : ∀ j, j ≤ 12 → c₁.nreg _ = c.nreg ztbya := fun j hj =>
    keep1 _ by_omega by_omega by_omega
      by_omega by_omega
  -- the normalised position
  set u : WPos := ztkv with hu
  obtain ⟨hNP, hue, hup, -, hcase⟩ := Restore.normOf_facts hpp
  have hu1 : (ztdqq : WPos) = Restore.normOf ztc zta u := by
    rw [n1e, n1h]; unfold nhgt
    rcases hn' : Restore.normOf _ _ u with ⟨e', h'⟩
    grind
  have hpp1 : ProperPos ztc zta P.n ztdqq := by rw [hu1]; exact hNP.1
  have hpos1 : (chainModel C).pos zta ztdqq = rayPt z σ τ := by
    grind
  have he1 : c₁.nreg e < (chainModel C).W.n := by_omega
  have hcase1 : c₁.nreg h = 0 ∨ 0 < (chainModel C).param zta ztdqq := by
    grind
  have hacc1 : AccOK P A Mod R₀ z σ L c₁ := by
    obtain ⟨f1, f2, f3⟩ := hacc
    zujwl
    zqzq
    rw [a1 1 by_norm_num, a1 2 by_norm_num, a1 3 by_norm_num]
    exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA by_grind
      by_grind
      by_grind
      by_grind⟩
  have hctx1 := hctx.transport ds1 by_grind hal1.ge
  have hm : C.m = (Mod _).m := rfl
  -- offering at a configuration with the same facts
  have doOffer : ∀ c₂ : Config, IInv W c₀ c₂ → c₂.nreg e = c₁.nreg e → c₂.nreg h = c₁.nreg h →
      c₂.nreg t = c.nreg t → c₂.nreg dR = c.nreg dR → c₂.nmem = c₁.nmem →
      c₂.nreg ALLOC = c₁.nreg ALLOC → ztxso →
      ChainCtx P W c₂ dsc C → c₂.nreg ALLOC + offerK ≤ W →
      OnCB C ztdpf →
      IRS P W c₀ ztcoa c₂ offerK (fun c' =>
        (∃ L', AccOK P A Mod R₀ z σ L' c' ∧
          ztxkb ∧
          ztfvm) ∧
        (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC →
          c'.nreg r = c₂.nreg r) ∧
        c₂.nreg ALLOC ≤ c'.nreg ALLOC ∧ ztdwt) := by
    intro c₂ hI₂ e2 h2 t2 d2 m2 al2 a2 hctx2 hroom2 hgood
    have hacc2 : AccOK P A Mod R₀ z (dirOf (c₂.nreg dR)) L c₂ := by
      zqzs
      rw [d2]
      zqzq
      zqzt
      exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA by_grind
        by_grind
        by_grind
        by_grind⟩
    refine (offer_irs (τ := τ) hI₂ hK hG hW3 hA
      by_omega
      by_grind hacc2 by_omega
      by_grind by_grind by_grind
      by_grind by_grind hy hroom2).mono
      le_rfl ?_
    grind
  have k5 := (hK.fix hI₁).2.2.2.2.1
  zuibf
  zumej
  have hn' : ztdh := C.sideWalk_n _
  have hz2 : (rayPt z σ τ).2 = z.2 := rfl
  -- dropping a point above the top
  have drop : ∀ c₂ : Config, IInv W c₀ c₂ → c.nreg ALLOC ≤ c₂.nreg ALLOC →
      ztimn →
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c₂.nreg r = c.nreg r) →
      ztxso →
      C.top.2 < z.2 → ∀ K, IRS P W c₀ .skip c₂ K (fun c' =>
        (∃ L', AccOK P A Mod R₀ z σ L' c' ∧
          ztxkb ∧ ztfvm) ∧
        (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    intro c₂ hI₂ hal hmm hk a2 habove K
    refine IRS.skip hI₂ ⟨⟨L, ?_, Or.inl rfl, by_grind⟩, hk, hal, hmm⟩
    zqzs
    zqzq
    zqzt
    exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA (a2 4 by_norm_num)
      (by rw [show A + 4 + 1 = A + 5 by omega]; exact a2 5 by_norm_num)
      (by rw [show A + 4 + 2 = A + 6 by omega]; exact a2 6 by_norm_num)
      (by rw [show A + 4 + 3 = A + 7 by omega]; exact a2 7 by_norm_num)⟩
  -- the frame of `c₁`
  have fr1 : ∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
      r ≠ ALLOC → c₁.nreg r = c.nreg r := fun r a1 _ a3 a4 a5 a6 => k1 r a1 a3 a4 a5 a6
  have hm1' : ztjbb := by_grind
  -- finishing an offer
  have fin : ∀ c₂ c' : Config, (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h →
      r ≠ o → r ≠ o + 1 → r ≠ ALLOC → c₂.nreg r = c.nreg r) →
      c.nreg ALLOC ≤ c₂.nreg ALLOC → ztimn →
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC →
          c'.nreg r = c₂.nreg r) → c₂.nreg ALLOC ≤ c'.nreg ALLOC →
      ztdwt →
      (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth :=
    fun c₂ c' h2 a2 m2 h' a' m' => ⟨fun r b1 b2 b3 b4 b5 b6 => (h' r b1 b2 b6).trans
      (h2 r b1 b2 b3 b4 b5 b6), a2.trans a', fun a ha => (m' a by_omega).trans zttsz⟩
  by_cases hlt5 : c₁.nreg e < c₁.nreg K5
  · -- a box edge below `5`
    zukxd
    refine (IRS.ifT by_omega ((doOffer c₁ hI₁ rfl rfl t1 d1 rfl rfl by_omega
      hctx1 (by zuouu; unfold offerFK at hroom; omega) ?_).mono le_rfl ?_)).mono
      by_omega ztb
    · zuezy
      exact walk_pos_good C _ he1 hpp1 ztdza
        ztcvk
    · rintro c' ⟨hL', hk', ha', hm'⟩
      exact ⟨hL', fin c₁ c' fr1 hal1.ge hm1' hk' ha' hm'⟩
  · refine IRS.ifF hlt5 ?_ |>.mono (K := offerK + 18) by_omega ztb
    zukxd
    by_cases hgt5 : c₁.nreg K5 < c₁.nreg e
    · zukxc
      refine IRS.ifT by_omega ?_ |>.mono (K := offerK + 16) by_omega ztb
      have hok : c₁.nreg e + c₁.nreg K1 ≤ W := by_omega
      refine IRS.seq (IRS.reg hI₁ (iscr_sw hregs.2.2.2.2.2.2.2.2.2.2.2.2.1 by_omega)
        (Exec.addN hI₁.hw o e K1 hok)) ?_ |>.mono (K := 1 + (offerK + 8)) by_omega (fun _ h => h)
      rintro c₂ hI₂ hA₂ hA₂' rfl
      have u : ∀ r, r ≠ o → (upd c₁.nreg o ztcho) r = c₁.nreg r := fun r hr =>
        upd_other _ _ _ hr
      have e2 := u e (Ne.symm hdist.2.1)
      have h2 := u h (Ne.symm hdist.2.2.1)
      have t2 := (u t ztvax).trans t1
      have d2 := (u dR ztvay).trans d1
      have n2 := (u nR ztvaz).trans nR1
      have al2 := u ALLOC ztu
      have a2 : ∀ j, j ≤ 12 → ztrxu _ = c₁.nreg ztbya :=
        fun j hj => u _ by_omega
      have hctx2 : ChainCtx P W { c₁ with nreg := upd c₁.nreg o _ } dsc C :=
        hctx1.transport (u dsc ztvba) ztcj al2.ge
      have fr2 : ∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o →
          r ≠ o + 1 → r ≠ ALLOC → ztrxu r = c.nreg r :=
        fun r b1 b2 b3 b4 b5 b6 => (u r b4).trans (fr1 r b1 b2 b3 b4 b5 b6)
      have off2 : OnCB C _ → IRS P W c₀ _
          { c₁ with nreg := upd c₁.nreg o _ } offerK _ := fun hg =>
        doOffer _ hI₂ e2 h2 t2 d2 rfl al2 a2 hctx2 (by
          show upd c₁.nreg o _ ALLOC + offerK ≤ W
          rw [al2, hal1]; unfold offerFK at hroom; omega) hg
      have alg : c.nreg ALLOC ≤ ({ c₁ with nreg := upd c₁.nreg o (c₁.nreg e + c₁.nreg K1) } :
          Config).nreg ALLOC := by
        omega
      have finish : ∀ c' : Config, (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ ALLOC →
          c'.nreg r = upd c₁.nreg o _ r) →
          upd c₁.nreg o _ ALLOC ≤ c'.nreg ALLOC →
          (∀ a, a < upd c₁.nreg o _ ALLOC → c'.nmem a = c₁.nmem a) →
          (∀ r, bandOf r ∉ oracleBands → ztnn → r ≠ h → r ≠ o → r ≠ o + 1 →
            r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth :=
        fun c' h' a' m' => fin { c₁ with nreg := upd c₁.nreg o _ } c' fr2
          alg hm1' h' a' m'
      by_cases hb1 : upd c₁.nreg o ztcho o < upd c₁.nreg o ztcho nR
      · zufol
        refine IRS.ifT ztgrd
          ztmzj |>.mono by_omega ztb
        · zuezy
          exact walk_pos_good C _ he1 hpp1 ztdza
            ztcvk
        · zqzr
      · refine IRS.ifF by_omega ?_ |>.mono
          (K := offerK + 6) by_omega ztb
        zufol
        by_cases hb2 : upd c₁.nreg o ztcho nR < upd c₁.nreg o ztcho o
        · zufom
          refine IRS.ifT ztgrd
            ztmzj |>.mono by_omega ztb
          · zuezy
            exact walk_pos_good C _ he1 hpp1 ztdza
              ztcvk
          · zqzr
        · refine IRS.ifF by_omega ?_ |>.mono
            (K := offerK + 4) by_omega ztb
          zufom
          have hlast : c₁.nreg e = 2 * C.m + 6 := by zvmwi; omega
          have k0₂ : upd c₁.nreg o ztcho K0 = 0 := by
            rw [u K0 (by unfold K0 sw; omega)]; exact (hK.fix hI₁).1
          by_cases hb3 : upd c₁.nreg o ztcho K0 < upd c₁.nreg o ztcho h
          · -- drop: above the top
            zuilf
            have hpar : 0 < (chainModel C).param _ ztdqq :=
              hcase1.resolve_left by_omega
            have habove := slit_above C _ hpp1 (Or.inr ⟨hlast, hpar⟩)
            zuikl
            refine IRS.ifT (by simp only; omega)
              (drop _ hI₂ alg hm1' fr2 a2 habove offerK)
          · refine IRS.ifF by_omega
              ((off2 ?_).mono by_omega ?_)
            · zuilf
              zuezy
              exact walk_pos_good C _ he1 hpp1 ztdza (fun _ => by
                show (chainModel C).param _ ztdqq = 0
                rw [show c₁.nreg h = 0 by omega]; rfl)
            · zqzr
    · -- the slit edge `5`: drop
      zukxc
      have h5 : c₁.nreg e = 5 := by_omega
      have habove := slit_above C _ hpp1 ztmbw
      zuikl
      exact IRS.ifF by_omega (drop c₁ hI₁ hal1.ge hm1' fr1 by_omega habove _)

/-! ## Transport -/

/-- **The accumulator survives** a step keeping its block. -/
theorem AccOK.transport {A : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point} {σ : ℝ} {L : Set ℝ}
    {c c' : Config} (h : AccOK P A Mod R₀ z σ L c) (hr : ∀ j, j ≤ 12 → c'.nreg ztbya = c.nreg ztbya) :
    AccOK P A Mod R₀ z σ L c' := by
  obtain ⟨f1, f2, f3⟩ := h
  have a0 : c'.nreg A = c.nreg A := by simpa using hr 0 by_norm_num
  refine ztmqh
  obtain ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, hrecA⟩ := f3 by_omega
  rw [hr 1 by_norm_num, hr 2 by_norm_num, hr 3 by_norm_num]
  exact ⟨τa, hτa, hmin, htagA, hppA, heA, hposA, absRec_transport hrecA by_simp_all
    by_grind
    by_grind
    by_grind⟩
end
end SweepIo
end Chazelle.Core
end
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers -/
def lMD : ℕ := sw 1100
def lCD : ℕ := sw 1101
def lNF : ℕ := sw 1102
def lE : ℕ := sw 1103
def lH : ℕ := sw 1104
def lD : ℕ := sw 1105
def lN : ℕ := sw 1106
def lT : ℕ := sw 1107
def lJ : ℕ := sw 1108
def lR0 : ℕ := sw 1109
def lR1 : ℕ := sw 1110
def lR2 : ℕ := sw 1111
def lX : ℕ := sw 1112
def lY : ℕ := sw 1113
def lA : ℕ := sw 1114
def lSB : ℕ := sw 1115
def lAB : ℕ := sw 1116
def lJP : ℕ := sw 1117
def lJN : ℕ := sw 1118
def lL : ℕ := sw 1119

/-- The accumulator of the answers. -/
def accA : ℕ := sw 2000

/-! ## The three regions -/

/-- Header reads: the number of arcs, the sequence table, the arc records. -/
def nbrHead : List Instr :=
  [.addN lX lNF K1, .loadN lA lX, .addN lX lNF K6, .loadN lSB lX, .addN lX lNF K4,
    .loadN lAB lX]

/-- The neighbouring spine positions. -/
def nbrJ : Stmt :=
  .seq ztfaw
    (.seq (.instr (.addN lJN lJ K1)) (.ifLtN lJN lA .skip (.instr (.constN lJN 0))))

/-- The region of the arc at the spine position in `p`, into `dst`. -/
def regOfL (p dst : ℕ) : List Instr :=
  [.addN lX lSB p, .loadN lX lX, .addN lY lX lX, .addN lY lY lY, .addN lY lY lX,
    .addN lY lAB lY, .loadN dst lY]

/-- The three regions. -/
def nbrRegsL : List Instr := regOfL lJP lR0 ++ regOfL lJ lR1 ++ regOfL lJN lR2

/-- Store the three regions at the allocator (list address in `lL`). -/
def put3 : Stmt :=
  block [.copyN lL ALLOC, .storeN ALLOC lR0, .addN ALLOC ALLOC K1, .storeN ALLOC lR1,
    .addN ALLOC ALLOC K1, .storeN ALLOC lR2, .addN ALLOC ALLOC K1]
variable (m f : ℕ → ℕ) {q : ℕ} {C : Chain}
theorem nbrRegsL_val :
    regB m nbrRegsL f lR0 = m (f lAB + 5 * m (f lSB + f lJP)) ∧
    regB m nbrRegsL f lR1 = m (f lAB + 5 * m ztdnk) ∧
    regB m nbrRegsL f lR2 = m (f lAB + 5 * m (f lSB + f lJN)) := by
  simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, regB, regI, upd, lX, lY, lSB,
    lAB, lJP, lJ, lJN, lR0, lR1, lR2, sw]
  grind
theorem nbrRegsL_other (h1 : q ≠ lX) (h2 : q ≠ lY) (h3 : q ≠ lR0)
    (h4 : q ≠ lR1) (h5 : q ≠ lR2) : regB m nbrRegsL f q = f q :=
  regB_other m nbrRegsL f (fun i hi => by
    simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> intro h <;> subst h <;>
      simp_all)
theorem nbrHead_val (hk1 : f K1 = 1) (hk4 : f K4 = 4) (hk6 : f K6 = 6) :
    regB m nbrHead f lA = m (f lNF + 1) ∧ regB m nbrHead f lSB = m (f lNF + 6) ∧
    regB m nbrHead f lAB = m (f lNF + 4) := by
  zubx
  zudmx
  zujxn
  simp only [nbrHead, regB, regI, upd, lX, lA, lSB, lAB, lNF, K1, K4, K6, sw]
  simp_all
theorem nbrHead_other (h1 : q ≠ lX) (h2 : q ≠ lA) (h3 : q ≠ lSB)
    (h4 : q ≠ lAB) : regB m nbrHead f q = f q :=
  regB_other m nbrHead f (fun i hi => by
    simp only [nbrHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> intro h <;>
      subst h <;> simp_all)
theorem nbrHead_ok (hk1 : f K1 = 1) (hk4 : f K4 = 4) (hk6 : f K6 = 6)
    (hb : f lNF + 6 ≤ W) : okB W m nbrHead f := by
  zubx
  zudmx
  zujxn
  have hb' : f 241102 + 6 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [nbrHead, okB, okI, regI, upd, lX, lA, lSB, lAB, lNF, K1, K4, K6, sw]
  grind
theorem nbrRegsL_ok (hb : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      f lSB + f p ≤ W ∧ f lAB + 5 * m (f lSB + f p) ≤ W) : okB W m nbrRegsL f := by
  obtain ⟨a1, a2⟩ := hb lJP ztp
  obtain ⟨b1, b2⟩ := hb lJ by_omega
  obtain ⟨d1, d2⟩ := hb lJN by_omega
  have a1' : f 241115 + f 241117 ≤ W := a1
  have a2' : f 241116 + 5 * m (f 241115 + f 241117) ≤ W := a2
  have b1' : ztpor := b1
  have b2' : f 241116 + 5 * m ztqmt ≤ W := b2
  have d1' : f 241115 + f 241118 ≤ W := d1
  have d2' : f 241116 + 5 * m (f 241115 + f 241118) ≤ W := d2
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [nbrRegsL, regOfL, List.cons_append, List.nil_append, okB, okI, regI, upd, lX, lY,
    lSB, lAB, lJP, lJ, lJN, lR0, lR1, lR2, sw]
  grind

/-- The memory after `put3`. -/
def mem3 (m : ℕ → ℕ) (A v0 v1 v2 : ℕ) : ℕ → ℕ := upd (upd ztlui ztbo v1) ztbcl v2
theorem put3_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 3 ≤ W) :
    IRS P W c₀ put3 c 7 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 3 ∧ c'.nreg lL = c.nreg ALLOC ∧
      (∀ r, r ≠ ALLOC → r ≠ lL → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem3 c.nmem ztm (c.nreg lR0) (c.nreg lR1) (c.nreg lR2)) := by
  zubgn
  zubod
  have hroom' : c.nreg 9999 + 3 ≤ W := hroom
  have ex : ∃ c' k, Exec P W (block [.copyN 241119 9999, .storeN 9999 241109,
      .addN 9999 9999 240611, .storeN 9999 241110, .addN 9999 9999 240611, .storeN 9999 241111,
      .addN 9999 9999 240611]) c c' k ∧ k = 7 ∧
      c'.nreg 9999 = c.nreg 9999 + 3 ∧ c'.nreg 241119 = c.nreg 9999 ∧
      (∀ r, r ≠ 9999 → r ≠ 241119 → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem3 c.nmem zterc (c.nreg 241109) (c.nreg 241110) (c.nreg 241111) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, ?_, rfl, rfl, rfl⟩
    · simp_all
    · config_simp
    · simp_all
    · config_simp
      simp only [k1, mem3]
  zubtw
  refine IRS.ofExec hI ex by_omega (fun r hr hra => h3 r hra (fun h => hr (by
    subst h; exact iscr_sw by_norm_num by_norm_num))) h5 (fun a ha => ?_) h6 h7
    ztljk ztjqi
    ⟨h1, h2, h3, h4⟩
  zujic
  zubcl

  unfold mem3
  zuby
  grind

/-- The neighbouring spine positions. -/
theorem nbrJ_irs (hI : IInv W c₀ c) (hK : Consts c) {A j : ℕ} (hA : c.nreg lA = A)
    (hj : c.nreg lJ = j) (hjA : j < A) :
    IRS P W c₀ nbrJ c 7 (fun c' => c'.nreg lJP = predP A j ∧ c'.nreg lJN = succP A j ∧
      (∀ r, r ≠ lJP → r ≠ lJN → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zubof
  have hAW : ztpio := by rw [← hA]; exact hI.hw.1 _
  unfold nbrJ
  -- the previous position
  have step1 : IRS P W c₀ ztfaw c 3
      (fun c' => c' = { c with nreg := upd c.nreg lJP (predP A j) }) := by
    by_cases h0 : c.nreg lJ < c.nreg K1
    · refine (IRS.ifT h0 (IRS.reg hI ztbua
        (Exec.subN hI.hw lJP lA K1))).mono by_omega ?_
      zuu
      rw [hA, k1, show predP A j = A - 1 by unfold predP; rw [ite_eq_left by_omega]]
    · refine (IRS.ifF h0 (IRS.reg hI ztbua
        (Exec.subN hI.hw lJP lJ K1))).mono le_rfl ?_
      zuu
      rw [hj, k1, show predP A j = j - 1 by unfold predP; rw [ite_eq_right by_omega]]
  refine IRS.seq step1 ?_ |>.mono (K := 3 + (1 + 3)) by_omega ztb
  zugn
  have c1J : c₁.nreg lJ = j := by
    zugdp
  have c1K : ztcpf := by
    zugdp
  have c1A : c₁.nreg lA = A := by
    zugdp
  have c1P : c₁.nreg lJP = predP A j := by
    simp_all
  have c1r : ∀ r, r ≠ lJP → c₁.nreg r = c.nreg r := by
    simp_all
  have hjW : c₁.nreg lJ + c₁.nreg K1 ≤ W := by_omega
  refine IRS.seq (IRS.reg hI₁ ztbua
    (Exec.addN hI₁.hw lJN lJ K1 hjW)) ?_
  zubib
  have v2N : c₂.nreg lJN = j + 1 := by
    simp_all
  have v2A : c₂.nreg lA = A := by
    zudua
  have v2P : c₂.nreg lJP = predP A j := by
    zudua
  have v2r : ∀ r, r ≠ lJP → r ≠ lJN → c₂.nreg r = c.nreg r := by
    simp_all
  by_cases hn : j + 1 < A
  · have hc : c₂.nreg lJN < c₂.nreg lA := by_omega
    refine (IRS.ifT hc (IRS.skip (K := 1) hI₂ ?_)).mono by_omega ztb
    refine ⟨v2P, by rw [v2N]; unfold succP; simp_all, v2r, by_simp_all⟩
  · have hc : ¬ c₂.nreg lJN < c₂.nreg lA := by_omega
    refine (IRS.ifF hc (IRS.reg hI₂ ztbua
        (Exec.constN hI₂.hw lJN 0 ztbg))).mono le_rfl ?_
    zuu
    have w1 : upd c₂.nreg lJN 0 lJP = predP A j := by
      tauto
    have w2 : upd c₂.nreg lJN 0 lJN = succP A j := by
      zunkc; unfold succP; simp_all
    simp_all

/-! ## The context -/

/-- A valid normal form of a chain model has an arc. -/
theorem arcs_pos (hP : C.P.Simple) {N : NF} (hNF : IsNF ztc zta N) :
    0 < N.arcs.length := by
  obtain ⟨hcov1, -⟩ := arcCover ztc zta ztwjq
    ztxgi hNF.1
  zueie
  obtain ⟨j, hj, -⟩ := NFLoc.listed_of_isArc hNF hU hab
  omega

/-- **The context of a local hit** in the chain model of `C` with the normal form `N` (bound
`E`), at a run configuration `c`: the descriptors in `lMD`, `lCD`, the normal form in `lNF`, the
table of powers above the normal form. -/
structure LCtx (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (E : ℕ) (c : Config) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hctx : ChainCtx P W c lCD C
  hcd : c.nreg lCD = c.nreg lMD + 1
  hmd : ModelDescAt c.nmem ztqiw zta ztc
  hmwf : ModelDescWF P ztm c.nmem ztqiw
  hm0 : c.nmem ztqiw = 0
  hP : C.P.Simple
  hNW : NFWithin c.nmem (c.nreg lNF) E N
  hE : E ≤ c.nreg ALLOC
  hNF : IsNF ztc zta N
  htab : ∀ j, j < c.nreg TLR → c.nmem ztllh = 2 ^ j
  hbig : N.arcs.length < 2 ^ c.nreg TLR
  hTB : E ≤ c.nreg TBR
  hTW : c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC

/-- The registers of part 1 (`lJ … lL`). -/
def LSet (r : ℕ) : Prop := sw 1108 ≤ r ∧ r ≤ sw 1119

/-- **Part 1** of the local hit. -/
def lh1 : Stmt :=
  .seq (locJ lMD lNF lE lH lJ) (.seq (block nbrHead) (.seq nbrJ (.seq (block nbrRegsL) put3)))

/-- The cost of part 1. -/
def lh1K (L : ℕ) : ℕ := 5500 * ztgt + 9 + 60
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Part 1 of the local hit**: the spine position of `x` and the list of its three regions. -/
theorem lh1_irs {N : NF} {E : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hL : LCtx P W C N E c) (he : c.nreg lE < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n zthj)
    (hroom : c.nreg ALLOC + lh1K zterd ≤ W) :
    IRS P W c₀ lh1 c (lh1K zterd) (fun c' =>
      c'.nreg lJ < N.arcs.length ∧
      (¬ (chainModel C).IsCut ztwjq
          ztxjo →
        N.F ztc zta = ∅ ∨
          sideInArc (sk ztc zta N ztfgj)
            (ek ztc zta N ztfgj)
            ztxjo) ∧
      ((chainModel C).IsCut ztwjq
          ztxjo →
        sk ztc zta N ztfgj =
            (chainModel C).key zta zthj ∨
          ek ztc zta N ztfgj =
            (chainModel C).key zta zthj) ∧
      c'.nreg lL = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 3 ∧
      (∀ i, i < 3 → c'.nmem ztfqi = (Sweep.nbrRegs N ztfgj).getD i 0) ∧
      zth ∧
      ztrn ∧
      c'.nreg lR0 = (N.arc (sj N (predP N.arcs.length ztfgj))).reg ∧
      c'.nreg lR1 = (N.arc (sj N ztfgj)).reg ∧
      c'.nreg lR2 = (N.arc (sj N (succP N.arcs.length ztfgj))).reg) := by
  zuus
  have hNA : ztpkv := hL.hNW.holds
  have hA0 := arcs_pos hL.hP hL.hNF
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hL.hNW hL.hNF hA0
  obtain ⟨-, -, b3, -, -, -⟩ := Restore.nf_bounds hL.hNW
  zubwc
  have hTB := hL.hTB
  have hTW := hL.hTW
  have hE := hL.hE
  -- 1. locate
  refine IRS.mono (K := ztwzf + (6 + (7 + (21 + 7))))
    (IRS.seq (locJ_irs hI hL.hG hL.hWh
      ⟨by_decide, by_decide, by_decide,
        by decide, by_decide, by_decide,
        by decide, by_decide⟩
      ⟨by_decide, by_decide⟩ hL.hmd hL.hmwf hL.hP hNA hL.hNF
      he hpp hL.htab hL.hbig by_omega by_omega by_omega by_omega
      (by unfold lh1K at hroom; omega)) ?_) (by unfold lh1K; omega) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨hj1, hl1, hl2, k1, hA1, hm1⟩
  zujmz
  have keep1 := fun r h1 h2 h3 =>
    k1 r ztsg h3 ztu
  have hNF1 : c₁.nreg lNF = c.nreg lNF := keep1 _ by_decide by_decide
    by_decide
  -- 2. the header
  zulij
  have hok2 : okB W c₁.nmem nbrHead c₁.nreg := nbrHead_ok _ _ hK₁.2.1 hK₁.2.2.2.1 hK₁.2.2.1
    by_omega
  refine IRS.seq (IRS.block nbrHead hI₁ hok2) ?_
  zubib
  obtain ⟨v2A, v2SB, v2AB⟩ := nbrHead_val c₁.nmem c₁.nreg hK₁.2.1 hK₁.2.2.2.1 hK₁.2.2.1
  zufvm
  have c2A : c₂.nreg lA = N.arcs.length := by
    zumyw; show regB c₁.nmem nbrHead c₁.nreg lA = _
    rw [v2A, hNF1, hm1]; exact hNA.2.1
  have c2SB : c₂.nreg lSB = c.nmem ztfqk := by
    simp_all
  have c2AB : c₂.nreg lAB = c.nmem zthvh := by
    simp_all
  have c2r : ∀ r, r ≠ lX → r ≠ lA → r ≠ lSB → r ≠ lAB → c₂.nreg r = c₁.nreg r := by
    intro r h1 h2 h3 h4; zumyw; exact nbrHead_other _ _ h1 h2 h3 h4
  have c2J : c₂.nreg lJ = j := c2r _ by_decide by_decide
    by_decide by_decide
  -- 3. the neighbouring positions
  refine IRS.seq (nbrJ_irs hI₂ ztqpi c2A c2J hj1) ?_
  rintro c₃ hI₃ - - ⟨v3P, v3N, k3, hm3'⟩
  have hjP := OracleQ.predP_lt hj1
  have hjN := OracleQ.succP_lt hj1
  have c3SB : c₃.nreg lSB = c.nmem ztfqk := by
    rw [k3 _ by_decide by_decide, c2SB]
  have c3AB : c₃.nreg lAB = c.nmem zthvh := by
    rw [k3 _ by_decide by_decide, c2AB]
  have c3J : ztpnp := by
    rw [k3 _ by_decide by_decide, c2J]
  have hm3 : ztckd := by_grind
  -- the regions
  have hseqv : ∀ p, p < N.arcs.length → c.nmem _ = sj N p := fun p hp =>
    hNA.2.2.2.2.2.2.2.2.1 p (by rw [NFLoc.seq_length hL.hNF]; exact hp)
  have hsjl : ∀ p, p < N.arcs.length → sj N p < N.arcs.length := fun p hp => NFLoc.seq_lt hL.hNF hp
  have hregv : ∀ p, p < N.arcs.length →
      c.nmem (c.nmem zthvh + 5 * c.nmem (c.nmem ztfqk + p)) = (N.arc ztmh).reg := by
    zuda
    rw [hseqv p hp]; exact (hNA.2.2.2.2.2.2.1 _ by_grind).1
  have hb1 : ∀ v, v < N.arcs.length → c.nmem ztfqk + v ≤ W ∧
      c.nmem zthvh + 5 * c.nmem (c.nmem ztfqk + v) ≤ W := by
    zuml
    zugem
    have := b3 _ ztobg
    omega
  have hbound : ∀ p, p = lJP ∨ p = lJ ∨ p = lJN →
      c₃.nreg lSB + c₃.nreg p ≤ W ∧ c₃.nreg lAB + 5 * c₃.nmem (c₃.nreg lSB + c₃.nreg p) ≤ W := by
    zuda
    rw [c3SB, c3AB, hm3]
    zubyb
    · grind
    · grind
    grind
  refine IRS.seq (IRS.block nbrRegsL hI₃ (nbrRegsL_ok _ _ hbound)) ?_
  zudsw
  obtain ⟨v40, v41, v42⟩ := nbrRegsL_val c₃.nmem c₃.nreg
  have c4R0 : ztyuk := by
    zumyv; show regB c₃.nmem nbrRegsL c₃.nreg lR0 = _
    rw [v40, c3SB, c3AB, v3P, hm3, hregv _ hjP]
  have c4R1 : ztyul := by
    zumyv; show regB c₃.nmem nbrRegsL c₃.nreg lR1 = _
    rw [v41, c3SB, c3AB, c3J, hm3, hregv _ hj1]
  have c4R2 : ztyum := by
    zumyv; show regB c₃.nmem nbrRegsL c₃.nreg lR2 = _
    rw [v42, c3SB, c3AB, v3N, hm3, hregv _ hjN]
  have c4r : ∀ r, r ≠ lX → r ≠ lY → r ≠ lR0 → r ≠ lR1 → r ≠ lR2 → c₄.nreg r = c₃.nreg r := by
    intro r h1 h2 h3 h4 h5; zumyv; exact nbrRegsL_other _ _ h1 h2 h3 h4 h5
  zudor
  have hA4 : ztgul := by
    rw [c4r _ by_decide by_decide
      by_decide by_decide by_decide,
      k3 _ by_decide by_decide,
      c2r _ by_decide by_decide
        by_decide by_decide, hA1]
  have c4J : ztpnv := by
    rw [c4r _ by_decide by_decide
      by_decide by_decide by_decide,
      c3J]
  -- 4. store the list
  refine (put3_irs hI₄ (hK.fix hI₄) (by zupcr; unfold lh1K at hroom; omega)).mono le_rfl ?_
  rintro c₅ ⟨hA5, hL5, k5, hm5⟩
  have ls : ∀ q, LSet q → q ≠ ALLOC := fun q hq => by unfold LSet sw at hq; unfold ALLOC; omega
  have nl : ∀ q g, LSet g → ¬ LSet q → q ≠ g := by_grind
  have c5J : ztpny := by
    rw [k5 _ by_decide by_decide, c4J]
  have hlist : c₅.nmem = mem3 c.nmem ztm (N.arc ztcay).reg
      (N.arc ztbhb).reg (N.arc ztcaz).reg := by
    grind
  refine ⟨by_omega, fun h => by_grind, fun h => by_grind,
    by omega, by_omega, fun i hi => ?_, fun a ha => ?_, fun r hr hrl hra => ?_,
    by rw [c5J, k5 _ by_decide by_decide, c4R0],
    by rw [c5J, k5 _ by_decide by_decide, c4R1],
    by rw [c5J, k5 _ by_decide by_decide, c4R2]⟩
  · rw [hlist, c5J]
    unfold mem3 Sweep.nbrRegs
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simp
    · simp
    simp
  · rw [hlist]; unfold mem3; zvmwf
    zugeu
  · have h1 := nl r lL by_trivial hrl
    rw [k5 r hra h1,
      c4r r ztqtx (nl r lY by_trivial hrl)
        (nl r lR0 by_trivial hrl) (nl r lR1 by_trivial hrl)
        (nl r lR2 by_trivial hrl),
      k3 r (nl r lJP by_trivial hrl) (nl r lJN by_trivial hrl),
      c2r r ztqtx (fun h => by subst h; unfold lA LSet sw at hrl; omega)
        (fun h => by subst h; unfold lSB LSet sw at hrl; omega)
        (fun h => by subst h; unfold lAB LSet sw at hrl; omega)]
    exact k1 r hr (nl r lJ by_trivial hrl) hra
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Det
variable {J : Merge.Junction}

/-- **A chord without attachment in the open right stretch is a stop chord.** -/
theorem stop_of_out (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {e : Set Point}
    (he : e ∈ F₂plus J S₂)
    (hout : ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (0 < oW J ztej ∧ oW J ztej < Lst J)) : StopChord2 J S₂ e := by
  zumv
  have hns : ¬ StopChord J S₂ e := fun h' => h zthrp
  obtain ⟨pB, tB, hB, h1, h2, -, -⟩ := stretch_end J hP hS₂ hS₂f he hns
  tauto

/-- **Completeness of the detection from the invariant.** -/
theorem det_of_evInv (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {oK : ℝ} {Λ : Set ztf}
    (hLK : (Lst J : ℝ) ≤ oK) (hInv : EvInv J S₂ oK Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : oK < oW J ztkm)
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ ztxrc)
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK) :
    (∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord2 J S₂ s) ∨
    ∃ h ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W h pK tK ∧
      ∃ (a : Point) (σ : ℝ) (c V : Set Point), c ∈ S₂ ∧ V ∈ (chainModel J.right).regions S₂ ∧
        ztgev ∧ Chazelle.Chain.TouchesIn (chainModel J.right).D c V ∧
        ztxel ∧ a ∈ J.right.set ∧
        a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧ h = Merge.shoot J.whole a σ := by
  zubfw

  zust
  zuiwi
  -- a non-cut position just before `K*`, after `K`
  obtain ⟨Rb, hRb, -, w, u, hw, hu, hncw, hfw, h1, h2, hgw⟩ := before_region_exists' hP hS₂a hS₂f
    hpK htK0 htK1 by_linarith (show 0 < oW J ztkm - oK by linarith)
  have hpos := hInv w u hw hu hncw by_linarith (fun e' he' q s hQ h3 h4 =>
    absurd ⟨h3, by_linarith⟩ (hgap e' he' q s hQ))
  zukma
  · -- enclosed: every chord at `K*` is a stop chord
    left
    obtain ⟨e', he', qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩ := hE
    have hqa : oW J zteuu ≤ oK := by
      grind
    rcases hby with hby | hby
    · -- a bracket
      have hqb : oW J ztkm ≤ oW J ztbjt := by
        grind
      rcases hqb.lt_or_eq with hqb | hqb
      · -- `K*` strictly inside: `e` is a bracket
        refine ztfzh
        by_cases hee : e' = e
        · subst hee
          rcases key_of_two hM zthxr hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            zumia
        · have := closed_nested hP hS₂a hS₂f he' he hee hA hB by_linarith heK by_linarith hqb hQ
          grind
      · -- `K*` is the closer: the bracket chord itself is a stop
        obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hB.1 hpK hB.2.1 hB.2.2.1 htK0 htK1 hqb.symm
        refine ⟨e', he', hB, stop_of_out hP hS₂a hS₂f he' fun q s hQ h => ?_⟩
        rcases key_of_two hM zthxr hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          zumia
    · -- a pocket: the chords after it are stops
      refine ztfzh
      have hee : e' ≠ e := by
        zunq
        rcases key_of_two hM zthxr hA hB hAB heK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      -- the other attachment of `e` in `(0, Lst)` would put `K*` inside `[0, A]`
      have := closed_nested hP hS₂a hS₂f he' he hee hB hA by_linarith hQ by_grind
        by_grind heK
      grind
  · -- a valid label: the next event of `next_event_origin`
    obtain ⟨L, hL, hLr, hv⟩ := hval Rb hRb hfw
    by_cases hstop : ∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord J S₂ s
    · obtain ⟨s, hs, hsK, hss⟩ := hstop
      exact Or.inl ⟨s, hs, hsK, Or.inl hss⟩
    push Not at hstop
    obtain ⟨h, hh, hhK, a, σ, hσ, hfree, rfl, hcase⟩ := next_event_origin J hP hS₂ hF hRb hLr hv hw hu
      hncw hfw (show (Lst J : ℝ) < oW J (w + u) by linarith) hpK htK0 htK1 h2
      (fun x hx hx0 hxn ⟨h3, h4⟩ => hgw x hx hx0 hxn ⟨h3, h4⟩) he heK hstop
    rcases hcase with ⟨c, hc, ⟨V, hLV, hT⟩, hac, ha, hav⟩ | hat
    · by_cases hatop : a = J.right.top
      · subst hatop
        exact Or.inl ztyko
      right
      have hV : V ∈ (chainModel J.right).regions S₂ ∧ ztgev := by
        rcases hLV with rfl | hg
        · grind
        · exact ⟨hg.2.1, Or.inr hg⟩
      grind
    · subst hat
      exact Or.inl ztyko

/-- **The partner at a tie** (beyond the start): a second chord `e'` at the key of a chord `e`
inside `c ∈ S₂` is the chord seen from an end of `c`. -/
theorem partner_of_parent (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) (hNTV : NoTieV J S₂)
    {e e' c : Set Point} (he : e ∈ F₂plus J S₂) (he' : e' ∈ F₂plus J S₂) (hne : e ≠ e')
    (hc : c ∈ S₂) (hec : e ⊆ c) {p : ℕ} {t : ℝ} (hA : SideAttach (chainModel J.whole).W e p t)
    (hA' : SideAttach (chainModel J.whole).W e' p t) (hL : (Lst J : ℝ) < oW J ztk) :
    (FreeAt J.whole ztffp 1 ∧ e' = Merge.shoot J.whole ztffp 1) ∨
      (FreeAt J.whole ztffq (-1) ∧ e' = Merge.shoot J.whole ztffq (-1)) := by
  zuv
  have hD : sidePt (chainModel J.whole).W p t ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f he he' hne hA hA' ztbay with h | h
    · zubh
    · exact (hNTV e he e' he' hne p t hA hA' h hL).elim
  obtain ⟨c', hc', hec', he'c'⟩ := tie_parent J hP hS₂ he he' ztnr hA hA' hD
  -- two distinct points of `e`
  obtain ⟨pb, tb, hB, hBne⟩ := hC.hM.other_attach ztfhs hA
  have hcc : c' = c := parent_unique hS₂ hc' hc hBne (hec' hB.2.2.2.1) (hec' hA.2.2.2.1)
    (hec hB.2.2.2.1) (hec hA.2.2.2.1)
  zulat
  exact piece_of_parent J hP hS₂ he' hc' he'c' hA' hD
end Det
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Step
variable {J : Merge.Junction}
variable {S₂ : Set (Set Point)}
/-- **The three kinds of chords of `F₂⁺`.** -/
theorem f2_cases (_hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) :
    (∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ztxel ∧
      FreeAt J.whole a σ ∧ e = Merge.shoot J.whole a σ) ∨
    (∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.shared σ ∧ e = Merge.shoot J.whole J.shared σ) ∨
    (∃ σ : ℝ, ztdd ∧ FreeAt J.whole J.right.top σ ∧
      e = Merge.shoot J.whole J.right.top σ) := by
  zubjm
  · grind
  · grind
  · tauto
  · zucec
    have hv : ztxmm := by
      zubut
    refine Or.inr ztkqi
    · zufab
    · zufaa

/-- A chord seen from an end of a chord of `S₂` along it lies in it. -/
theorem shoot_sub_end (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point}
    (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm) :
    Merge.shoot J.whole a σ ⊆ c := by
  zucol
  zuht
  · zukuu
    exact Merge.shoot_subset_pos J.whole hH.lt (fun hd => hH.right_not zteex)
  · zukvv
    exact Merge.shoot_subset_neg J.whole hH.lt (fun hd => hH.left_not zteex)

/-- **A non-stop chord is an endpoint-query chord.** -/
theorem nonstop_cases (hS₂ : S₂ ⊆ Merge.augChords J.right) {e : Set Point}
    (he : e ∈ F₂plus J S₂) (hns : ¬ StopChord2 J S₂ e) :
    ∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ztxel ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ := by
  rcases f2_cases hS₂ he with ⟨c, hc, a, σ, ha, hfree, rfl⟩ | ⟨σ, hσ, hfree, rfl⟩ |
      ⟨σ, hσ, hfree, rfl⟩
  · refine ⟨c, hc, a, σ, ha, ?_, ?_, ?_, hfree, rfl⟩
    · zuhbw
      exact hns (Or.inl (Or.inr ⟨c, hc, a, σ, ha, hn, hfree, rfl⟩))
    · zunq
      zune
      exact hns ztzcl
    · zunq
      zune
      exact hns ztbaey
  · exact absurd ztzcl hns
  · exact absurd ztbaey hns

/-- **Every non-stop chord at the next key is found** from the label set, the gap regions, or
the chord of `S₂` containing a stop chord at the key. -/
theorem nonstop_found (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {oK : ℝ} {Λ : Set ztf}
    (hLK : (Lst J : ℝ) ≤ oK) (hInv : EvInv J S₂ oK Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hoK : oK < oW J ztkm)
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ ztxrc)
    {e : Set Point} (he : e ∈ F₂plus J S₂) (heK : SideAttach (chainModel J.whole).W e pK tK)
    (hns : ¬ StopChord2 J S₂ e) :
    ∃ c ∈ S₂, ∃ (a : Point) (σ : ℝ), ztxel ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ ∧
      ((∃ V ∈ (chainModel J.right).regions S₂, ztgev ∧
          Chazelle.Chain.TouchesIn (chainModel J.right).D c V) ∨
        (∃ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s pK tK ∧ StopChord2 J S₂ s ∧
          s ⊆ c)) := by
  zuhxo

  have hNTV : NoTieV J S₂ := noTieV hP hS₂a
  have hLt : (Lst J : ℝ) < oW J ztkm := by_linarith
  obtain ⟨c, hc, a, σ, ha, haR, hav, hat, hfree, rfl⟩ := nonstop_cases hS₂a he hns
  have hsub := shoot_sub_end hS₂a hc ha
  rcases det_of_evInv hP hS₂ hF hLK hInv hpK htK0 htK1 hoK hgap he heK with
    ⟨s, hs, hsK, hss⟩ | ⟨h, hh, hhK, a', σ', c', V, hc', hV, hVΛ, hT, ha', ha'R, ha'v, ha't,
      hfree', rfl⟩
  · -- a stop chord at the key: it is the other piece of `c`
    have hne : Merge.shoot J.whole a σ ≠ s := fun h' => hns (h' ▸ hss)
    have hpar := partner_of_parent hP hS₂a hS₂f hNTV he hs hne hc hsub heK hsK hLt
    refine ⟨c, hc, a, σ, ha, haR, hav, hat, hfree, rfl, Or.inr ⟨s, hs, hsK, hss, ?_⟩⟩
    rcases hpar with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact shoot_sub_end hS₂a hc ztwzn
    · exact shoot_sub_end hS₂a hc ztxch
  · by_cases hhe : Merge.shoot J.whole a' σ' = Merge.shoot J.whole a σ
    · grind
    · -- the other piece of `c'`
      have hsub' := shoot_sub_end hS₂a hc' ha'
      have hpar := partner_of_parent hP hS₂a hS₂f hNTV hh he hhe hc' hsub' hhK heK hLt
      rcases hpar with ⟨hf₁, he₁⟩ | ⟨hf₁, he₁⟩
      · zujiw
        obtain ⟨c₂, hc₂, a₂, σ₂, ha₂, ha₂R, ha₂v, ha₂t, hfree₂, he₂⟩ :=
          nonstop_cases hS₂a (he₁ ▸ he) hns
        have hR : Merge.lend c' ∈ J.right.set := by
          zuhbw
          exact hns (Or.inl (Or.inr ⟨c', hc', _, 1, Or.inl ztrh, hn, hf₁, rfl⟩))
        have hv : Merge.lend c' ≠ J.shared := by
          zugog
          exact hns (Or.inl (Or.inl ztmpx))
        have ht : Merge.lend c' ≠ J.right.top := by
          zugof
          exact hns (Or.inr ztmpx)
        grind
      · zujiw
        have hR : Merge.rend c' ∈ J.right.set := by
          zuhbw
          exact hns (Or.inl (Or.inr ⟨c', hc', _, -1, Or.inr ztrh, hn, hf₁, rfl⟩))
        have hv : Merge.rend c' ≠ J.shared := by
          zugog
          exact hns (Or.inl (Or.inl ztluy))
        have ht : Merge.rend c' ≠ J.right.top := by
          zugof
          exact hns (Or.inr ztluy)
        grind

/-- The right stretch is not empty. -/
theorem Lst_pos (J : Merge.Junction) : (0 : ℝ) < Lst J := by
  zumay
  have h2 : ztdjs := rfl
  have : 0 < Lst J := by
    unfold Lst; zupcm; unfold rlen
    grind
  simp_all

/-- **The label rule at a key.**  From the invariant at `oL`, at the next key `K` (no cut in
between): if a chord at `K` is attached at offset `0` (a pocket), any label set; if some chord at
`K` is anchored, a label set containing the side labels of every anchored chord at `K`; otherwise
(bracket chords only) the old label set. -/
theorem evInv_step (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {oL : ℝ} {Λ : Set ztf}
    (hInv : EvInv J S₂ oL Λ) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J ztkm) (hoL : oL ≤ oW J ztkm)
    (hgap : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      ¬ (oL < oW J ztej ∧ oW J ztej < oW J ztkm))
    {Λ' : Set ztf}
    (hrule : (∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J ztej = 0) ∨
      ((∃ Z ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W Z pK tK ∧ ¬ EvBrk J Z) ∧
        ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
          EvSideLab J S₂ Λ' e) ∨
      ((∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → EvBrk J e) ∧ Λ' = Λ)) :
    EvInv J S₂ ztyrk Λ' := by
  zubfw

  by_cases hpock : ∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK ∧
      ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J ztej = 0
  · zudeh
    have hne : sidePt (chainModel J.whole).W pK tK ≠ sidePt (chainModel J.whole).W q s := by
      zuq
      zufkp
      have := Lst_pos J
      linarith
    exact evInv_pocket he heK hQ hne hLst hQ0 Λ'
  zujce
  rcases hrule with h | ⟨⟨Z, hZ, hZK, hZb⟩, hlab⟩ | ⟨hbr, rfl⟩
  · grind
  · zucuk

    exact evInv_anchor hP hS₂ hF (noTieV hP hS₂a) hpK htK0 htK1 hLst hZ hZK hZz hzL
      (fun e he heK q s hQ => hpock e he heK q s hQ)
      (fun e he heK hnb _ => hlab e he heK hnb)
  · refine evInv_mono hInv hoL fun e he q s hQ h1 h2 => ?_
    zudt
    · grind
    · obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hpK hQ.2.1 hQ.2.2.1 htK0 htK1 h2
      grind
end Step
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Map
variable (J : Merge.Junction)

/-- The first vertex of the walk of `C₁` read along the `C₁` part. -/
noncomputable def b₁ : ℕ := if Lst J < lOff J then 2 * J.left.m + 6 else 6 + tpos J.left J.m₁

/-- The number of steps of the walk of `C₁` read along the `C₁` part. -/
noncomputable def E₁ : ℕ := (chainModel J.whole).W.n - Lst J + lδ J

/-- The `C₁`-part offset (beyond `Lst`) of the `b₁`-offset `d`. -/
noncomputable def ψ (d : ℕ) : ℕ :=
  if 0 < lδ J ∧ lL1 J < d then (if d < lL1 J + lδ J then lL1 J else d - lδ J) else d

/-- The walk edge of `M` at the `C₁`-part offset of `d`. -/
noncomputable def mEdge (d : ℕ) : ℕ := ztzlz % (chainModel J.whole).W.n

/-- A `b₁`-offset `d` and parameter `t` of the walk of `C₁` with a counterpart on the `C₁` part,
whose point is not the shared vertex. -/
def MValid (d : ℕ) (t : ℝ) : Prop :=
  d < E₁ J ∧ ¬ ztrv ∧ ¬ ztbft ∧
    (t = 0 → sidePt (chainModel J.left).W ztwjw 0 ≠ J.shared)

/-! ## The cases -/
theorem vtx_tpos' (C : Chain) {k : ℕ} (hk : k ≤ C.m) :
    (chainModel C).W.vtx ztpuv = C.vertex k := by
  zukk
  zufwx
  zueqa
  have := walk_tour C k 0 by_omega
  zuhkd
  zubk
  zuhrg

  unfold Chazelle.Chain.sideE; simp_all
theorem Lst_rlen : Lst J = rlen J := rL1_add_rL2 J

/-- When `v` is the top of `C` it is the top of `C₁`, at the tour position `0` of `C₁`, and the left
correspondence has no gap. -/
theorem nvt_left (hP : J.P.Simple) (hv : ¬ VNotTop J) :
    tpos J.left J.m₁ = 0 ∧ lδ J = 0 ∧ lL1 J = 2 * J.m₁ ∧ lL2 J = 0 ∧ llen J = 2 * J.m₁ := by
  have htop := left_top_eq J hv
  zufd
  have hk : J.left.topIdx = J.m₁ := by
    have h1 : J.left.vertex J.left.topIdx = J.left.vertex J.m₁ := htop
    exact J.left.sideVertex_inj hP J.left.topIdx_le (by zvmxz) h1
  zudnh
  have hτ : ztsmo := by
    unfold tpos bS Chain.sideS
    rw [hk, hm1]
    split_ifs
    · simp
    · rw [show J.m₁ + 2 * J.m₁ - (2 * J.m₁ - J.m₁) = 2 * J.m₁ by omega, Nat.mod_self]
  zukhu
  zucz
  have hA : ztxzy := by
    zuezn
    have hτ0 := tpos_lt J.whole J.m₁
    zuivf
    zunc
    rcases vtop_cases J hv with h | h
    · rw [h, zero_add, Nat.mod_eq_of_lt (show 2 * J.m₂ < 2 * J.whole.m by omega)]
      omega
    simp_all
  refine ⟨hτ, ?_, ?_, ?_, ?_⟩
  · unfold lδ; simp_all
  · unfold lL1; simp_all
  · unfold lL2; simp_all
  · unfold llen; grind

/-- Case b: the box block of `M` precedes the left stretch. -/
theorem caseB_facts (hlt : Lst J < lOff J) :
    ¬ VNotTop J ∧ lOff J = Lst J + 7 ∧ tpos J.whole J.m₁ + 2 * J.m₂ = 2 * J.whole.m ∧
      Lst J = 2 * J.m₂ := by
  zunf
  zucz
  rw [Lst_rlen, lOff_eq] at *
  unfold rlen at *
  unfold VNotTop
  grind

/-- Case c: `v` is the top of `C` and the box block of `M` follows the left stretch. -/
theorem caseC_facts (hv : ¬ VNotTop J) (hle : ¬ Lst J < lOff J) :
    tpos J.whole J.m₁ = 0 ∧ lOff J = Lst J ∧ Lst J = 2 * J.m₂ := by
  zunf
  zucz
  zuivf
  zunc
  have hc := vtop_cases J hv
  rw [Lst_rlen, lOff_eq] at *
  unfold rlen at *
  grind

/-- The base of the left stretch is `gW + lOff`. -/
theorem gL_eq : (gW J + lOff J) % (chainModel J.whole).W.n = 6 + tpos J.whole ztbv := by
  zuhf
  zunf
  zudpt
  unfold gW lOff
  exact add_dOf by_omega by_omega

/-- The walk edge of the left stretch at `d` is the edge at offset `lOff + d`. -/
theorem left_edge_eq (d : ℕ) :
    ztwtl % (chainModel J.whole).W.n =
      (gW J + ztrsx) % (chainModel J.whole).W.n := by
  rw [← gL_eq J, ← add_assoc, Nat.mod_add_mod]
end Map
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section MapSound
variable {J : Merge.Junction}
theorem mEdge_def (d : ℕ) :
    mEdge J d = ztzlz % (chainModel J.whole).W.n := rfl
theorem oW_def (x : ℝ) : oW J x = off (chainModel J.whole).W.n ((gW J : ℕ) : ℝ) x := rfl

/-- The point of `v` in the walk of `C₁` at its tour position. -/
theorem left_v_pt :
    sidePt (chainModel J.left).W ztgcv 0 = J.shared := by
  rw [Chazelle.Chain.sidePt_zero, vtx_tpos' J.left (k := J.m₁) (show J.m₁ ≤ J.left.m from le_refl _)]; rfl

/-- The points of the copies of the top of `C₁` (when `v` is the top of `C`). -/
theorem left_top_pts (hv : ¬ VNotTop J) :
    sidePt (chainModel J.left).W 6 0 = J.shared ∧
      sidePt (chainModel J.left).W ztjev 0 = J.shared := by
  obtain ⟨h1, h2⟩ := sidePt_top_copies J.left
  rw [left_top_eq J hv] at h1 h2
  simp_all

/-- `lδ = 0` forces `lL2 = 0`. -/
theorem lL2_of_lδ (h : lδ J = 0) : lL2 J = 0 := by
  unfold lδ lL2 at *; grind

/-- The left case G. -/
theorem left_G (h : 0 < lδ J) :
    lδ J = 7 ∧ lL1 J = 2 * J.m₁ - tpos J.left J.m₁ ∧ lL2 J = tpos J.left J.m₁ ∧
      0 < tpos J.left J.m₁ ∧ tpos J.left J.m₁ < 2 * J.m₁ := by
  have := tpos_lt J.left J.m₁
  zufd
  zvmxz at this
  unfold lδ lL1 lL2 at *
  grind

/-- **Soundness of the reading of the `C₁` part.** -/
theorem map_sound (hP : J.P.Simple) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ : ℝ}
    (hτ : 0 < τ) (hhit : J.whole.hitParam a σ = τ) {d : ℕ} {t : ℝ} (hv : MValid J d t)
    (hA : Sweep.Arrival (chainModel J.left).W ztiu σ
      ztwjw t) :
    SideAttach (chainModel J.whole).W ztxc ztbqk t ∧
      oW J ztbvj = (Lst J : ℝ) + ψ J d + t := by
  zuhf
  zucwn
  zucz
  zufd
  zubft

  zudzr

  obtain ⟨hdE, hgap, hsplit, hnv⟩ := hv
  -- the left stretch, at position `d'` (`dq d' = D`)
  have viaGen : ∀ d' : ℕ, d' < lL1 J + lL2 J → (t = 0 → d' ≠ 0 ∧ d' ≠ lL1 J) →
      zthm % (chainModel J.left).W.n =
        ztyan % (chainModel J.left).W.n →
      lOff J + d' = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W ztxc ztbqk t ∧
        oW J ztbvj = (Lst J : ℝ) + ψ J d + t := by
    intro d' hd' hsec he hoff
    zukuc
    obtain ⟨hS, hO⟩ := cut_of_genuine_gen J hP hσ hτ hhit hd' hsec hA
    have hE : ztxfi := by
      zuedo
    zuwx

    have : ((lOff J + d' : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := by rw [hoff]
    grind
  -- the split vertex
  have viaSplit : lL1 J < lL1 J + lL2 J → t = 0 →
      (zthm % (chainModel J.left).W.n = 6 ∨
        zthm % (chainModel J.left).W.n = 2 * J.left.m + 6) →
      lOff J + lL1 J = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W ztxc ztbqk t ∧
        oW J ztbvj = (Lst J : ℝ) + ψ J d + t := by
    intro hlt ht hk hoff
    zucfb
    have hS := attach_split_of_arrival J hP hlt hσ hτ hk hA
    have hshoot : Merge.shoot J.whole a σ = Chazelle.segment a ztiu := by
      unfold Merge.shoot; grind
    have hE : mEdge J d = (6 + tpos J.whole ztbv + lL1 J) %
        (chainModel J.whole).W.n := by
      zuedo
    rw [hE, hshoot]
    refine ztonx
    rw [oW_def, show ((gW J : ℕ) : ℝ) = ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) from rfl,
      off_left_gen J (by zuooo; omega) le_rfl one_pos]
    have : ((lOff J + lL1 J : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := by rw [hoff]
    grind
  -- the box block of `C`
  have viaBox : ∀ d'' : ℕ, (hv' : ¬ VNotTop J) → d'' < 7 → (t = 0 → 1 ≤ d'') →
      zthm % (chainModel J.left).W.n = ztnfb % (chainModel J.left).W.n →
      gW J + ztffn = 2 * J.whole.m + 6 + d'' →
      2 * J.whole.m - tpos J.whole J.m₁ + d'' = Lst J + ψ J d →
      SideAttach (chainModel J.whole).W ztxc ztbqk t ∧
        oW J ztbvj = (Lst J : ℝ) + ψ J d + t := by
    intro d'' hv' hd'' hsec he hidx hoff
    zukuc
    obtain ⟨hS, hO⟩ := cut_of_genuine_box J hv' hσ hτ hhit hd'' hsec hA
    have hE : ztgay := by
      zukxi
    zuwx

    have : ((2 * J.whole.m - tpos J.whole J.m₁ + d'' : ℕ) : ℝ) = ((Lst J + ψ J d : ℕ) : ℝ) := by
      zumnw
    grind
  zueod
  · -- case a: the left stretch fills the `C₁` part
    zubqt
    have hlen : ztckb := by
      zubyk
    zuom

    zubux
    zuhln
    zuirq
    · zucwt
      refine viaGen d by_omega (fun ht => ⟨fun hd0 => ?_, by_omega⟩) ?_ by_omega
      · zuhbf
        rw [hd0, add_zero, Nat.mod_eq_of_lt by_omega]
        exact left_v_pt
      · zuiqb
    · zueoi
      · have := lL2_of_lδ hδ; omega
      · zubkq

        by_cases hd1 : d = lL1 J
        · zukfz
          refine viaSplit by_omega ht ztgej ?_
          · rw [hd1, hl1, hn₁, hm1, Nat.mod_eq_of_lt by_omega]; omega
          · have hψ : ψ J d = lL1 J := by unfold ψ; grind
            omega
        · have hd2 : ztrgt := by
            omega
          have hψ : ztpqz := by
            unfold ψ; rw [ite_eq_left ⟨hδ', by_omega⟩, ite_eq_right by_omega, h7]
          by_cases hs : d = lL1 J + 7 ∧ t = 0
          · refine viaSplit by_omega hs.2 ztenp ?_
            · rw [hs.1, hl1, hn₁, hm1]
              rw [show 6 + tpos J.left J.m₁ + ztdki =
                6 + ztgcb by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
            omega
          · refine viaGen ztfqv by_omega (fun ht => ⟨by_omega, fun h => hs ⟨by_omega, ht⟩⟩)
              ?_ by_omega
            zucre
  · -- `v` is the top of `C`: no gap, `ψ = id`
    zuot
    have hψ : ztguy := by unfold ψ; zvmyd
    obtain ⟨hp6, hp26⟩ := left_top_pts hVNT
    zucfl
    · zuhh

      zubux
      zuhln
      zujte
      · refine viaBox d hVNT hd7 ztefc ztgft ztkty
          by_omega
        zuccr
        zuhbf
        rw [show d = 0 by omega, add_zero, Nat.mod_eq_of_lt by_omega]
        omega
      · refine viaGen ztfqv by_omega ztjvw ?_
          by_omega
        · zuhbf
          rw [hn₁, show 2 * J.left.m + 6 + d = 6 + ztcsh by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt by_omega]
          omega
        · zufqc
          rw [show 2 * J.left.m + 6 + d = ztzbh + ztcsh by omega,
            Nat.add_mod_right]
    · zuhz

      zubux
      rw [hb, hτ0] at hA hnv viaGen viaSplit
      zuhsz
      · refine viaGen d by_omega ztjvw ?_ by_omega
        · zuhbf
          rw [h0, Nat.mod_eq_of_lt by_omega]
          omega
        · zudcm
      · refine viaBox ztqkx hVNT by_omega ztefc ?_ ?_ ?_
        · zuccr
          zuhbf
          rw [show 6 + 0 + d = 2 * J.left.m + 6 by omega, Nat.mod_eq_of_lt by_omega]
          omega
        · zukto
          zucr
          omega
        · rw [hψ]; unfold gW; omega
        omega
end MapSound
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section MapComplete
variable {J : Merge.Junction}

/-- **Completeness of the reading of the `C₁` part.** -/
theorem map_complete (hP : J.P.Simple) {a : Point} (ha₁ : a.2 ≤ J.left.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : FreeAt J.whole a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W ztxc p t)
    (hend : sidePt (chainModel J.whole).W p t = rayPt a σ zton)
    (hoff : (Lst J : ℝ) < oW J ztk) (hnv : sidePt (chainModel J.whole).W p t ≠ J.shared) :
    Genuine J.left a σ zton ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
      Sweep.Arrival (chainModel J.left).W ztwqt σ
        ztwjw t := by
  zumh
  zuerx
  zucz
  zufd
  zubft

  have hτw' := tpos_lt J.whole ztbv
  zuerz
  zudzr

  zucwh
  zufae
  have hD := dOf_lt (show 0 < (chainModel J.whole).W.n by omega) ztead p
  zudoy
  rw [hoW] at hoff
  have hDL : ztull := by
    zumv
    have : (D : ℝ) + 1 ≤ Lst J := by exact_mod_cast by_simp_all
    linarith
  have hpD : p = (gW J + (Lst J + zthqv)) % (chainModel J.whole).W.n := by
    rw [show Lst J + zthqv = D by omega, hDdef, add_dOf hg hp]
  set r := D - Lst J with hr
  -- the left stretch
  have viaLeft : ∀ r' : ℕ, r' < llen J → p = (6 + tpos J.whole ztbv + r') %
      (chainModel J.whole).W.n → (t = 0 → r' ≠ 0 ∧ r' ≠ lL1 J) →
      ∀ d, zthm % (chainModel J.left).W.n =
        (6 + tpos J.left J.m₁ + dq ztdov ztety r') % (chainModel J.left).W.n →
      MValid J d t → mEdge J d = p →
      Genuine J.left a σ zton ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Sweep.Arrival (chainModel J.left).W ztwqt σ
          ztwjw t := by
    intro r' hr' hp' hsec d hd hvd hmd
    zujjs
    obtain ⟨hg', hArr⟩ := genuine_of_attach J hP ha₁ hσ hfree (by zuogn; omega)
      hsec hA hend
    exact ztlwh
  -- the box block of `C`
  have viaBox : ∀ (hv : ¬ VNotTop J) (r'' : ℕ), r'' < 7 →
      p = (2 * J.whole.m + 6 + r'') % (chainModel J.whole).W.n → (t = 0 → 1 ≤ r'') →
      ∀ d, zthm % (chainModel J.left).W.n =
        (2 * J.left.m + 6 + r'') % (chainModel J.left).W.n →
      MValid J d t → mEdge J d = p →
      Genuine J.left a σ zton ∧ ∃ d, MValid J d t ∧ mEdge J d = p ∧
        Sweep.Arrival (chainModel J.left).W ztwqt σ
          ztwjw t := by
    intro hv r'' hr'' hp' hsec d hd hvd hmd
    zujjs
    obtain ⟨hg', hArr⟩ := genuine_of_attach_box J hP hv ha₁ hσ hfree hr'' hsec hA hend
    exact ztlwh
  -- the point of the arrival position is the point of `p`
  have hpt₁ : ∀ e₁, Sweep.Arrival (chainModel J.left).W ztwqt σ e₁ t →
      sidePt (chainModel J.left).W e₁ t ≠ J.shared := by
    intro e₁ hArr h
    rw [hArr.2.2.2.1, ← hend] at h
    grind
  have hvM : sidePt (chainModel J.whole).W ztxfw 0 = J.shared := by
    have := start_pt J hP
    rwa [add_zero, Nat.mod_eq_of_lt by_omega] at this
  zueod
  · zubqt
    have hlen : ztckb := by
      zubyk
    zuom

    have hrl : r < llen J := by_omega
    have hpL : ztxiy := by
      rw [left_edge_eq, hlOff]; omega
    by_cases hsp : t = 0 ∧ r = lL1 J ∧ lL1 J < llen J
    · -- the split vertex
      obtain ⟨ht, hrl1, hlt⟩ := hsp
      have hδ : zthoc := by
        by_contra h; have := lL2_of_lδ (J := J) by_omega; omega
      zueau
      have htop : sidePt (chainModel J.whole).W p t = J.left.top := by
        rw [hpL, hrl1, ht]
        exact sidePt_splitL0 J hP ztzi finite_empty by_omega
      obtain ⟨hgen, hA1, hA2⟩ := genuine_of_split J hP ha₁ hσ hfree by_grind
      obtain ⟨hp6, hp26⟩ := sidePt_top_copies J.left
      have hψ1 : ψ J ztdov = lL1 J := by unfold ψ; simp
      have hψ2 : ψ J ztrsv = lL1 J := by
        unfold ψ; rw [ite_eq_left by_omega, ite_eq_right by_omega, h7]; omega
      have hvtop : J.left.top ≠ J.shared := by_grind
      zukmy
      · refine ⟨hgen, lL1 J, ⟨by_omega, by_omega, by_grind, fun _ => ?_⟩, ?_, ?_⟩
        · rw [hb, hl1, hn₁, hm1, Nat.mod_eq_of_lt by_omega,
            show 6 + tpos J.left J.m₁ + ztgyg = 2 * J.left.m + 6 by omega,
            hp26]
          omega
        · rw [mEdge_def, hψ1, hpD, hrl1]
        · rw [hb, hl1, hn₁, hm1, Nat.mod_eq_of_lt by_omega,
            show 6 + tpos J.left J.m₁ + ztgyg = 2 * J.left.m + 6 by omega,
            ht]
          grind
      · refine ⟨hgen, lL1 J + 7, ⟨by_omega, by_omega, by_omega, fun _ => ?_⟩, ?_, ?_⟩
        · have e6 : (b₁ J + ztrsv) % (chainModel J.left).W.n = 6 := by
            rw [hb, hl1, hn₁, hm1, show 6 + tpos J.left J.m₁ + ztdki =
              6 + ztgcb by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
          grind
        · rw [mEdge_def, hψ2, hpD, hrl1]
        · rw [hb, hl1, hn₁, hm1, show 6 + tpos J.left J.m₁ + ztdki =
            6 + ztgcb by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega, ht]
          grind
    · have hsec : ztknp := by
        zuibv
        refine ⟨fun h0 => hnv ?_, by_grind⟩
        zubsm

      -- the position `dq r` of the walk of `C₁`
      have hdq : dq ztdov ztety r < E₁ J := by
        rw [hE₁]; unfold dq; split_ifs <;> omega
      have hψ : ψ J (dq ztdov ztety r) = r := by
        unfold ψ dq
        by_cases hr1 : r < lL1 J
        · grind
        · rw [ite_eq_right hr1]
          zueoi
          · zujkg
          · rw [ite_eq_left by_omega, ite_eq_right by_omega]; omega
      refine viaLeft r hrl hpL hsec _ ztgft ⟨hdq, ?_, ?_, ?_⟩ ?_
      · zugip
      · zugip
      · zuhgq
        have hArr := (genuine_of_attach J hP ha₁ hσ hfree by_omega hsec
          by_grind by_grind).2
        zujmd
        zudgt
      · zubem
  · zuot
    have hψ : ∀ d, ψ J d = d := fun d => by unfold ψ; zvmyd
    have htopC : sidePt (chainModel J.whole).W ztjew 0 = J.shared := by
      rw [(sidePt_top_copies J.whole).2, shared_eq_top J hVNT]
    have hsplit : ∀ d, ¬ ztbft := by_grind
    have hgap : ∀ d, ¬ ztrv := by_grind
    zucfl
    · zuhh

      zukfg
      by_cases hr7 : r < 7
      · have hpB : p = (2 * J.whole.m + 6 + r) % (chainModel J.whole).W.n := by
          zufnp
        have hsec : t = 0 → 1 ≤ r := by
          zujbc

          rw [hpB, ht, show r = 0 by omega, add_zero, Nat.mod_eq_of_lt by_omega]
          omega
        refine viaBox hVNT r hr7 hpB hsec r ztgft ztfvy ?_
        · zuhgq
          have hArr := (genuine_of_attach_box J hP hVNT ha₁ hσ hfree hr7 hsec by_grind
            by_grind).2
          zujmd
          zudgt
        · zubem
      · have hpL : p = (6 + tpos J.whole ztbv + ztkdf) % (chainModel J.whole).W.n := by
          zuobs; congr 1; omega
        have hsec : t = 0 → r - 7 ≠ 0 ∧ r - 7 ≠ lL1 J := by
          zuibv
          refine ztonm
          zubsm

        refine viaLeft _ by_omega hpL hsec r ?_ ztfvy ?_
        · zuenv
          rw [show 2 * J.left.m + 6 + r = ztzbi + ztcsh by omega,
            Nat.add_mod_right]
        · zuhgq
          have hArr := (genuine_of_attach J hP ha₁ hσ hfree
            by_omega hsec by_grind by_grind).2
          have e : (6 + tpos J.left J.m₁ + dq ztdov ztety ztkdf) %
              (chainModel J.left).W.n = ztlka % (chainModel J.left).W.n := by
            zuenv
            rw [show 2 * J.left.m + 6 + r = ztzbi + ztcsh by omega,
              Nat.add_mod_right]
          zukrc
          zudgt
        · zubem
    · zuhz

      zukfg
      by_cases hr2 : r < 2 * J.m₁
      · have hpL : ztxiy := by
          zuobs
        have hsec : ztknp := by
          zuibv
          refine ztonm
          zubsm

        refine viaLeft r by_omega hpL hsec r ?_ ztfvy ?_
        · zuham
        · zuhgq
          have hArr := (genuine_of_attach J hP ha₁ hσ hfree
            by_omega hsec by_grind by_grind).2
          have e : (6 + tpos J.left J.m₁ + dq ztdov ztety r) % (chainModel J.left).W.n =
              ztlka % (chainModel J.left).W.n := by
            zuham
          zukrc
          zudgt
        · zubem
      · have hpB : p = (2 * J.whole.m + 6 + ztqva) % (chainModel J.whole).W.n := by
          zufnp
        have hsec : t = 0 → 1 ≤ r - 2 * J.m₁ := by
          zujbc

          rw [hpB, ht, show r - 2 * J.m₁ = 0 by omega, add_zero, Nat.mod_eq_of_lt by_omega]
          omega
        have e : ztlka % (chainModel J.left).W.n =
            (2 * J.left.m + 6 + ztqva) % (chainModel J.left).W.n := by
          rw [hb, hτ0]; congr 1; omega
        refine viaBox hVNT _ by_omega hpB hsec r e
          ⟨by_omega, hgap r, hsplit r, ?_⟩ ?_
        · zuhgq
          have hArr := (genuine_of_attach_box J hP hVNT ha₁ hσ hfree by_omega hsec by_grind
            by_grind).2
          zvmyr at hArr
          zudgt
        · zubem
end MapComplete
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
variable {J : Merge.Junction}

/-- **The chord of `C₂` seen from an end** of an augmented chord `c`, along `c`: the direction is
free and the first hit is the far end (at distance the length of `c`). -/
theorem right_hit_end {c : Set Point} (hc : c ∈ Merge.augChords J.right) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm) :
    FreeAt J.right a σ ∧ a.2 ≤ J.right.top.2 ∧
      0 < (Merge.rend c).1 - (Merge.lend c).1 ∧
      J.right.hitParam a σ = (Merge.rend c).1 - (Merge.lend c).1 ∧
      (Merge.lend c).2 = a.2 ∧ (Merge.rend c).2 = a.2 := by
  zubrv

  zubwk
  zuht
  · zudug
    refine ⟨Merge.freeAt_of_isHChordIn_left _ hH, hy, by_simp_all, ?_, rfl, rfl⟩
    refine J.right.hitParam_eq_of_first _ 1 by_simp_all ?_ fun s hs1 hs2 => ?_
    · have : rayPt (ztetv : Point) 1 ztbju = (ztevf : Point) := by
        zubzy
      zubi
      zvmwk; exact hH.right_not
    · have e : rayPt (ztetv : Point) 1 s = ((l + s, y) : Point) := by zvmxf
      zui
      exact hH.open_mem _ by_linarith by_grind
  · zubim
    refine ⟨Merge.freeAt_of_isHChordIn_right _ hH, hy, by_simp_all, ?_, rfl, rfl⟩
    refine J.right.hitParam_eq_of_first _ (-1) by_simp_all ?_ fun s hs1 hs2 => ?_
    · have : rayPt (ztevf : Point) (-1) ztbju = (ztetv : Point) := by
        zubiu
      zubi
      zvmwk; exact hH.left_not
    · have e : rayPt (ztevf : Point) (-1) s = ((r - s, y) : Point) := by
        zubvf
      zui
      exact hH.open_mem _ by_grind by_linarith

/-- A point of `C₂` other than the shared vertex is off `C₁`. -/
theorem not_mem_left_of_right (hP : J.P.Simple) {a : Point} (ha : a ∈ J.right.set)
    (hv : a ≠ J.shared) : a ∉ J.left.set := fun h => hv (by
  have : a ∈ J.left.set ∩ J.right.set := ⟨h, ha⟩
  zuigq
  simp_all)

/-- **The direction along a chord of `C₂` from an end on `C₂`** (not the shared vertex) is free for
`C`. -/
theorem whole_free_end (hP : J.P.Simple) {a : Point} (ha : a ∈ J.right.set) (hv : a ≠ J.shared)
    {σ : ℝ} (hfree : FreeAt J.right a σ) : FreeAt J.whole a σ := by
  have haw : ztlal :=
    J.whole.snd_le_top_of_mem_set ztuzf
  have ha₂ : a.2 ≤ J.right.top.2 := J.right.snd_le_top_of_mem_set ha
  rw [freeAt_whole_iff J haw]
  have hR₂ : ztpkl := rfl
  have hR₁ : J.left.radius = J.whole.radius := rfl
  have hleft : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), rayPt a σ t ∉ J.left.set := by
    zufrp
    · have haD : a ∈ J.left.dom := by
        zuhbw
        rcases (Merge.not_mem_dom_iff J.left h₁).1 hn with hb | hs
        · rw [hR₁, ← hR₂] at hb; exact hb (J.right.set_subset_box ha)
        · exact not_mem_left_of_right hP ha hv hs
      filter_upwards [Merge.freeAt_of_mem_dom J.left haD σ] with t ht
      zumgt
      exact J.left.not_mem_set_of_mem_dom ht hs
    · zujcf
      exact Filter.Eventually.of_forall fun t hs => by
        have := J.left.snd_le_top_of_mem_set hs
        zueze

  filter_upwards [hfree, hleft] with t ht hl
  have h2 : (rayPt a σ t).2 ≤ J.right.top.2 := by_simp_all
  have hnd := (Merge.not_mem_dom_iff J.right h2)
  simp_all
variable {a : Point}
/-- **The first hit of `C`** when the genuine hit of `C₁` comes strictly before that of `C₂`. -/
theorem whole_hit_lt (ha₁ : a.2 ≤ J.left.top.2) (ha₂ : a.2 ≤ J.right.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < J.right.hitParam a σ) : J.whole.hitParam a σ = τ := by
  have haw : ztlal := le_trans ha₁ J.left_top_le
  rw [whole_hitParam_eq_min J haw hσ, left_hitParam_eq J ha₁, right_hitParam_eq J ha₂]
  rw [((genuine_iff J.left ha₁ hσ).1 hg).2]
  grind

/-- **The first hit of `C`** when that of `C₂` is not later than that of `C₁` (or `a` is above
the top of `C₁`). -/
theorem whole_hit_right (ha₂ : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : a.2 ≤ J.left.top.2 → J.right.hitParam a σ ≤ J.left.hitParam a σ)
    (hbox : J.right.hitParam a σ ≤ Merge.rayHit J.whole.radius ∅ a σ) :
    J.whole.hitParam a σ = J.right.hitParam a σ := by
  have haw : ztlal := le_trans ha₂ J.right_top_le
  rw [whole_hitParam_eq_min J haw hσ, right_hitParam_eq J ha₂]
  apply min_eq_right
  zufrp
  · zuoog; simp_all
  · zujcf
    rw [rayHit_eq_empty_of_above J.left h₁]
    omega

/-- **The chord seen from an end of a chord of `S₂`** belongs to `F₂⁺`. -/
theorem shoot_end_mem {S₂ : Set ztf} {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm) (hfree : FreeAt J.whole a σ) :
    Merge.shoot J.whole a σ ∈ F₂plus J S₂ := by
  zuht
  · exact Or.inl (Or.inl (Or.inl ztonb))
  · exact Or.inl (Or.inl (Or.inr ztonb))
theorem lerp_rayPt (a : Point) (σ τ s : ℝ) : lerp a ztiu s = rayPt a σ (s * τ) := by
  zubjw
  · zuhpd
  simp

/-- **Soundness of a candidate.**  The hit `rayPt a σ τ` of `C₁`, genuine and strictly before the
far end of `c`, arriving at the `b₁`-offset `d` of the walk of `C₁` (a valid offset): the chord of
`C` seen from `a` belongs to `F₂⁺`, ends there, and is attached at `(mEdge d, t)`, on the `C₁`
part. -/
theorem cand_sound (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm) (haR : a ∈ J.right.set)
    (hv : a ≠ J.shared) (ha₁ : a.2 ≤ J.left.top.2) {τ : ℝ} (hg : Genuine J.left a σ τ)
    (hlt : τ < (Merge.rend c).1 - (Merge.lend c).1) {d : ℕ} {t : ℝ}
    (hMV : d < E₁ J ∧ ¬ ztrv ∧
      ¬ ztbft)
    (hA : Arrival (chainModel J.left).W ztiu σ ztwjw t) :
    FreeAt J.whole a σ ∧ J.whole.hitParam a σ = τ ∧ Merge.shoot J.whole a σ ∈ F₂plus J S₂ ∧
      SideAttach (chainModel J.whole).W ztxc ztbqk t ∧
      sidePt (chainModel J.whole).W ztbqk t = rayPt a σ τ ∧
      oW J ztbvj = (Lst J : ℝ) + ψ J d + t := by
  zune
  obtain ⟨hfr, ha₂, hlen, hR, -, -⟩ := right_hit_end ztbac ha
  have hfree := whole_free_end hP haR hv hfr
  have hτ : ztrzs := hg.1
  have hhit : J.whole.hitParam a σ = τ := whole_hit_lt ha₁ ha₂ hσ hg by_simp_all
  -- the hit point is in the open chord `c`, hence not the shared vertex
  have hwD : rayPt a σ τ ∈ J.right.dom := by
    obtain ⟨-, -, hdom⟩ := Merge.hit_of_freeAt J.right ha₂ hσ hfr
    simp_all
  have hwv : rayPt a σ τ ≠ J.shared := fun h =>
    J.right.not_mem_set_of_mem_dom hwD (by zvmwc; exact J.shared_mem_right)
  have hMV' : ztult := ⟨hMV.1, hMV.2.1, hMV.2.2, fun ht => by
    have hpt : sidePt (chainModel J.left).W ztwjw t =
        rayPt a σ τ := hA.2.2.2.1
    simp_all⟩
  obtain ⟨hS, hO⟩ := map_sound hP hσ hτ hhit hMV' hA
  zugb
  have hpt : sidePt (chainModel J.whole).W ztbqk t = rayPt a σ τ := by
    have hmem : sidePt (chainModel J.whole).W ztbqk t ∈
        Chazelle.segment a ztiu := by
      have := hS.2.2.2.1
      unfold Merge.shoot at this; simp_all
    have hnd : sidePt (chainModel J.whole).W ztbqk t ∉ J.whole.dom :=
      hM.trace _ hS.1 t hS.2.1 hS.2.2.1.le
    refine seg_end hmem hnd ztjwm ztep
    · zugwa
      obtain ⟨-, -, hdom⟩ := Merge.hit_of_freeAt J.whole
        ztoct hσ hfree
      exact hdom _ ztttt (by rw [hhit]; nlinarith [hs.2])
    · have := off_right_pt J hP hS₂ hS₂f hS.1 hS.2.1 hS.2.2.1 by_simp_all
        by_simp_all
      have h2 : oW J ztbvj < Lst J := by
        unfold oW gW; exact_mod_cast this.2
      rw [hO] at h2
      zujvt
      linarith [hS.2.1]
  exact ⟨hfree, hhit, shoot_end_mem hc ha hfree, hS, hpt, hO⟩
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed
namespace Sweep
section EdgeCorr
variable {J : Merge.Junction}

/-- **The walk edges agree** at a valid offset with a positive parameter. -/
theorem edge_corr (hP : J.P.Simple) {d : ℕ} {t : ℝ} (hv : MValid J d t) (htp : 0 < t) (s : ℝ) :
    sidePt (chainModel J.whole).W ztbqk s =
      sidePt (chainModel J.left).W ztwjw s := by
  zuhf
  zucwn
  zucz
  zufd
  zubft

  obtain ⟨hdE, hgap, hsplit, -⟩ := hv
  have ht0 : ztmwx := htp.ne'
  have viaGen : ∀ d' : ℕ, d' < lL1 J + lL2 J →
      zthm % (chainModel J.left).W.n =
        ztyan % (chainModel J.left).W.n →
      lOff J + d' = Lst J + ψ J d →
      sidePt (chainModel J.whole).W ztbqk s =
        sidePt (chainModel J.left).W ztwjw s := by
    intro d' hd' he hoff
    have hE : ztxfi := by
      zuedo
    zuksi
    exact (corr_left0 J hP (S₁ := ∅) ztzi finite_empty).sidePt_eq hd' s
  have viaBox : ∀ d'' : ℕ, (hv' : ¬ VNotTop J) → d'' < 7 →
      zthm % (chainModel J.left).W.n = ztnfb % (chainModel J.left).W.n →
      gW J + ztffn = 2 * J.whole.m + 6 + d'' →
      sidePt (chainModel J.whole).W ztbqk s =
        sidePt (chainModel J.left).W ztwjw s := by
    intro d'' hv' hd'' he hidx
    have hE : ztgay := by
      zukxi
    zuksi
    exact (box_agree J hv').sidePt_eq hd'' s
  zueod
  · zubqt
    have hlen : ztckb := by
      zubyk
    zuom

    zubux
    zujiq
    zuirq
    · zucwt
      zukns
      zuiqb
    · zueoi
      · have := lL2_of_lδ hδ; omega
      · zubkq

        have hd1 : d ≠ lL1 J := fun hd1 => hsplit ⟨by_omega, hd1, ht0⟩
        have hd2 : ztrgt := by
          omega
        have hψ : ztpqz := by
          zudwk
        zuknt
        zucre
  · zuot
    zucwt
    zucfl
    · zuhh

      zubux
      zujiq
      zujte
      · have := viaBox d hVNT hd7 ztgft ztkty
        simp_all
      · zuknt
        zufqc
        rw [show 2 * J.left.m + 6 + d = ztzbh + ztcsh by omega,
          Nat.add_mod_right]
    · zuhz

      zubux
      rw [hb, hτ0] at viaGen ⊢
      zuhsz
      · zukns
        zudcm
      · have := viaBox ztqkx hVNT by_omega (by
          zukto
          zucr
          omega) (by rw [hψ]; unfold gW; omega)
        simp_all

/-- **A height code has the same parameter** in `M` at `mEdge d` and in `M₁` at `(b₁ + d) % n₁`
(valid offset, positive parameter). -/
theorem param_corr (hP : J.P.Simple) {d : ℕ} {t : ℝ} (hv : MValid J d t) (htp : 0 < t)
    (Q : Polygon) (h : ℕ) :
    (chainModel J.whole).param Q ⟨mEdge J d, h⟩ =
      (chainModel J.left).param Q ⟨zthm % (chainModel J.left).W.n, h⟩ := by
  have e0 := edge_corr hP hv htp 0
  have e1 := edge_corr hP hv htp 1
  simp only [Chazelle.Chain.sidePt_zero] at e0
  have hwa : (chainModel J.whole).wa ztbqk =
      (chainModel J.left).wa ztwjw := e0
  have hwb : (chainModel J.whole).wb ztbqk =
      (chainModel J.left).wb ztwjw := by
    zumrf
    zumlv
    unfold Chazelle.Chain.sidePt at e1
    simp_all
  zufde
  simp_all
end EdgeCorr
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed
namespace Sweep
section Ends
def endPos (N : NF) (k s : ℕ) : WPos := if s = 0 then (N.chord k).lpos else (N.chord k).rpos

/-- The far end of the end `s` of chord `k`. -/
def farEnd (N : NF) (k s : ℕ) : WPos := if s = 0 then (N.chord k).rpos else (N.chord k).lpos

/-- **The ends of a chord record are the ends of its chord.** -/
theorem rec_ends {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF ztc Q N) {k : ℕ}
    (hk : k < N.nChords) :
    ∃ y a b : ℝ, a < b ∧ (N.chord k).toSet ztc Q = Visibility.hseg y a b ∧
      (chainModel C).pos Q (N.chord k).lpos = ztdv ∧ (chainModel C).pos Q (N.chord k).rpos = ztdy ∧
      (Q.vtx (N.chord k).h).2 = y := by
  have hmem : ztxcx := by
    zuno

  obtain ⟨y, a, b, hH, -, heq, -, -⟩ := Merge.augChords_spec ztglw
  obtain ⟨h1, h2, h3⟩ := rec_pos_ends zttmn heq hH.lt
  exact ⟨y, a, b, hH.lt, heq, h1, h2, h3⟩
theorem endOrigin_eq (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N) {j : ℕ} (hj : j < 2 * N.nChords) :
    endOrigin J Q N j = (chainModel J.right).pos Q (endPos N ztwm ztfsu) ∧
      (endDir j = 1 ↔ j % 2 = 0) := by
  zucij
  unfold endOrigin endDir endPos
  zudab
  zudww
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, Merge.lend_hseg hab.le, hl]; simp_all
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, Merge.rend_hseg hab.le, hr]
    grind

/-- The far end of an end is the other end of the chord. -/
theorem farOrigin_eq (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF ztj Q N) {j : ℕ} (hj : j < 2 * N.nChords) :
    (if j % 2 = 0 then Merge.rend ztwqa
      else Merge.lend ztwqa) =
      (chainModel J.right).pos Q (farEnd N ztwm ztfsu) := by
  zucij
  unfold farEnd
  zudab
  zudww
  · rw [ite_eq_left h, ite_eq_left h, Merge.rend_hseg hab.le, hr]
  · rw [ite_eq_right h, ite_eq_right h, Merge.lend_hseg hab.le, hl]
end Ends
section Classify
variable (C : Chain)

/-- **A position of a chain model lies on the chain** iff it is a tour position, or the last copy of
the top (normalised height code `0`). -/
theorem pos_mem_set_iff (_hP : C.P.Simple) {Q : Polygon} {x : WPos}
    (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) (hnorm : x.hgt = 0 ↔ (chainModel C).param Q x = 0) :
    (chainModel C).pos Q x ∈ C.set ↔
      (6 ≤ x.edge ∧ x.edge ≤ 2 * C.m + 5) ∨ (x.edge = 2 * C.m + 6 ∧ x.hgt = 0) := by
  zukk
  show sidePt (chainModel C).W x.edge ztuy ∈ C.set ↔ _
  zucn
  rw [hW] at hx ⊢
  constructor
  · zujbb
    rcases C.sideWalk_pos_cases C.sideBeta hx h0 with hb | ⟨i, hi, he, hit⟩
    · exact absurd hm (C.sideWalk_box_pt C.sideBeta hb h0 h1).1
    grind
  · rintro (⟨h6, h5⟩ | ⟨he, h0'⟩)
    · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := (chainModel C).param Q x)
        by_omega ztpbm h0 h1
      simp_all
    · have := C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := (chainModel C).param Q x)
        le_rfl (fun _ => hnorm.1 h0') h0 h1
      simp_all

/-- **A tour vertex**: at height code `0` the position `e` is the vertex `sideIdx (e - 6)`. -/
theorem pos_vertex {Q : Polygon} {x : WPos} (h6 : 6 ≤ x.edge) (he : x.edge ≤ 2 * C.m + 6)
    (h0 : x.hgt = 0) :
    (chainModel C).pos Q x = C.vertex ztyop := by
  zuicg
  simp only at h6 he h0
  zubvi
  show sidePt (chainModel C).W e ztymr = _
  rw [show (chainModel C).param Q ztjy = 0 from rfl, Chazelle.Chain.sidePt_zero, cm_W,
    show e = ztbcs + 6 by omega, C.sideWalk_vtx_tour _ by_omega]
  rfl

/-- **Inside a tour edge** no position is a vertex of the chain. -/
theorem pos_ne_vertex (hP : C.P.Simple) {Q : Polygon} {x : WPos} (h6 : 6 ≤ x.edge)
    (he : x.edge ≤ 2 * C.m + 5) (h0 : 0 < (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) (k : ℕ) : (chainModel C).pos Q x ≠ C.vertex k := by
  zuicg
  simp only at h6 he
  show sidePt (chainModel C).W e ((chainModel C).param Q ztugj) ≠ _
  zugue
  obtain ⟨k', -, s, hs, hpt, -⟩ := C.sideTour_open C.sideBeta (i := e - 6) by_omega
    (t := (chainModel C).param Q ztugj) zteyi
  rw [show e - 6 + 6 = e by omega] at hpt
  zubil
  exact C.sideOpen_ne_vertex hP hs
