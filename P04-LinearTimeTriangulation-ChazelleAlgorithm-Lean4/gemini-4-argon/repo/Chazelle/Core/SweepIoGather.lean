module

public import Chazelle.Core.SweepIoLH
public import Chazelle.Core.RestoreTArcs
public import Chazelle.Core.RestoreTRead

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
    IRS P W c₀ (.whileLtN a b body) c (Φ c + 2) (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨K, c₁, k₁, e₁, hk₁, hI₁, hfr₁, hc₁, hΦ₁⟩ := hbody c hI hc ht hroom
      have hA₁ := hfr₁.2.2.2.2
      have hroom₁ : c₁.nreg ALLOC + Φ c₁ ≤ W := by omega
      obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := ih (Φ c₁) (by omega) hI₁ hc₁ hroom₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, by omega, hI',
        (hfr₁.trans hfr₂).mono (by omega), hq⟩
    · exact ⟨c, 2, .whileLtN_false ht hI.hw, by omega, hI, IFr.refl c 2, hc, ht⟩

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
  upd (upd (upd (upd m A v0) (A + 1) v1) (A + 2) v2) (A + 3) v3

theorem put4_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 4 ≤ W) :
    IRS P W c₀ put4 c 8 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem4 c.nmem (c.nreg ALLOC) (c.nreg gS) (c.nreg gS1) (c.nreg gE) (c.nreg gE1) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have hw := hI.hw
  have hroom' : c.nreg 9999 + 4 ≤ W := hroom
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 241016, .addN 9999 9999 240611,
      .storeN 9999 241017, .addN 9999 9999 240611, .storeN 9999 241018, .addN 9999 9999 240611,
      .storeN 9999 241019, .addN 9999 9999 240611]) c c' k ∧ k = 8 ∧
      c'.nreg 9999 = c.nreg 9999 + 4 ∧
      (∀ r, r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.nmem = mem4 c.nmem (c.nreg 9999) (c.nreg 241016) (c.nreg 241017) (c.nreg 241018)
        (c.nreg 241019) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp
      simp only [upd, ite_eq_right hr]
    · config_simp
      simp only [k1, mem4]
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := ex
  refine IRS.ofExec hI ex (by omega) (fun r _ hr => h2 r hr) h4 (fun a ha => ?_) h5 h6
    (by show c.nreg 9999 ≤ c'.nreg 9999; omega) (by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega)
    ⟨h1, h2, h3, h4, h5, h6⟩
  rw [h3]
  have h0 : c₀.nreg 9999 ≤ c.nreg 9999 := hI.hA
  have ha' : a < c₀.nreg 9999 := ha
  unfold mem4
  simp only [upd]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

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
  Bprim r || decide (50200 ≤ r ∧ r < 50210) || decide (r = ph) || decide (r = o) ||
    decide (r = o + 1)

theorem normS_wr (dsc pe ph o : ℕ) : SignK.wr (BnS ph o) (normS dsc pe ph o) = true := by
  have hoff : SignK.wr (BnS ph o) offCmp = true :=
    wr_mono wr_offCmp (fun r h => by simp [BnS, h])
  simp [normS, normBox, callOff, callP, cps, block, SignK.wr, SignK.wrOK, BnS, hoff]

/-- `normS` keeps the allocator and the memory. -/
theorem normS_exact {dsc pe ph o : ℕ} {Q : Config → Prop} {K : ℕ}
    (h : IRS P W c₀ (normS dsc pe ph o) c K Q) (ho : 240000 ≤ ph ∧ 240000 ≤ o) :
    IRS P W c₀ (normS dsc pe ph o) c K (fun c' => Q c' ∧ c'.nreg ALLOC = c.nreg ALLOC ∧
      c'.nmem = c.nmem) := by
  refine (IRS.addFrameB (normS_wr dsc pe ph o) h).mono le_rfl ?_
  rintro c' ⟨hq, hf⟩
  refine ⟨hq, hf.1 _ ?_, hf.2.2.1⟩
  unfold BnS Bprim ALLOC
  have h1 : (9999 : ℕ) ≠ ph := by omega
  have h2 : (9999 : ℕ) ≠ o := by omega
  have h3 : (9999 : ℕ) ≠ o + 1 := by omega
  simp [h1, h2, h3]

/-! ## The arcs of a list of regions -/

/-- The arcs of a list of regions, in order. -/
def regArcs (N : NF) (rs : List ℕ) : List ℕ := rs.flatMap fun r => (N.region r).arcs

/-- The normalised ends of an arc. -/
noncomputable def nArc (M : Model) (Q : Polygon) (N : NF) (a : ℕ) : WPos × WPos :=
  (Restore.normOf M Q (N.arc a).s, Restore.normOf M Q (N.arc a).e)

theorem regArcs_take_succ (N : NF) (rs : List ℕ) {i : ℕ} (hi : i < rs.length) :
    regArcs N (rs.take (i + 1)) = regArcs N (rs.take i) ++ (N.region (rs.getD i 0)).arcs := by
  unfold regArcs
  rw [List.take_add_one, List.flatMap_append, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **The ends of an arc** of a valid normal form of a chain model: proper positions on walk
edges, inside the height band of the box unless on a horizontal box edge. -/
theorem arc_end_facts {C : Chain} (hP : C.P.Simple) {N : NF}
    (hNF : IsNF (chainModel C) (Qof P) N) {a : ℕ} (ha : a < N.arcs.length) :
    (ProperPos (chainModel C) (Qof P) P.n (N.arc a).s ∧ (N.arc a).s.edge < (chainModel C).W.n ∧
      ((N.arc a).s.edge < 6 → (N.arc a).s.edge ≠ 0 → (N.arc a).s.edge ≠ 2 →
        (N.arc a).s.edge ≠ 4 → |((chainModel C).pos (Qof P) (N.arc a).s).2| < C.radius)) ∧
    (ProperPos (chainModel C) (Qof P) P.n (N.arc a).e ∧ (N.arc a).e.edge < (chainModel C).W.n ∧
      ((N.arc a).e.edge < 6 → (N.arc a).e.edge ≠ 0 → (N.arc a).e.edge ≠ 2 →
        (N.arc a).e.edge ≠ 4 → |((chainModel C).pos (Qof P) (N.arc a).e).2| < C.radius)) := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hNF' := hNF
  obtain ⟨hFam, -, -, reg, -, -, hArcs, -, -, -, hpp⟩ := hNF'
  obtain ⟨hps, hpe⟩ := hpp a ha
  rw [hQn] at hps hpe
  obtain ⟨-, harc⟩ := hArcs.1 a ha
  obtain ⟨hs0, hsn, he0, hen, hcase, -⟩ := harc
  have hedge : ∀ x : WPos, ProperPos (chainModel C) (Qof P) P.n x →
      (chainModel C).key (Qof P) x < (chainModel C).W.n → x.edge < (chainModel C).W.n := by
    intro x hx hk
    have hkey : (chainModel C).key (Qof P) x = x.edge + (chainModel C).param (Qof P) x := rfl
    have : ((x.edge : ℕ) : ℝ) < (chainModel C).W.n := by linarith [hx.1]
    exact_mod_cast this
  have hzero : ∀ x : WPos, ProperPos (chainModel C) (Qof P) P.n x →
      (chainModel C).key (Qof P) x = 0 → x.edge = 0 := by
    intro x hx hk
    have hkey : (chainModel C).key (Qof P) x = x.edge + (chainModel C).param (Qof P) x := rfl
    have : ((x.edge : ℕ) : ℝ) ≤ 0 := by linarith [hx.1]
    have : x.edge ≤ 0 := by exact_mod_cast this
    omega
  rcases (N.F (chainModel C) (Qof P)).eq_empty_or_nonempty with hF | hF
  · rcases hcase with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1, h2⟩
    · rw [hF] at hc; exact absurd hc (Set.notMem_empty c)
    have zs := hzero _ hps h1
    have ze := hzero _ hpe h2
    exact ⟨⟨hps, hedge _ hps hsn, fun _ h => absurd zs h⟩,
      ⟨hpe, hedge _ hpe hen, fun _ h => absurd ze h⟩⟩
  · have hab := Restore.arc_abs_lt hP hNF hF ha
    exact ⟨⟨hps, hedge _ hps hsn, fun _ _ _ _ => hab.1⟩, ⟨hpe, hedge _ hpe hen, fun _ _ _ _ => hab.2⟩⟩

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
  .seq (block gRegHead) (.seq (.ifLtN K0 gN (.instr (.addN gLs gLs gL7)) .skip)
    (.seq (.instr (.constN gT 0)) (.seq (.whileLtN gT gN (gArc dsc)) (block [.addN gI gI K1]))))

/-- The cost of a region with `na` arcs. -/
def regK (na : ℕ) : ℕ := 20 + (arcK + 2) * na

/-- The head of the gather. -/
def gHead : List Instr :=
  [.copyN gBase ALLOC, .constN gK 0, .constN gI 0, .addN gX gNF K4, .loadN gA4 gX,
    .addN gX gNF K5, .loadN gR5 gX, .addN gX gX K2, .loadN gL7 gX]

/-- **The gather.** -/
def gather (dsc : ℕ) : Stmt := .seq (block gHead) (.whileLtN gI gC (gReg dsc))

/-! ## Invariants -/

/-- The state of the gather after the records of `pre` (relative to the entry `cS`). -/
def GW (M : Model) (Q : Polygon) (N : NF) (cS c : Config) (pre : List ℕ) : Prop :=
  c.nreg gBase = cS.nreg ALLOC ∧ c.nreg gK = pre.length ∧
    c.nreg ALLOC = cS.nreg ALLOC + 4 * pre.length ∧
    (∀ k, k < pre.length →
      ShotList.arcAt c.nmem (cS.nreg ALLOC) k = nArc M Q N (pre.getD k 0)) ∧
    (∀ a, a < cS.nreg ALLOC → c.nmem a = cS.nmem a) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ GSet r → r ≠ ALLOC → c.nreg r = cS.nreg r) ∧
    c.nreg gA4 = cS.nmem (cS.nreg gNF + 4) ∧ c.nreg gR5 = cS.nmem (cS.nreg gNF + 5) ∧
    c.nreg gL7 = cS.nmem (cS.nreg gNF + 7)

/-- The state inside region `i` of the list. -/
def GIn (M : Model) (Q : Polygon) (N : NF) (cS : Config) (rs : List ℕ) (i : ℕ) (c : Config) :
    Prop :=
  GW M Q N cS c (regArcs N (rs.take i) ++ (N.region (rs.getD i 0)).arcs.take (c.nreg gT)) ∧
    c.nreg gI = i ∧ c.nreg gR = rs.getD i 0 ∧
    c.nreg gN = (N.region (rs.getD i 0)).arcs.length ∧
    (0 < (N.region (rs.getD i 0)).arcs.length → c.nreg gLs = cS.nmem (cS.nreg gNF + 7) +
      cS.nmem (cS.nmem (cS.nreg gNF + 5) + 5 * rs.getD i 0 + 1)) ∧
    c.nreg gT ≤ (N.region (rs.getD i 0)).arcs.length

/-! ## The register effect of the blocks -/

theorem gRead_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m gRead f gS = m (f gA4 + 5 * m (f gLs + f gT) + 1) ∧
    regB m gRead f gS1 = m (f gA4 + 5 * m (f gLs + f gT) + 2) ∧
    regB m gRead f gE = m (f gA4 + 5 * m (f gLs + f gT) + 3) ∧
    regB m gRead f gE1 = m (f gA4 + 5 * m (f gLs + f gT) + 4) := by
  have e1 : f 240611 = 1 := hk1
  simp only [gRead, regB, regI, upd, gX, gLs, gT, gA, gA4, gS, gS1, gE, gE1, K1, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
  refine ⟨congrArg m (by ring), congrArg m (by ring), congrArg m (by ring), congrArg m (by ring)⟩

theorem gRead_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ gX) (h2 : q ≠ gA) (h3 : q ≠ gS)
    (h4 : q ≠ gS1) (h5 : q ≠ gE) (h6 : q ≠ gE1) : regB m gRead f q = f q :=
  regB_other m gRead f (fun i hi => by
    simp only [gRead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp_all)

theorem gRead_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f gLs + f gT ≤ W)
    (hb2 : f gA4 + 5 * m (f gLs + f gT) + 4 ≤ W) : okB W m gRead f := by
  have e1 : f 240611 = 1 := hk1
  have s1 : IScr (240000 + 1015) := iscr_sw (by norm_num) (by norm_num)
  have s2 : IScr (240000 + 1014) := iscr_sw (by norm_num) (by norm_num)
  have s3 : IScr (240000 + 1016) := iscr_sw (by norm_num) (by norm_num)
  have s4 : IScr (240000 + 1017) := iscr_sw (by norm_num) (by norm_num)
  have s5 : IScr (240000 + 1018) := iscr_sw (by norm_num) (by norm_num)
  have s6 : IScr (240000 + 1019) := iscr_sw (by norm_num) (by norm_num)
  have hb' : f 241010 + f 241008 ≤ W := hb
  have hb2' : f 241011 + 5 * m (f 241010 + f 241008) + 4 ≤ W := hb2
  simp only [gRead, okB, okI, regI, upd, gX, gLs, gT, gA, gA4, gS, gS1, gE, gE1, K1, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1] at s1 s2 s3 s4 s5 s6 ⊢
  refine ⟨⟨s1, hb'⟩, s2, ⟨s1, by omega⟩, ⟨s1, by omega⟩, ⟨s1, by omega⟩, ⟨s1, by omega⟩,
    ⟨s1, by omega⟩, s3, ⟨s1, by omega⟩, s4, ⟨s1, by omega⟩, s5, ⟨s1, by omega⟩, s6, trivial⟩

theorem getD_append_left {l l' : List ℕ} {n d : ℕ} (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_last {l : List ℕ} {a d : ℕ} : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

/-! ## One arc -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One arc of the gather.** -/
theorem gArc_irs {dsc : ℕ} {C : Chain} {N : NF} {B E : ℕ} {cS : Config} {rs : List ℕ} {i : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hNW : NFWithin cS.nmem B E N) (hBS : cS.nreg gNF = B) (hE : E ≤ cS.nreg ALLOC)
    (hri : rs.getD i 0 < N.nRegions)
    (hin : GIn (chainModel C) (Qof P) N cS rs i c) (ht : c.nreg gT < c.nreg gN)
    (hroom : c.nreg ALLOC + arcK ≤ W) :
    IRS P W c₀ (gArc dsc) c arcK (fun c' => GIn (chainModel C) (Qof P) N cS rs i c' ∧
      c'.nreg gT = c.nreg gT + 1 ∧ ChainCtx P W c' dsc C) := by
  have hK₀ := hK.fix hI
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩, hgI, hgR, hgN, hgLs, hgT⟩ := hin
  set r := rs.getD i 0
  set t := c.nreg gT
  set pre := regArcs N (rs.take i) ++ (N.region r).arcs.take t with hpre
  have htl : t < (N.region r).arcs.length := by rwa [← hgN]
  set a := (N.region r).arcs.getD t 0 with had
  have ham : a ∈ (N.region r).arcs := by
    rw [had, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
    exact List.getElem_mem htl
  have ha : a < N.arcs.length := by
    obtain ⟨-, -, -, reg, -, -, hArcs, -⟩ := hNF
    exact ((hArcs.2.2.2 r hri a).1 ham).1
  -- the memory of the normal form
  have hNWc : NFWithin c.nmem B E N := hNW.transport (fun a' ha' => w5 a' (by omega))
  have hNA : NFAt c.nmem B N := hNWc.holds
  obtain ⟨b1, -, b3, b4, b5, -⟩ := Restore.nf_bounds hNWc
  have hgNF : c.nreg gNF = B := by
    rw [w6 gNF (not_oracle_sw (by unfold gNF sw; norm_num) (by unfold gNF sw; norm_num))
      (fun h => by unfold GSet gNF sw at h; omega) (by unfold gNF ALLOC sw; omega), hBS]
  have m4 : cS.nmem (B + 4) = c.nmem (B + 4) := (w5 _ (by omega)).symm
  have m5 : cS.nmem (B + 5) = c.nmem (B + 5) := (w5 _ (by omega)).symm
  have m7 : cS.nmem (B + 7) = c.nmem (B + 7) := (w5 _ (by omega)).symm
  have hreg := (hNA.2.2.2.2.2.2.2.1 r hri)
  have mr1 : cS.nmem (c.nmem (B + 5) + 5 * r + 1) = c.nmem (c.nmem (B + 5) + 5 * r + 1) :=
    (w5 _ (by have := b4 r hri; omega)).symm
  have vLs : c.nreg gLs = c.nmem (B + 7) + c.nmem (c.nmem (B + 5) + 5 * r + 1) := by
    rw [hgLs (by omega), hBS, m7, m5, mr1]
  have vA4 : c.nreg gA4 = c.nmem (B + 4) := by rw [w7, hBS, m4]
  have hblt := b5 r hri t htl
  have hat : c.nmem (c.nreg gLs + c.nreg gT) = a := by
    rw [vLs]; exact hreg.2.2.2.1 t htl
  have harec := hNA.2.2.2.2.2.2.1 a ha
  have hab := b3 a ha
  obtain ⟨⟨hps, hse, hsy⟩, ⟨hpe, hee, hey⟩⟩ := arc_end_facts hP hNF ha
  -- the read block
  have hok : okB W c.nmem gRead c.nreg := gRead_ok _ _ hK₀.2.1 (by rw [vLs]; omega)
    (by rw [hat, vA4]; omega)
  refine IRS.mono (K := gRead.length + (11015 + (11015 + (8 + 2)))) (IRS.seq (IRS.block gRead hI hok)
    ?_) (by simp [gRead, arcK]) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  set c₁ : Config := { c with nreg := regB c.nmem gRead c.nreg }
  obtain ⟨r1s, r1s1, r1e, r1e1⟩ := gRead_val c.nmem c.nreg hK₀.2.1
  rw [hat, vA4] at r1s r1s1 r1e r1e1
  have v1s : c₁.nreg gS = (N.arc a).s.edge := by rwa [← harec.2.1]
  have v1s1 : c₁.nreg gS1 = (N.arc a).s.hgt := by rwa [← harec.2.2.1]
  have v1e : c₁.nreg gE = (N.arc a).e.edge := by rwa [← harec.2.2.2.1]
  have v1e1 : c₁.nreg gE1 = (N.arc a).e.hgt := by rwa [← harec.2.2.2.2]
  have k1' : ∀ q, q ≠ gX → q ≠ gA → q ≠ gS → q ≠ gS1 → q ≠ gE → q ≠ gE1 →
      c₁.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => gRead_other _ _ h1 h2 h3 h4 h5 h6
  have k1 : ∀ q, ¬ GSet q → c₁.nreg q = c.nreg q := fun q hq =>
    gRead_other _ _ (fun h => hq (by subst h; unfold GSet gX sw; omega))
      (fun h => hq (by subst h; unfold GSet gA sw; omega)) (fun h => hq (by subst h; unfold GSet gS sw; omega))
      (fun h => hq (by subst h; unfold GSet gS1 sw; omega)) (fun h => hq (by subst h; unfold GSet gE sw; omega))
      (fun h => hq (by subst h; unfold GSet gE1 sw; omega))
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold GSet ALLOC sw; omega)
  have hctx₁ : ChainCtx P W c₁ dsc C := hctx.transport (k1 _ hd.2.2) (fun _ _ => rfl) hA1.ge
  -- normalise the start
  have hy1 : c₁.nreg gS < 6 → c₁.nreg gS ≠ 0 → c₁.nreg gS ≠ 2 → c₁.nreg gS ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₁.nreg gS, c₁.nreg gS1⟩).2| < C.radius := by
    rwa [v1s, v1s1]
  refine IRS.seq (normS_exact (normS_irs (dsc := dsc) (pe := gS) (ph := gS1) (o := gO) hI₁
    (hK.fix hI₁) hctx₁ ⟨hd.1, hd.2.1, by unfold gS sw; norm_num, by unfold gS sw; norm_num,
      by unfold gS1 sw; norm_num, by unfold gS1 sw; norm_num⟩
    ⟨by unfold gO sw; norm_num, by unfold gO sw; norm_num, by unfold gO gS sw; norm_num,
      by unfold gO gS1 sw; norm_num, by unfold gO gS sw; norm_num, by unfold gO gS1 sw; norm_num,
      by unfold gS gS1 sw; norm_num⟩
    (by rwa [v1s]) (by rwa [v1s, v1s1]) hy1
    (by rw [hA1]; unfold arcK at hroom; omega)) ⟨by unfold gS1 sw; norm_num, by unfold gO sw; norm_num⟩) ?_
  rintro c₂ hI₂ - - ⟨⟨n2s, n2s1, k2, -, -⟩, hA2, hm2⟩
  have hctx₂ : ChainCtx P W c₂ dsc C := hctx₁.transport
    (k2 _ (not_oracle_sw hd.1 hd.2.1) (fun h => hd.2.2 (by subst h; unfold GSet gS1 sw; omega))
      (fun h => hd.2.2 (by subst h; unfold GSet gO sw; omega))
      (fun h => hd.2.2 (by subst h; unfold GSet gO sw; omega)) (by unfold ALLOC; omega))
    (fun a' _ => by rw [hm2]) hA2.ge
  have v2e : c₂.nreg gE = (N.arc a).e.edge := by
    rw [k2 _ (not_oracle_sw (by unfold gE sw; norm_num) (by unfold gE sw; norm_num))
      (by unfold gE gS1 sw; norm_num) (by unfold gE gO sw; norm_num) (by unfold gE gO sw; norm_num)
      (by unfold gE ALLOC sw; norm_num), v1e]
  have v2e1 : c₂.nreg gE1 = (N.arc a).e.hgt := by
    rw [k2 _ (not_oracle_sw (by unfold gE1 sw; norm_num) (by unfold gE1 sw; norm_num))
      (by unfold gE1 gS1 sw; norm_num) (by unfold gE1 gO sw; norm_num)
      (by unfold gE1 gO sw; norm_num) (by unfold gE1 ALLOC sw; norm_num), v1e1]
  -- normalise the end
  have hy2 : c₂.nreg gE < 6 → c₂.nreg gE ≠ 0 → c₂.nreg gE ≠ 2 → c₂.nreg gE ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₂.nreg gE, c₂.nreg gE1⟩).2| < C.radius := by
    rw [v2e, v2e1]; exact hey
  refine IRS.seq (normS_exact (normS_irs (dsc := dsc) (pe := gE) (ph := gE1) (o := gO) hI₂
    (hK.fix hI₂) hctx₂ ⟨hd.1, hd.2.1, by unfold gE sw; norm_num, by unfold gE sw; norm_num,
      by unfold gE1 sw; norm_num, by unfold gE1 sw; norm_num⟩
    ⟨by unfold gO sw; norm_num, by unfold gO sw; norm_num, by unfold gO gE sw; norm_num,
      by unfold gO gE1 sw; norm_num, by unfold gO gE sw; norm_num, by unfold gO gE1 sw; norm_num,
      by unfold gE gE1 sw; norm_num⟩
    (by rw [v2e]; exact hee) (by rw [v2e, v2e1]; exact hpe) hy2
    (by rw [hA2, hA1]; unfold arcK at hroom; omega)) ⟨by unfold gE1 sw; norm_num, by unfold gO sw; norm_num⟩) ?_
  rintro c₃ hI₃ - - ⟨⟨n3e, n3e1, k3, -, -⟩, hA3, hm3⟩
  have v3s : c₃.nreg gS = c₂.nreg gS := k3 _ (not_oracle_sw (by unfold gS sw; norm_num)
    (by unfold gS sw; norm_num)) (by unfold gS gE1 sw; norm_num) (by unfold gS gO sw; norm_num)
    (by unfold gS gO sw; norm_num) (by unfold gS ALLOC sw; norm_num)
  have v3s1 : c₃.nreg gS1 = c₂.nreg gS1 := k3 _ (not_oracle_sw (by unfold gS1 sw; norm_num)
    (by unfold gS1 sw; norm_num)) (by unfold gS1 gE1 sw; norm_num) (by unfold gS1 gO sw; norm_num)
    (by unfold gS1 gO sw; norm_num) (by unfold gS1 ALLOC sw; norm_num)
  have ns : (⟨c₃.nreg gS, c₃.nreg gS1⟩ : WPos) = Restore.normOf (chainModel C) (Qof P) (N.arc a).s := by
    rw [v3s, v3s1, n2s1, n2s, v1s, v1s1]
    unfold nhgt
    have := (Restore.normOf_facts hps).2.1
    rcases hn : Restore.normOf (chainModel C) (Qof P) (N.arc a).s with ⟨e', h'⟩
    rw [hn] at this
    simp only at this ⊢
    rw [this]
  have ne' : (⟨c₃.nreg gE, c₃.nreg gE1⟩ : WPos) = Restore.normOf (chainModel C) (Qof P) (N.arc a).e := by
    rw [n3e1, n3e, v2e, v2e1]
    unfold nhgt
    have := (Restore.normOf_facts hpe).2.1
    rcases hn : Restore.normOf (chainModel C) (Qof P) (N.arc a).e with ⟨e', h'⟩
    rw [hn] at this
    simp only at this ⊢
    rw [this]
  have hA3' : c₃.nreg ALLOC = c.nreg ALLOC := by rw [hA3, hA2, hA1]
  have hm3' : c₃.nmem = c.nmem := by rw [hm3, hm2]
  -- store the record
  refine IRS.seq (put4_irs hI₃ (hK.fix hI₃) (by rw [hA3']; unfold arcK at hroom; omega)) ?_
  rintro c₄ hI₄ - - ⟨hA4, k4, hm4, -, -, -⟩
  -- advance
  -- the frame from `c` to `c₄`
  have k14 : ∀ q, bandOf q ∉ oracleBands → q ≠ gX → q ≠ gA → q ≠ gS → q ≠ gS1 → q ≠ gE →
      q ≠ gE1 → q ≠ gO → q ≠ gO + 1 → q ≠ ALLOC → c₄.nreg q = c.nreg q := by
    intro q hq h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [k4 _ h9, k3 _ hq h6 h7 h8 h9, k2 _ hq h4 h7 h8 h9, k1' _ h1 h2 h3 h4 h5 h6]
  have k14' (q) (h : 241000 ≤ q ∧ q ≤ 241013 := by
      simp only [gBase, gK, gI, gR, gT, gN, gLs, gA4, gR5, gL7, sw]; omega) :
      c₄.nreg q = c.nreg q :=
    k14 q (not_oracle_sw (by omega) (by omega)) (by unfold gX sw; omega) (by unfold gA sw; omega)
      (by unfold gS sw; omega) (by unfold gS1 sw; omega) (by unfold gE sw; omega)
      (by unfold gE1 sw; omega) (by unfold gO sw; omega) (by unfold gO sw; omega)
      (by unfold ALLOC; omega)
  have hA4' : c₄.nreg ALLOC = c.nreg ALLOC + 4 := by rw [hA4, hA3']
  have k4K : c₄.nreg gK = c.nreg gK := k14' gK
  have k4T : c₄.nreg gT = t := k14' gT
  have hK1₄ : c₄.nreg K1 = 1 := (hK.fix hI₄).2.1
  have hpl : pre.length + 1 ≤ W := by
    have := w3; unfold arcK at hroom; omega
  have htW : t + 1 ≤ W := by
    have := hI.hw.1 gN; rw [hgN] at this; omega
  have hok5 : okB W c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg := by
    have e1 : c₄.nreg 240611 = 1 := hK1₄
    have e2 : c₄.nreg 241005 = pre.length := by rwa [← w2]
    have e3 : c₄.nreg 241008 = t := k4T
    simp only [okB, okI, regI, upd, gK, gT, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_false, e1, e2, e3]
    exact ⟨⟨iscr_sw (by norm_num) (by norm_num), hpl⟩, ⟨iscr_sw (by norm_num) (by norm_num), htW⟩,
      trivial⟩
  refine (IRS.block _ hI₄ hok5).mono (by simp) ?_
  rintro c₅ rfl
  have r5 : ∀ q, q ≠ gK → q ≠ gT → regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg q =
      c₄.nreg q := fun q h1 h2 => regB_other _ _ _ (fun i hi => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp only [dstI] <;> intro h <;> subst h <;> simp_all)
  have v5K : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg gK = pre.length + 1 := by
    have e1 : c₄.nreg 240611 = 1 := hK1₄
    have e2 : c₄.nreg 241005 = pre.length := by rwa [← w2]
    simp only [regB, regI, upd, gK, gT, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e2]
  have v5T : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg gT = t + 1 := by
    have e1 : c₄.nreg 240611 = 1 := hK1₄
    have e3 : c₄.nreg 241008 = t := k4T
    simp only [regB, regI, upd, gK, gT, K1, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1, e3]
  -- the frame from `c` to `c₅`
  have k15 : ∀ q, bandOf q ∉ oracleBands → ¬ GSet q → q ≠ ALLOC →
      regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg q = c.nreg q := by
    intro q hq hg hqa
    have ne : ∀ g, GSet g → q ≠ g := fun g hgs h => hg (h ▸ hgs)
    rw [r5 q (ne _ (by unfold GSet gK sw; omega)) (ne _ (by unfold GSet gT sw; omega)),
      k14 q hq (ne _ (by unfold GSet gX sw; omega)) (ne _ (by unfold GSet gA sw; omega))
        (ne _ (by unfold GSet gS sw; omega)) (ne _ (by unfold GSet gS1 sw; omega))
        (ne _ (by unfold GSet gE sw; omega)) (ne _ (by unfold GSet gE1 sw; omega))
        (ne _ (by unfold GSet gO sw; omega)) (ne _ (by unfold GSet gO sw; omega)) hqa]
  have kk (g) (h : 241000 ≤ g ∧ g ≤ 241013 ∧ g ≠ gK ∧ g ≠ gT := by
      simp only [gBase, gI, gR, gN, gLs, gA4, gR5, gL7, gK, gT, sw]; omega) :
      regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg g = c.nreg g :=
    (r5 g h.2.2.1 h.2.2.2).trans (k14' g ⟨h.1, h.2.1⟩)
  have hpre' : regArcs N (rs.take i) ++ (N.region r).arcs.take (t + 1) = pre ++ [a] := by
    rw [hpre, List.take_add_one, List.getElem?_eq_getElem htl, List.append_assoc]
    simp only [Option.toList_some]
    rw [had, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl, Option.getD_some]
  have hA5 : regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg ALLOC = c.nreg ALLOC + 4 := by
    rw [r5 _ (by unfold gK ALLOC sw; norm_num) (by unfold gT ALLOC sw; norm_num), hA4']
  have hmem5 : c₄.nmem = mem4 c.nmem (cS.nreg ALLOC + 4 * pre.length) (c₃.nreg gS) (c₃.nreg gS1)
      (c₃.nreg gE) (c₃.nreg gE1) := by rw [hm4, hm3', hA3', w3]
  have hT5 : ({ c₄ with nreg := regB c₄.nmem [.addN gK gK K1, .addN gT gT K1] c₄.nreg } :
      Config).nreg gT = t + 1 := v5T
  have hpre'' : regArcs N (rs.take i) ++ (N.region (rs.getD i 0)).arcs.take (t + 1) =
      pre ++ [a] := hpre'
  unfold GIn GW
  rw [hT5, hpre'']
  refine ⟨⟨⟨(kk gBase).trans w1, by show regB _ _ _ gK = _; rw [v5K]; simp,
    by show regB _ _ _ ALLOC = _; rw [hA5, w3]; simp; ring, ?_, ?_,
    fun q hq hg hqa => (k15 q hq hg hqa).trans (w6 q hq hg hqa),
    (kk gA4).trans w7, (kk gR5).trans w8, (kk gL7).trans w9⟩,
    (kk gI).trans hgI, (kk gR).trans hgR, (kk gN).trans hgN,
    fun hpos => (kk gLs).trans (hgLs hpos), htl⟩, rfl, ?_⟩
  · intro k hk
    show ShotList.arcAt c₄.nmem _ k = _
    rw [hmem5]
    unfold mem4
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rcases Nat.lt_or_ge k pre.length with hl | hg
    · rw [Restore.arcAt_upd4 hl, w4 k hl, getD_append_left hl]
    · have hk' : k = pre.length := by omega
      subst hk'
      rw [Restore.arcAt_upd4_new, getD_append_last]
      unfold nArc
      rw [← ns, ← ne']
  · intro a' ha'
    show c₄.nmem a' = _
    rw [hmem5]
    unfold mem4
    simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), w5 a' ha']
  · refine hctx.transport (k15 _ (not_oracle_sw hd.1 hd.2.1) hd.2.2 (by unfold ALLOC; omega))
      (fun a' ha' => ?_) (by show c.nreg ALLOC ≤ regB _ _ _ ALLOC; rw [hA5]; omega)
    show c₄.nmem a' = _
    rw [hm4, hm3', hA3']
    unfold mem4
    simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The working registers of the gather (not the outputs and not the bases). -/
def GFree (q : ℕ) : Prop :=
  q = gI ∨ q = gR ∨ q = gT ∨ q = gN ∨ q = gLs ∨ q = gA ∨ q = gX ∨ q = gS ∨ q = gS1 ∨ q = gE ∨
    q = gE1 ∨ q = gO ∨ q = gO + 1

theorem gfree_gset {q : ℕ} (h : GFree q) : GSet q := by
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
  refine ⟨by rw [hr _ (nf _ (by simp)), w1], by rw [hr _ (nf _ (by simp)), w2],
    by rw [hr _ (nf _ (by simp)), w3], fun k hk => by rw [hm]; exact w4 k hk,
    fun a ha => by rw [hm]; exact w5 a ha, fun q hq hg hqa => ?_,
    by rw [hr _ (nf _ (by simp)), w7], by rw [hr _ (nf _ (by simp)), w8],
    by rw [hr _ (nf _ (by simp)), w9]⟩
  rw [hr q (fun hf => hg (gfree_gset hf)), w6 q hq hg hqa]

/-! ## One region -/

theorem gRegHead_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m gRegHead f gR = m (f gL + f gI) ∧
    regB m gRegHead f gN = m (f gR5 + 5 * m (f gL + f gI)) ∧
    regB m gRegHead f gLs = m (f gR5 + 5 * m (f gL + f gI) + 1) := by
  have e1 : f 240611 = 1 := hk1
  simp only [gRegHead, regB, regI, upd, gX, gL, gI, gR, gR5, gN, gLs, K1, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1]
  exact ⟨trivial, congrArg m (by ring), congrArg m (by ring)⟩

theorem gRegHead_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ gX) (h2 : q ≠ gR) (h3 : q ≠ gN)
    (h4 : q ≠ gLs) : regB m gRegHead f q = f q :=
  regB_other m gRegHead f (fun i hi => by
    simp only [gRegHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      intro h <;> subst h <;> simp_all)

theorem gRegHead_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f gL + f gI ≤ W)
    (hb2 : f gR5 + 5 * m (f gL + f gI) + 1 ≤ W) : okB W m gRegHead f := by
  have e1 : f 240611 = 1 := hk1
  have s1 : IScr (240000 + 1015) := iscr_sw (by norm_num) (by norm_num)
  have s2 : IScr (240000 + 1007) := iscr_sw (by norm_num) (by norm_num)
  have s3 : IScr (240000 + 1009) := iscr_sw (by norm_num) (by norm_num)
  have s4 : IScr (240000 + 1010) := iscr_sw (by norm_num) (by norm_num)
  have hb' : f 241001 + f 241006 ≤ W := hb
  have hb2' : f 241012 + 5 * m (f 241001 + f 241006) + 1 ≤ W := hb2
  simp only [gRegHead, okB, okI, regI, upd, gX, gL, gI, gR, gR5, gN, gLs, K1, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1] at s1 s2 s3 s4 ⊢
  refine ⟨⟨s1, hb'⟩, s2, ⟨s1, by omega⟩, ⟨s1, by omega⟩, ⟨s1, by omega⟩, ⟨s1, by omega⟩,
    s3, ⟨s1, by omega⟩, s4, trivial⟩

theorem getD_mem_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One region of the gather.** -/
theorem gReg_irs {dsc : ℕ} {C : Chain} {N : NF} {B E : ℕ} {cS : Config} {rs : List ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hNW : NFWithin cS.nmem B E N) (hBS : cS.nreg gNF = B) (hE : E ≤ cS.nreg ALLOC)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hL : ∀ j, j < rs.length → cS.nmem (cS.nreg gL + j) = rs.getD j 0)
    (hLA : cS.nreg gL + rs.length ≤ cS.nreg ALLOC)
    (hgo : GW (chainModel C) (Qof P) N cS c (regArcs N (rs.take (c.nreg gI))))
    (hctx : ChainCtx P W c dsc C) (hi : c.nreg gI < rs.length)
    (hroom : c.nreg ALLOC + regK ((N.region (rs.getD (c.nreg gI) 0)).arcs.length) ≤ W) :
    IRS P W c₀ (gReg dsc) c (regK ((N.region (rs.getD (c.nreg gI) 0)).arcs.length))
      (fun c' => GW (chainModel C) (Qof P) N cS c' (regArcs N (rs.take (c'.nreg gI))) ∧
        c'.nreg gI = c.nreg gI + 1 ∧ ChainCtx P W c' dsc C) := by
  have hK₀ := hK.fix hI
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hgo
  set i := c.nreg gI
  set r := rs.getD i 0 with hrd
  have hr : r < N.nRegions := hrs r (getD_mem_of_lt hi)
  set na := (N.region r).arcs.length
  have hNWc : NFWithin c.nmem B E N := hNW.transport (fun a' ha' => w5 a' (by omega))
  have hNA : NFAt c.nmem B N := hNWc.holds
  obtain ⟨b1, -, -, b4, b5, -⟩ := Restore.nf_bounds hNWc
  have hgL : c.nreg gL = cS.nreg gL := w6 gL (not_oracle_sw (by unfold gL sw; norm_num)
    (by unfold gL sw; norm_num)) (fun h => by unfold GSet gL sw at h; omega)
    (by unfold gL ALLOC sw; omega)
  have hmL : c.nmem (c.nreg gL + i) = r := by
    rw [hgL, w5 _ (by omega), hL i hi]
  have m5 : cS.nmem (B + 5) = c.nmem (B + 5) := (w5 _ (by omega)).symm
  have m7 : cS.nmem (B + 7) = c.nmem (B + 7) := (w5 _ (by omega)).symm
  have vR5 : c.nreg gR5 = c.nmem (B + 5) := by rw [w8, hBS, m5]
  have hreg := hNA.2.2.2.2.2.2.2.1 r hr
  have hb4 := b4 r hr
  have hLW : c.nreg gL + i ≤ W := by
    have := hI.hw.1 ALLOC; rw [hgL]; omega
  -- the head of the region
  have hok : okB W c.nmem gRegHead c.nreg := gRegHead_ok _ _ hK₀.2.1 hLW
    (by rw [hmL, vR5]; have := hI.hw.1 ALLOC; omega)
  refine IRS.mono (K := gRegHead.length + (3 + (1 + ((arcK + 2) * na + 2 + 1))))
    (IRS.seq (IRS.block gRegHead hI hok) ?_) (by simp [gRegHead, regK]; omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨v1R, v1N, v1Ls⟩ := gRegHead_val c.nmem c.nreg hK₀.2.1
  rw [hmL] at v1R
  rw [hmL, vR5] at v1N v1Ls
  rw [hreg.1] at v1N
  have k1 : ∀ q, q ≠ gX → q ≠ gR → q ≠ gN → q ≠ gLs →
      regB c.nmem gRegHead c.nreg q = c.nreg q := fun q h1 h2 h3 h4 =>
    gRegHead_other _ _ h1 h2 h3 h4
  set c₁ : Config := { c with nreg := regB c.nmem gRegHead c.nreg }
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 ALLOC (by unfold gX ALLOC sw; omega)
    (by unfold gR ALLOC sw; omega) (by unfold gN ALLOC sw; omega) (by unfold gLs ALLOC sw; omega)
  -- the list start
  have step2 : IRS P W c₀ (.ifLtN K0 gN (.instr (.addN gLs gLs gL7)) .skip) c₁ 3
      (fun c' => c'.nmem = c₁.nmem ∧ (∀ q, q ≠ gLs → c'.nreg q = c₁.nreg q) ∧
        (0 < na → c'.nreg gLs = c.nmem (B + 7) + c.nmem (c.nmem (B + 5) + 5 * r + 1))) := by
    have k0 : c₁.nreg K0 = 0 := (hK.fix hI₁).1
    by_cases hp : 0 < na
    · have hlt : c₁.nreg K0 < c₁.nreg gN := by
        rwa [k0, show c₁.nreg gN = na from v1N]
      have hL7 : c₁.nreg gL7 = c.nmem (B + 7) := by
        rw [show c₁.nreg gL7 = c.nreg gL7 from k1 gL7 (by unfold gL7 gX sw; omega)
          (by unfold gL7 gR sw; omega) (by unfold gL7 gN sw; omega) (by unfold gL7 gLs sw; omega),
          w9, hBS, m7]
      have hb := b5 r hr 0 hp
      refine (IRS.ifT hlt (IRS.reg hI₁ (iscr_sw (by unfold gLs sw; norm_num)
        (by unfold gLs sw; norm_num)) (Exec.addN hI₁.hw gLs gLs gL7 ?_))).mono (by omega) ?_
      · show regB c.nmem gRegHead c.nreg gLs + c₁.nreg gL7 ≤ W
        rw [v1Ls, hL7]; have := hI.hw.1 ALLOC; omega
      · rintro c' rfl
        refine ⟨rfl, fun q hq => by simp only; rw [upd_other _ _ _ hq],
          fun _ => ?_⟩
        simp only [upd_same]
        show regB c.nmem gRegHead c.nreg gLs + c₁.nreg gL7 = _
        rw [v1Ls, hL7]; ring
    · have hlt : ¬ c₁.nreg K0 < c₁.nreg gN := by rw [k0, show c₁.nreg gN = na from v1N]; omega
      exact (IRS.ifF hlt (IRS.skip (K := 1) hI₁ ⟨rfl, fun _ _ => rfl, fun h => absurd h hp⟩)).mono
        (by omega) (fun _ h => h)
  refine IRS.seq step2 ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hm2, k2, v2Ls⟩
  have hfr : ∀ g, GFree g → dsc ≠ g := fun g hg h => hd.2.2 (by rw [h]; exact gfree_gset hg)
  -- the arc place
  refine IRS.seq (IRS.reg hI₂ (iscr_sw (by unfold gT sw; norm_num) (by unfold gT sw; norm_num))
    (Exec.constN hI₂.hw gT 0 (Nat.zero_le _))) ?_
  rintro c₃ hI₃ hA₃ hA₃' rfl
  have k3 : ∀ q, q ≠ gT → q ≠ gLs → q ≠ gX → q ≠ gR → q ≠ gN →
      (upd c₂.nreg gT 0) q = c.nreg q := by
    intro q h1 h2 h3 h4 h5
    rw [upd_other _ _ _ h1, k2 q h2]
    exact k1 q h3 h4 h5 h2
  have v3R : (upd c₂.nreg gT 0) gR = r := by
    rwa [upd_other _ _ _ (by unfold gR gT sw; norm_num), k2 _ (by unfold gR gLs sw; norm_num)]
  have v3N : (upd c₂.nreg gT 0) gN = na := by
    rwa [upd_other _ _ _ (by unfold gN gT sw; norm_num), k2 _ (by unfold gN gLs sw; norm_num)]
  have v3I : (upd c₂.nreg gT 0) gI = i := k3 _ (by unfold gI gT sw; norm_num)
    (by unfold gI gLs sw; norm_num) (by unfold gI gX sw; norm_num) (by unfold gI gR sw; norm_num)
    (by unfold gI gN sw; norm_num)
  have hm3 : c₂.nmem = c.nmem := hm2
  have hGW3 : GW (chainModel C) (Qof P) N cS { c₂ with nreg := upd c₂.nreg gT 0 }
      (regArcs N (rs.take i) ++ (N.region r).arcs.take 0) := by
    rw [List.take_zero, List.append_nil]
    refine GW.step ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ hm3 (fun q hq => ?_)
    simp only [GFree, not_or] at hq
    exact k3 q hq.2.2.1 hq.2.2.2.2.1 hq.2.2.2.2.2.2.1 hq.2.1 hq.2.2.2.1
  have hctx₃ : ChainCtx P W { c₂ with nreg := upd c₂.nreg gT 0 } dsc C :=
    hctx.transport (k3 _ (hfr gT (by simp [GFree])) (hfr gLs (by simp [GFree]))
      (hfr gX (by simp [GFree])) (hfr gR (by simp [GFree])) (hfr gN (by simp [GFree])))
      (fun _ _ => by simp only; rw [hm3])
      (by simp only
          rw [k3 ALLOC (by unfold gT ALLOC sw; omega) (by unfold gLs ALLOC sw; omega)
            (by unfold gX ALLOC sw; omega) (by unfold gR ALLOC sw; omega)
            (by unfold gN ALLOC sw; omega)])
  have hIn3 : GIn (chainModel C) (Qof P) N cS rs i { c₂ with nreg := upd c₂.nreg gT 0 } := by
    refine ⟨by simp only [upd_same]; exact hGW3, v3I, v3R, v3N,
      fun hp => ?_, by simp only [upd_same]; omega⟩
    simp only
    rw [← hrd] at hp ⊢
    rw [upd_other _ _ _ (by unfold gLs gT sw; norm_num), v2Ls hp, hBS, m7, m5,
      ← w5 (c.nmem (B + 5) + 5 * r + 1) (by omega)]
  -- the arcs
  refine IRS.seq (IRS.while (fun c' => GIn (chainModel C) (Qof P) N cS rs i c' ∧
      ChainCtx P W c' dsc C) (fun c' => na - c'.nreg gT) arcK
    (fun c' ⟨hg, _⟩ hlt => by
      obtain ⟨-, -, -, hgN', -, -⟩ := hg
      rw [hgN', ← hrd] at hlt; omega)
    (fun c' hI' ⟨hg, hc'⟩ hlt hr' => (gArc_irs hI' hK hc' hd hP hNF hNW hBS hE (hrd ▸ hr) hg hlt
      hr').mono le_rfl (fun c'' ⟨hg', ht', hc''⟩ => ⟨⟨hg', hc''⟩, by
        obtain ⟨-, -, -, hgN', -, -⟩ := hg
        rw [hgN', ← hrd] at hlt; rw [ht']; omega⟩))
    hI₃ ⟨hIn3, hctx₃⟩ (by
      show (upd c₂.nreg gT 0) ALLOC + (arcK + 2) * (na - (upd c₂.nreg gT 0) gT) ≤ W
      rw [upd_same, Nat.sub_zero, upd_other _ _ _ (by unfold gT ALLOC sw; omega),
        k2 _ (by unfold gLs ALLOC sw; omega), hA1]
      unfold regK at hroom; omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨hIn4, hctx₄⟩, hnlt⟩
  obtain ⟨hGW4, hgI4, hgR4, hgN4, -, hgT4⟩ := hIn4
  have hT4 : c₄.nreg gT = (N.region (rs.getD i 0)).arcs.length := by
    rw [hgN4] at hnlt; omega
  rw [hT4, List.take_length, ← regArcs_take_succ N rs hi] at hGW4
  -- advance the region index
  have hiW : c₄.nreg gI + c₄.nreg K1 ≤ W := by
    rw [hgI4, (hK.fix hI₄).2.1]; have := hI.hw.1 ALLOC; omega
  have hok6 : okB W c₄.nmem [.addN gI gI K1] c₄.nreg :=
    ⟨⟨iscr_sw (by unfold gI sw; norm_num) (by unfold gI sw; norm_num), hiW⟩, trivial⟩
  refine (IRS.block _ hI₄ hok6).mono (by simp) ?_
  rintro c₅ rfl
  simp only [regB, regI, upd_same]
  rw [hgI4, (hK.fix hI₄).2.1]
  refine ⟨GW.step hGW4 rfl (fun q hq => upd_other _ _ _ (fun h => hq (by simp [h, GFree]))), rfl,
    hctx₄.transport (upd_other _ _ _ (hfr gI (by simp [GFree]))) (fun _ _ => rfl)
      (by show c₄.nreg ALLOC ≤ upd c₄.nreg gI (i + 1) ALLOC
          rw [upd_other _ _ _ (by unfold gI ALLOC sw; omega)])⟩

/-! ## The gather -/

/-- The cost of the gather of a list of regions. -/
def gatherK (N : NF) (rs : List ℕ) : ℕ :=
  11 + (rs.map fun r => regK (N.region r).arcs.length + 2).sum

/-- The potential of the region loop. -/
def gPot (N : NF) (rs : List ℕ) (i : ℕ) : ℕ :=
  ((rs.drop i).map fun r => regK (N.region r).arcs.length + 2).sum

theorem gPot_succ (N : NF) (rs : List ℕ) {i : ℕ} (hi : i < rs.length) :
    gPot N rs i = regK (N.region (rs.getD i 0)).arcs.length + 2 + gPot N rs (i + 1) := by
  unfold gPot
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.sum_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem gHead_val (m f : ℕ → ℕ) :
    regB m gHead f gBase = f ALLOC ∧ regB m gHead f gK = 0 ∧ regB m gHead f gI = 0 ∧
    regB m gHead f gA4 = m (f gNF + f K4) ∧ regB m gHead f gR5 = m (f gNF + f K5) ∧
    regB m gHead f gL7 = m (f gNF + f K5 + f K2) := by
  simp only [gHead, regB, regI, upd, gX, gNF, gBase, gK, gI, gA4, gR5, gL7, K4, K5, K2, ALLOC, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem gHead_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ GSet q) : regB m gHead f q = f q :=
  regB_other m gHead f (fun i hi => by
    simp only [gHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      intro he <;> subst he <;> apply h <;>
      simp [GSet, gX, gBase, gK, gI, gA4, gR5, gL7, sw])

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The gather**: the normalised arcs of the listed regions, in order, at the allocator. -/
theorem gather_irs {dsc : ℕ} {C : Chain} {N : NF} {B E : ℕ} {rs : List ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hd : 240000 ≤ dsc ∧ dsc < 250000 ∧ ¬ GSet dsc)
    (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hNW : NFWithin c.nmem B E N) (hB : c.nreg gNF = B) (hE : E ≤ c.nreg ALLOC)
    (hrs : ∀ r ∈ rs, r < N.nRegions)
    (hL : ∀ j, j < rs.length → c.nmem (c.nreg gL + j) = rs.getD j 0)
    (hLA : c.nreg gL + rs.length ≤ c.nreg ALLOC) (hC : c.nreg gC = rs.length)
    (hroom : c.nreg ALLOC + gatherK N rs ≤ W) :
    IRS P W c₀ (gather dsc) c (gatherK N rs)
      (fun c' => GW (chainModel C) (Qof P) N c c' (regArcs N rs) ∧ ChainCtx P W c' dsc C) := by
  have hK₀ := hK.fix hI
  obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK₀
  obtain ⟨b1, -⟩ := Restore.nf_bounds hNW
  have hBW : B + 7 ≤ W := by have := hI.hw.1 ALLOC; omega
  have hok : okB W c.nmem gHead c.nreg := by
    have e4 : c.nreg 240613 = 4 := k4
    have e5 : c.nreg 240614 = 5 := k5
    have e2 : c.nreg 240615 = 2 := k2
    have eB : c.nreg 241000 = B := hB
    have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
      iscr_sw (by omega) (by omega)
    simp only [gHead, okB, okI, regI, upd, gX, gNF, gBase, gK, gI, gA4, gR5, gL7, K4, K5, K2,
      ALLOC, sw]
    simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e4, e5, e2, eB]
    refine ⟨s 1004 (by norm_num) (by norm_num), ⟨s 1005 (by norm_num) (by norm_num), by omega⟩,
      ⟨s 1006 (by norm_num) (by norm_num), by omega⟩, ⟨s 1015 (by norm_num) (by norm_num), by omega⟩,
      s 1011 (by norm_num) (by norm_num), ⟨s 1015 (by norm_num) (by norm_num), by omega⟩,
      s 1012 (by norm_num) (by norm_num), ⟨s 1015 (by norm_num) (by norm_num), by omega⟩,
      s 1013 (by norm_num) (by norm_num), trivial⟩
  refine IRS.mono (K := gHead.length + (gPot N rs 0 + 2)) (IRS.seq (IRS.block gHead hI hok) ?_)
    (by simp [gHead, gatherK, gPot]; omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  obtain ⟨vB, vK, vI, vA4, vR5, vL7⟩ := gHead_val c.nmem c.nreg
  set c₁ : Config := { c with nreg := regB c.nmem gHead c.nreg }
  have ko : ∀ q, ¬ GSet q → c₁.nreg q = c.nreg q := fun q hq => gHead_other _ _ hq
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := ko _ (by unfold GSet ALLOC sw; omega)
  have hGW1 : GW (chainModel C) (Qof P) N c c₁ (regArcs N (rs.take (c₁.nreg gI))) := by
    rw [show c₁.nreg gI = 0 from vI, List.take_zero]
    refine ⟨vB, vK, by rw [hA1]; simp [regArcs], fun k hk => by simp [regArcs] at hk,
      fun _ _ => rfl, fun q _ hq _ => ko q hq, ?_, ?_, ?_⟩
    · show regB c.nmem gHead c.nreg gA4 = _; rw [vA4, k4]
    · show regB c.nmem gHead c.nreg gR5 = _; rw [vR5, k5]
    · show regB c.nmem gHead c.nreg gL7 = _; rw [vL7, k5, k2]
  have hctx₁ : ChainCtx P W c₁ dsc C := hctx.transport (ko _ hd.2.2) (fun _ _ => rfl) hA1.ge
  have hgC : ∀ c', GW (chainModel C) (Qof P) N c c' (regArcs N (rs.take (c'.nreg gI))) →
      c'.nreg gC = rs.length := fun c' hg => by
    rw [hg.2.2.2.2.2.1 gC (not_oracle_sw (by unfold gC sw; norm_num) (by unfold gC sw; norm_num))
      (by unfold GSet gC sw; omega) (by unfold gC ALLOC sw; omega), hC]
  refine (IRS.whileP (fun c' => GW (chainModel C) (Qof P) N c c' (regArcs N (rs.take (c'.nreg gI))) ∧
      c'.nreg gI ≤ rs.length ∧ ChainCtx P W c' dsc C) (fun c' => gPot N rs (c'.nreg gI))
    (fun c' hI' ⟨hg, hle, hc'⟩ hlt hr' => ?_) hI₁ ⟨hGW1, by
      rw [show c₁.nreg gI = 0 from vI]; omega, hctx₁⟩
    (by rw [hA1, show c₁.nreg gI = 0 from vI]; unfold gatherK at hroom; unfold gPot; simp at hroom ⊢;
        omega)).mono le_rfl ?_
  · rw [hgC c' hg] at hlt
    refine ⟨regK (N.region (rs.getD (c'.nreg gI) 0)).arcs.length,
      (gReg_irs hI' hK hd hP hNF hNW hB hE hrs hL hLA hg hc' hlt (by
        rw [gPot_succ N rs hlt] at hr'; omega)).mono le_rfl ?_⟩
    rintro c'' ⟨hg'', hi'', hc''⟩
    refine ⟨⟨hg'', by omega, hc''⟩, ?_⟩
    rw [hi'', gPot_succ N rs hlt]
    omega
  · rintro c' ⟨⟨hg, hle, hc'⟩, hnlt⟩
    rw [hgC c' hg] at hnlt
    have : c'.nreg gI = rs.length := by omega
    rw [this, List.take_length] at hg
    exact ⟨hg, hc'⟩

end

end SweepIo

end Chazelle.Core
