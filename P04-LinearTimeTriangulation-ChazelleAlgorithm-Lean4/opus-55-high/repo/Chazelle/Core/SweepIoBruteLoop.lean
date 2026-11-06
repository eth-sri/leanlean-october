module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoLHit3
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.SweepEvPrep
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.SweepIoGather

namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers and code -/
def bX : ℕ := sw 4001
def bN : ℕ := sw 4002
def bA4 : ℕ := sw 4003
def bBase : ℕ := sw 4004
def bT : ℕ := sw 4005

/-- The registers the loop writes outside the oracle bands (besides the allocator). -/
def BSet (r : ℕ) : Prop := (sw 4001 ≤ r ∧ r ≤ sw 4005) ∨ (sw 1016 ≤ r ∧ r ≤ sw 1021)

/-- The head: the number of arcs, the base of the arc records, the output base, the counter. -/
def bHead : List Instr :=
  [.addN bX ztea K1, .loadN bN bX, .addN bX ztea K4, .loadN bA4 bX, .copyN bBase ALLOC,
    .constN bT 0]

/-- Read the ends of arc `bT`. -/
def bRead : List Instr :=
  [.addN bX bT bT, .addN bX bX bX, .addN bX bX bT, .addN bX bA4 bX, .addN bX bX K1, .loadN gS bX,
    .addN bX bX K1, .loadN gS1 bX, .addN bX bX K1, .loadN gE bX, .addN bX bX K1, .loadN gE1 bX]

/-- One arc: read, normalise both ends, store, advance. -/
def bArc : Stmt :=
  .seq (block bRead) (.seq (normS ztiw gS gS1 gO) (.seq (normS ztiw gE gE1 gO)
    (.seq put4 (block [.addN bT bT K1]))))

/-- **The loop** over the arcs. -/
def bLoop : Stmt := .seq (block bHead) (.whileLtN bT bN bArc)

/-- The cost of one arc. -/
def bArcK : ℕ := 22051

/-- The cost of the loop over `A` arcs. -/
def bLoopK (A : ℕ) : ℕ := 6 + ((bArcK + 2) * A + 2)

/-! ## The blocks -/
variable (m f : ℕ → ℕ) {q : ℕ} {C : Chain}
theorem bRead_val (hk1 : f K1 = 1) :
    regB m bRead f gS = m (f bA4 + 5 * f bT + 1) ∧
    regB m bRead f gS1 = m (f bA4 + 5 * f bT + 2) ∧
    regB m bRead f gE = m (f bA4 + 5 * f bT + 3) ∧
    regB m bRead f gE1 = m (f bA4 + 5 * f bT + 4) := by
  zubx
  simp only [bRead, regB, regI, upd, bX, bT, bA4, gS, gS1, gE, gE1, K1, sw]
  grind
theorem bRead_other (h : ¬ BSet q) : regB m bRead f q = f q :=
  regB_other m bRead f (fun i hi => by
    zufbj
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> apply h <;>
      simp [BSet, bX, gS, gS1, gE, gE1, sw])
theorem bRead_other' (h1 : q ≠ bX) (h2 : q ≠ gS) (h3 : q ≠ gS1)
    (h4 : q ≠ gE) (h5 : q ≠ gE1) : regB m bRead f q = f q :=
  regB_other m bRead f (fun i hi => by
    zufbj
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro h <;> subst h <;> simp_all)
theorem bRead_ok (hk1 : f K1 = 1) (hb : f bA4 + 5 * f bT + 4 ≤ W) :
    okB W m bRead f := by
  zubx
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  have hb' : f 244003 + 5 * f 244005 + 4 ≤ W := hb
  simp only [bRead, okB, okI, regI, upd, bX, bT, bA4, gS, gS1, gE, gE1, K1, sw]
  grind
theorem bHead_val (hk1 : f K1 = 1) (hk4 : f K4 = 4) :
    regB m bHead f bN = m ztzlo ∧ regB m bHead f bA4 = m ztxea ∧
    regB m bHead f bBase = f ALLOC ∧ regB m bHead f bT = 0 := by
  zubx
  zudmx
  simp only [bHead, regB, regI, upd, bX, bN, bA4, bBase, bT, K1, K4, ALLOC, sw]
  simp_all
theorem bHead_other (h : ¬ BSet q) : regB m bHead f q = f q :=
  regB_other m bHead f (fun i hi => by
    simp only [bHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> apply h <;>
      simp [BSet, bX, bN, bA4, bBase, bT, sw])
theorem bHead_ok (hk1 : f K1 = 1) (hk4 : f K4 = 4) (hb : f ztea + 4 ≤ W) :
    okB W m bHead f := by
  zubx
  zudmx
  have hb' : f 240003 + 4 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [bHead, okB, okI, regI, upd, bX, bN, bA4, bBase, bT, K1, K4, ALLOC, sw]
  grind

/-! ## The invariant -/

/-- **The state of the loop** after `i` arcs (relative to the entry `cS`). -/
def BW (M : Model) (Q : Polygon) (N : NF) (cS c : Config) (i : ℕ) : Prop :=
  c.nreg bBase = cS.nreg ALLOC ∧ c.nreg bT = i ∧ i ≤ N.arcs.length ∧
    c.nreg bN = N.arcs.length ∧ c.nreg bA4 = cS.nmem (cS.nreg ztea + 4) ∧
    c.nreg ALLOC = cS.nreg ALLOC + 4 * i ∧
    (∀ k, k < i → ShotList.arcAt c.nmem ztvkv k = nArc M Q N k) ∧
    ztimo ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ BSet r → r ≠ ALLOC → c.nreg r = cS.nreg r)
theorem bset_sw20 : ¬ BSet ztiw := by unfold BSet sw; omega
theorem nob_sw {j : ℕ} (h : j < 10000) : bandOf ztgc ∉ oracleBands :=
  not_oracle_sw ztce ztce

/-- The chain context survives the loop. -/
theorem BW.ctx {M : Model} {Q : Polygon} {N : NF} {cS : Config} {i : ℕ} {C : Chain}
    (h : BW M Q N cS c i) (hctx : ChainCtx P W cS ztiw C) : ChainCtx P W c ztiw C :=
  hctx.transport (h.2.2.2.2.2.2.2.2 _ (nob_sw by_norm_num) bset_sw20
    by_decide) h.2.2.2.2.2.2.2.1 (by rw [h.2.2.2.2.2.1]; omega)
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One arc of the loop.** -/
theorem bArc_irs {N : NF} {B E : ℕ} {cS : Config} {i : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W cS ztiw C)
    (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hNW : NFWithin cS.nmem B E N) (hB : cS.nreg ztea = B) (hE : E ≤ cS.nreg ALLOC)
    (hin : BW ztc zta N cS c i) (hi : i < N.arcs.length)
    (hroom : c.nreg ALLOC + bArcK ≤ W) :
    IRS P W c₀ bArc c bArcK (fun c' => BW ztc zta N cS c' ztg) := by
  zuus
  have hctxc := hin.ctx hctx
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hin
  zuclz

  obtain ⟨b1, -, b3, -⟩ := Restore.nf_bounds hNWc
  have vA4 : c.nreg bA4 = c.nmem ztow := by_grind
  have harec := hNA.2.2.2.2.2.2.1 i hi
  have hab := b3 i hi
  obtain ⟨⟨hps, hse, hsy⟩, ⟨hpe, hee, hey⟩⟩ := arc_end_facts hP hNF hi
  zuki
  -- the read block
  have hok : okB W c.nmem bRead c.nreg := bRead_ok _ _ hK₀.2.1 by_omega
  refine IRS.mono (K := bRead.length + (11015 + (11015 + ztsuf))) (IRS.seq
    (IRS.block bRead hI hok) ?_) by_rfl (fun _ h => h)
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem bRead c.nreg } with hc₁
  obtain ⟨r1s, r1s1, r1e, r1e1⟩ := bRead_val c.nmem c.nreg hK₀.2.1
  rw [vA4, w2] at r1s r1s1 r1e r1e1
  have v1s : c₁.nreg gS = (N.arc i).s.edge := by_grind
  have v1s1 : c₁.nreg gS1 = (N.arc i).s.hgt := by_grind
  have v1e : c₁.nreg gE = (N.arc i).e.edge := by_grind
  have v1e1 : c₁.nreg gE1 = (N.arc i).e.hgt := by_grind
  have k1 : ∀ q, ¬ BSet q → c₁.nreg q = c.nreg q := fun q hq => bRead_other _ _ hq
  have hA1 : ztdc := k1 _ ztnvc
  have hctx₁ : ChainCtx P W c₁ _ C :=
    hctxc.transport (k1 _ bset_sw20) by_grind hA1.ge
  -- normalise the start
  have hy1 : c₁.nreg gS < 6 → c₁.nreg gS ≠ 0 → c₁.nreg gS ≠ 2 → c₁.nreg gS ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₁.nreg gS, c₁.nreg gS1⟩).2| < C.radius := by
    zuimy
  refine IRS.seq (normS_exact (normS_irs hI₁
    ztqph hctx₁ ⟨by_decide, by_decide,
      by decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    by_omega ztliv hy1
    (by zvnhf; unfold bArcK at hroom; omega)) ⟨by_decide,
      by decide⟩) ?_
  zucja
  have nb : ∀ j, j < 10000 → bandOf _ ∉ oracleBands := fun j hj => nob_sw hj
  have hctx₂ : ChainCtx P W c₂ _ C := hctx₁.transport
    (k2 _ by_grind by_decide by_decide
      by_decide by_decide)
    by_grind hA2.ge
  have v2e : c₂.nreg gE = (N.arc i).e.edge := by
    rw [k2 gE (nb 1018 by_norm_num) by_decide by_decide
      by_decide by_decide, v1e]
  have v2e1 : c₂.nreg gE1 = (N.arc i).e.hgt := by
    rw [k2 gE1 (nb 1019 by_norm_num) by_decide
      by_decide by_decide
      by_decide, v1e1]
  -- normalise the end
  have hy2 : c₂.nreg gE < 6 → c₂.nreg gE ≠ 0 → c₂.nreg gE ≠ 2 → c₂.nreg gE ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c₂.nreg gE, c₂.nreg gE1⟩).2| < C.radius := by
    zuimz
  refine IRS.seq (normS_exact (normS_irs hI₂
    ztqpi hctx₂ ⟨by_decide, by_decide,
      by decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    by_omega ztlix hy2
    (by zuooy; unfold bArcK at hroom; omega)) ⟨by_decide,
      by decide⟩) ?_
  zucjb
  have v3s := k3 gS (nb 1016 by_norm_num)
    by_decide by_decide
    by_decide by_decide
  have v3s1 := k3 gS1 (nb 1017 by_norm_num)
    by_decide by_decide
    by_decide by_decide
  have ns : (ztrca : WPos) =
      Restore.normOf ztc zta (N.arc i).s := by
    zudvj

    have := (Restore.normOf_facts hps).2.1
    rcases hn : Restore.normOf _ _ (N.arc i).s with ⟨e', h'⟩
    grind
  have ne' : (ztrbz : WPos) =
      Restore.normOf ztc zta (N.arc i).e := by
    zufoa

    have := (Restore.normOf_facts hpe).2.1
    rcases hn : Restore.normOf _ _ (N.arc i).e with ⟨e', h'⟩
    grind
  zuffx

  -- store the record
  refine IRS.seq (put4_irs hI₃ ztvtj (by zupdb; unfold bArcK at hroom; omega)) ?_
  zudfl
  -- the frame from `c` to `c₄`
  have k14 : ∀ q, bandOf q ∉ oracleBands → q ≠ bX → q ≠ gS → q ≠ gS1 → q ≠ gE → q ≠ gE1 →
      q ≠ gO → q ≠ gO + 1 → q ≠ ALLOC → c₄.nreg q = c.nreg q := by
    intro q hq h1 h2 h3 h4 h5 h6 h7 h8
    rw [k4 _ h8, k3 _ hq h5 h6 h7 h8, k2 _ hq h3 h6 h7 h8]
    exact bRead_other' _ _ h1 h2 h3 h4 h5
  zujyx
  have k4T : c₄.nreg bT = i := by
    rw [k14 bT (nb 4005 by_norm_num) by_decide by_decide
      by_decide by_decide
      by_decide by_decide
      by_decide by_decide, w2]
  zuhwy
  have hok5 : okB W c₄.nmem [.addN bT bT K1] c₄.nreg := by
    zuffc

    simp only [okB, okI, bT, K1, sw]
    simp only [Nat.reduceAdd, e1, e3]
    exact ⟨ztgpa, trivial⟩
  zuevs

  have r5 : ∀ q, q ≠ bT → regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c₄.nreg q := fun q h1 =>
    regB_other _ _ _ (fun i hi => by
      zuvx
      rcases hi with rfl; zvmwd; omega)
  have v5T : regB c₄.nmem [.addN bT bT K1] c₄.nreg bT = i + 1 := by
    zuffc

    simp only [regB, regI, upd, bT, K1, sw]
    grind
  have kk :=
    fun q hq h0 h1 h2 h3 h4 h5 h6 h7 h8 => (r5 q h0).trans (k14 q hq h1 h2 h3 h4 h5 h6 h7 h8)
  have kb : ∀ q, bandOf q ∉ oracleBands → ¬ BSet q → q ≠ ALLOC →
      regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c.nreg q := by
    intro q hq hb hqa
    have ne : ∀ g, BSet g → q ≠ g := by_grind
    exact kk q hq (ne _ (by unfold BSet bT sw; omega)) (ne _ (by unfold BSet bX sw; omega))
      (ne _ (by unfold BSet gS sw; omega)) (ne _ (by unfold BSet gS1 sw; omega))
      (ne _ (by unfold BSet gE sw; omega)) (ne _ (by unfold BSet gE1 sw; omega))
      ztkbg ztkbg hqa
  have kreg : ∀ q, (q = bBase ∨ q = bN ∨ q = bA4) →
      regB c₄.nmem [.addN bT bT K1] c₄.nreg q = c.nreg q := by
    zuco
    rcases hq with rfl | rfl | rfl <;>
      exact kk _ (nb _ by_norm_num) by_decide
        by_decide by_decide
        by_decide by_decide
        by_decide by_decide
        by_decide by_decide
  have hA5 : regB c₄.nmem [.addN bT bT K1] c₄.nreg ALLOC = c.nreg ALLOC + 4 := by
    rw [r5 _ by_decide, hA4']
  have hmem5 : c₄.nmem = mem4 c.nmem (cS.nreg ALLOC + 4 * i) ztvnl ztvnm
      ztvnj ztvnk := by_grind
  refine ⟨?_, v5T, hi, ?_, ?_, ?_, fun k hk => ?_, fun a' ha' => ?_, fun q hq hb hqa => ?_⟩
  · show regB _ _ _ bBase = _; rw [kreg _ ztp, w1]
  · show regB _ _ _ bN = _; rw [kreg _ by_omega, w4]
  · show regB _ _ _ bA4 = _; rw [kreg _ by_omega, w5]
  · grind
  · show ShotList.arcAt c₄.nmem _ k = _
    zuduh

    rcases Nat.lt_or_ge k i with hl | hg
    · rw [Restore.arcAt_upd4 hl, w7 k hl]
    · have hk' : k = i := by_omega
      zujpq
      rw [Restore.arcAt_upd4_new]
      zujqr
      grind
  · show c₄.nmem a' = _
    zuduh

    zuby
    rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, w8 a' ha']
  · show regB _ _ _ q = _
    rw [kb q hq hb hqa, w9 q hq hb hqa]
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The loop**: the normalised arcs of `N` at the allocator on entry, base in `bBase`, count
in `bN`. -/
theorem bLoop_irs {N : NF} {B E : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c ztiw C)
    (hP : C.P.Simple) (hNF : IsNF ztc zta N)
    (hNW : NFWithin c.nmem B E N) (hB : c.nreg ztea = B) (hE : E ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + bLoopK N.arcs.length ≤ W) :
    IRS P W c₀ bLoop c (bLoopK N.arcs.length)
      (fun c' => BW ztc zta N c c' N.arcs.length) := by
  zuus
  zuhhh
  zuiwq
  have hok : okB W c.nmem bHead c.nreg := bHead_ok _ _ hK₀.2.1 hK₀.2.2.2.1
    by_omega
  refine (IRS.seq (IRS.block bHead hI hok) ?_).mono by_rfl ztb
  zuer
  obtain ⟨vN, vA4, vB, vT⟩ := bHead_val c.nmem c.nreg hK₀.2.1 hK₀.2.2.2.1
  set A := N.arcs.length with hAd
  have hBW1 : BW ztc zta N c { c with nreg := regB c.nmem bHead c.nreg } 0 := by
    refine ⟨vB, vT, Nat.zero_le _, ?_, vA4, ?_, by_simp_all, by_simp_all,
      fun q _ hq _ => bHead_other _ _ hq⟩
    · show regB _ _ _ bN = _; rw [vN, hB]; exact hNA.2.1
    rfl
  have hT1 : ({ c with nreg := regB c.nmem bHead c.nreg } : Config).nreg bT = 0 := vT
  have hA1 : ({ c with nreg := regB c.nmem bHead c.nreg } : Config).nreg ALLOC = c.nreg ALLOC :=
    bHead_other (q := ALLOC) c.nmem c.nreg ztnvc
  refine (IRS.while (fun c' => ∃ i, BW _ _ N c c' i)
    (fun c' => A - c'.nreg bT) bArcK ?_ ?_ hI₁ ⟨0, hBW1⟩ ?_).mono ?_ ?_
  · rintro c' ⟨i, hw⟩ hlt
    rw [hw.2.1, hw.2.2.2.1] at hlt
    rw [hw.2.1]; omega
  · rintro c' hI' ⟨i, hw⟩ hlt hroom'
    have hi : i < A := by rw [hw.2.1, hw.2.2.2.1] at hlt; omega
    refine (bArc_irs hI' hK hctx hP hNF hNW hB hE hw hi hroom').mono le_rfl
      (fun c'' h => ztbbk)
    rw [h.2.1, hw.2.1]; omega
  · rw [hA1, hT1, Nat.sub_zero]; unfold bLoopK at hroom; omega
  · simp
  · rintro c' ⟨⟨i, hw⟩, hn⟩
    rw [hw.2.1, hw.2.2.2.1] at hn
    have : i = A := by have := hw.2.2.1; omega
    simp_all
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt rayPt_snd)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The shot block preparation: model descriptor, arcs, origin `sO`, direction `qD`, weight bound
`sw 5`, context handle `sw 10`, no holes. -/
def sPrepL (md base cnt : ℕ) : List Instr :=
  [.copyN 241300 md, .copyN 241301 base, .copyN 241302 cnt, .copyN 241303 sO,
    .copyN 241304 ztkep, .copyN 241305 ztkeq, .copyN 241306 qD, .copyN 241307 ztbcb,
    .copyN 241308 ztcwl, .constN 241309 0]

/-- Offer the hit of the shot. -/
def sOffer (dsc tg : ℕ) : Stmt := .ifLtN K0 241320 (offer accA dsc 241321 241322 tg qD) .skip

/-- **The shot from `sO`** and the offer of its hit. -/
def symShot (sh : Stmt) (md base cnt dsc tg : ℕ) : Stmt :=
  .seq (block ztbnm) (.seq ztjmw (sOffer dsc tg))

/-- The cost of the shot and its offer. -/
def symShotK (Fg K : ℕ) : ℕ := 10 + (ShotList.shotCost Fg K + (offerK + 2))

/-- A register usable as an input of `symShot`: in band `bSweep`, outside the shot block and the
accumulator. -/
def SRegOK (r : ℕ) : Prop :=
  240000 ≤ r ∧ r < 250000 ∧ (r < 241300 ∨ 241600 ≤ r) ∧ (r < 242000 ∨ 242012 < r)
variable (m f : ℕ → ℕ)
theorem sPrepL_val {md base cnt : ℕ} (_h1 : md < 241300 ∨ 241309 < md)
    (h2 : base < 241300 ∨ 241309 < base) (h3 : cnt < 241300 ∨ 241309 < cnt) :
    regB m ztbnm f 241300 = f md ∧ regB m ztbnm f 241301 = f base ∧
    regB m ztbnm f 241302 = f cnt ∧ regB m ztbnm f 241303 = f sO ∧
    regB m ztbnm f 241304 = f ztkep ∧
    regB m ztbnm f 241305 = f ztkeq ∧
    regB m ztbnm f 241306 = f qD ∧ regB m ztbnm f 241307 = f ztbcb ∧
    regB m ztbnm f 241308 = f ztcwl ∧ regB m ztbnm f 241309 = 0 ∧
    (∀ q, zteus → regB m ztbnm f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => regB_other _ _ _ (fun i hi => by
    simp only [sPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;>
      omega)⟩ <;>
  · simp only [sPrepL, regB, regI, upd, sO, qD, sw]
    grind
theorem sPrepL_ok (md base cnt : ℕ) (hW : 0 ≤ W) : okB W m ztbnm f := by
  simp only [sPrepL, okB, okI]
  tauto
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The shot from `sO`** and the offer of its hit. -/
theorem symShot_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {H : Host} {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ}
    {s : SymPt} {z : Point} {md base cnt dsc tg : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztc) (hmd : MdFacts P c zthvi H C)
    (hreg : HostRegular P.n H) (hctx : ChainCtx P W c dsc C)
    (harcs : ∀ j, j < c.nreg cnt →
      ShotList.PieceOK ztc zta P.n (ShotList.arcAt c.nmem ztjsf j) ∧
      (chainModel C).arcWt ((chainModel C).key zta (ShotList.arcAt c.nmem ztjsf j).1)
        ((chainModel C).key zta (ShotList.arcAt c.nmem ztjsf j).2) ≤ c₀.nreg ztbcb)
    (hAB : c.nreg base + 4 * c.nreg cnt ≤ c.nreg ALLOC)
    (hs : SymPtIn c sO s) (hsl : s.Lt P.n) (hz : s.eval zta = z)
    (hzD : z ∈ C.dom) (hz1 : |z.1| < C.radius) (hz2 : |z.2| < C.radius) (hzt : z.2 ≤ C.top.2)
    (hacc : AccOK P accA Mod R₀ z ztba L c) (htag : c.nreg tg ≤ 2)
    (hMod : Mod (c.nreg tg) = C) (hR : C.radius = R₀)
    (hr : SRegOK md ∧ SRegOK base ∧ SRegOK cnt ∧ SRegOK dsc ∧ SRegOK tg)
    (hroom : c.nreg ALLOC + symShotK ztwiu ztqiq ≤ W) :
    IRS P W c₀ (symShot sh md base cnt dsc tg) c (symShotK ztwiu ztqiq)
      (fun c' => ∃ L', AccOK P accA Mod R₀ z ztba L' c' ∧
        (L' = L ∨ ∃ τ, L' = insert τ L ∧ 0 < τ ∧ OnCB C ztwod) ∧
        (FreeAt C z ztba →
          rayPt z ztba (C.hitParam z ztba) ∈
            ShotList.loSet ztc zta c.nmem ztjsf ztqiq [] →
          C.hitParam z ztba ∈ L') ∧
        (∀ r, bandOf r ∉ oracleBands → ¬ ztbmg → ztbni →
          r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuus
  zufam
  set K := c.nreg cnt with hKd
  zusw
  zumce
  obtain ⟨rmd, rbase, rcnt, rdsc, rtg⟩ := hr
  -- 1. prepare the shot block
  refine IRS.seq
    (IRS.block _ hI (sPrepL_ok _ _ _ _ _ ztbg)) ?_ |>.mono
      by_rfl ztb
  zugn
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, po⟩ := sPrepL_val c.nmem c.nreg
    (md := md) (base := base) (cnt := cnt) (by unfold SRegOK at rmd; omega)
    (by unfold SRegOK at rbase; omega) (by unfold SRegOK at rcnt; omega)
  zull
  have q1 : ∀ q, zteus → c₁.nreg q = c.nreg q := by_simp_all
  zuhwh
  have c0 : c₁.nreg RS = c.nreg md := by zvmwl; exact p0
  have c1' : c₁.nreg ztnoq = c.nreg base := by zvmwl; exact p1
  have c2' : ztyyo := by zvmwl; exact p2
  have c6 : c₁.nreg ztnor = c.nreg qD := by zvmwl; exact p6
  have c7 : ztylo := by
    zury
  have c8 : ztylp := by
    zurz
  zuepo
  have hhl : ztrfv := by
    unfold ShotList.holeList; simp_all
  have hori : ztlae :=
    SweepIo.symPtIn_copy hs ztmdm ztmdn
      ztmdo
  obtain ⟨hmd0, hmdC, hmdW, hmdA⟩ := hmd
  -- 2. the precondition of the shot
  zuiyh
  have hX1 : ztyll := by
    zuexb

  have hcap1 : ztxtf := by
    zubeh
  have hev : Origin.eval ztc _ ztvco = z := hz
  have pre : ztiys := by
    refine ⟨hG, hWh, hX1, hcap1, by_grind, by_grind,
      by omega, by_omega, H, C, by_grind,
      fun H' hH' => ?_, hOk, hctx.2.2.2.2.2, fun j hj => ?_, fun j hj => ?_, .sym s, hori, hsl,
      Or.inr ⟨by rw [hev]; exact innerPt_box C hz1 hz2, by_grind⟩,
      by grind, ?_⟩
    · rw [c0, hm1] at hH'
      rw [← NFLoc.hostAt_unique hmdC.1 hH']
      omega
    · grind
    · omega
    · rw [hhl, hev]
      zujbj
      exact absurd hpt (walk_ne_of_dom C hP hzD hp ht0 ht1)
  -- 3. the shot
  refine IRS.seq (shot_irs hsh hBs hXl hI₁ pre (by
    zvnja; unfold symShotK at hroom; omega)) ?_ |>.mono (by zuooz) (fun _ h => h)
  zubse
  have hmdC1 : ztzov := by
    grind
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost ztc ztuvq hmdC1 hori
  rw [c6, hev] at hyes hno
  zutr

  have hAoff : A ⊆ C.domᶜ := by
    zucdk
    have := hhi hw
    zuwe

    zuisu
  -- registers after the shot
  have keep2 :=
    fun r h1 h2 h3 => k2 r ztsg ztu h3
  have keepc :=
    fun r h1 h2 h3 => (keep2 r h1 h2 by_omega).trans ztkdb
  have t2 := keepc _ rtg.1 rtg.2.1 (by unfold RS; have := rtg.2.2.1; omega)
  have d2 : c₂.nreg qD = c.nreg qD := keepc _ by_decide
    by_decide by_decide
  have cd2 :=
    keepc _ rdsc.1 rdsc.2.1 (by unfold RS; have := rdsc.2.2.1; omega)
  have a2 : ztyab := fun j hj =>
    keepc _ zthk zthk ztnvn
  zuljj
  zuftj
  have hm2' : ztux := fun a ha => by
    zucjp
  zuixq
  zudzv
  -- the completeness of the shot
  have complete : FreeAt C z σ →
      rayPt z σ ztbtm ∈
        ShotList.loSet ztc zta c.nmem ztjsf K [] →
      c₂.nreg 241320 = 1 ∧ ∀ t, FirstHit A z σ t → t = C.hitParam z σ := by
    intro hf hlo'
    zuixb

    zuct
    zucss

  have frame2 : ∀ r, bandOf r ∉ oracleBands → ¬ ztbmg → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r hr hrs hrA => by
    zuobv; exact q1 r zthft
  unfold sOffer
  zuhta
  · zugex
    have h1 : ztpne := by have : ztpnf := hfl; omega
    zublb
    have hroom2 : c₂.nreg ALLOC + offerK ≤ W := by
      zvnja at hAb; unfold symShotK at hroom; omega
    refine (IRS.ifT by_omega (offer_irs hI₂ hK hG
      ztdha
      ⟨by_decide, by_decide⟩
      ⟨rdsc.1, rdsc.2.1, by_norm_num, by_norm_num, by_norm_num, by_norm_num, rtg.1, rtg.2.1,
        by decide, by_decide⟩
      ⟨by unfold accA; have := rdsc.2.2.2; tauto, by_decide,
        by decide, by unfold accA; have := rtg.2.2.2; tauto,
        by decide⟩
      ztntg by_omega by_grind
      by_grind ztdmd
      ztdmd ztjqh
      by_grind hroom2)).mono by_omega ?_
    rintro c' ⟨hacc', k3, hA3, hm3⟩
    rw [d2] at hacc'
    refine ⟨insert t L, hacc', Or.inr ⟨t, rfl, hFH.1, ?_⟩, fun hf hlo' => ?_,
      fun r hr hrs hra hrA => ?_, hA2'.trans hA3, fun a ha => by
        zuopa; exact hm2' a ha⟩
    · rw [← hpos2]
      refine walk_hit_onCB C _ he2 hpp2 ?_
      rw [hpos2, rayPt_snd]; omega
    · obtain ⟨-, ht⟩ := complete hf hlo'
      rw [← ht t hFH]
      simp
    · rw [k3 r hr hra hrA]; exact frame2 r hr hrs hrA
  · refine (IRS.ifF hflag (IRS.skip (K := offerK) hI₂ ⟨L, hacc2, Or.inl rfl, fun hf hlo' => ?_,
      fun r hr hrs hra hrA => frame2 r hr hrs hrA, hA2', hm2'⟩)).mono by_omega (fun _ h => h)
    grind
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def bruteS (sh : Stmt) : Stmt := .seq bLoop (symShot sh ztbbz bBase bN ztiw K0)

/-- The cost constant. -/
def bruteK : ℕ := 600000
theorem brute_cost (A Fg : ℕ) : bLoopK A + symShotK Fg A ≤ bruteK * ztbo * ztclk := by
  unfold bLoopK symShotK ShotList.shotCost bArcK offerK bruteK
  grind
theorem sregOK_sw {j : ℕ} (h1 : j < 1300 ∨ 1600 ≤ j) (h2 : j < 2000 ∨ 2012 < j) (h3 : j < 10000) :
    SRegOK ztgc := by
  unfold SRegOK sw; omega
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The brute-force shot meets its contract.** -/
theorem bruteSpec : BruteSpec := by
  refine ⟨bruteS, bruteK, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L s z hA hI hs hsl hz hzC hz1 hz2 hzt
    hbL hacc hroom
  have hcost := brute_cost N₁.arcs.length ztwiu
  have hP : J.left.P.Simple := hA.hP
  have hNF := hA.hNF₁
  have hNW : NFWithin c.nmem ztxnx E N₁ :=
    hA.hN₁.transport (fun a ha => hI.hm a (by have := hA.hE; omega))
  have hroom' : c.nreg ALLOC + (bLoopK N₁.arcs.length + symShotK ztwiu N₁.arcs.length) ≤ W := by
    omega
  refine (IRS.seq (K₂ := symShotK ztwiu N₁.arcs.length) (bLoop_irs hI hA.hK (hA.ctxL hI) hP hNF hNW
    ztdhk (hA.hE.trans hI.hA) (le_trans ztzuk hroom')) ?_).mono
    hcost ztb
  rintro c₁ hI₁ hA₁ hA₁' hBW
  zucig
  zufxc
  have keep : ∀ j, j < 10000 → ¬ BSet ztgc → c₁.nreg ztgc = c.nreg ztgc := fun j hj hb =>
    w9 _ zttua hb ztbpx
  have a1 : ∀ j, j ≤ 12 → c₁.nreg ztbzh = c.nreg ztbzh := fun j hj => by
    have e : accA + j = sw ztsst := by unfold accA sw; omega
    zvmwe; exact keep ztsst by_omega ztbfz
  have d1 : ztizm := keep 3212 by_norm_num ztbfz
  have hacc1 : AccOK P accA ztdm J.whole.radius z
      ztqma L c₁ := by rw [d1]; exact hacc.transport a1
  have hs1 : SymPtIn c₁ sO s := symPtIn_copy hs (keep 3231 by_norm_num ztbfz)
    (keep 3232 by_norm_num ztbfz)
    (keep 3233 by_norm_num ztbfz)
  have hK0 : zteib := (hA.hK.fix hI₁).1
  have hMod : ModB J ztcpq ztcpr (c₁.nreg K0) = J.left := by
    rw [hK0, hbL]; rfl
  have hzD : z ∈ J.left.dom := mem_dom_of J.left hzt hz1 hz2 hzC
  have hN1 : c₁.nreg bN = N₁.arcs.length := w4
  have harcs : ∀ j, j < c₁.nreg bN →
      ShotList.PieceOK ztbw zta P.n (ShotList.arcAt c₁.nmem ztqki j) ∧
      (chainModel J.left).arcWt
        ((chainModel J.left).key zta (ShotList.arcAt c₁.nmem ztqki j).1)
        ((chainModel J.left).key zta (ShotList.arcAt c₁.nmem ztqki j).2) ≤
        c₀.nreg ztbcb := by
    zun
    zuels

    exact nArc_piece hP hNF hA.hsg₁ hj
  refine (symShot_irs (C := J.left) (H := H) (md := sw 30) (base := bBase) (cnt := bN)
    (dsc := sw 20) (tg := K0) hsh hBs hXl hI₁ hA.hK hA.hG hA.hWh hA.hX hA.hcap hA.hOk₁
    (hA.mdL hI₁) hA.hostReg (hA.ctxL hI₁) harcs by_omega hs1 hsl hz hzD hz1 hz2 hzt
    hacc1 by_omega hMod rfl
    ⟨sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num⟩
    by_grind).mono (by rw [hN1]) ?_
  rintro c' ⟨L', hacc', hL', hcomp, k2, hA2, hm2⟩
  rw [d1] at hacc' hcomp hL'
  refine ⟨⟨L', hacc', ?_, fun τ hτ => ?_, fun hf => ?_⟩, ?_, ?_, fun a ha => ?_⟩
  · zuflj
    · simp
    simp
  · zuejr
    · grind
    grind
  · refine hcomp hf ?_
    obtain ⟨p, t, hp, ht0, ht1, ⟨j, hj, hin⟩, hpt⟩ :=
      exit_in_arcs J.left hP hNF (Q := Qof P) (dirOf_cases _) hzt hf
    refine ⟨p, t, hp, ht0, ht1, ztrdp, fun g hg => absurd hg
      (List.not_mem_nil), hpt.symm⟩
    zupl

  · intro r hr h1 h2 h3 hrA
    rw [k2 r hr (fun h => h1 (by unfold RS at h; unfold sw; omega))
      ztmer hrA]
    exact w9 r hr (fun h => by unfold BSet sw at h; unfold sw at h1 h3; omega) hrA
  · omega
  grind
open Sweep
open Chazelle.Chain (sidePt sideLeft sideInArc sidePrev sideNext)
variable {J : Merge.Junction}

/-! ## Candidates -/
variable {x : Point} {z : Point} {P : Polygon} {C : Chain}
theorem onCB_left (h : OnCB J.left x) : OnCB J.whole x := by
  zude
  · exact Or.inl ztpzf
  · tauto
  tauto
theorem onCB_right (h : OnCB J.right x) : OnCB J.whole x := by
  zude
  · zulel
  · tauto
  tauto

/-- **Both bits `1`**: the first hit of `C` is the earlier of the first hits of `C₁`, `C₂`. -/
theorem whole_eq_min (h₁ : z.2 ≤ J.left.top.2) (h₂ : z.2 ≤ J.right.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam z σ = min ztnlt ztsyl := by
  rw [whole_hitParam_eq_min J ztvwv hσ, left_hitParam_eq J h₁,
    right_hitParam_eq J h₂]

/-- **Above the top of `C₂`**: the first hit of `C` is the first hit of `C₁`. -/
theorem whole_eq_left (h₁ : z.2 ≤ J.left.top.2) (h₂ : J.right.top.2 < z.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : J.whole.hitParam z σ = J.left.hitParam z σ := by
  rw [whole_hitParam_eq_min J ztvwv hσ, left_hitParam_eq J h₁,
    rayHit_eq_empty_of_above J.right h₂]
  refine min_eq_left ?_
  rw [← left_hitParam_eq J h₁]
  exact Merge.rayHit_anti ztjmt z hσ

/-- A membership of the first hit of `C` from those of `C₁` and `C₂` (both bits `1`). -/
theorem whole_mem_of_both (h₁ : z.2 ≤ J.left.top.2) (h₂ : z.2 ≤ J.right.top.2)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {L : Set ℝ} (hl : J.left.hitParam z σ ∈ L)
    (hr : J.right.hitParam z σ ∈ L) : J.whole.hitParam z σ ∈ L := by
  rw [whole_eq_min h₁ h₂ hσ]
  grind

/-- Freeness for `C` gives freeness for `C₂` below the top of `C₂`. -/
theorem freeAt_right_of_whole (h₂ : z.2 ≤ J.right.top.2) {σ : ℝ}
    (h : FreeAt J.whole z σ) : FreeAt J.right z σ := by
  zucfc

  zuhcr

/-! ## The log entry -/

/-- **The log entry of a key on the `C₁` part exists.** -/
theorem logIdx_exists {Q : Polygon} {N : NF} {S₂ : Set ztf}
    {ls : List ztck} (hlog : LogOK J S₂ (logOf J Q N ls)) {x : ℝ}
    (hx : (Lst J : ℝ) ≤ oW J x) : ∃ i, LogIdx J Q N ls x i := by
  obtain ⟨hne, -, hhead, -⟩ := hlog
  have hlen : 0 < ls.length := by
    zugsa
    · tauto
    · simp
  have h0 : oW J (logKey J Q N ls 0) ≤ oW J x := by
    zugsa
    · simp_all
    · simp only [logOf, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq,
        forall_eq'] at hhead
      unfold logKey
      simp only [logOf, List.map_cons, List.getD_cons_zero]
      simp_all
  classical
  set p : ℕ → Prop := fun i => oW J ztpcq ≤ oW J x
  refine ⟨Nat.findGreatest p ztocz, by
    have := Nat.findGreatest_le (P := p) ztocz; omega,
    Nat.findGreatest_spec (P := p) (m := 0) ztbg h0, fun hi => ?_⟩
  have := Nat.findGreatest_is_greatest (P := p) (n := ls.length - 1) (k := Nat.findGreatest p ztocz + 1)
    by_omega by_omega
  simp only [p, not_le] at this
  zufep

/-! ## The shared vertex among the positions of `M₁` -/
theorem cstL_one : cstL J 1 = 6 + tpos J.left J.m₁ := rfl
theorem cstR_one : cstR J 1 = 6 + tpos J.right 0 := rfl

/-- **The shared vertex in the model of `C₁`**: parameter `0`, and the edge is `cstL 1` or the
last walk edge when `cstL 1 = 6`. -/
theorem shared_iff₁ (hP : J.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.left).W.n) (h0 : 0 ≤ (chainModel J.left).param Q x)
    (h1 : (chainModel J.left).param Q x < 1) :
    (chainModel J.left).pos Q x = J.shared ↔ (chainModel J.left).param Q x = 0 ∧
      (x.edge = cstL J 1 ∨ (x.edge + 1 = 2 * J.m₁ + 7 ∧ cstL J 1 = 6)) := by
  have e : J.shared = J.left.vertex J.left.m := rfl
  rw [e, atEnd_iff J.left hP ztbt Q hx h0 h1, cstL_one]
  simp

/-! ## The geometric conditions of the local hits -/
theorem sideChain_zero' : sideChain J 0 = J.left := ite_eq_left rfl

/-- **The query position** of side `0` satisfies `LHGeo` in the model of `C₁`. -/
theorem lhGeo_query {q : ℕ × ℕ × ℕ} (hq : QueryOK J zta 0 q)
    (hht : ((chainModel J.left).pos zta ztpo).2 = ((Qof P).vtx zteut).2) :
    LHGeo P J.left ztpo q.2.2 := by
  zuc
  obtain ⟨-, hh1, hh2, -, -, htop, hsec⟩ := hq
  simp only [sideChain_zero'] at htop hsec
  refine ⟨q.2.1 - 1, by_simp_all, by_omega, hht.symm, ?_, htop⟩
  have e : rayPt ((chainModel J.left).pos zta ztpo) zthwj 1 =
      (((chainModel J.left).pos zta ztpo).1 + dirOf q.2.2,
        ((chainModel J.left).pos zta ztpo).2) := by
    zugyz
  simp_all

/-- `sideLeft` at a position depends only on the edge ends when the parameter is positive. -/
theorem sideLeft_congr {W W' : Polygon} {p p' : ℕ} {t : ℝ} (ht : t ≠ 0)
    (ha : W.vtx p = W'.vtx p') (hb : W.vtx ztwjb = W'.vtx ztgwe)
    (x : Point) : sideLeft W p t x ↔ sideLeft W' p' t x := by
  zulce

/-- **The box twin**: a query position on a vertical side of the box satisfies `LHGeo` in the
model of `C₂` when it is not above the top of `C₂`. -/
theorem lhGeo_box {x : WPos} {d : ℕ} (he : x.edge = 1 ∨ x.edge = 3)
    (hg : LHGeo P J.left x d)
    (hy : |((chainModel J.left).pos zta x).2| < J.left.radius)
    (h₂ : ((chainModel J.left).pos zta x).2 ≤ J.right.top.2) :
    LHGeo P J.right x d ∧
      (chainModel J.right).pos zta x = (chainModel J.left).pos zta x := by
  obtain ⟨ha, hb, hpar, hpos⟩ := boxTwin_pos (C₁ := J.left) (C₂ := J.right) rfl he zta x.hgt
  zudrd
  have hR := J.left.radius_pos
  have ht : (chainModel J.left).param zta x ≠ 0 := by
    zubww
    have e : (chainModel J.left).pos zta x = (chainModel J.left).wa x.edge := by
      zuckw
    zugcs
    have hW : (chainModel J.left).W = J.left.sideWalk J.left.sideBeta := rfl
    zucfd

    · rw [J.left.sideWalk_vtx_one] at hy; grind
    · rw [J.left.sideWalk_vtx_three] at hy; grind
  have hx : (chainModel J.right).pos zta zthnv =
      (chainModel J.left).pos zta zthnv := hpos.symm
  refine ⟨ztklg, hx⟩
  · zukwl
  · rw [hx, show (chainModel J.right).param zta x = (chainModel J.left).param zta x
      from hpar.symm]
    zugkb
  · zvnly; exact h₂

/-- **An arrival position** at a point with a height code naming its height satisfies `LHGeo`
with that code. -/
theorem lhGeo_arr {z : Point} {σ : ℝ} {p : ℕ} {t : ℝ}
    (harr : Arrival (chainModel C).W z (-σ) p t) {h : ℕ} (hh : h < P.n)
    (hhz : ((Qof P).vtx h).2 = z.2) (htop : z.2 ≤ C.top.2) {d : ℕ} (hd : dirOf d = σ) :
    LHGeo P C ztdw d ∧ (chainModel C).pos zta ztdw = z ∧
      (chainModel C).param zta ztdw = t := by
  zueiv
  zubvb
  have hsec' : ztwnr := by
    simp_all
  zubdu

/-! ## Positions -/

/-- A position of the class off the box is a point of the chain. -/
theorem posClass_mem {Q : Polygon} {x : WPos} (hx : PosClass C Q x) (h6 : 6 ≤ x.edge)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x ∈ C.set := by
  zucn
  rw [pos_eq_sidePt' C Q x, hW]
  rcases hx with (h | h) | ⟨-, hlt⟩ | ⟨hend, hz⟩
  · omega
  · omega
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := (chainModel C).param Q x)
      by_omega ztczk h0 h1
    simp_all
  · rw [hend, hz]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl ztdnl le_rfl
      one_pos

/-- **The shared vertex in the model of `C₂`**: the position `(cstR 1, h + 1)` (`cstR 1` the tour
edge starting at vertex `0` of `C₂`) with a height code naming the height of the shared vertex. -/
theorem shared_pos₂ (hP : J.P.Simple) (Q : Polygon) {h : ℕ} (hh : (Q.vtx h).2 = J.shared.2) :
    cstR J 1 < (chainModel J.right).W.n ∧
      (chainModel J.right).param Q zthms = 0 ∧
      (chainModel J.right).pos Q zthms = J.shared := by
  zudhu
  zubau
  have hlt : ztmuz := by rw [cstR_one, hn]; omega
  have hwa : (chainModel J.right).wa zttim = J.shared := by
    have := (vtx_pos_iff J.right hP (k := 0) ztbg (p := cstR J 1) hlt le_rfl
      one_pos).2 ⟨rfl, tpos J.right 0, by_omega, by rw [cstR_one]; ring,
        (endIdx J.right ztp by_omega).2 ztp⟩
    rw [Chazelle.Chain.sidePt_zero] at this
    tauto
  have hpar : (chainModel J.right).param Q zthms = 0 := by
    zufde
    simp_all
  refine ⟨hlt, hpar, ?_⟩
  zuckw

/-- A position on a vertical side of the box is not a point of the chain. -/
theorem box_not_mem {Q : Polygon} {x : WPos} (he : x.edge = 1 ∨ x.edge = 3)
    (hm : (chainModel C).pos Q x ∈ C.set) : False := by
  zubo
  have hb := (C.abs_le_coordBound_of_mem_set hm).1
  have hc := C.coordBound_lt_radius
  rw [pos_eq_sidePt' C Q x] at hb
  zucsg
  zucn
  grind
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
open ShotList (chainDescAt_copy chainWF_copy)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The facts of one side -/

/-- **The facts of `c₀` about one side** (chain `C`, normal form `N` with bound `E`): the chain
descriptor in `cd`, the model descriptor in `md` holding a copy of it, the normal form in `nf`,
the walk length in `nr`. -/
structure SideD (P : Polygon) (W : ℕ) (Ok : Polygon → Model → Prop) (c₀ : Config) (C : Chain)
    (N : NF) (E md cd nf nr : ℕ) : Prop where
  hctx : ChainCtx P W c₀ cd C
  hmd : ModelDescAt c₀.nmem ztmhz zta ztc
  hmwf : ModelDescWF P ztdq c₀.nmem ztmhz
  hcopy : ∀ j, j < 5 → c₀.nmem ztpal = c₀.nmem ztroa
  hNW : NFWithin c₀.nmem (c₀.nreg nf) E N
  hE : E ≤ c₀.nreg ALLOC
  hNF : IsNF ztc zta N
  hOk : Ok P ztc
  hsg : (chainModel C).Semigranular ztwjq ztq
  hdeg : (chainModel C).DegLe ztwjq zto
  hbig : N.arcs.length < 2 ^ c₀.nreg TLR
  hnr : c₀.nreg nr = 2 * C.m + 7
theorem chainModel_ne_int (C : Chain) (Q : Polygon) : chainModel C ≠ interiorModel Q := by
  zuq
  have := congrArg (fun M : Model => M.counted 0) h
  zuckl
section AEnv
variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}

/-- The chain context of a chain descriptor of the stage-0 state. -/
theorem ctx_of_aenv (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {C : Chain} {cd : ℕ}
    (hC : ChainDescAt c₀.nmem ztvmi zta H C)
    (hw : ChainWF P ztdq c₀.nmem ztvmi) (hP : C.P.Simple)
    (hm : C.m ≤ J.whole.m) : ChainCtx P W c₀ cd C := by
  zuddr
  refine ⟨hA.hG, hA.hWh, hw, ⟨H, hC, hJW.2.2.2 H hJ.2.2.1⟩, hP, ?_⟩
  have := hA.hWm; omega

/-- **The side of `C₁`.** -/
theorem sideD₁ (hA : AEnv P W X Ok J H N₁ N₂ E c₀) :
    SideD P W Ok c₀ J.left N₁ E ztbbz ztiw ztea ztna := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -, -, -, -, -, -, h33, -, -, d30, w30, -, -⟩ := hA.hst
  exact ⟨ctx_of_aenv hA d20 w20 hA.hP by_simp, d30, w30, hA.hmd₁,
    hA.hN₁, hA.hE, hA.hNF₁, hA.hOk₁, hA.hsg₁, hA.hdeg₁, hA.hbig₁, h33⟩

/-- **The side of `C₂`.** -/
theorem sideD₂ (hA : AEnv P W X Ok J H N₁ N₂ E c₀) :
    SideD P W Ok c₀ J.right N₂ E ztqm zted ztbz zthy := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -, -, -, -, -, h34, -, -, -, d31, w31⟩ := hA.hst
  exact ⟨ctx_of_aenv hA d21 w21 hA.hP by_simp, d31, w31, hA.hmd₂,
    hA.hN₂, hA.hE, hA.hNF₂, hA.hOk₂, hA.hsg₂, hA.hdeg₂, hA.hbig₂, h34⟩
end AEnv

/-- **The local-hit context** at a configuration whose `lMD`, `lCD`, `lNF` hold the model
descriptor, its chain descriptor and the normal form of a side. -/
theorem lctx_of {Ok : Polygon → Model → Prop} {C : Chain} {N : NF} {E md cd nf nr : ℕ}
    (hS : SideD P W Ok c₀ C N E md cd nf nr) (hI : IInv W c₀ c)
    (htab : ∀ j, j < c₀.nreg TLR → c₀.nmem zthwa = 2 ^ j)
    (hTB : E ≤ c₀.nreg TBR) (hTW : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC)
    (hmd : c.nreg lMD = c₀.nreg md) (hcd : c.nreg lCD = c₀.nreg md + 1)
    (hnf : c.nreg lNF = c₀.nreg nf) : LCtx P W C N E c := by
  obtain ⟨hG, hWh, hwf, ⟨H, hC, hreg⟩, hP, hWm⟩ := hS.hctx
  have hmw := hS.hmwf
  zuta
  have hm0 : c₀.nmem ztmhz = 0 := by
    rcases hS.hmd with ⟨h0, -⟩ | ⟨-, -, hI'⟩
    · zulyi
    · exact absurd hI' (chainModel_ne_int C _)
  have he := hI.hm
  have hc : ∀ j, j < 5 → c.nmem ztpal = c₀.nmem ztroa := fun j hj => by
    zunlh; exact hS.hcopy j hj
  have hC' : ChainDescAt c.nmem _ _ H C := chainDescAt_copy hC hEb he hc
  have hw' : ChainWF P _ c.nmem _ :=
    chainWF_copy hwf hC he hc (by have := hmw.1; have := hI.hA; omega) hI.hA
  have hm0' : c.nmem ztmhz = 0 := by zunlh; omega
  have eTB : ztgug := hI.hin _ by_trivial
  have eTL : ztguh := hI.hin _ by_trivial
  refine ⟨hG, hWh, ⟨hG, hWh, by_simp_all, by_grind, hP, hWm⟩,
    by omega, by rw [hmd]; exact Or.inl by_grind,
    by rw [hmd]; exact ⟨by have := hmw.1; have := hI.hA; omega, by_simp_all⟩,
    by simp_all, hP, by rw [hnf]; exact hS.hNW.transport by_grind, by have := hS.hE; have := hI.hA; omega, hS.hNF,
    fun j hj => ?_, by rw [eTL]; exact hS.hbig, by_omega,
    by zunqt; have := hI.hA; omega⟩
  grind

/-! ## The inputs of the local hit -/

/-- The inputs of the local hit: model descriptor `md` (its chain descriptor at the next
address), normal form `nf`, walk length `nr`, the position `(e, qH)`, the direction `qD`, the
tag `t`. -/
def setL (md nf nr e t : ℕ) : List Instr :=
  [.copyN lMD md, .addN lCD lMD K1, .copyN lNF nf, .copyN lE e, .copyN lH qH, .copyN lD qD,
    .copyN lN nr, .constN lT t]

/-- A register outside the inputs of the local hit. -/
def OutL (r : ℕ) : Prop := r < sw 1100 ∨ sw 1107 < r
variable (m f : ℕ → ℕ) {md nf nr e t : ℕ}
theorem setL_val (hnf : OutL nf) (hnr : OutL nr)
    (he : OutL e) :
    regB m ztkg f lMD = f md ∧ regB m ztkg f lCD = f md + f K1 ∧
    regB m ztkg f lNF = f nf ∧ regB m ztkg f lE = f e ∧
    regB m ztkg f lH = f qH ∧ regB m ztkg f lD = f qD ∧
    regB m ztkg f lN = f nr ∧ regB m ztkg f lT = t ∧
    ztxpe := by
  unfold OutL sw at hnf hnr he
  refine ztfcx <;>
  · try unfold OutL sw at hq
    simp (disch := omega) only [setL, regB, regI, lMD, lCD, lNF, lE, lH, lD, lN, lT, K1, qH, qD,
      sw, Nat.reduceAdd, upd_same, upd_other]
theorem setL_ok (_hmd : OutL md) (hW : f md + 1 ≤ W)
    (hk : f K1 = 1) (ht : t ≤ W) : okB W m ztkg f := by
  have s : ztxtp := fun j h1 h2 =>
    iscr_sw ztce ztce
  zueey

  refine ⟨s 1100 le_rfl by_norm_num, ztpfr,
    s 1102 by_norm_num by_norm_num, s 1103 by_norm_num by_norm_num,
    s 1104 by_norm_num by_norm_num, s 1105 by_norm_num by_norm_num,
    s 1106 by_norm_num by_norm_num, ztpfs, trivial⟩
  have e1 : upd f lMD _ lMD = f md := upd_same _ _ _
  zufsy

/-- **A local hit with its inputs.** -/
def lhs (md nf nr e t : ℕ) (sh : Stmt) : Stmt := .seq ztbafr ztkak

/-- The cost of `lhs`. -/
def lhsK (T Fg D : ℕ) : ℕ := 8 + localK T Fg ztef D

/-! ## Region bounds -/

/-- **Arcs and exit chords of the regions** of a normal form of degree `≤ D`. -/
theorem region_bounds' {C : Chain} {Q : Polygon} {N : NF} {D : ℕ} (hP : C.P.Simple)
    (hNF : IsNF ztc Q N) (hdeg : (chainModel C).DegLe ztwjh D) :
    ztgsg ∧
      ztibz := by
  zubtj

  have hregs : Restore.NFRegs _ Q N reg := zteyk
  zuiv
  refine ztkld
  · have := Restore.arcs_le_deg hGM hNF hregs hr
    have := hdeg _ ztdhm
    omega
  · have := Restore.chords_le_deg hNF hregs hr
    have := hdeg _ ztdhm
    omega

/-! ## The run step -/
section Run
variable {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
  {N₁ N₂ : NF} {E : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The local hit with its inputs**: from `AEnv` and the facts `SideD` of a side, at the
position `x = (e, qH)` of its chain model. -/
theorem lhs_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok)
    (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal) (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
    {C : Chain} {N : NF} {md cd nf nr e t : ℕ} (hS : SideD P W Ok c₀ C N E md cd nf nr)
    (hfix : IFix md ∧ IFix nf ∧ IFix nr) (heo : OutL e) (hI : IInv W c₀ c)
    {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ} {z : Point}
    (he : c.nreg e < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztbte)
    (hz : (chainModel C).pos zta ztbte = z)
    (hy : |z.2| < C.radius)
    (hloc : ztdmv ∨ ztmah)
    (hacc : AccOK P accA Mod R₀ z ztba L c) (ht : t ≤ 2) (hMod : Mod t = C)
    (hR : C.radius = R₀)
    (hroom : c.nreg ALLOC + lhsK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ ztocx c
      ztbajg (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z ztba L' c' ∧ L ⊆ L' ∧
        ztbakq ∧
        ztxvf) ∧
      ztcfn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zubbx

  have hmdW : ztrgf := by
    zuksm
    have := hS.hmwf.1; have := hI.hA; omega
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, vo⟩ :=
    setL_val c.nmem c.nreg (md := md) (t := t) zttux zttuy heo
  unfold lhs
  refine IRS.seq
    ((IRS.block _ hI (setL_ok c.nmem c.nreg by_simp_all hmdW hK.2.1
      (by unfold lhsK at hroom; omega))).mono by_rfl (fun _ h => h)) ?_
  zubun
  have hm₁ : ztwh := by zvmxj
  have hreg₁ : c₁.nreg = regB c.nmem ztkg c.nreg := by zvmxj
  rw [← hreg₁] at v1 v2 v3 v4 v5 v6 v7 v8 vo
  have r1 : ztlby := by_omega
  have hL := lctx_of hS hI₁ hA.htab hA.hTB hA.hTW
    (by zuobw)
    (by zunud)
    (by zuobx)
  obtain ⟨hAr, hCh⟩ := region_bounds' hL.hP hS.hNF hS.hdeg
  zuhvu
  have hacc₁ : AccOK P accA Mod R₀ ztymu
      ztqlz L c₁ := by
    rw [v4, v5, v6, hz]
    exact hacc.transport zthhb
  have h := localHit_irs hsh hBs hXl hI₁ hA.hK hL hA.hX hA.hcap hS.hOk hS.hsg hAr hCh rfl rfl rfl
    by_simp_all by_simp_all by_simp_all
    by_simp_all
    hacc₁ by_omega by_simp_all hR
    (by rw [v7, hI.hin _ hfr]; exact hS.hnr)
    (by rw [eTL]; unfold lhsK at hroom; omega)
  zubif

  rw [v4, v5, v6, hz] at a' g'
  rw [v4, v5, v6] at geo'
  zvncr at geo'
  have hAA := r1 ALLOC ztnvi
  refine ⟨by_grind, fun r h1 h2 h3 => ?_, by_omega,
    fun a ha => ?_⟩
  · zufmv

  grind
end Run
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The accumulator and the frames -/

/-- **The accumulator holds good candidates** (tags under the bits of `c`). -/
def AccSt (P : Polygon) (J : Merge.Junction) (z : Point) (c : Config) (L : Set ℝ)
    (c' : Config) : Prop :=
  AccOK P accA ztdm J.whole.radius z ztba L c' ∧
    ∀ τ ∈ L, 0 < τ ∧ OnCB J.whole ztwod
theorem CandFr.trans {c₁ c₂ c₃ : Config} (h₁ : CandFr c₁ c₂) (h₂ : CandFr c₂ c₃) :
    CandFr c₁ c₃ :=
  ⟨fun r a b d e f => (h₂.1 r a b d e f).trans (h₁.1 r a b d e f), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a ztkan).trans ztdux⟩

/-- The pipeline registers survive. -/
theorem CandFr.pipe {c c' : Config} (h : CandFr c c') {r : ℕ} (h1 : sw 3200 ≤ r)
    (h2 : r < sw 3230) : c'.nreg r = c.nreg r :=
  h.1 r ztxxs
    by_omega by_omega zteo
    ztum

/-- The frame of a local hit is a frame of a candidate step. -/
theorem candFr_of_lh {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 h2 _ _ h5 => h r h1 (fun h' => h2 (by unfold LHW sw at h'; unfold sw; omega)) h5,
    hA, hm⟩

/-- The frame of a part is a frame of a candidate step. -/
theorem candFr_of_part {c c' : Config} (h : PartFr c c') : CandFr c c' :=
  ⟨fun r h1 h2 h3 h4 h5 => h.1 r h1 h2 (fun h' => h3 zteo)
    (fun h' => h4 zteo) h5, h.2.1, h.2.2⟩

/-- A frame keeping all registers but a set `S` of scratch registers of the candidate step. -/
theorem candFr_of_set {c c' : Config} {S : ℕ → Prop}
    (hS : ∀ r, S r → ztdpq ∨ ztbwg)
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 _ h3 h4 h5 => h r h1 (fun h' => by_grind) h5,
    hA, hm⟩
theorem modB_left (J : Merge.Junction) (r : ℕ) : ModB J 1 r 0 = J.left := by_rfl
theorem modB_right (J : Merge.Junction) : ModB J 1 1 1 = J.right := by_rfl

/-! ## The facts of a side-0 query -/
section Q
variable {J : Merge.Junction} {z : Point}

/-- **The facts of a side-0 query** used by the steps. -/
structure Q0 (P : Polygon) (J : Merge.Junction) (z : Point) (c : Config) : Prop where
  hσ : dirOf ztql = 1 ∨ dirOf ztql = -1
  hz1 : z.2 ≤ J.left.top.2
  hbL : c.nreg bL = 1
  hy : |z.2| < J.left.radius
  hgeo : LHGeo P J.left zthz ztql
  hpos : (chainModel J.left).pos zta zthz = z
  hcls : PosClass J.left zta zthz
  he : c.nreg qE < (chainModel J.left).W.n
  hpp : ProperPos ztbw zta P.n zthz
  hh1 : 1 ≤ c.nreg qH
  hhn : c.nreg qH ≤ P.n
  hzh : ((Qof P).vtx ztbmn).2 = z.2
  hfree : FreeAt J.whole z ztba
  hP0 : 0 ≤ (chainModel J.left).param zta zthz
  hP1 : (chainModel J.left).param zta zthz < 1
theorem q0_of (hQ : QState P J 0 z c) : Q0 P J z c := by
  zuc
  have hq := hQ.hq
  have hgeo := lhGeo_query hq (by
    have := hQ.hht; tauto)
  have hpos : (chainModel J.left).pos zta zthz = z := by
    have := hQ.hz; tauto
  obtain ⟨he, hh1, hh2, h0, h1, htop, -⟩ := hq
  simp only [sideChain_zero'] at he h0 h1 htop
  have hσ := SweepPrim.dirOf_cases ztql
  have ⟨_, _, _, _, hsec, _⟩ := hgeo
  have hy := query_abs he h0 h1 htop hσ hsec
  zuher
  zvnbl at hy htop
  have hht := hQ.hht
  simp only [sideChain_zero'] at hht
  zvnbl at hht
  exact ⟨hσ, htop, (hQ.hbL.2).2 htop, hy, hgeo, hpos, hcls, he, ⟨h0, h1, by_simp_all⟩,
    hh1, by_simp_all, hht.symm, hQ.hfree, h0, h1⟩
end Q

/-! ## The first local hit and the box twin -/
section Steps
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}

/-- The cost of a local hit of the step. -/
abbrev Klh (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  lhsK ztdg ztwiu zto

/-- **The local hit in the model of `C₁`** at the query position, from a cleared accumulator. -/
theorem start_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) (hQ : QState P J 0 z c)
    (h0 : c.nreg accA = 0) (hroom : c.nreg ALLOC + Klh c₀ F ≤ W) :
    IRS P W c₀ ztxkz c ztsyt (fun c' =>
      ∃ L, AccSt P J z c L c' ∧ J.left.hitParam z ztba ∈ L ∧ CandFr c c') := by
  zubwt
  have hloc : ztbvu ∨ (6 ≤ c.nreg qE ∧ z ∈ J.left.set) := by
    zudso
    · simp_all
    · exact Or.inr ⟨h6, q.hpos ▸ posClass_mem q.hcls h6 q.hP0 q.hP1⟩
    · have h6' : c.nreg qE = 2 * J.left.m + 6 := h6
      exact Or.inr ⟨by_omega, q.hpos ▸ posClass_mem q.hcls by_omega
        q.hP0 q.hP1⟩
  refine (lhs_irs hsh hBs hXl hA (sideD₁ hA) ⟨by_trivial, by_trivial,
    by trivial⟩ (by unfold OutL qE sw; omega) hI (L := ∅)
    (Mod := ModB J ztcpq ztcpr) (R₀ := J.whole.radius) (t := 0) q.he q.hpp q.hpos q.hy
    hloc (accOK_init _ _ _ _ _ h0) by_norm_num (by rw [q.hbL]; rfl) rfl
    hroom).mono le_rfl ?_
  rintro c' ⟨⟨L', a', -, g', geo'⟩, fr, hA', hm'⟩
  refine ⟨L', ⟨a', fun τ hτ => ?_⟩, geo' q.hgeo, candFr_of_lh fr hA' hm'⟩
  zucee
  · simp_all
  · exact ⟨h1, onCB_left h2⟩

/-- **The box twin** (`bR = 1`, the query on a vertical side of the box): the local hit in the
model of `C₂` at the same position completes the candidates. -/
theorem box_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {c' : Config} (hI : IInv W c₀ c') (hQ : QState P J 0 z c)
    (hfr : CandFr c c') {L : Set ℝ} (hst : AccSt P J z c L c')
    (hl : J.left.hitParam z ztba ∈ L) (hbR : c.nreg bR = 1)
    (hbox : c.nreg qE < 4) (hroom : c'.nreg ALLOC + Klh c₀ F ≤ W) :
    IRS P W c₀ ztxla c' ztsyt (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  zubwt
  have eE : c'.nreg qE = c.nreg qE := hfr.pipe by_decide by_decide
  have eH : c'.nreg qH = c.nreg qH := hfr.pipe by_decide by_decide
  have eD : c'.nreg qD = c.nreg qD := hfr.pipe by_decide by_decide
  have h13 : c.nreg qE = 1 ∨ c.nreg qE = 3 := by
    zudso
    · zubh
    · grind
    grind
  zugnm
  obtain ⟨hg₂, hpos₂⟩ := lhGeo_box h13 q.hgeo (by rw [q.hpos]; exact q.hy)
    (by rw [q.hpos]; omega)
  rw [q.hpos] at hpos₂
  obtain ⟨-, -, hpar, -⟩ := boxTwin_pos (C₁ := J.left) (C₂ := J.right) rfl h13 zta (c.nreg qH)
  have hn₂ : c.nreg qE < (chainModel J.right).W.n := by zvokr; omega
  refine (lhs_irs hsh hBs hXl hA (sideD₂ hA) ⟨by_trivial, by_trivial,
    by trivial⟩ (by unfold OutL qE sw; omega) hI (L := L)
    (Mod := ModB J ztcpq ztcpr) (R₀ := J.whole.radius) (t := 1) (z := z)
    by_omega
    (by zvpby; exact ⟨hpar ▸ q.hpp.1, hpar ▸ q.hpp.2.1, q.hpp.2.2⟩)
    by_simp_all q.hy by_omega
    (by zunle; exact hst.1) by_norm_num ztlii rfl
    hroom).mono le_rfl ?_
  zucpi
  zudts

  have hr := geo' hg₂
  refine ⟨⟨L', a', fun τ hτ => ?_, whole_mem_of_both q.hz1 hz2 q.hσ ztwcx hr⟩,
    hfr.trans ztrmz⟩
  zucee
  · zulza
  · exact ztlwe

/-- **Above the top of `C₂`** (`bR = 0`): the local hit in the model of `C₁` completes the
candidates. -/
theorem above_out (hQ : QState P J 0 z c) {c' : Config} (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z ztba ∈ L)
    (hbR : ¬ c.nreg bR = 1) : CandOut P J z c c' ∧ CandFr c c' := by
  zubwt
  have hz2 : J.right.top.2 < z.2 := by
    by_contra h; exact hbR ((hQ.hbR.2).2 ztmmq)
  refine ⟨⟨L, hst.1, hst.2, ?_⟩, hfr⟩
  rw [whole_eq_left q.hz1 hz2 q.hσ]; exact hl
end Steps
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The bodies of the part contracts -/

/-- The body of `Lab0Spec` for the program `lab0` and the cost constant `κ`. -/
def Lab0Body (lab0 : Stmt → Stmt) (κ : ℕ → ℕ) : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z ztba →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos ztbm zta P.n ztlo →
      Arrival (chainModel J.whole).W z ztwtj ztdmx
        ztwmc →
      SymPtIn c sO s → s.Lt P.n → s.eval zta = z →
      c.nreg bR = 1 →
      AccOK P accA ztdm J.whole.radius z ztba L c →
      c.nreg ALLOC + κ zto * ztwit ≤ W →
      IRS P W c₀ ztqst c ztbajz
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius z
              ztba L' c' ∧ L ⊆ L' ∧
            ztbaks ∧
            ∀ (ls : List ztck), ls.length = rd c₀ bSweep 301 →
              LogRecsAt c₀.nmem ztjt ls →
              ∀ i, LogIdx J zta N₂ ls
                  ztyav i →
                ∀ V ∈ (chainModel J.right).regions ztwis,
                  (V ∈ logLab J zta N₂ ls i ∨ ztwxq ∨
                    GapLab J ztwis V) →
                  ztxfa →
                  J.right.hitParam z ztba ∈ L') ∧
          PartFr c c')
theorem lab0Spec_iff : Lab0Spec ↔ ∃ lab0 κ, Lab0Body lab0 κ := Iff.rfl

/-- The per-query body of `S0CandSpec`. -/
def S0Body (candC : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ) :
    Prop :=
  ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
      (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c →
      z ∈ J.left.set → z ≠ J.shared → z.2 ≤ J.right.top.2 →
      FreeAt J.whole z ztba →
      c.nreg zP < (chainModel J.whole).W.n →
      ProperPos ztbm zta P.n ztlo →
      Arrival (chainModel J.whole).W z ztwtj ztdmx
        ztwmc →
      c.nreg bL = 1 → c.nreg bR = 1 →
      AccOK P accA ztdm J.whole.radius z ztba L c →
      c.nreg ALLOC + κ zto * ztgf ≤ W →
      IRS P W c₀ candC c ztxen
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius z
              ztba L' c' ∧ L ⊆ L' ∧
            ztwjm ∧
            (∀ (rs : List ztcf), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem ztdpi rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param zta ztbhg =
                  (chainModel J.whole).param zta ztlo →
                dirOf r.2.2.2.2 = -dirOf ztql →
                ∀ τ, 0 < τ → stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z ztba τ → τ ∈ L') ∧
            (∀ j, j < 2 * N₂.nChords →
              tabOf J zta c₀.nmem ztdaf j =
                some ztxbi →
              endDir j = -dirOf ztql → endOrigin J zta N₂ j ∈ J.right.set →
              endOrigin J zta N₂ j ≠ J.shared → endOrigin J zta N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J zta N₂ j = rayPt z ztba τ →
                τ ∈ L')) ∧
          PartFr c c')
theorem s0CandSpec_iff : S0CandSpec ↔ ∃ initC candC Aux κ, InitSpec initC Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧ S0Body candC Aux κ := Iff.rfl

/-! ## The pipeline registers -/

/-- The pipeline registers of a later configuration. -/
theorem pipe8 {c c' : Config} (h : CandFr c c') :
    c'.nreg qE = c.nreg qE ∧ c'.nreg qH = c.nreg qH ∧ c'.nreg qD = c.nreg qD ∧
    c'.nreg zE = c.nreg zE ∧ c'.nreg zP = c.nreg zP ∧ c'.nreg zPh = c.nreg zPh ∧
    c'.nreg bL = c.nreg bL ∧ c'.nreg bR = c.nreg bR :=
  ⟨h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide,
    h.pipe by_decide by_decide⟩

/-! ## The shared vertex -/

/-- The outputs of the arrival position of the shared vertex (`aO`, `aO + 1`, `aO + 2`). -/
def aO : ℕ := sw 4820

/-- **The shared vertex**: its arrival position in the model of `C₂`, then the local hit there. -/
def sharedS (sh : Stmt) : Stmt :=
  .seq (callArr zted ztbex qH qD aO)
    (.ifLtN aO K1 .skip (lhs ztqm ztbz zthy ztjnz 1 sh))
section Steps
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}
set_option maxHeartbeats 4000000 in
/-- **The shared vertex** completes the candidates. -/
theorem shared_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {c' : Config} (hI : IInv W c₀ c') (hQ : QState P J 0 z c)
    (hfr : CandFr c c') {L : Set ℝ} (hst : AccSt P J z c L c')
    (hl : J.left.hitParam z ztba ∈ L) (hzs : z = J.shared)
    (hroom : c'.nreg ALLOC + ztfmu ≤ W) :
    IRS P W c₀ ztqwf c' ztfmu (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  zubwt
  obtain ⟨eE, eH, eD, -, -, -, -, -⟩ := pipe8 hfr
  zuiwt
  have hz2 : ztsnq := by
    rw [hzs, ← J.right_vertex_zero]; exact J.right.vertex_snd_le_top ztbg
  have hbR := (hQ.hbR.2).2 hz2
  zulje
  have hctx : ChainCtx P W c' _ J.right :=
    hS.hctx.transport ztdhk hI.hm hI.hA
  have e41 : c'.nreg ztbex = cstR J 1 := by
    zubuy
    zubfc
    grind
  obtain ⟨hlt, hpar0, hpos0⟩ := shared_pos₂ (h := c.nreg qH - 1) hP zta
    (by rw [q.hzh, hzs])
  have hqh : ztmuq := by have := q.hh1; omega
  rw [hqh] at hpar0 hpos0
  have hyS := absy_lt J.right J.shared_mem_right
  unfold sharedS
  refine IRS.seq
    (callArr_irs hI hctx
      by_decide by_decide by_omega
      (by rw [e41, eH]; exact ⟨by_simp_all, by_simp_all, q.hhn⟩)
      by_simp_all by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨harr, fr2, hA2, hm2⟩
  rw [e41, eH, eD] at harr
  zumqg
  rw [hpos0] at harr
  have k2 : ∀ r, sw 3200 ≤ r → r < sw 3230 → c₂.nreg r = c'.nreg r := fun r h1 h2 =>
    fr2 r ztxxs
      ztggr ztggr ztggr
      ztum
  have hfr₂ := hfr.trans (candFr_of_set (fun r hr => Or.inr (by rcases hr with rfl | rfl | rfl <;> unfold aO sw <;> omega))
    (fun r h1 h2 h3 => fr2 r h1 ztzey ztbapk
      (fun h => h2 ztwxb) h3) hA2 hm2)
  obtain ⟨eE2, eH2, eD2, -, -, -, -, -⟩ := pipe8 hfr₂
  have hk1 := (hA.hK.fix hI₂).2.1
  zumfg
  refine IRS.ite ztrqd ztrqd
  · -- no arrival position: impossible, the direction is free for `C₂`
    exfalso
    zukuo
    have hne : c₂.nreg aO ≠ 1 := by_omega
    obtain ⟨p, t, hpt⟩ := arrival_of_freeC J.right hP hσ (Or.inl (hzs ▸ J.shared_mem_right))
      (freeAt_right_of_whole hz2 q.hfree)
    grind
  · zukuo
    have hf1 : c₂.nreg aO = 1 := by_omega
    obtain ⟨hp, hpp, hA'⟩ := harr.2.1 hf1
    rw [← hzs] at hA'
    have hzh' : ((Qof P).vtx _).2 = z.2 := q.hzh
    obtain ⟨hgeo, hposA, hparA⟩ := lhGeo_arr hA' (by have := q.hhn; grind)
      hzh' hz2 rfl
    rw [hqh] at hgeo hposA hparA
    have hcls := posClass_of hp
      (by zunue; exact hpp.1) (by zunue; exact hpp.2.1) by_grind
      by_grind
    have hloc : (c₂.nreg ztjnz = 1 ∨ c₂.nreg ztjnz = 3) ∨
        (6 ≤ c₂.nreg ztjnz ∧ z ∈ J.right.set) := by
      have hzr := hzs ▸ J.shared_mem_right
      rcases hcls with h | ⟨h6, -⟩ | ⟨h6, -⟩
      · grind
      · grind
      grind
    have hacc₂ : AccOK P accA ztdm J.whole.radius z
        ztjty L c₂ := by
      rw [eD2]
      exact hst.1.transport (fun j hj => by
        rw [fr2 _ ztxld
          zthfv zthfv
          zthfv ztbjo])
    refine (lhs_irs hsh hBs hXl hA hS ⟨by_trivial, by_trivial,
      by trivial⟩ (by unfold OutL aO sw; omega) hI₂
      hp (by rw [eH2]; exact ⟨by zunue; exact hpp.1, by zunue; exact hpp.2.1, q.hhn⟩)
      by_grind q.hy hloc hacc₂ by_norm_num
      ztlii rfl
      by_grind).mono le_rfl ?_
    zucpi
    rw [eD2] at a' g' geo'
    rw [eH2] at geo'
    have hr := geo' hgeo
    refine ⟨⟨L', a', fun τ hτ => ?_, whole_mem_of_both q.hz1 hz2 hσ ztwcx hr⟩,
      hfr₂.trans ztrmz⟩
    zucee
    · zulza
    · exact ztlwe
end Steps
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **The main class.** -/
def mainS (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (callSym ztjl zE qH ztwgf) (.seq ztqst candC)

/-- The cost of the main class. -/
def Kmain (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  16707 + (κL zto * ztwit +
    κS zto * ztgf)
section Steps
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}
set_option maxHeartbeats 8000000 in
/-- **The main class** completes the candidates. -/
theorem main_irs {lab0 : Stmt → Stmt} {candC : Stmt}
    {Aux : Polygon → Merge.Junction → NF → Config → Prop} {κL κS : ℕ → ℕ}
    (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z ztba ∈ L)
    (hzL : z ∈ J.left.set) (hzs : z ≠ J.shared) (hbR : c.nreg bR = 1)
    (hroom : c'.nreg ALLOC + Kmain κL κS c₀ F ≤ W) :
    IRS P W c₀ zthyv c' (Kmain κL κS c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  zubwt
  zumfg
  zugnm
  obtain ⟨-, -, eD, eZ, eP, ePh, eL, eR⟩ := pipe8 hfr
  -- the chain context of `C`
  have hctx₀ : ztziz := by
    zuddr
    exact ctx_of_aenv hA hJ.2.2 hJW.2.2.1 hA.hP le_rfl
  have hctx : ChainCtx P W c' ztjl J.whole :=
    hctx₀.transport ztdhk zttj hI.hA
  have hzW : (chainModel J.whole).pos zta ztdqo = z := hQ.hzM
  have hcls := posClass_of (C := J.whole) hQ.hzE hQ.hzpp.1 hQ.hzpp.2.1
    (by zupdc; exact q.hy) (Or.inl (by zupdc; exact q.hz1.trans J.left_top_le))
  have hcls' : (6 ≤ c.nreg zE ∧ c.nreg zE < 2 * J.whole.m + 6) ∨
      (c.nreg zE = 2 * J.whole.m + 6 ∧
        (chainModel J.whole).param zta ztdqo = 0) := by
    rcases hcls with h | h | h
    · exact absurd (hzW ▸ J.left_set_subset hzL) (fun hm => box_not_mem h hm)
    · simp_all
    grind
  obtain ⟨-, eH, -, -, -, -, -, -⟩ := pipe8 hfr
  -- 1. the symbolic point
  unfold mainS Kmain
  unfold Kmain at hroom
  refine IRS.seq (K₁ := 16707) (callSym_irs (dsc := sw 2) (re := zE) (rh := qH) (o := sw 3230)
    hI hctx by_decide by_decide (by rw [eZ]; exact hQ.hzE)
    (by rw [eZ, eH]; exact hQ.hzpp) (by rw [eZ, eH, hzW]; exact q.hy)
    by_simp_all by_omega) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨sp, hsp, hspl, hspe, fr2, hA2, hm2⟩
  rw [eZ, eH, hzW] at hspe
  have hfr₂ : CandFr c c₂ := hfr.trans (candFr_of_set (S := fun r => sw 3230 ≤ r ∧ r ≤ sw 3233)
    (fun r hr => Or.inl zteo)
    (fun r h1 h2 h3 => fr2 r h1 zteo h3) hA2 hm2)
  obtain ⟨-, -, eD2, -, eP2, ePh2, eL2, eR2⟩ := pipe8 hfr₂
  have hacc₂ : AccOK P accA (ModB J (c₂.nreg bL) (c₂.nreg bR)) J.whole.radius z
      ztjty L c₂ := by
    rw [eL2, eR2, eD2]
    exact hst.1.transport (fun j hj => by
      rw [fr2 _ ztxld
        zthk ztbjo])
  -- 2. the label candidates
  refine IRS.seq (hLab sh Bs F X Ok hsh hBs hXl P W c₀ c₂ J H N₁ N₂ E L sp z hA hI₂ hzL hzs hz2
    (by rw [eD2]; exact q.hfree) (by rw [eP2]; exact hQ.hzP) (by rw [eP2, ePh2]; exact hQ.hzPp)
    (by rw [eP2, ePh2, eD2]; exact hQ.harr) by_tauto hspl hspe
    by_omega hacc₂ by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨L₃, a3, s3, g3, comp3⟩, fr3⟩
  rw [eL2, eR2, eD2] at a3
  rw [eD2] at g3 comp3
  rw [eP2, ePh2] at comp3
  have hfr₃ : CandFr c c₃ := hfr₂.trans (candFr_of_part fr3)
  obtain ⟨-, -, eD3, -, eP3, ePh3, eL3, eR3⟩ := pipe8 hfr₃
  -- 3. the stop and table candidates
  refine (hSC P W X Ok J H N₁ N₂ E c₀ c₃ L₃ z hA hAux hI₃ hzL hzs hz2
    (by rw [eD3]; exact q.hfree) (by zupcp; exact hQ.hzP) (by rw [eP3, ePh3]; exact hQ.hzPp)
    (by rw [eP3, ePh3, eD3]; exact hQ.harr) (by rw [eL3]; exact q.hbL) by_omega
    by_grind by_omega).mono le_rfl ?_
  rintro c₄ ⟨⟨L₄, a4, s4, g4, stp, tab⟩, fr4⟩
  rw [eL3, eR3, eD3] at a4
  rw [eD3] at g4 stp tab
  rw [eP3, ePh3] at stp tab
  have hfr₄ : CandFr c c₄ := hfr₃.trans (candFr_of_part fr4)
  refine ⟨⟨L₄, a4, fun τ hτ => ?_, ?_⟩, hfr₄⟩
  · rcases g4 τ hτ with h | h
    · rcases g3 τ h with h' | ⟨h1, h2⟩
      · exact hst.2 τ h'
      · exact ztlwe
    omega
  -- completeness
  obtain ⟨rs, ls, hrsl, hrsAt, hStops, -, hlsl, hlsAt, hLog, -, hTab, -⟩ := hA.hout
  obtain ⟨hLst, hcases⟩ := hM P J N₂ rs ls (tabOf J zta c₀.nmem ztdaf) hA.hG
    hA.hP hA.hNF₂ hLog hStops hTab z ztba hσ hzL hzs hz2 q.hfree ztdmx
    ztwmc hQ.harr
  obtain ⟨i, hi⟩ := logIdx_exists hLog hLst
  have hpos : 0 < J.whole.hitParam z ztba :=
    (Merge.hit_of_freeAt J.whole (q.hz1.trans J.left_top_le) hσ q.hfree).1
  rcases hcases i hi with h1 | ⟨h2, V, hV, hlab, hev⟩ | ⟨r, hr, hr1, hr2, hr3, hr4⟩ |
      ⟨j, hj, hT, hd, ho1, ho2, ho3, ho4⟩
  · rw [← h1]; exact s4 (s3 hl)
  · rw [← h2]; exact s4 (comp3 ls hlsl hlsAt i hi V hV hlab hev)
  · exact stp rs hrsl hrsAt r hr hr1 hr2 hr3 _ hpos hr4
  · exact tab j hj hT hd ho1 ho2 ho3 _ hpos ho4
end Steps
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The program -/

/-- Scratch registers of the class test. -/
def nE : ℕ := sw 4810
def nH : ℕ := sw 4811
def nO : ℕ := sw 4812
def tq : ℕ := sw 4814

/-- The test of the last walk edge (`qE + 1 = 2 m₁ + 7` and `cstL 1 = 6`). -/
def t3S (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (block [.addN tq qE K1])
    (.ifLtN tq ztna zthyv (.ifLtN K6 ztbuy zthyv ztqwf))

/-- **The class test** of a query off the box, not above the top of `C₂`. -/
def cls0 (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq (block [.copyN nE qE, .copyN nH qH])
    (.seq (normS ztiw nE nH nO)
      (.ifLtN K0 nH zthyv
        (.ifLtN qE ztbuy ztlud
          (.ifLtN ztbuy qE ztlud ztqwf))))

/-- **The candidate step of side `0`.** -/
def cand0 (lab0 : Stmt → Stmt) (candC sh : Stmt) : Stmt :=
  .seq ztxkz
    (.ifLtN bR K1 .skip
      (.ifLtN qE K4 ztxla ztrnl))

/-- The cost of a branch (main class or shared vertex). -/
def Kbr (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  Kmain κL κS c₀ F + ztfmu

/-- The cost of the class test. -/
def Kcls (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ := 11030 + Kbr κL κS c₀ F

/-- The cost of the candidate step. -/
def Kc0 (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  Klh c₀ F + (2 + (2 + ztlex))

/-! ## Frames of the scratch blocks -/

/-- The accumulator state survives a step keeping the accumulator registers. -/
theorem AccSt.keep {J : Merge.Junction} {z : Point} {L : Set ℝ} {c₁ c₂ : Config}
    (h : AccSt P J z c L c₁) (hr : ∀ j, j ≤ 12 → c₂.nreg ztbzh = c₁.nreg ztbzh) :
    AccSt P J z c L c₂ :=
  ⟨h.1.transport hr, h.2⟩

/-- The scratch set of the class test. -/
def NS (r : ℕ) : Prop := sw 4810 ≤ r ∧ r ≤ sw 4814
theorem candFr_ns {c₁ c₂ : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r)
    (hA : c₁.nreg ALLOC ≤ c₂.nreg ALLOC) (hm : ∀ a, a < c₁.nreg ALLOC → c₂.nmem a = c₁.nmem a) :
    CandFr c₁ c₂ :=
  candFr_of_set (fun r hr => Or.inr (by unfold NS sw at hr; unfold sw; omega)) h hA hm
theorem acc_ns {c₁ c₂ : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) :
    ∀ j, j ≤ 12 → c₂.nreg ztbzh = c₁.nreg ztbzh := fun j hj =>
  h _ ztxld
    (by unfold NS accA sw; omega) ztbjo

/-! ## The class test -/
section Steps
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}
  {lab0 : Stmt → Stmt} {candC : Stmt} {Aux : Polygon → Merge.Junction → NF → Config → Prop}
  {κL κS : ℕ → ℕ}
theorem kmain_le : Kmain κL κS c₀ F ≤ Kbr κL κS c₀ F := by unfold Kbr; omega
theorem kshared_le : 35007 + (Klh c₀ F + 2) ≤ Kbr κL κS c₀ F := by unfold Kbr; omega
set_option maxHeartbeats 8000000 in
/-- **The test of the last walk edge.** -/
theorem t3_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z ztba ∈ L)
    (hzL : z ∈ J.left.set) (hbR : c.nreg bR = 1)
    (hpar : (chainModel J.left).param zta zthz = 0)
    (hne : c.nreg qE ≠ cstL J 1)
    (hroom : c'.nreg ALLOC + ztzsl ≤ W) :
    IRS P W c₀ ztlud c' ztzsl (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  zubwt
  obtain ⟨eE, -, -, -, -, -, -, -⟩ := pipe8 hfr
  zuhee
  have hWq : c'.nreg qE + c'.nreg K1 ≤ W := by
    rw [hK.2.1]; have := hI.hw.1 qE; have := hI.hw.1 ALLOC
    rw [eE]; have := q.he; zvokr at this
    have := hA.hWm; have : ztpkj := by_simp
    omega
  unfold t3S
  refine IRS.seq ((IRS.block [.addN tq qE K1] hI (by
    zumzu; exact ⟨⟨iscr_sw by_decide by_decide,
      hWq⟩, trivial⟩)).mono by_simp (fun _ h => h)) ?_
  zudfk

  have hr₂ : ∀ r, r ≠ tq → c₂.nreg r = c'.nreg r := fun r hr => by
    zumxp; simp only [regB, regI, ]; simp_all
  have htq : c₂.nreg tq = c'.nreg qE + c'.nreg K1 := by
    zumxp; rfl
  have fr2 : ztflj :=
    fun r _ h2 _ => hr₂ r ztwuu
  zugmf

  have hA2e := hr₂ ALLOC by_decide
  obtain ⟨eE2, -, -, -, -, -, -, -⟩ := pipe8 hfr₂
  have e33 : c₂.nreg ztna = 2 * J.m₁ + 7 := by
    zugdf
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -⟩ := hA.hst
    simp_all
  have e46 : c₂.nreg ztbuy = cstL J 1 := by
    zugdf
    zuhg
    grind
  zuheg
  have htq' : c₂.nreg tq = c.nreg qE + 1 := by rw [htq, eE, hK.2.1]
  have hmain : z ≠ J.shared → IRS P W c₀ _ c₂ _ (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := fun hzs =>
    (main_irs hM hLab hSC hsh hBs hXl hA hAux hI₂ hQ hfr₂ hst₂ hl hzL hzs hbR
      (by have := kmain_le (κL := κL) (κS := κS) (c₀ := c₀) (F := F); omega)).mono kmain_le
      by_simp_all
  have hn₁ : c.nreg qE < 2 * J.m₁ + 7 := by have := q.he; zvokr at this; simp_all
  refine (IRS.ite (K := 2 + Kbr κL κS c₀ F) ztyq ztyq).mono by_omega
    ztb
  · refine (hmain fun hzs => ?_).mono by_omega by_simp_all
    zuikr
    zudez
    · simp_all
    simp_all
  · zuikr
    refine (IRS.ite (K := Kbr κL κS c₀ F) ztczl ztczl).mono by_omega
      ztb
    · refine hmain fun hzs => ?_
      zuiix
      zudez
      · simp_all
      omega
    · zuiix
      have h6 : cstL J 1 = 6 := by rw [cstL_one] at h2 ⊢; omega
      have hzs := q.hpos.symm.trans
        ztkpm
      exact (shared_irs hsh hBs hXl hA hI₂ hQ hfr₂ hst₂ hl hzs
        (by have := kshared_le (κL := κL) (κS := κS) (c₀ := c₀) (F := F); omega)).mono
        kshared_le by_simp_all

/-- The cost of `t3S`. -/
abbrev Kt3 (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) : ℕ := 1 + ztcsl
set_option maxHeartbeats 8000000 in
/-- **The class test.** -/
theorem cls0_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) {c' : Config}
    (hI : IInv W c₀ c') (hQ : QState P J 0 z c) (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z ztba ∈ L)
    (hbR : c.nreg bR = 1) (h4 : 4 ≤ c.nreg qE)
    (hroom : c'.nreg ALLOC + Kcls κL κS c₀ F ≤ W) :
    IRS P W c₀ ztrnl c' (Kcls κL κS c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  zubwt
  obtain ⟨eE, eH, -, -, -, -, -, -⟩ := pipe8 hfr
  have h6 : 6 ≤ c.nreg qE := by
    rcases q.hcls with h | ⟨h, -⟩ | ⟨h, -⟩
    · grind
    · zubh
    simp_all
  have hzL := q.hpos ▸ posClass_mem q.hcls h6 q.hP0 q.hP1
  unfold cls0
  refine (IRS.seq (K₁ := 2) (K₂ := 11015 + (2 + (2 + ztnfi)))
    ((IRS.block [.copyN nE qE, .copyN nH qH] hI (by
      zudu
      exact ⟨iscr_sw by_decide by_decide,
        iscr_sw by_decide by_decide, trivial⟩)).mono
      by_simp ztb) ?_).mono (by unfold Kcls Kt3; omega) (fun _ h => h)
  zudfk

  have v2 : c₂.nreg nE = c'.nreg qE ∧ c₂.nreg nH = c'.nreg qH ∧
      ∀ r, r ≠ nE → r ≠ nH → c₂.nreg r = c'.nreg r := by
    zumxp
    refine ztfdb <;>
      simp (disch := (unfold nE nH qE qH sw at *; omega)) only [regB, regI, upd_same, upd_other]
  obtain ⟨vE, vH, vo⟩ := v2
  have fr2 : ztflj :=
    fun r _ h2 _ => vo r ztwuu
      ztwuu
  zugmf

  have hA2e := vo ALLOC by_decide
    by_decide
  zuheg
  have hctx₂ : ChainCtx P W c₂ _ J.left :=
    (sideD₁ hA).hctx.transport (hI₂.hin _ by_trivial) hI₂.hm
      hI₂.hA
  rw [eE] at vE
  rw [eH] at vH
  -- normalise
  refine IRS.seq (normS_irs hI₂ hK₂
    hctx₂ by_decide by_decide (by zuogo; exact q.he)
    (by rw [vE, vH]; exact q.hpp) by_simp_all
    (by unfold Kcls at hroom; omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨n3E, n3H, fr3, hA3, hm3⟩
  rw [vE, vH] at n3H
  have fr3' : ∀ r, bandOf r ∉ oracleBands → ¬ NS r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => fr3 r h1 ztwuu
      ztwuu
      ztwuu h3
  have hfr₃ := hfr₂.trans (candFr_ns fr3' hA3 hm3)
  have hst₃ := hst₂.keep (acc_ns fr3')
  obtain ⟨eE3, -, -, -, -, -, -, -⟩ := pipe8 hfr₃
  zulil
  have e46 : c₃.nreg ztbuy = cstL J 1 := by
    rw [hI₃.hin _ by_trivial]
    zuhg
    grind
  have hKbr := kmain_le (κL := κL) (κS := κS) (c₀ := c₀) (F := F)
  refine (IRS.ite (K := 2 + ztnfi) ztyq ztyq).mono by_omega
    ztb
  · -- a positive parameter: not the shared vertex
    zuiiy
    have hpar : (chainModel J.left).param _ zthz ≠ 0 := fun h0 =>
      by rw [(nhgt_eq_zero_iff _ _ _).2 h0] at h1; omega
    refine (main_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL (fun hzs => hpar
      ((shared_iff₁ hA.hP _ q.he q.hP0 q.hP1).1 ztquy).1) hbR
      (by have h := hroom; unfold Kcls Kbr at h; omega)).mono
      by_grind by_grind
  · zuiiy
    have hpar : (chainModel J.left).param zta zthz = 0 :=
      (nhgt_eq_zero_iff _ _ _).1 by_omega
    refine (IRS.ite (K := 2 + Kt3 κL κS c₀ F) ztczl ztczl).mono by_omega
      ztb
    · zuihs
      exact (t3_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL hbR hpar by_omega
        (by have h := hroom; unfold Kcls at h; omega)).mono
        by_simp by_grind
    · zuihs
      refine (IRS.ite (K := Kt3 κL κS c₀ F) ztrqa ztrqa).mono by_omega
        ztb
      · zuiht
        exact t3_irs hM hLab hSC hsh hBs hXl hA hAux hI₃ hQ hfr₃ hst₃ hl hzL hbR hpar by_omega
          (by have h := hroom; unfold Kcls at h; omega)
      · zuiht
        have hzs := q.hpos.symm.trans
          ztkpm
        exact (shared_irs hsh hBs hXl hA hI₃ hQ hfr₃ hst₃ hl hzs
          (by have h := hroom; unfold Kcls Kbr at h; omega)).mono
          (by show _ ≤ 1 + ztcsl; unfold Kbr; omega) by_grind
set_option maxHeartbeats 8000000 in
/-- **The candidate step of side `0`.** -/
theorem cand0_irs (hM : Side0MathSpec) (hLab : Lab0Body lab0 κL) (hSC : S0Body candC Aux κS)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hAux : Aux P J N₂ c₀) (hI : IInv W c₀ c)
    (hQ : QState P J 0 z c) (h0 : c.nreg accA = 0) (hroom : c.nreg ALLOC + Kc0 κL κS c₀ F ≤ W) :
    IRS P W c₀ (cand0 lab0 candC sh) c (Kc0 κL κS c₀ F) (fun c' =>
      CandOut P J z c c' ∧ CandFr c c') := by
  unfold cand0 Kc0
  unfold Kc0 at hroom
  refine IRS.seq (start_irs hsh hBs hXl hA hI hQ h0 by_omega) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨L, hst, hl, hfr⟩
  obtain ⟨eE, -, -, -, -, -, -, eR⟩ := pipe8 hfr
  zulii
  have hbR1 := hQ.hbR.1
  refine (IRS.ite (K := 2 + ztlex) ztyq ztyq).mono
    by_omega ztb
  · zuiiv
    exact IRS.skip hI₁ (above_out hQ hfr hst hl by_omega)
  · zuiiv
    have hbR : ztpmh := by_omega
    refine (IRS.ite (K := Klh c₀ F + Kcls κL κS c₀ F) ztczl ztczl).mono
      by_omega ztb
    · zuiiw
      exact (box_irs hsh hBs hXl hA hI₁ hQ hfr hst hl hbR h2 by_omega).mono by_omega
        by_simp_all
    · zuiiw
      exact (cls0_irs hM hLab hSC hsh hBs hXl hA hAux hI₁ hQ hfr hst hl hbR by_omega
        by_omega).mono by_omega by_simp_all
end Steps
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
def TabStepSpec : Prop :=
  ∃ (tabB : Stmt) (κT : ℕ), ∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ c : Config) (L : Set ℝ)
    (z : Point),
    AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
    c.nreg qJ < 2 * N₂.nChords → endOrigin J zta N₂ ztccx = z →
    endDir ztccx = dirOf ztql →
    z ∈ J.right.set → z ≠ J.shared → z ≠ J.right.top →
    AccOK P accA ztdm J.whole.radius z ztba L c →
    c.nreg ALLOC + κT ≤ W →
    IRS P W c₀ tabB c κT
      (fun c' =>
        (∃ L', AccOK P accA ztdm J.whole.radius z
            ztba L' c' ∧ L ⊆ L' ∧
          ztwjm ∧
          (J.whole.hitParam z ztba ∈ L' ∨
            J.whole.hitParam z ztba = J.right.hitParam z ztba)) ∧
        CandFr c c')
def sSide : ℕ := sw 98

/-- The loop registers: the query index, the query address, the result address. -/
def pJ : ℕ := sw 5000
def pA : ℕ := sw 5001
def pR : ℕ := sw 5002

/-- **The base configuration of the answer phase.** -/
structure ABase (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (Aux : Polygon → Merge.Junction → NF → Config → Prop) (J : Merge.Junction) (H : Host)
    (N₁ N₂ : NF) (E : ℕ) (L : List zte) (i : ℕ) (c₀ : Config) : Prop where
  hw : WordsBounded W c₀
  hA : AEnv P W X Ok J H N₁ N₂ E c₀
  hi : i ≤ 1
  hside : c₀.nreg sSide = i
  hAux : i = 0 → Aux P J N₂ c₀
  hLn : c₀.nreg ztgml = L.length
  hLm : c₀.nreg ztfiw + 3 * L.length ≤ c₀.nreg ALLOC
  hLat : ChordListAt c₀.nmem (c₀.nreg ztfiw) L
  hq : ∀ q ∈ L, QueryOK J zta i q
  hht : ∀ q ∈ L, ((chainModel ztgi).pos zta ztpo).2 =
    ((Qof P).vtx zteut).2
  hend : i = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3
  hres : c₀.nreg ztbor = c₀.nreg ALLOC
  hTLR : c₀.nreg TLR ≤ Nat.clog 2 ztks + 6

/-- The point of the query `j`. -/
noncomputable def qPt (J : Merge.Junction) (P : Polygon) (i : ℕ) (L : List zte) (j : ℕ) :
    Point :=
  (chainModel ztgi).pos zta ⟨(L.getD j ztt).1, (L.getD j ztt).2.1⟩
open Classical in
/-- **The cost of the query `j`**: `κ D (F γ + TLR + 1)`, plus `κ D (A₁ + 1) (F γ + 1)` for a
brute-force query of side `1`. -/
noncomputable def qCost (κ : ℕ → ℕ) (F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List zte) (i j : ℕ) : ℕ :=
  κ zto * ztwit +
    (if i = 1 ∧ BruteQ J N₂ j ztdvu then
      κ zto * ztyz * ztwju else 0)

/-- **The per-query procedure** (`qry sh`) for the query `j`, from the loop registers. -/
def QrySpec (Aux : Polygon → Merge.Junction → NF → Config → Prop) : Prop :=
  ∃ (qry : Stmt → Stmt) (κq : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : List zte) (i j : ℕ),
      ABase P W X Ok Aux J H N₁ N₂ E L i c₀ → IInv W c₀ c →
      c.nreg pJ = j → j < L.length → c.nreg pA = c₀.nreg ztfiw + 3 * j →
      c.nreg pR = c₀.nreg ztbor + 4 * j → c.nreg pR + 4 ≤ c.nreg ALLOC →
      c.nreg ALLOC + qCost κq F c₀ J P N₁ N₂ L i j ≤ W →
      IRS P W c₀ ztwcd c (qCost κq F c₀ J P N₁ N₂ L i j) (fun c' =>
        (∃ r : ℕ × ℕ × ℕ × ℕ, c'.nmem ztqix = r.1 ∧ c'.nmem ztrml = r.2.1 ∧
          c'.nmem ztrmm = r.2.2.1 ∧ c'.nmem ztrmn = r.2.2.2 ∧
          SeesInWhole J zta i ztwzi r) ∧
        ztdws ∧
        ztfyx ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC)

/-- **The cost of the loop**. -/
def loopCost (κ : ℕ → ℕ) (F : ℕ → ℕ) (c₀ : Config) (N₁ : NF) (L : List zte) : ℕ :=
  κ zto * ztkr * ztwit +
    κ zto * ztyz * ztwju

/-- **The query loop** (`loopS sh`) from the base `c₀`: the result list at `sw 11`. -/
def LoopSpec (Aux : Polygon → Merge.Junction → NF → Config → Prop) : Prop :=
  ∃ (loopS : Stmt → Stmt) (κL : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : List zte) (i : ℕ),
      ABase P W X Ok Aux J H N₁ N₂ E L i c₀ →
      c₀.nreg ALLOC + loopCost κL F c₀ N₁ L ≤ W →
      IRS P W c₀ ztvyj c₀ (loopCost κL F c₀ N₁ L) (fun c' =>
        ∃ R : List ztpl, R.length = L.length ∧
          c₀.nreg ztbor + 4 * L.length ≤ c'.nreg ALLOC ∧
          ResultListAt c'.nmem ztbahc R ∧
          ∀ j, j < L.length → SeesInWhole J zta i ztwzi ztxkj)

/-- **The assembly**: `SweepSpecH` from stages 2/3, a side-0 initialisation and the loop. -/
def AsmGoal : Prop :=
  SweepEvSpec → ∀ (init0 : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop)
    (κ0 : ℕ → ℕ), InitSpec init0 Aux κ0 → LoopSpec Aux → SweepSpecH
variable {P : Polygon} {W : ℕ}

/-! ## Descriptors -/
variable {m m' : ℕ → ℕ} {c c' : Config}
/-- A model descriptor survives a change of the memory above its bound. -/
theorem asm_modelDesc {D E E' : ℕ} {M : Model}
    (hd : ModelDescAt m D zta M) (hwf : ModelDescWF P E m D)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescAt m' D zta M ∧ ModelDescWF P E' m' D := by
  zucis
  · zudjf

  · zuclr

/-- A junction survives a change of the memory above its bound. -/
theorem asm_junction {b0 b1 b2 E E' : ℕ} {H : Host} {J : Merge.Junction}
    (hJ : JunctionAt m b0 b1 b2 zta H J) (hwf : JunctionWF P E m b0 b1 b2)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    JunctionAt m' b0 b1 b2 zta H J ∧ JunctionWF P E' m' b0 b1 b2 := by
  zuflb
  obtain ⟨j0, w0⟩ := chainDesc_keep wl hJ.1 he hE
  obtain ⟨j1, w1⟩ := chainDesc_keep wr' hJ.2.1 he hE
  obtain ⟨j2, w2⟩ := chainDesc_keep ww hJ.2.2 he hE
  refine ⟨ztrdq, w0, w1, w2, fun H' hH' => ?_⟩
  have hb : m' b2 = m b2 := he _ (by have := ww.1; omega)
  zucpv

  have hH : HostAt m' _ H := ShotList.hostAt_agree hJ.2.2.1 hEb he
  zugcg
  zulyy

/-! ## The stage-0 state -/

/-- **`St0S` with new model descriptors.** -/
theorem st0S_md {H : Host} {J : Merge.Junction} (h : SweepEv.St0S P c H J)
    (hr : ∀ j, j < 96 → j ≠ 11 → j ≠ 30 → j ≠ 31 → c'.nreg ztgc = c.nreg ztgc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (md30 : ModelDescAt c'.nmem ztbafw zta ztbw)
    (w30 : ModelDescWF P ztdo c'.nmem ztbafw)
    (md31 : ModelDescAt c'.nmem ztbafz zta ztj)
    (w31 : ModelDescWF P ztdo c'.nmem ztbafz) :
    SweepEv.St0S P c' H J := by
  obtain ⟨h90, h91, h92, h93, hJ, hwf, d20, w20, d21, w21, h23, h24, h40, h45, h33, h34, h35,
    -, -, -, -⟩ := h
  have r : ∀ j, j < 96 → j ≠ 11 → j ≠ 30 → j ≠ 31 → c'.nreg _ = c.nreg _ := hr
  obtain ⟨hJ', hwf'⟩ := asm_junction hJ hwf hm hA
  zucbg

  refine ⟨by_simp_all,
    by simp_all,
    by simp_all,
    by simp_all, ?_, ?_, ?_, ?_, ?_, ?_,
    by simp_all,
    by simp_all,
    fun k hk => by_grind,
    fun k hk => by_grind,
    by simp_all,
    by simp_all,
    by simp_all, md30, w30, md31, w31⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-- **`St0S` survives** a step keeping `sw 0 … 99`, the memory below the allocator, and growing
the allocator. -/
theorem st0S_transport {H : Host} {J : Merge.Junction}
    (h : SweepEv.St0S P c H J) (hr : ∀ j, j < 100 → j ≠ 11 → c'.nreg ztgc = c.nreg ztgc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SweepEv.St0S P c' H J := by
  zuivb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, d30, w30, d31, w31⟩ := h'
  obtain ⟨d30', w30'⟩ := asm_modelDesc d30 w30 hm hA
  obtain ⟨d31', w31'⟩ := asm_modelDesc d31 w31 hm hA
  rw [← hr 30 by_omega by_omega] at d30' w30'
  rw [← hr 31 by_omega by_omega] at d31' w31'
  exact st0S_md h by_grind hm hA d30' w30' d31' w31'

/-! ## The outputs of stages 2/3 -/

/-- **The outputs of stages 2/3 survive** a step keeping their registers and the memory below the
allocator. -/
theorem out_transport {J : Merge.Junction} {N₂ : NF}
    (h : SweepEv.Out P J N₂ c)
    (hr : ∀ j, j = 200 ∨ j = 201 ∨ j = 300 ∨ j = 301 ∨ j = 302 → c'.nreg ztgc = c.nreg ztgc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hs : rd c bSweep 200 + 5 * rd c bSweep 201 ≤ c.nreg ALLOC)
    (hl : rd c bSweep 300 + 7 * rd c bSweep 301 ≤ c.nreg ALLOC)
    (ht : rd c bSweep 302 + 3 * ztbxu ≤ c.nreg ALLOC) :
    SweepEv.Out P J N₂ c' := by
  have e :=
    hr
  unfold SweepEv.Out at h ⊢
  rw [show rd c' bSweep 200 = rd c bSweep 200 from e 200 by_simp,
    show rd c' bSweep 201 = rd c bSweep 201 from e 201 by_simp,
    show rd c' bSweep 300 = rd c bSweep 300 from e 300 by_simp,
    show rd c' bSweep 301 = rd c bSweep 301 from e 301 by_simp,
    show rd c' bSweep 302 = rd c bSweep 302 from e 302 by_simp]
  obtain ⟨rs, ls, hrl, hrs, hsok, hrw, hll, hls, hlok, hlw, htab, htw⟩ := h
  have htabeq : ∀ j, j < 2 * N₂.nChords →
      tabOf J zta c'.nmem ztlsn j = tabOf J zta c.nmem ztlsn j := by
    zun
    unfold tabOf
    rw [hm _ by_omega, hm _ by_omega,
      hm _ by_omega]
  refine ⟨rs, ls, hrl, fun i hi => ?_, hsok, hrw, hll, fun i hi => ?_, hlok, hlw, ?_, fun j hj => ?_⟩
  · have hi' : i < rd c bSweep 201 := by_omega
    rw [hm _ by_omega, hm _ by_omega,
      hm _ by_omega, hm _ by_omega,
      hm _ by_omega]
    exact hrs i hi
  · have hi' : i < rd c bSweep 301 := by_omega
    rw [hm _ by_omega, hm _ by_omega,
      hm _ by_omega, hm _ by_omega,
      hm _ by_omega, hm _ by_omega,
      hm _ by_omega]
    exact hls i hi
  · intro j hj h1 h2 h3
    have := htab j hj h1 h2 h3
    grind
  · rw [hm _ by_omega, hm _ by_omega,
      hm _ by_omega]
    grind

/-! ## The environment of the answer phase -/

/-- **`AEnv` survives** a step keeping `sw j` for `j < 700` other than `sw 11` and the registers
`sw 620 … 659`, the memory below the allocator, and growing the allocator. -/
theorem aenv_transport {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
    {H : Host} {N₁ N₂ : NF} {E : ℕ} {c c' : Config} (hX : X.CapLocal)
    (h : AEnv P W X Ok J H N₁ N₂ E c)
    (hr : ∀ j, j < 700 → j ≠ 11 → ztoca → c'.nreg ztgc = c.nreg ztgc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    AEnv P W X Ok J H N₁ N₂ E c' := by
  have r : ∀ j, j < 620 → j ≠ 11 → c'.nreg _ = c.nreg _ := fun j h1 h2 =>
    hr j by_omega h2 ztfft
  have e3 := r 3 by_omega by_omega
  have e4 := r 4 by_omega by_omega
  have e5 := r 5 by_omega by_omega
  have e6 := r 6 by_omega by_omega
  have e10 := r 10 by_omega by_omega
  have e20 := r 20 by_omega by_omega
  have e21 := r 21 by_omega by_omega
  have e30 := r 30 by_omega by_omega
  have e31 := r 31 by_omega by_omega
  have eTB : c'.nreg TBR = c.nreg TBR := r 600 by_omega by_omega
  have eTL : c'.nreg TLR = c.nreg TLR := r 601 by_omega by_omega
  have hmE : ∀ a, a < E → c'.nmem a = c.nmem a := fun a ha => hm a (by have := h.hE; omega)
  have h3 : ∀ j, j < 5 → c.nreg ztbbz + 1 + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1; omega
  have h3' : ∀ j, j < 5 → c.nreg ztqm + 1 + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have h20 : ∀ j, j < 5 → c.nreg ztiw + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.1.1; omega
  have h21 : ∀ j, j < 5 → c.nreg zted + j < c.nreg ALLOC := by
    intro j hj; have := h.hst.2.2.2.2.2.2.2.2.2.1.1; omega
  obtain ⟨b3, -⟩ := Restore.nf_bounds h.hN₁
  obtain ⟨b4, -⟩ := Restore.nf_bounds h.hN₂
  have hEA := h.hE
  refine
    { hG := h.hG
      hWh := h.hWh
      hX := ?_
      hcap := ?_
      hP := h.hP
      hOk₁ := h.hOk₁
      hOk₂ := h.hOk₂
      hN₁ := by zvnak; exact Robust.transport h.hN₁ hmE
      hN₂ := by rw [e4]; exact Robust.transport h.hN₂ hmE
      hNF₁ := h.hNF₁
      hNF₂ := h.hNF₂
      hdeg₁ := by rw [e6]; exact h.hdeg₁
      hdeg₂ := by rw [e6]; exact h.hdeg₂
      hsg₁ := by rw [e5]; exact h.hsg₁
      hsg₂ := by rw [e5]; exact h.hsg₂
      hst := st0S_transport h.hst by_grind hm hA
      hE := by_omega
      hWm := h.hWm
      hK := ?_
      htab := ?_
      hbig₁ := by rw [eTL]; exact h.hbig₁
      hbig₂ := by rw [eTL]; exact h.hbig₂
      hbigE := ?_
      hTB := by zupcn; exact h.hTB
      hTW := by zunqt; have := h.hTW; omega
      hout := ?_
      hstops := ?_
      hlog := ?_
      htabw := ?_
      hK₁ := by rw [e3, hm _ by_omega]; exact h.hK₁
      hK₂ := by rw [e4, hm _ by_omega]; exact h.hK₂
      hmd₁ := fun j hj => by rw [e30, e20, hm _ by_grind, hm _ by_grind]; exact h.hmd₁ j hj
      hmd₂ := fun j hj => by rw [e31, e21, hm _ by_grind, hm _ by_grind]; exact h.hmd₂ j hj }
  · rw [e10]; exact X.mono _ _ _ _ _ hA (X.local_ _ _ _ _ _ by_grind h.hX)
  · rw [e5, e10, hX _ _ _ _ _ hm h.hX]; exact h.hcap
  · obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := h.hK
    exact ⟨(r 610 by_omega by_omega).trans k0, (r 611 by_omega by_omega).trans k1,
      (r 612 by_omega by_omega).trans k6, (r 613 by_omega by_omega).trans k4,
      (r 614 by_omega by_omega).trans k5, (r 615 by_omega by_omega).trans k2,
      (r 616 by_omega by_omega).trans k3⟩
  · zun
    zukra
    rw [eTB, hm _ (by have := h.hTW; omega)]
    exact h.htab j hj
  · show rd c' bSweep 201 + rd c' bSweep 301 + 2 * N₂.nChords < 2 ^ c'.nreg TLR
    rw [eTL, show rd c' bSweep 201 = rd c bSweep 201 from r 201 by_omega by_omega,
      show rd c' bSweep 301 = rd c bSweep 301 from r 301 by_omega by_omega]
    exact h.hbigE
  · exact out_transport h.hout by_grind hm h.hstops h.hlog h.htabw
  · show rd c' bSweep 200 + 5 * rd c' bSweep 201 ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 200 = rd c bSweep 200 from r 200 by_omega by_omega,
      show rd c' bSweep 201 = rd c bSweep 201 from r 201 by_omega by_omega]
    have := h.hstops; omega
  · show rd c' bSweep 300 + 7 * rd c' bSweep 301 ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 300 = rd c bSweep 300 from r 300 by_omega by_omega,
      show rd c' bSweep 301 = rd c bSweep 301 from r 301 by_omega by_omega]
    have := h.hlog; omega
  · show rd c' bSweep 302 + 3 * ztbxu ≤ c'.nreg ALLOC
    rw [show rd c' bSweep 302 = rd c bSweep 302 from r 302 by_omega by_omega]
    have := h.htabw; omega
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim
@[expose] public section
def tT : ℕ := sw 700
def tV : ℕ := sw 701
def tN : ℕ := sw 702
def tA : ℕ := sw 703
def tB : ℕ := sw 704

/-- The constants `K0 … K6`. -/
def ksL : List Instr :=
  [.constN K0 0, .constN K1 1, .constN K6 6, .constN K4 4, .constN K5 5, .constN K2 2, .constN K3 3]

/-- The side, `64 (K₁ + K₂ + 1)`, the table base, the counters. -/
def tHead : List Instr :=
  [.copyN sSide ztgmm, .loadN tA ztea, .loadN tB ztbz, .addN tN tA tB, .addN tN tN K1,
    .addN tN tN tN, .addN tN tN tN, .addN tN tN tN, .addN tN tN tN, .addN tN tN tN,
    .addN tN tN tN, .copyN TBR ALLOC, .constN tT 0, .constN tV 1]

/-- One entry of the table. -/
def tBody : List Instr :=
  [.storeN ALLOC tV, .addN ALLOC ALLOC K1, .addN tV tV tV, .addN tT tT K1]

/-- **The initialisation of the answers.** -/
def ansInit : Stmt :=
  .seq ztvfd (.seq mdBlk (.seq ztvfo
    (.seq ztndb (block [.copyN TLR tT]))))
variable {P : Polygon} {W : ℕ}

/-! ## The blocks -/
variable (c : Config)
theorem ksL_exec (hw : WordsBounded W c) (hW : 6 ≤ W) :
    ∃ c' k, Exec P W ztvfd c c' k ∧ k = 7 ∧ Consts c' ∧
      (∀ r, (r < K0 ∨ K3 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ksL Consts K0 K1 K2 K3 K4 K5 K6
  zvmyk at *
  exec_block
  all_goals try omega
  refine ⟨rfl, ztuv, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
  zuby
  grind
theorem tHead_exec (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1) {n : ℕ}
    (hn : c.nmem ztwsx + c.nmem ztwrb + 1 = n) (hW : 64 * n ≤ W) :
    ∃ c' k, Exec P W ztvfo c c' k ∧ k = 14 ∧ c'.nreg sSide = c.nreg ztgmm ∧
      c'.nreg tN = 64 * n ∧ c'.nreg TBR = c.nreg ALLOC ∧ c'.nreg tT = 0 ∧ c'.nreg tV = 1 ∧
      (∀ r, r ≠ sSide → r ≠ tA → r ≠ tB → r ≠ tN → r ≠ TBR → r ≠ tT → r ≠ tV →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tHead sSide tA tB tN TBR tT tV ALLOC K1 at *
  zvmyk at *
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; omega
  · config_simp
  · config_simp
  · config_simp
  simp_all
theorem tBody_exec (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1)
    (h1 : c.nreg ALLOC + 1 ≤ W) (h2 : c.nreg tV + c.nreg tV ≤ W) (h3 : c.nreg tT + 1 ≤ W) :
    ∃ c' k, Exec P W (block tBody) c c' k ∧ k = 4 ∧ c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      c'.nreg tV = c.nreg tV + c.nreg tV ∧ c'.nreg tT = c.nreg tT + 1 ∧
      (∀ r, r ≠ ALLOC → r ≠ tV → r ≠ tT → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem ztm (c.nreg tV) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold tBody tT tV ALLOC K1 at *
  zvmyk at *
  exec_block
  all_goals try (config_simp; omega)
  simp_all

/-! ## The table loop -/
theorem pow_clog64 (n : ℕ) : 64 * n ≤ 2 ^ ztenm := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) n
  grind
theorem lt_of_pow_lt {t n : ℕ} (h : 2 ^ t < 64 * n) : t < Nat.clog 2 n + 6 := by
  zux

  have := Nat.pow_le_pow_right ztciz hc
  have := pow_clog64 n
  omega

/-- The invariant of the table loop (base `A`, bound `Λ = ⌈log₂ n⌉`). -/
abbrev tInv (A Λ n : ℕ) (c' : Config) : Prop :=
  c'.nreg tV = 2 ^ c'.nreg tT ∧ c'.nreg ALLOC = A + c'.nreg tT ∧
    (∀ i, i < c'.nreg tT → c'.nmem ztfna = 2 ^ i) ∧ c'.nreg tT ≤ Λ + 6 ∧ c'.nreg tN = 64 * n
set_option maxRecDepth 20000 in
/-- **The table loop.** -/
theorem tLoop_exec (hw : WordsBounded W c) (hk1 : c.nreg K1 = 1) {n : ℕ}
    (htN : c.nreg tN = 64 * n) (htT : c.nreg tT = 0) (htV : c.nreg tV = 1)
    (hW1 : c.nreg ALLOC + 6 * ztenm ≤ W) (hW2 : 128 * n ≤ W)
    (hW3 : Nat.clog 2 n + 7 ≤ W) :
    ∃ c' k, Exec P W ztndb c c' k ∧ k ≤ 6 * ztenm + 2 ∧
      c'.nreg ALLOC = c.nreg ALLOC + c'.nreg tT ∧ 64 * n ≤ 2 ^ c'.nreg tT ∧
      c'.nreg tT ≤ Nat.clog 2 n + 6 ∧
      (∀ i, i < c'.nreg tT → c'.nmem ztfqi = 2 ^ i) ∧
      zth ∧
      ztgo ∧
      (∀ j, j < 700 → c'.nreg ztgc = c.nreg ztgc) ∧
      ztgnj ∧
      ztimy ∧ c'.output = c.output ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  have hI0 : ztulb := ⟨hw, by_omega, le_rfl, by_omega, by_simp_all⟩
  zujq
  set Λ := Nat.clog 2 n with hΛ
  have hI : tInv A Λ n c := by_grind
  have hiK : ∀ c', IInv W c c' → c'.nreg K1 = 1 := fun c' h' => by
    rw [h'.hin _ by_trivial]; omega
  have hw' := IRS.while (b := tN) _
    (fun c' => Λ + 6 - c'.nreg tT) 4
    (fun c' hc' hlt => by
      obtain ⟨h1, -, -, -, h5⟩ := hc'
      rw [h1, h5] at hlt
      have := lt_of_pow_lt hlt
      omega)
    (fun c' hI' hc' hlt hroom => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hc'
      have hlt' : 2 ^ c'.nreg tT < 64 * n := by_omega
      have htl := lt_of_pow_lt hlt'
      obtain ⟨c'', k, ex, hk, a1, aV, aT, ar, am, arr, arm, ao⟩ :=
        tBody_exec (P := P) c' hI'.hw (hiK c' hI') by_omega by_omega by_omega
      refine IRS.ofExec hI' ex by_omega (fun r hr hra => ar r hra ?_ ?_) arr ztts
        arm ao by_omega by_omega ⟨⟨?_, ?_, fun i hi => ?_, ?_, ?_⟩, ?_⟩ |>.mono le_rfl
        ztb
      · intro h; subst h; exact hr (iscr_sw by_decide by_decide)
      · intro h; subst h; exact hr (iscr_sw by_rfl by_decide)
      · rw [am, upd_other _ _ _ by_grind]
      · grind
      · omega
      · rw [aT] at hi
        zuoem
        zucyp
        · zurj
        simp_all
      · omega
      · rw [ar _ by_decide by_decide
          by_decide]; exact h5
      omega)
    hI0 hI by_omega
  obtain ⟨c', k, ex, hk, hI', hfr, ⟨h1, h2, h3, h4, h5⟩, hex⟩ := hw'
  rw [htT] at hk
  refine ⟨c', k, ex, by_omega, h2, ?_, h4, h3, hI'.hm, hI'.hrm, fun j hj => hI'.hin _ (by
    unfold IFix sw; omega), hfr.1, hfr.2.1, hfr.2.2.1, hfr.2.2.2.2⟩
  omega

/-! ## The initialisation -/
theorem copy1_exec (hw : WordsBounded W c) (d s : ℕ) :
    ∃ c' k, Exec P W (block [.copyN d s]) c c' k ∧ k = 1 ∧ c'.nreg d = c.nreg s ∧
      ztivi ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  simp_all
theorem sw_band {r : ℕ} (hr : bandOf r ∉ sweepBands ∪ oracleBands) (j : ℕ) (hj : j < 10000) :
    r ≠ sw j := by
  zunq
  zuhbg
  rw [band_sw ztce ztce]
  decide
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **The initialisation of the answers.** -/
theorem ansInit_exec (hw : WordsBounded W c) (h90 : c.nreg ztcwn = 0)
    (h91 : c.nreg ztxr = 1) (s20 : c.nreg ztiw + 5 ≤ c.nreg ALLOC)
    (s21 : c.nreg zted + 5 ≤ c.nreg ALLOC) (b3 : c.nreg ztea < c.nreg ALLOC)
    (b4 : c.nreg ztbz < c.nreg ALLOC) {n : ℕ}
    (hn : c.nmem ztwsx + c.nmem ztwrb + 1 = n)
    (hW1 : c.nreg ALLOC + 100 + 6 * ztenm ≤ W) (hW2 : 128 * n ≤ W) :
    ∃ c' k, Exec P W ansInit c c' k ∧ k ≤ 100 + 6 * ztenm ∧
      Frame ztdwg c c' k ∧
      Consts c' ∧ c'.nreg sSide = c.nreg ztgmm ∧
      c'.nreg ztbbz = c.nreg ALLOC ∧ c'.nreg ztqm = c.nreg ALLOC + 6 ∧
      c'.nmem ztm = 0 ∧
      ztxhq ∧
      c'.nmem zthve = 0 ∧
      ztxhr ∧
      c'.nreg TBR = c.nreg ALLOC + 12 ∧ c'.nreg ALLOC = c'.nreg TBR + c'.nreg TLR ∧
      64 * n ≤ 2 ^ c'.nreg TLR ∧ c'.nreg TLR ≤ Nat.clog 2 n + 6 ∧
      (∀ i, i < c'.nreg TLR → c'.nmem (c'.nreg TBR + i) = 2 ^ i) ∧
      zth ∧
      (∀ j, j < 700 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → j ≠ 600 → j ≠ 601 →
        zthif → c'.nreg ztgc = c.nreg ztgc) := by
  zujq
  zuehq
  -- 1. the constants
  obtain ⟨c₁, k₁, e₁, hk₁, hK₁, r₁, m₁, rr₁, rm₁, o₁⟩ := ksL_exec (P := P) c hw by_omega
  have q₁ : ∀ j, zthif → c₁.nreg _ = c.nreg ztgc := fun j hj =>
    r₁ _ (by unfold K0 K3 sw; omega)
  have A₁ : ztizl := r₁ _ by_decide
  -- 2. the model descriptors
  obtain ⟨c₂, k₂, e₂, hk₂, zA, z30, z31, z0, zq, z6, zl, zlo, zr, zrr, zrm, zo⟩ :=
    mdBlk_exec (P := P) c₁ e₁.wb_right by_simp_all
      by_simp_all by_simp_all
      by_simp_all by_omega
  rw [A₁] at zA z30 z31 z0 zq z6 zl zlo
  rw [q₁ 20 by_omega, m₁] at zq
  rw [q₁ 21 by_omega, m₁] at zl
  zvmxn at zlo
  have q₂ : ∀ j, j < 10000 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 →
      c₂.nreg _ = c₁.nreg _ := fun j hj h1 h2 h3 h4 h5 =>
    zr _ ztvzi ztce ztce ztce
      ztce ztce
  have hK₂ : ztgat := by
    rw [show K1 = sw 611 from rfl, q₂ 611 by_omega by_omega by_omega by_omega by_omega
      by_omega]; exact hK₁.2.1
  -- 3. the head of the table
  obtain ⟨c₃, k₃, e₃, hk₃, t98, tN3, tB3, tT3, tV3, tr, tm, trr, trm, tout⟩ :=
    tHead_exec (P := P) c₂ e₂.wb_right hK₂ (n := n) (by
      grind) by_omega
  have q₃ : ∀ j, j < 10000 → j ≠ 98 → j ≠ 703 → j ≠ 704 → j ≠ 702 → j ≠ 600 → j ≠ 700 →
      j ≠ 701 → c₃.nreg _ = c₂.nreg ztgc := fun j hj h1 h2 h3 h4 h5 h6 h7 =>
    tr _ (by unfold sSide sw; omega) (by unfold tA sw; omega) (by unfold tB sw; omega)
      (by unfold tN sw; omega) (by unfold TBR sw; omega) (by unfold tT sw; omega)
      (by unfold tV sw; omega)
  have A₃ : c₃.nreg ALLOC = A + 12 := by
    rw [tr _ by_decide by_decide
      by_decide by_decide by_decide
      by_decide by_decide, zA]
  have hK₃ : ztizo := by
    rw [show K1 = sw 611 from rfl, q₃ 611 by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega by_omega]; exact hK₂
  -- 4. the loop
  obtain ⟨c₄, k₄, e₄, hk₄, l1, l2, l3, l4, lm, lrm, lsw, lr, lrr, lo, lA⟩ :=
    tLoop_exec (P := P) c₃ e₃.wb_right hK₃ tN3 tT3 tV3 by_omega hW2 by_omega
  -- 5. `TLR := tT`
  obtain ⟨c₅, k₅, e₅, hk₅, v5, r5, m5, rr5, rm5, o5⟩ := copy1_exec (P := P) c₄ e₄.wb_right TLR tT
  have ex : Exec P W ansInit c c₅ _ :=
    .seq e₁ ztbq
  have q₅ : ∀ j, j < 700 → j ≠ 601 → c₅.nreg _ = c₄.nreg ztgc := fun j hj h =>
    r5 _ (by unfold TLR sw; omega)
  have A₅ : ztcrj := r5 _ by_decide
  have TB₅ : c₅.nreg TBR = A + 12 := by
    rw [show TBR = sw 600 from rfl, q₅ 600 by_omega by_omega, lsw 600 by_omega]
    exact tB3.trans zA
  have TL₅ := v5
  -- memory
  have mem5 : ∀ a, a < A + 12 → c₅.nmem a = c₂.nmem a := fun a ha => by
    rw [m5, lm a by_omega, tm]
  refine ⟨c₅, _, ex, by_omega, ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_,
    ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, TB₅, ?_, ?_, ?_,
    fun i hi => ?_, fun a ha => ?_, fun j hj h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
  · -- registers outside the bands
    have hT := sw_band hr 601 by_omega
    rw [r5 r hT, lr r hr hra,
      tr r ztrxi (sw_band hr 703 by_omega) (sw_band hr 704 by_omega)
        (sw_band hr 702 by_omega) (sw_band hr 600 by_omega) (sw_band hr 700 by_omega)
        (sw_band hr 701 by_omega),
      zr r hra (sw_band hr 30 by_omega) (sw_band hr 31 by_omega) (sw_band hr 96 by_omega)
        (sw_band hr 97 by_omega) ztrxi,
      r₁ r ?_]
    unfold K0 K3 sw
    zux

    zuhbg
    rw [band_sw by_omega by_omega]
    decide
  · rw [rr5, lrr r hr, trr, zrr, rr₁]
  · zugwe
  · rw [rm5, lrm a by_omega, trm, zrm, rm₁]
  · grind
  · omega
  · omega
  · -- the constants
    have k : ∀ j, 610 ≤ j → j ≤ 616 → c₅.nreg _ = c₁.nreg _ := fun j h1 h2 => by
      rw [q₅ j by_omega by_omega, lsw j by_omega,
        q₃ j by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
        q₂ j by_omega by_omega by_omega by_omega by_omega by_omega]
    obtain ⟨k0, k1, k6, k4, k5, k2, k3⟩ := hK₁
    exact ⟨(k 610 le_rfl by_omega).trans k0, (k 611 by_omega by_omega).trans k1,
      (k 612 by_omega by_omega).trans k6, (k 613 by_omega by_omega).trans k4,
      (k 614 by_omega by_omega).trans k5, (k 615 by_omega by_omega).trans k2,
      (k 616 by_omega le_rfl).trans k3⟩
  · rw [show sSide = sw 98 from rfl, q₅ 98 by_omega by_omega, lsw 98 by_omega]
    rw [show sw 98 = sSide from rfl, t98, q₂ 99 by_omega by_omega by_omega by_omega by_omega by_omega,
      q₁ 99 by_omega]
  · rw [q₅ 30 by_omega by_omega, lsw 30 by_omega,
      q₃ 30 by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      z30]
  · rw [q₅ 31 by_omega by_omega, lsw 31 by_omega,
      q₃ 31 by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      z31]
  · zungy; exact z0
  · zungy; grind
  · zungy; exact z6
  · zungy; exact zl j hj
  · omega
  · grind
  · omega
  · rw [TL₅] at hi
    rw [TB₅, m5, ← A₃]; exact l4 i hi
  · zugwe
  · rw [q₅ j hj h7, lsw j hj,
      q₃ j by_omega h5 by_omega by_omega by_omega h6 by_omega by_omega,
      q₂ j by_omega h1 h2 h3 h4 h5, q₁ j h8]
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim
@[expose] public section
def preS : List Instr := [.copyN ztgmm ztbdl, .constN ztbdl 0]

/-- **The program of the sweep.** -/
def asmProg (ev init loop : Stmt) : Stmt :=
  .seq ztvfj (.seq initS (.seq ev (.seq ansInit (.seq init
    (.seq (.instr (.copyN ztbor ALLOC)) loop)))))

/-- The constant of the assembly. -/
def asmK (κE κ0 κL : ℕ → ℕ) (D : ℕ) : ℕ := κE D + 238 * κ0 D + 10 * κL D + 1000
variable {P : Polygon} {W : ℕ}
theorem preS_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W ztvfj c c' k ∧ k = 2 ∧ c'.nreg ztgmm = c.nreg ztbdl ∧
      c'.nreg ztbdl = 0 ∧ (∀ r, r ≠ sw 99 → r ≠ sw 7 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold preS
  zvmyk at *
  exec_block
  all_goals try omega
  simp_all

/-- Stage 0 keeps `sw 99`. -/
theorem initS_keep99 {c c' : Config} {k : ℕ} (h : Exec P W initS c c' k) :
    c'.nreg ztgmm = c.nreg ztgmm := by
  have hw : BuildRam.wrM (fun r => decide (r ≠ 240099)) initS = true := by_decide
  exact (BuildRam.exec_frameM h hw).1 _ by_rfl

/-! ## The cost -/
theorem clog_mono {a b : ℕ} (h : a ≤ b) : Nat.clog 2 a ≤ Nat.clog 2 b :=
  Nat.clog_mono_right 2 h

/-- **The cost of the assembly.** -/
theorem asm_cost {κE κ0 κL f Λ l₁ n₁ nT K₁ K₂ Lq S Lg TLR A₁ k₂ k₃ k₄ k₅ k₇ : ℕ}
    (hn₁ : n₁ = K₁ + K₂ + 1) (hnT : nT = n₁ + Lq) (hl : l₁ ≤ Λ) (hS : S ≤ 16 * n₁)
    (hLg : Lg ≤ 16 * n₁) (hT : TLR ≤ l₁ + 6) (hA₁ : A₁ ≤ 3 * K₁ + 1)
    (h₂ : k₂ ≤ 220) (h₃ : k₃ ≤ κE * n₁ * ztqms) (h₄ : k₄ ≤ 100 + 6 * (l₁ + 6))
    (h₅ : k₅ ≤ κ0 * ztlfp * zttdn)
    (h₇ : k₇ ≤ κL * ztszo * ztqmr + κL * ztjgo * ztbax) :
    2 + ztcnu ≤
      (κE + 238 * κ0 + 10 * κL + 1000) * nT * ztbsq := by
  set X := nT * ztbsq with hX
  have hnT1 : 1 ≤ nT := by_omega
  have hX1 : Λ + 1 ≤ X := by
    have : 1 * ztbsq ≤ nT * ztbsq := Nat.mul_le_mul_right _ hnT1
    omega
  have e3 : k₃ ≤ κE * X := by
    calc k₃ ≤ κE * n₁ * ztqms := h₃
      _ ≤ κE * nT * ztbsq := by
        zulvp
      _ = κE * X := by_grind
  have e5 : k₅ ≤ 238 * κ0 * X := by
    calc k₅ ≤ κ0 * ztlfp * zttdn := h₅
      _ ≤ κ0 * (34 * nT) * ztzsv := by
        zulvp
      _ = 238 * κ0 * X := by_grind
  have e7 : k₇ ≤ 10 * κL * X := by
    have a : κL * ztszo * ztqmr ≤ κL * nT * ztzsv :=
      Nat.mul_le_mul ztdfv by_omega
    have b : κL * ztjgo * ztbax ≤ κL * (3 * nT) * ztbsq :=
      Nat.mul_le_mul ztdfv by_omega
    grind
  grind
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim Sweep
@[expose] public section
variable {P : Polygon} {W : ℕ}

/-- A chord list below a bound survives a change of the memory above it. -/
theorem chordList_keep {m m' : ℕ → ℕ} {A E : ℕ} {L : List zte} (h : ChordListAt m A L)
    (hb : A + 3 * L.length ≤ E) (he : ∀ a, a < E → m' a = m a) : ChordListAt m' A L := by
  zug
  rw [he _ by_omega, he ztnif by_omega, he ztnig by_omega]
  exact h i hi
theorem bands_sub {r : ℕ} (hr : bandOf r ∉ sweepBands ∪ oracleBands) :
    bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) := by
  zuq
  zuhbg
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> zvmwc <;> decide
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **The environment of the answer phase after `ansInit`.** -/
theorem asm_aenv {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {c c₃ c₄ : Config} (hXl : X.CapLocal) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hX : X.holds P c.nmem ztbagm ztm)
    (hcap : c.nreg ztbcb ≤ X.cap P c.nmem ztbagm) (hP : J.P.Simple)
    (hOk₁ : Ok P ztbw) (hOk₂ : Ok P ztj)
    (hNW₁ : NFWithin c.nmem ztwsx ztm N₁)
    (hNW₂ : NFWithin c.nmem ztwrb ztm N₂)
    (hNF₁ : IsNF ztbw zta N₁) (hNF₂ : IsNF ztj zta N₂)
    (hdeg₁ : (chainModel J.left).DegLe ztwjx ztxgn)
    (hdeg₂ : (chainModel J.right).DegLe ztwis ztxgn)
    (hsg₁ : (chainModel J.left).Semigranular ztwjx ztbagh)
    (hsg₂ : (chainModel J.right).Semigranular ztwis ztbagh)
    (hWm : 2 * J.whole.m + 7 ≤ W)
    -- after stages 2/3
    (hst₃ : SweepEv.St0S P c₃ H J) (hout₃ : SweepEv.Out P J N₂ c₃)
    (hs₃ : rd c₃ bSweep 200 + 5 * rd c₃ bSweep 201 ≤ c₃.nreg ALLOC)
    (hl₃ : rd c₃ bSweep 300 + 7 * rd c₃ bSweep 301 ≤ c₃.nreg ALLOC)
    (ht₃ : rd c₃ bSweep 302 + 3 * ztbxu ≤ c₃.nreg ALLOC)
    (hS : rd c₃ bSweep 201 ≤ 16 * ztks)
    (hLg : rd c₃ bSweep 301 ≤ 16 * ztks)
    (hr₃ : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 10 → c₃.nreg ztgc = c.nreg ztgc)
    (hm₃ : ∀ a, a < c.nreg ALLOC → c₃.nmem a = c.nmem a) (hA₃ : c.nreg ALLOC ≤ c₃.nreg ALLOC)
    -- after `ansInit`
    (hK : Consts c₄) (z30 : c₄.nreg ztbbz = c₃.nreg ALLOC)
    (z31 : c₄.nreg ztqm = c₃.nreg ALLOC + 6) (z0 : c₄.nmem zterl = 0)
    (zq : ∀ j, j < 5 → c₄.nmem (c₃.nreg ALLOC + 1 + j) = c₃.nmem (c₃.nreg ztiw + j))
    (z6 : c₄.nmem (c₃.nreg ALLOC + 6) = 0)
    (zl : ∀ j, j < 5 → c₄.nmem (c₃.nreg ALLOC + 6 + 1 + j) = c₃.nmem (c₃.nreg zted + j))
    (tb : c₄.nreg TBR = c₃.nreg ALLOC + 12) (ta : c₄.nreg ALLOC = c₄.nreg TBR + c₄.nreg TLR)
    (t64 : 64 * ztks ≤ 2 ^ c₄.nreg TLR)
    (ttab : ∀ i, i < c₄.nreg TLR → c₄.nmem (c₄.nreg TBR + i) = 2 ^ i)
    (m₄ : ∀ a, a < c₃.nreg ALLOC → c₄.nmem a = c₃.nmem a)
    (r₄ : ∀ j, j < 700 → j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → j ≠ 600 → j ≠ 601 →
      zthif → c₄.nreg ztgc = c₃.nreg ztgc) :
    AEnv P W X Ok J H N₁ N₂ ztm c₄ := by
  zuce
  set A₃ := c₃.nreg ALLOC with hA₃d
  have hA₄ : A₃ + 12 ≤ c₄.nreg ALLOC := by_omega
  have r : ∀ j, j < 30 → c₄.nreg ztgc = c₃.nreg ztgc := fun j hj =>
    r₄ j by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      ztec
  have rr : ∀ j, (j = 200 ∨ j = 201 ∨ j = 300 ∨ j = 301 ∨ j = 302) →
      c₄.nreg ztgc = c₃.nreg ztgc := fun j hj =>
    r₄ j by_omega by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      ztec
  have e3 : ztzqa := (r 3 by_omega).trans (hr₃ 3 by_simp)
  have e4 : c₄.nreg ztbz = c.nreg ztbz := (r 4 by_omega).trans (hr₃ 4 by_simp)
  have e5 : c₄.nreg ztbcb = c.nreg ztbcb := (r 5 by_omega).trans (hr₃ 5 by_simp)
  have e6 : c₄.nreg ztbey = c.nreg ztbey := (r 6 by_omega).trans (hr₃ 6 by_simp)
  have e10 : c₄.nreg ztcwl = c.nreg ztcwl := (r 10 by_omega).trans (hr₃ 10 by_simp)
  have m : ztced := fun a ha => (m₄ a by_omega).trans (hm₃ a ha)
  zudea

  have hK₁ : ztbaoy := hNW₁.nfAt.1
  have hK₂ : ztbaox := hNW₂.nfAt.1
  -- the stage-0 state with the new model descriptors
  have hst₃' := hst₃
  obtain ⟨-, -, -, -, -, -, d20, w20, d21, w21, -⟩ := hst₃'
  have hn₂ : ztbld := WalkEmbed.cm_n J.right
  obtain ⟨md30, mw30, -⟩ := modelDesc_of_copy (P := P) (A := A₃) (E' := c₄.nreg ALLOC) w20 d20
    le_rfl m₄ z0 zq by_omega
  obtain ⟨md31, mw31, -⟩ := modelDesc_of_copy (P := P) (A := A₃ + 6) (E' := c₄.nreg ALLOC) w21 d21
    by_omega m₄ z6 zl by_omega
  have hst₄ : SweepEv.St0S P c₄ H J := by
    refine st0S_md hst₃ (fun j hj h11 h30 h31 => r₄ j by_omega h30 h31 by_omega by_omega
      by_omega by_omega by_omega ztec) m₄ by_omega ?_ ?_ ?_ ?_
    · grind
    · grind
    · grind
    grind
  have h20 := w20.1
  have h21 := w21.1
  have hnar₁ := SweepEv.arcsTask J.left zta N₁ hP hNF₁
  have hnar₂ := SweepEv.arcsTask J.right zta N₂ hP hNF₂
  refine
    { hG := hG
      hWh := hWh
      hX := ?_
      hcap := ?_
      hP := hP
      hOk₁ := hOk₁
      hOk₂ := hOk₂
      hN₁ := by zvnak; exact Robust.transport hNW₁ m
      hN₂ := by rw [e4]; exact Robust.transport hNW₂ m
      hNF₁ := hNF₁
      hNF₂ := hNF₂
      hdeg₁ := by_grind
      hdeg₂ := by_grind
      hsg₁ := by_grind
      hsg₂ := by_grind
      hst := hst₄
      hE := by_omega
      hWm := hWm
      hK := hK
      htab := ttab
      hbig₁ := by_omega
      hbig₂ := by_omega
      hbigE := ?_
      hTB := by_omega
      hTW := by_omega
      hout := out_transport hout₃ rr m₄ hs₃ hl₃ ht₃
      hstops := ?_
      hlog := ?_
      htabw := ?_
      hK₁ := by_grind
      hK₂ := by_grind
      hmd₁ := fun j hj => by
        rw [z30, zq j hj, r 20 by_omega, m₄ _ by_omega]
      hmd₂ := fun j hj => by
        rw [z31, zl j hj, r 21 by_omega, m₄ _ by_omega] }
  · zummf
    exact X.mono _ _ _ _ _ by_omega (X.local_ _ _ _ _ _ (fun a ha => (m a ha).symm) hX)
  · rw [e5, e10, hXl _ _ _ _ _ m hX]; omega
  · show rd c₄ bSweep 201 + rd c₄ bSweep 301 + 2 * N₂.nChords < 2 ^ c₄.nreg TLR
    rw [show rd c₄ bSweep 201 = rd c₃ bSweep 201 from rr 201 by_simp,
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from rr 301 by_simp]
    omega
  · show rd c₄ bSweep 200 + 5 * rd c₄ bSweep 201 ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 200 = rd c₃ bSweep 200 from rr 200 by_simp,
      show rd c₄ bSweep 201 = rd c₃ bSweep 201 from rr 201 by_simp]
    omega
  · show rd c₄ bSweep 300 + 7 * rd c₄ bSweep 301 ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 300 = rd c₃ bSweep 300 from rr 300 by_simp,
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from rr 301 by_simp]
    omega
  · show rd c₄ bSweep 302 + 3 * ztbxu ≤ c₄.nreg ALLOC
    rw [show rd c₄ bSweep 302 = rd c₃ bSweep 302 from rr 302 by_simp]
    omega
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim Sweep
@[expose] public section
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The assembly of the sweep.** -/
theorem asmGoal : AsmGoal := by
  intro hEv init0 Aux κ0 hInit hLoop
  obtain ⟨evMk, κE, hEv⟩ := hEv
  obtain ⟨loopS, κL, hL⟩ := hLoop
  refine ⟨fun sh => asmProg (evMk sh) init0 ztvyj, asmK κE κ0 κL, ?_⟩
  intro sh Bs F X Ok hXl hBs hsh P W c hw hpre hroom
  obtain ⟨hG, hWh, hX, hcap, h7, hJWF, H, J, N₁, N₂, L, hJ, hP, hOk₁, hOk₂, hNW₁, hNW₂, hNF₁,
    hNF₂, hdeg₁, hdeg₂, hsg₁, hsg₂, hLn, hLm, hLat, hq, hend, hht⟩ := hpre
  zufqq
  -- abbreviations
  have hK₁ : ztplu := hNW₁.nfAt.1
  have hK₂ : ztplv := hNW₂.nfAt.1
  zudea

  zuce
  set n₁ := N₁.nChords + N₂.nChords + 1 with hn₁
  set nT := n₁ + L.length with hnT
  set f := F _ with hf
  set D := rd c bSweep 6 with hD
  set Λ := Nat.clog 2 nT with hΛ
  have eT : c.nmem ztwb + c.nmem ztrl + rd c bSweep 9 + 1 = nT := by
    omega
  rw [eT] at hroom
  have hroomK : A₀ + ztibv * nT * ztbsq ≤ W := hroom
  clear hroom
  have hl₁ : Nat.clog 2 n₁ ≤ Λ := clog_mono by_omega
  have hbig : 1000 * nT ≤ ztibv * nT * ztbsq := by
    grind
  have b3' : c.nreg ztea + 7 < A₀ := b3
  have b4' : c.nreg ztbz + 7 < A₀ := b4
  have hK₁' : ztbaoy := hK₁
  have hK₂' : ztbaox := hK₂
  have hLm' : c.nreg ztfiw + 3 * L.length ≤ A₀ := hLm
  have hWm : 2 * J.whole.m + 7 ≤ W := by
    have := MergeAsm.chain_m_le hJWF.2.2.1 hJ.2.2
    unfold hostWords at hWh; omega
  have hnar₁ := SweepEv.arcsTask J.left _ N₁ hP hNF₁
  -- 1. save the side
  obtain ⟨c₁, k₁, e₁, hk₁, p99, p7, pr, pm, prr, prm, po⟩ := preS_exec (P := P) c hw
  have p : ∀ j, j ≠ 99 → j ≠ 7 → c₁.nreg _ = c.nreg ztgc := fun j h1 h2 =>
    pr _ ztce ztce
  have pA : ztpmy := pr _ by_decide by_decide
  -- 2. stage 0
  obtain ⟨c₂, k₂, e₂, hk₂, hSt0, hF₂⟩ := initS_exec (P := P) c₁ e₁.wb_right (H := H) (J := J)
    by_omega
    (by rw [pm, p 0 by_omega by_omega, p 1 by_omega by_omega, p 2 by_omega by_omega]
        exact hJ)
    (by rw [pm, pA, p 0 by_omega by_omega, p 1 by_omega by_omega,
        p 2 by_omega by_omega]; tauto)
    hWm by_omega
  have h99₂ : c₂.nreg _ = rd c bSweep 7 := (initS_keep99 e₂).trans p99
  have hSt0S₂ := SweepEv.st0S_of_st0 hSt0 p7
  obtain ⟨s90, s91, -, -, slo, sA, sJ, sJWF, -, sw20, -, sw21, -⟩ := hSt0
  have e2 : ∀ j, j < 20 → j ≠ 7 → c₂.nreg _ = c.nreg _ := fun j hj h =>
    (slo j hj).trans (p j by_omega h)
  have A2 : c₂.nreg ALLOC = A₀ + 12 := by_omega
  have m2 : ztfak := fun a ha =>
    (hF₂.2.2.1 a by_omega).trans by_grind
  -- 3. stages 2/3
  have r2 : ∀ j, j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 10 → rd c₂ bSweep j = rd c bSweep j :=
    fun j hj => e2 j by_omega by_omega
  have hPre₂ : SweepEv.Pre X Ok P W c₂ := by
    refine ⟨hG, hWh, ?_, ?_, sJWF, H, J, N₁, N₂, sJ, hP, hOk₁, hOk₂, ?_, ?_, hNF₁, hNF₂, ?_, ?_,
      ?_, ?_, hSt0S₂⟩
    · rw [r2 10 by_simp]
      exact X.mono _ _ _ _ _ by_omega (X.local_ _ _ _ _ _ (fun a ha => (m2 a ha).symm) hX)
    · rw [r2 5 by_simp, r2 10 by_simp, hXl _ _ _ _ _ m2 hX]; omega
    · rw [r2 3 by_simp]; exact (Robust.transport hNW₁ m2).mono by_omega
    · zuoox; exact (Robust.transport hNW₂ m2).mono by_omega
    · zuimh
    · zuimh
    · zuimg
    · zuimg
  have eK2 : c₂.nmem (rd c₂ bSweep 3) + c₂.nmem ztrwj + 1 = n₁ := by
    rw [r2 3 by_simp, r2 4 by_simp, m2 _ by_omega, m2 _ by_omega, hK₁, hK₂]
  have hc3 : SweepEv.cost κE F P c₂ = κE D * n₁ * ztnyf := by
    unfold SweepEv.cost
    rw [eK2, r2 6 by_simp, r2 5 by_simp]
  have room3 := asm_cost (κ0 := κ0 D) (κL := κL D) (nT := nT) (S := 0) (Lg := 0) (TLR := 0)
    (k₃ := κE D * n₁ * ztnyf) (k₄ := 0) rfl rfl hl₁
    by_omega by_omega by_omega by_omega le_rfl le_rfl by_omega ztbg
    ztbg
  obtain ⟨c₃, k₃, e₃, hk₃, hPost, hF₃⟩ := hEv sh Bs F X Ok hXl hBs hsh P W c₂ e₂.wb_right hPre₂
    by_omega
  zvnar at hk₃
  obtain ⟨keep, -, b200', -, b300', -, b302', hS16, hL16, hOut⟩ := hPost
  rw [eK2] at hS16 hL16
  rw [show c₂.nmem ztrwj = N₂.nChords by rw [r2 4 by_simp, m2 _ by_omega, hK₂]]
    at b302'
  have m3 := fun a ha =>
    (hF₃.2.2.1 a by_omega).trans zttsz
  have A3 := hF₃.2.2.2.2.2.1
  have A3' := hF₃.2.2.2.2.2.2
  have hOut₃ := hOut H J N₂ sJ
    (by zuoox; exact NFWithin.nfAt (Robust.transport hNW₂ m2)) hNF₂
  have hSt0S₃ :=
    st0S_transport hSt0S₂ (fun j hj _ => keep j by_omega) hF₃.2.2.1 A3
  have e3 : ∀ j, j < 20 → j ≠ 7 → c₃.nreg _ = c.nreg _ := fun j hj h =>
    (keep j by_omega).trans (e2 j hj h)
  -- 4. the initialisation of the answers
  have room4 := asm_cost (κ0 := κ0 D) (κL := κL D) (nT := nT) (TLR := 0) rfl rfl hl₁
    by_omega by_omega by_omega by_omega hk₂ hk₃ le_rfl ztbg ztbg
  have hF2A := hF₂.2.2.2.2.2.2
  obtain ⟨c₄, k₄, e₄, hk₄, hF₄, hCs, hside, z30, z31, z0, zq, z6, zl, tb, ta, t64, tle, ttab, m4,
    r4⟩ := ansInit_exec (P := P) c₃ e₃.wb_right (n := n₁)
      (by rw [keep 90 by_omega, s90]) (by rw [keep 91 by_omega, s91])
      (by rw [keep 20 by_omega]; have := sw20.1; omega)
      (by rw [keep 21 by_omega]; have := sw21.1; omega)
      (by rw [e3 3 by_omega by_omega]; omega) (by rw [e3 4 by_omega by_omega]; omega)
      (by rw [e3 3 by_omega by_omega, e3 4 by_omega by_omega, m3 _ by_omega,
        m3 _ by_omega, hK₁', hK₂'])
      by_omega by_omega
  have hAE₄ :=
    asm_aenv hXl hG hWh hX hcap hP hOk₁ hOk₂ hNW₁ hNW₂ hNF₁ hNF₂ hdeg₁ hdeg₂ hsg₁ hsg₂ hWm
      hSt0S₃ hOut₃ b200' b300' b302' hS16 hL16 (fun j hj => e3 j by_omega by_omega) m3 by_omega
      hCs z30 z31 z0 zq z6 zl tb ta t64 ttab m4 r4
  have e4 : ∀ j, j < 20 → j ≠ 7 → c₄.nreg _ = c.nreg _ := fun j hj h =>
    (r4 j by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega).trans (e3 j hj h)
  have e4r : ∀ j, (j = 201 ∨ j = 301) → c₄.nreg _ = c₃.nreg _ := fun j hj =>
    r4 j by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega by_omega
  -- 5. the side-0 initialisation
  have hc5 : κ0 (c₄.nreg ztbey) * (rd c₄ bSweep 201 + rd c₄ bSweep 301 + 2 * N₂.nChords + 1) *
      ztlmq = κ0 D * zthkd *
      ztlmq := by
    rw [e4 6 by_omega by_omega, show rd c₄ bSweep 201 = rd c₃ bSweep 201 from e4r 201 by_simp,
      show rd c₄ bSweep 301 = rd c₃ bSweep 301 from e4r 301 by_simp]
    rfl
  have room5 := asm_cost (κL := κL D) (nT := nT)
    (k₅ := κ0 D * zthkd * ztlmq) rfl rfl hl₁ hS16 hL16 tle by_omega hk₂ hk₃ hk₄ le_rfl ztbg
  have hF3A := hF₃.2.2.2.2.2.2
  have hF4A := hF₄.2.2.2.2.2.2
  obtain ⟨c₅, k₅, e₅, hk₅, hF₅, hr₅, hAux₅⟩ := hInit.1 P W X Ok J H N₁ N₂ A₀ c₄ e₄.wb_right hAE₄
    by_omega
  rw [hc5] at hk₅
  have hAE₅ :=
    aenv_transport hXl hAE₄ (fun j hj _ hj' => hr₅ j hj hj') hF₅.2.2.1 hF₅.2.2.2.2.2.1
  -- 6. the result base
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg (sw 11) (c₅.nreg ALLOC) } with hc₆
  have e₆ : Exec P W _ c₅ c₆ 1 := Exec.copyN e₅.wb_right _ ALLOC
  have r6 : ∀ r, r ≠ sw 11 → c₆.nreg r = c₅.nreg r := fun r hr => upd_other _ _ _ hr
  have A6 : ztfkx := r6 _ by_decide
  have hAE₆ :=
    aenv_transport hXl hAE₅ (fun j hj h11 _ => r6 _ ztce) ztcj
      (by rw [A6])
  have e6 : ∀ j, j < 20 → j ≠ 7 → j ≠ 11 → c₆.nreg ztgc = c.nreg _ := fun j hj h h' => by
    rw [r6 _ ztce, hr₅ j by_omega by_omega, e4 j hj h]
  have A5 := hF₅.2.2.2.2.2.1
  have A5' := hF₅.2.2.2.2.2.2
  have m6 : ztkoa := fun a ha => by
    show c₅.nmem a = c.nmem a
    rw [hF₅.2.2.1 a by_omega, m4 a by_omega, m3 a ha]
  have hTL6 : c₆.nreg TLR = c₄.nreg TLR := by
    rw [r6 _ by_decide]; exact hr₅ 601 by_omega by_omega
  have hAB : ABase P W X Ok Aux J H N₁ N₂ A₀ L ztdae c₆ := by
    refine
      { hw := e₆.wb_right
        hA := hAE₆
        hi := h7
        hside := ?_
        hAux := fun _ => hInit.2 P J N₂ c₅ _ hAux₅
        hLn := by rw [e6 9 by_omega by_omega by_omega]; exact hLn
        hLm := by rw [e6 8 by_omega by_omega by_omega, A6]; omega
        hLat := by
          rw [e6 8 by_omega by_omega by_omega]; exact chordList_keep hLat hLm m6
        hq := hq
        hht := hht
        hend := hend
        hres := by_rfl
        hTLR := by rw [hTL6]; omega }
    rw [r6 _ by_decide, show sSide = sw 98 from rfl,
      hr₅ 98 by_omega by_omega, show sw 98 = sSide from rfl, hside,
      keep 99 by_omega, h99₂]
  -- 7. the loop
  have hlc : loopCost κL F c₆ N₁ L = κL D * ztkr * ztpbb +
      κL D * ztyz * ztbax := by
    unfold loopCost
    rw [hTL6, e6 6 by_omega by_omega by_omega, e6 5 by_omega by_omega by_omega]
    rfl
  have room7 := asm_cost (nT := nT)
    (k₇ := κL D * ztkr * ztpbb +
      κL D * ztyz * ztbax) rfl rfl hl₁ hS16 hL16 tle hnar₁ hk₂ hk₃ hk₄ hk₅
    le_rfl
  obtain ⟨c₇, k₇, e₇, hk₇, hI₇, hfr₇, R, hRl, hR11, hRat, hSees⟩ :=
    hL sh Bs F X Ok hsh hBs hXl P W c₆ J H N₁ N₂ A₀ L ztdae hAB
      by_omega
  rw [hlc] at hk₇
  have final := asm_cost (nT := nT) rfl rfl hl₁
    hS16 hL16 tle hnar₁ hk₂ hk₃ hk₄ hk₅ hk₇
  have A7 := hfr₇.2.2.2.1
  have A7' := hfr₇.2.2.2.2
  have h11 : c₇.nreg _ = c₆.nreg ztbor := hI₇.hin _ by_trivial
  have v11 : c₆.nreg ztbor = c₅.nreg ALLOC := by_rfl
  refine ⟨c₇, k₁ + ztcnu,
    .seq e₁ ztfc, ?_, ?_, ?_⟩
  · -- the cost
    beta_reduce
    rw [eT, hk₁]
    unfold asmK
    omega
  · -- the postcondition
    intro H' J' L' hJ' hL9 hL8
    obtain rfl := junction_unique hJ hJ'
    obtain rfl := BuildNF.chordListAt_unique hLat hL8 by_omega
    refine ⟨R, ?_, ?_, hRl, ?_, hSees⟩
    · show A₀ ≤ c₇.nreg ztbor
      omega
    · show c₇.nreg ztbor + 4 * L.length ≤ c₇.nreg ALLOC
      omega
    · show ResultListAt c₇.nmem (c₇.nreg ztbor) R
      rw [h11]; omega
  · -- the frame
    zuife
    · rw [hfr₇.1 r hr hra, r6 r (sw_band hr 11 by_omega), hF₅.1 r hr hra, hF₄.1 r hr hra,
        hF₃.1 r hr hra, hF₂.1 r ztvet hra, pr r (sw_band hr 99 by_omega)
        (sw_band hr 7 by_omega)]
    · rw [hfr₇.2.1 r hr]
      show c₅.rreg r = c.rreg r
      rw [hF₅.2.1 r hr, hF₄.2.1 r hr, hF₃.2.1 r hr, hF₂.2.1 r ztvet, prr]
    · rw [hI₇.hm a by_omega, m6 a ha]
    · rw [hI₇.hrm a by_omega]
      show c₅.rmem a = c.rmem a
      rw [hF₅.2.2.2.1 a by_omega, hF₄.2.2.2.1 a by_omega, hF₃.2.2.2.1 a by_omega,
        hF₂.2.2.2.1 a by_omega, prm]
    · rw [hfr₇.2.2.1]
      show c₅.output = c.output
      rw [hF₅.2.2.2.2.1, hF₄.2.2.2.2.1, hF₃.2.2.2.2.1, hF₂.2.2.2.2.1, po]
    · omega
    omega
open WalkEmbed
theorem qPt_end {J : Merge.Junction} {P : Polygon} {N₂ : NF} (hN : IsNF ztj zta N₂)
    (L₁ : List zte) {j : ℕ} (hj : j < 2 * N₂.nChords) :
    qPt J P 1 ztqxd j = endOrigin J zta N₂ j := by
  rw [(endOrigin_eq J hN hj).1]
  have hlen : ztmsd := by
    zugge
  have hget : (sweepEndQ N₂.chords ++ L₁).getD j ztt =
      (let r := N₂.chords.getD ztwm ztrp
       if j % 2 = 0 then ztdic else ztdid) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left by_omega]
    simp only [sweepEndQ, List.getElem?_map, List.getElem?_range (show j < 2 * N₂.chords.length
      from hj), Option.map_some, Option.getD_some]
  unfold qPt
  zujiy
  have hsc : ztsmf := by_rfl
  rw [hsc]
  unfold endPos NF.chord CRec.lpos CRec.rpos
  grind
open Classical in
/-- **At most five brute-force queries.** -/
theorem brute_card (hT : TopCountSpec) {P : Polygon} {J : Merge.Junction} {N₂ : NF}
    (hG : GoodEnv P) (hP : J.P.Simple) (hN : IsNF ztj zta N₂)
    {L : List zte} {i : ℕ}
    (hend : i = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3) :
    ((Finset.range L.length).filter
      (fun j => i = 1 ∧ BruteQ J N₂ j ztdvu)).card ≤ 5 := by
  by_cases hi : i = 1
  swap
  · simp_all
  obtain ⟨L₁, rfl, hL₁⟩ := hend hi
  zuipx
  have hlen : (sweepEndQ N₂.chords ++ L₁).length = 2 * N₂.nChords + L₁.length := by
    zugge
  set K := 2 * N₂.nChords with hK
  have hsub : (Finset.range (sweepEndQ N₂.chords ++ L₁).length).filter
      (fun j => 1 = 1 ∧ BruteQ J N₂ j (qPt J P 1 ztqxd j)) ⊆
      Finset.Ico K ztnly ∪
        (Finset.range K).filter ztwsy := by
    zun
    simp only [Finset.mem_filter, Finset.mem_range, hlen] at hj
    obtain ⟨hjL, -, hb⟩ := hj
    rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    zucor
    · omega
    · by_cases hjK : K ≤ j
      · omega
      · push Not at hjK
        refine Or.inr ⟨hjK, ?_⟩
        rw [← qPt_end hN L₁ hjK]; exact hb
  have h2 : ((Finset.range K).filter ztwsy).card ≤ 2 := by
    tauto
  calc _ ≤ (Finset.Ico K ztnly ∪
        (Finset.range K).filter ztwsy).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Ico K ztnly).card +
        ((Finset.range K).filter ztwsy).card :=
      Finset.card_union_le _ _
    _ ≤ 5 := by rw [Nat.card_Ico]; omega
open Classical in
/-- **The sum of the query costs.** -/
theorem qCost_sum (hT : TopCountSpec) {κ : ℕ → ℕ} {F : ℕ → ℕ} {c₀ : Config} {P : Polygon}
    {J : Merge.Junction} {N₁ N₂ : NF} (hG : GoodEnv P) (hP : J.P.Simple)
    (hN : IsNF ztj zta N₂) {L : List zte} {i : ℕ}
    (hend : i = 1 → ∃ L₁ : List zte, L = sweepEndQ N₂.chords ++ L₁ ∧ L₁.length ≤ 3) :
    ∑ j ∈ Finset.range L.length, qCost κ F c₀ J P N₁ N₂ L i j ≤
      L.length * ztbajz +
        5 * (κ zto * ztyz * ztwju) := by
  unfold qCost
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have := brute_card hT hG hP hN hend (i := i)
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _
