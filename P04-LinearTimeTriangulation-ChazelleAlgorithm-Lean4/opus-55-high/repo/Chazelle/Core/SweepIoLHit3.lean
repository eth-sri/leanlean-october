module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.DownPhaseTransWt

namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The far end of a chord at `x` -/
variable {C : Chain} {N : NF} (m f : ℕ → ℕ)
/-- **A chord record attached at `x` along the direction** has its far end on the ray. -/
theorem chord_far (hNF : IsNF ztc zta N) {k : ℕ}
    (hk : k < N.nChords) {x : WPos} {d : ℕ} (hca : Sweep.ChordAt ztcgt x d) :
    ProperPos ztc zta P.n ztypy ∧
      (Sweep.farPos ztcgt d).edge < (chainModel C).W.n ∧
      ∃ τ, 0 < τ ∧ (chainModel C).pos zta ztypy =
        rayPt ztwjd ztwf τ := by
  zuc
  zuftg
  have hFam := hNF.1
  obtain ⟨-, -, -, reg, -, -, -, -, -, hhlt, -⟩ := hNF
  have hh := hhlt k hk
  zvmxg at hh
  have hmem : (N.chord k).toSet _ _ ∈ N.F ztc zta :=
    ⟨N.chord k, by unfold NF.chord; rw [NFLoc.getD_of_lt _ hk]; grind, rfl⟩
  obtain ⟨y, a, b, hH, -, hey, -, -⟩ := Merge.augChords_spec (hFam.2.1 hmem)
  zudoh
  obtain ⟨hla, hrb, -⟩ := Sweep.rec_pos_ends hA hey hab
  obtain ⟨⟨hlp, hl0, hl1, -⟩, ⟨hrp, hr0, hr1, -⟩⟩ := hA
  unfold Sweep.ChordAt at hca
  unfold Sweep.farPos
  rcases hca with ⟨hd, hlx, hhx⟩ | ⟨hd, hrx, hhx⟩
  · have hx : x = (N.chord k).lpos := by
      unfold CRec.lpos; simp_all
    rw [ite_eq_left hd, hx, hla, hrb, hd]
    refine ⟨⟨hr0, hr1, by_tauto⟩, hrp, b - a, by_linarith, ?_⟩
    apply Geometry.point_ext <;> simp [rayPt, dirOf]
  · have hx : x = (N.chord k).rpos := by
      unfold CRec.rpos; simp_all
    rw [ite_eq_right hd, hx, hla, hrb]
    refine ⟨⟨hl0, hl1, by_tauto⟩, hlp, b - a, by_linarith, ?_⟩
    apply Geometry.point_ext <;> simp [rayPt, dirOf, hd]

/-! ## Registers and programs of the scan -/
def sX : ℕ := sw 1130
def sY : ℕ := sw 1131
def sNc : ℕ := sw 1132
def sCl : ℕ := sw 1133
def sT : ℕ := sw 1134
def sK : ℕ := sw 1135
def sCh : ℕ := sw 1136
def sLp : ℕ := sw 1137
def sRp : ℕ := sw 1138
def sH1 : ℕ := sw 1139
def sFe : ℕ := sw 1140
def sFh : ℕ := sw 1141
def sR5 : ℕ := sw 1142
def sL7 : ℕ := sw 1143
def sC3 : ℕ := sw 1144

/-- The registers of the scan. -/
def SSet (r : ℕ) : Prop := sw 1130 ≤ r ∧ r ≤ sw 1144

/-- The bases of the normal form. -/
def scanInitL : List Instr :=
  [.addN sX lNF K5, .loadN sR5 sX, .addN sX sX K2, .loadN sL7 sX, .addN sX lNF K3, .loadN sC3 sX]

/-- The head of the scan of the region in `rr`. -/
def scanHeadL (rr : ℕ) : List Instr :=
  [.addN sX rr rr, .addN sX sX sX, .addN sX sX rr, .addN sX sR5 sX, .addN sY sX K2, .loadN sNc sY,
    .addN sY sX K3, .loadN sCl sY, .constN sT 0]
def scanHead (rr : ℕ) : Stmt :=
  .seq (block ztglu) (.ifLtN K0 sNc (.instr ztlde) .skip)

/-- Read the chord at place `sT`: its height code (plus one) and its walk edges. -/
def scanReadL : List Instr :=
  [.addN sX sCl sT, .loadN sK sX, .addN sX sK sK, .addN sX sX sX, .addN sX sX sK, .addN sX sC3 sX,
    .loadN sCh sX, .addN sY sX K1, .loadN sLp sY, .addN sY sY K1, .loadN sRp sY,
    .addN sH1 sCh K1]

/-- `s` if the registers `a`, `b` hold equal values. -/
def eqT (a b : ℕ) (s : Stmt) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip s)

/-- Offer the position `(src, sH1)`. -/
def offerFar (src : ℕ) : Stmt :=
  .seq (block [.copyN sFe src, .copyN sFh sH1]) (offerF accA lCD sFe sFh lT lD lN lO)

/-- The test `ChordAt` and the offer of the far end. -/
def scanTest : Stmt :=
  .ifLtN lD K1 ztisi
    (.ifLtN K1 lD ztisi
      (eqT sLp lE (eqT sH1 lH (offerFar sRp))))
def scanBody : Stmt := .seq (block scanReadL) (.seq scanTest (block [.addN sT sT K1]))
def scanR (rr : ℕ) : Stmt := .seq ztwdh (.whileLtN sT sNc scanBody)

/-- **The chord ends of the three regions.** -/
def lhScan : Stmt := .seq (block scanInitL) (.seq (scanR lR0) (.seq (scanR lR1) (scanR lR2)))
theorem scanReadL_val (hk1 : f K1 = 1) :
    regB m scanReadL f sLp = m (f sC3 + 5 * m ztesa + 1) ∧
    regB m scanReadL f sRp = m (f sC3 + 5 * m ztesa + 2) ∧
    regB m scanReadL f sH1 = m ztyqi + 1 := by
  zubx
  simp only [scanReadL, regB, regI, upd, sX, sY, sCl, sT, sK, sC3, sCh, sLp, sRp, sH1, K1, sw]
  grind
theorem scanReadL_ok (hk1 : f K1 = 1) (hb : f sCl + f sT ≤ W)
    (hb2 : f sC3 + 5 * m ztesa + 2 ≤ W) (hb3 : m ztyqi + 1 ≤ W) :
    okB W m scanReadL f := by
  zubx
  have hb' : f 241133 + f 241134 ≤ W := hb
  have hb2' : f 241144 + 5 * m ztdnj + 2 ≤ W := hb2
  have hb3' : m (f 241144 + (m ztdnj + m ztdnj +
      (m ztdnj + m ztdnj) + m ztdnj)) + 1 ≤ W := by
    rw [show f 241144 + (m _ + m _ +
      (m _ + m _) + m _) =
      f 241144 + 5 * m _ by ring]; tauto
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [scanReadL, okB, okI, regI, upd, sX, sY, sCl, sT, sK, sC3, sCh, sLp, sRp, sH1, K1, sw]
  grind

/-! ## The accumulator during the scan -/

/-- The chords of a list whose far ends (attached at `x` along `d`) are offered. -/
def ChordsDone (P : Polygon) (C : Chain) (N : NF) (x : WPos) (d : ℕ) (ks : List ℕ)
    (L : Set ℝ) : Prop :=
  ∀ k ∈ ks, Sweep.ChordAt ztcgt x d → ∃ τ ∈ L,
    (chainModel C).pos zta ztypy =
      rayPt ztwjd ztwf τ
theorem chordsDone_mono {x : WPos} {d : ℕ} {ks : List ℕ} {L L' : Set ℝ}
    (h : ChordsDone P C N x d ks L) (hL : L ⊆ L') : ChordsDone P C N x d ks L' := by
  intro k hk hca
  obtain ⟨τ, hτ, he⟩ := h k hk hca
  grind

/-! ## Offering a far end -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem offerFar_irs {src : ℕ} (hsrc : src = sLp ∨ src = sRp) {C : Chain} {Mod : ℕ → Chain}
    {R₀ : ℝ} {z : Point} {L : Set ℝ} {τ : ℝ} (hI : IInv W c₀ c) (hK : Consts c₀)
    (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W) (hctx : ChainCtx P W c lCD C)
    (hacc : AccOK P accA Mod R₀ z ztmk L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod ztjsj = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (he : c.nreg src < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztkjz)
    (hpos : (chainModel C).pos zta ztkjz = rayPt z ztmk τ)
    (hy : |z.2| < R₀) (hroom : c.nreg ALLOC + ztjfl ≤ W) :
    IRS P W c₀ ztwax c ztjfl (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z ztmk L' c' ∧
        (L' = L ∨ (L' = insert τ L ∧ OnCB C (rayPt z ztmk τ))) ∧
        ztfvm) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → ztbni → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hs : src ≠ sFe ∧ src ≠ sFh ∧ 240700 ≤ src ∧ src < 250000 := by
    rcases hsrc with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sLp, sRp, sFe, sFh, sw]
  have hok : okB W c.nmem [.copyN sFe src, .copyN sFh sH1] c.nreg :=
    ⟨iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide, trivial⟩
  refine IRS.seq (K₂ := offerFK) zteei ?_ |>.mono by_simp ztb
  zugn
  have vFe : c₁.nreg sFe = c.nreg src := by
    zubuz
  have vFh : c₁.nreg sFh = c.nreg sH1 := by
    zubuz
  have k1 : ∀ q, q ≠ sFe → q ≠ sFh → c₁.nreg q = c.nreg q := by
    intro q h1 h2; zvmwl; show regB c.nmem [.copyN sFe src, .copyN sFh sH1] c.nreg q = _
    zuie
  zull
  have kk : ∀ q, ¬ SSet q → c₁.nreg q = c.nreg q := fun q hq =>
    k1 q ztwpt
      ztwpt
  have t1 := kk lT (by unfold SSet lT sw; omega)
  have d1 := kk lD (by unfold SSet lD sw; omega)
  have n1 := kk lN (by unfold SSet lN sw; omega)
  have cd1 := kk lCD (by unfold SSet lCD sw; omega)
  have hA1 := kk ALLOC (by unfold SSet ALLOC sw; omega)
  have a1 : ∀ j, j ≤ 12 → c₁.nreg _ = c.nreg ztbzh := fun j hj =>
    kk _ (by unfold SSet accA sw; omega)
  refine (offerF_irs (τ := τ) hI₁ hK hG hW3
    ⟨by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    (by rw [d1]; exact hacc.transport a1) by_omega
    (by rw [t1, hMod]; exact hctx.transport cd1 by_simp_all hA1.ge)
    by_simp_all by_simp_all by_simp_all
    by_simp_all by_simp_all hy
    by_omega).mono le_rfl ?_
  rintro c' ⟨⟨L', hacc', hL', hc'⟩, k2, hA2, hm2⟩
  simp only [d1, t1, hMod] at hacc' hL' hc'
  refine ⟨by_grind, fun r hr hs1 hs2 hra hro hro1 hrA => ?_, by_omega,
    fun a ha => by_grind⟩
  grind

/-! ## The test of a chord -/

/-- The cost of the test. -/
def scanTestK : ℕ := 14 + offerFK
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The double equality test and the offer.** -/
theorem eqOffer_irs {a src : ℕ} (_ha : a = sLp ∨ a = sRp) (hsrc : src = sLp ∨ src = sRp)
    {C : Chain} {N : NF} {k : ℕ} (hk : k < N.nChords) {Mod : ℕ → Chain} {R₀ : ℝ} {z : Point}
    {L : Set ℝ} (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hW3 : P.n + 3 ≤ W)
    (hctx : ChainCtx P W c lCD C) (hNF : IsNF ztc zta N)
    (hacc : AccOK P accA Mod R₀ z ztmk L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod ztjsj = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hz : z = (chainModel C).pos zta ⟨c.nreg lE, c.nreg lH⟩) (hy : |z.2| < R₀)
    (hiff : (c.nreg a = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt ztcgt zthj ztcuy)
    (hfar : Sweep.farPos ztcgt ztcuy = ztkjz)
    (hroom : c.nreg ALLOC + ztndr ≤ W) :
    IRS P W c₀ (eqT a lE (eqT sH1 lH ztwax)) c ztndr (fun c' =>
      (∃ L', AccOK P accA Mod R₀ z ztmk L' c' ∧ L ⊆ L' ∧
        ztxaq ∧
        ztxpa) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → ztbni → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  -- no match: nothing offered
  have hnone : ¬ Sweep.ChordAt ztcgt zthj ztcuy → ∀ K',
      IRS P W c₀ .skip c K' (fun c' =>
        (∃ L', AccOK P accA Mod R₀ z ztmk L' c' ∧ L ⊆ L' ∧
          ztxaq ∧
          ztxpa) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → ztbni → r ≠ lO →
          r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    intro hnc K'
    refine IRS.skip hI ⟨⟨L, hacc, le_rfl, fun τ hτ => Or.inl hτ, fun _ k' hk' hca => ?_⟩,
      fun _ _ _ _ _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩
    simp_all
  zumso
  by_cases h1 : c.nreg a < c.nreg lE
  · exact (IRS.ifT h1 (hnone by_grind ztsug)).mono
      by_omega by_grind
  refine IRS.mono (K := ztsug + 2) ztfnr by_omega ztb
  by_cases h2 : c.nreg lE < c.nreg a
  · exact (IRS.ifT h2 (hnone by_grind ztsub)).mono
      by_omega by_grind
  refine IRS.mono (K := ztsub + 2) ztsya by_omega ztb
  by_cases h3 : c.nreg sH1 < c.nreg lH
  · exact (IRS.ifT h3 (hnone by_grind ztstd)).mono
      by_omega by_grind
  refine IRS.mono (K := ztstd + 2) (IRS.ifF h3 ?_) by_omega ztb
  by_cases h4 : c.nreg lH < c.nreg sH1
  · exact (IRS.ifT h4 (hnone by_grind ztjfl)).mono
      by_omega by_grind
  refine IRS.mono (K := ztjfl + 2) (IRS.ifF h4 ?_) by_omega ztb
  -- a match
  have hca : Sweep.ChordAt _ zthj _ := hiff.1 by_omega
  obtain ⟨hpp, hedge, τ, hτ, hpos⟩ := chord_far hNF hk hca
  rw [hfar] at hpp hedge hpos
  rw [← hz] at hpos
  refine (offerFar_irs hsrc hI hK hG hW3 hctx hacc htag hMod hR hn hedge hpp hpos hy
    by_omega).mono le_rfl ?_
  rintro c' ⟨⟨L', hacc', hL', hc'⟩, k', hA', hm'⟩
  refine ⟨⟨L', hacc', ?_, fun τ' hτ' => ?_, fun hzt k'' hk'' hca' => ?_⟩, k', hA', hm'⟩
  · grind
  · grind
  grind
end
end SweepIo
end Chazelle.Core
section
set_option hygiene false
local macro "zqbbz" : tactic => `(tactic| have e2 : c.nmem zter + 5 * r + 3 = c.nmem zter + (5 * r + 3) := by_ring)
local macro "zqbca" : tactic => `(tactic| (have e2 : ztpoq := hk2
                                           have e3 : ztdjw := hk3))
local macro "zqbcb" : tactic => `(tactic| (rintro c₁ hI₁ - - hc1
                                           have hm1 : ztwh := by zvmwl))
local macro "zqbcc" : tactic => `(tactic| (unfold SSet sw at hrr
                                           have n1 : rr ≠ 241130 := by_omega
                                           have n2 : rr ≠ 241131 := by_omega))
local macro "zqbcd" : tactic => `(tactic| have hAW : ztcga := by_omega)
set_option hygiene true

/-!
# The sweep RAM (WP-D), answers: the local hit, part 4 (the scan loops)

The test of one chord, the loop over the exit chords of one region, and the scan of the three
regions of the local hit.
-/
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open OracleQ (sj sk ek succP predP)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Two list and memory facts -/
variable {E : ℕ} {m : ℕ → ℕ} {X : ℕ → Prop} {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ} {x : WPos} {d : ℕ} {rr : ℕ}
/-- A word reached through a doubly indirect pointer that robustly holds a value lies below the
bound. -/
theorem robust_addr3 {b a o t v : ℕ}
    (h : Robust E m fun m' => m' (m' b + m' (m' a + o) + t) = v) (ha : a < E)
    (hao : m a + o < E) : b < E ∧ m b + m ztlre + t < E := by
  have hb : ztsdn := by
    zucux
    have := h (Function.update (Function.update m b ztds) (b + 1 + m ztlre + t) ztsp)
      ztjwq
    grind
  refine ztonz
  zucux
  have := h (Function.update m (m b + m ztlre + t) ztsp) (fun x hx => by
    grind)
  grind
theorem take_succ_getD {l : List ℕ} {t : ℕ} (h : t < l.length) :
    l.take ztbx = l.take t ++ [l.getD t 0] := by
  simp_all

/-! ## Register sets and frames -/

/-- The registers written by the read of a chord. -/
def RSet (q : ℕ) : Prop :=
  q = sX ∨ q = sY ∨ q = sK ∨ q = sCh ∨ q = sLp ∨ q = sRp ∨ q = sH1

/-- The registers written by one test (read and offer). -/
def WSet (q : ℕ) : Prop := RSet q ∨ q = sFe ∨ q = sFh
theorem scanReadL_other' (m f : ℕ → ℕ) {q : ℕ} (h : ¬ RSet q) : regB m scanReadL f q = f q :=
  regB_other m scanReadL f (fun i hi => by
    simp only [scanReadL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> apply h <;> simp [RSet])

/-- **The frame of a scan step**: registers outside the oracle bands, the set `X`, the
accumulator block, `lO, lO + 1` and the allocator are unchanged; the allocator grows; memory
below it is kept. -/
def XFr (X : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ X r → ztbni → r ≠ lO → r ≠ lO + 1 →
    r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
theorem XFr.refl (X : ℕ → Prop) (c : Config) : XFr X c c :=
  ⟨by_omega, le_rfl, by_omega⟩
theorem XFr.trans {c₁ c₂ c₃ : Config} (h₁ : XFr X c₁ c₂) (h₂ : XFr X c₂ c₃) :
    XFr X c₁ c₃ :=
  ⟨fun r a b d e f g => (h₂.1 r a b d e f g).trans (h₁.1 r a b d e f g), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a ztkan).trans ztdux⟩
theorem XFr.mono {X Y : ℕ → Prop} {c c' : Config} (h : XFr X c c') (hXY : ∀ r, X r → Y r) :
    XFr Y c c' :=
  ⟨fun r a b d e f g => h.1 r a by_grind d e f g, h.2.1, h.2.2⟩

/-! ## The environment of the scan -/

/-- **The environment of the scan**: the chain and its normal form, the tag, the position `x`
(registers `lE, lH`) and the direction code `d` (register `lD`). -/
structure SEnv (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (Mod : ℕ → Chain) (R₀ : ℝ) (x : WPos)
    (d : ℕ) (c : Config) : Prop where
  hG : GoodEnv P
  hW3 : P.n + 3 ≤ W
  hctx : ChainCtx P W c lCD C
  hNF : IsNF ztc zta N
  htag : c.nreg lT ≤ 2
  hMod : Mod ztjsj = C
  hR : C.radius = R₀
  hn : c.nreg lN = 2 * C.m + 7
  hE : c.nreg lE = x.edge
  hH : c.nreg lH = x.hgt
  hD : c.nreg lD = d
  hy : |((chainModel C).pos zta x).2| < R₀
theorem SEnv.transport
    {c c' : Config} (h : SEnv P W C N Mod R₀ x d c)
    (hr : ∀ r, r = lCD ∨ r = lT ∨ r = lN ∨ r = lE ∨ r = lH ∨ r = lD → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    SEnv P W C N Mod R₀ x d c' := by
  obtain ⟨hG, hW3, hctx, hNF, htag, hMod, hR, hn, hE, hH, hD, hy⟩ := h
  have r1 := hr lCD ztp
  have r2 := hr lT by_omega
  have r3 := hr lN by_omega
  have r4 := hr lE by_omega
  have r5 := hr lH by_omega
  have r6 := hr lD by_omega
  exact ⟨hG, hW3, hctx.transport r1 hm hA, hNF, by_omega, by_simp_all, hR,
    by omega, by_omega, by_omega, by_omega, hy⟩

/-- The registers of the environment lie outside the scan's writes. -/
theorem SEnv.keep
    {c c' : Config} (h : SEnv P W C N Mod R₀ x d c) (fr : XFr SSet c c') :
    SEnv P W C N Mod R₀ x d c' :=
  h.transport (fun r hr => by
    refine fr.1 r ztods ?_ ?_ ?_ ?_ ?_ <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [SSet, accA, lO, ALLOC, lCD, lT, lN, lE, lH, lD, sw] <;> omega) fr.2.2 fr.2.1

/-! ## Growth of the accumulator -/

/-- **A step of the accumulator**: from `L`, only good candidates are added, and (below the top)
the far ends of the matching chords of `ks` are offered. -/
def AccStep (P : Polygon) (C : Chain) (N : NF) (Mod : ℕ → Chain) (R₀ : ℝ) (x : WPos) (d : ℕ)
    (ks : List ℕ) (L : Set ℝ) (c : Config) : Prop :=
  ∃ L', AccOK P accA Mod R₀ ztwjd ztwf L' c ∧ L ⊆ L' ∧
    (∀ τ ∈ L', τ ∈ L ∨ ztbajy) ∧
    (((chainModel C).pos zta x).2 ≤ C.top.2 → ChordsDone P C N x d ks L')
theorem AccStep.transport
    {ks : List ℕ} {L : Set ℝ} {c c' : Config} (h : AccStep P C N Mod R₀ x d ks L c)
    (hr : ∀ j, j ≤ 12 → c'.nreg ztbzh = c.nreg ztbzh) :
    AccStep P C N Mod R₀ x d ks L c' := by
  obtain ⟨L', a, s, g, dn⟩ := h
  exact ⟨L', a.transport hr, s, g, dn⟩
theorem AccStep.init
    {L : Set ℝ} {c : Config}
    (h : AccOK P accA Mod R₀ ztwjd ztwf L c) :
    AccStep P C N Mod R₀ x d [] L c :=
  ⟨L, h, le_rfl, by_simp_all, fun _ _k hk => by_simp_all⟩
theorem AccStep.trans
    {ks₁ ks₂ : List ℕ} {L L' : Set ℝ} {c : Config} (h₁ : L ⊆ L')
    (g₁ : ∀ τ ∈ L', τ ∈ L ∨
      ztbajy)
    (d₁ : ((chainModel C).pos zta x).2 ≤ C.top.2 → ChordsDone P C N x d ks₁ L')
    (h₂ : AccStep P C N Mod R₀ x d ks₂ L' c) : AccStep P C N Mod R₀ x d (ks₁ ++ ks₂) L c := by
  obtain ⟨L'', a, s, g, dn⟩ := h₂
  refine ⟨L'', a, h₁.trans s, fun τ hτ => ?_, fun ht k hk hca => ?_⟩
  · grind
  · rcases List.mem_append.1 hk with hk | hk
    · exact chordsDone_mono (d₁ ht) s k hk hca
    tauto

/-! ## The test of a chord -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The test of a chord** read into `sLp, sRp, sH1`. -/
theorem scanTest_irs
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {k : ℕ}
    (hk : k < N.nChords) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ztwjd ztwf L c)
    (hlp : c.nreg sLp = (N.chord k).lp) (hrp : c.nreg sRp = (N.chord k).rp)
    (hh1 : c.nreg sH1 = (N.chord k).h + 1) (hroom : c.nreg ALLOC + scanTestK ≤ W) :
    IRS P W c₀ scanTest c scanTestK (fun c' =>
      AccStep P C N Mod R₀ x d [k] L c' ∧ XFr ztkwe c c') := by
  zuebn
  obtain ⟨hG, hW3, hctx, hNF, htag, hMod, hR, hn, hE, hH, hD, hy⟩ := hS
  simp only at hE hH
  subst hE hH hD
  zudzd
  have hiffR : c.nreg lD ≠ 1 → ((c.nreg sRp = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt ztcgt zthj ztcuy) := by
    zudqe
    unfold Sweep.ChordAt
    simp_all
  have hiffL : c.nreg lD = 1 → ((c.nreg sLp = c.nreg lE ∧ c.nreg sH1 = c.nreg lH) ↔
      Sweep.ChordAt ztcgt zthj ztcuy) := by
    zudqe
    unfold Sweep.ChordAt
    simp_all
  have hfarR : c.nreg lD ≠ 1 → Sweep.farPos ztcgt ztcuy = ⟨c.nreg sLp, c.nreg sH1⟩ := by
    intro hd; unfold Sweep.farPos CRec.lpos; simp_all
  have hfarL : c.nreg lD = 1 → Sweep.farPos ztcgt ztcuy = ⟨c.nreg sRp, c.nreg sH1⟩ := by
    intro hd; unfold Sweep.farPos CRec.rpos; simp_all
  have r1 : c.nreg ALLOC + ztndr ≤ W := by unfold scanTestK at hroom; omega
  have conv : ∀ c', ((∃ L', AccOK P accA Mod R₀ ztwlk
        ztmk L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨ (0 < τ ∧ OnCB C (rayPt ((chainModel C).pos zta
          ⟨c.nreg lE, c.nreg lH⟩) (dirOf (c.nreg lD)) τ))) ∧
        (((chainModel C).pos zta zthj).2 ≤ C.top.2 →
          ChordsDone P C N zthj ztcuy [k] L')) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ sFe → r ≠ sFh → ztbni → r ≠ lO →
        r ≠ lO + 1 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) →
      AccStep P C N Mod R₀ zthj ztcuy [k] L c' ∧
        XFr ztkwe c c' := by
    rintro c' ⟨hst, h5, h6, h7⟩
    exact ⟨hst, by_grind, h6, h7⟩
  unfold scanTest
  by_cases h1 : c.nreg lD < c.nreg K1
  · exact (IRS.ifT h1 (eqOffer_irs ztbt ztp hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy by_grind by_grind r1)).mono
      by_decide conv
  refine IRS.mono (K := (12 + offerFK) + 2) ztfnr by_rfl
    ztb
  by_cases h2 : c.nreg K1 < c.nreg lD
  · exact (IRS.ifT h2 (eqOffer_irs ztbt ztp hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy by_grind by_grind r1)).mono by_omega conv
  · exact (IRS.ifF h2 (eqOffer_irs ztp ztbt hk hI hK hG hW3 hctx hNF hacc htag
      hMod hR hn rfl hy by_grind by_grind r1)).mono by_omega conv

/-! ## The body of the loop over the chords of a region -/

/-- The cost of the body. -/
def scanBodyK : ℕ := 13 + scanTestK
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One chord of the region `r`**: read the chord at place `sT` of its list, test, offer. -/
theorem scanBody_irs
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {r B E : ℕ}
    (hr : r < N.nRegions) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    (hC3 : c.nreg sC3 = c.nmem ztkh)
    (hCl : c.nreg sCl = c.nmem ztlw + c.nmem ztwrt)
    (hT : c.nreg sT < (N.region r).chords.length) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ztwjd ztwf L c)
    (hroom : c.nreg ALLOC + scanBodyK ≤ W) :
    IRS P W c₀ scanBody c scanBodyK (fun c' =>
      AccStep P C N Mod R₀ x d [(N.region r).chords.getD (c.nreg sT) 0] L c' ∧
      c'.nreg sT = c.nreg sT + 1 ∧ XFr ztdoa c c') := by
  zuiwo
  zuese
  zudzd
  obtain ⟨k, hkdef⟩ : ∃ k, k = (N.region r).chords.getD (c.nreg sT) 0 := by_simp_all
  rw [← hkdef]
  have hkmem : k ∈ (N.region r).chords := by
    simp_all
  have hNF := hS.hNF
  obtain ⟨-, -, -, reg, -, -, -, hRegs, -, hhlt, -⟩ := hNF
  have hk := (((hRegs r hr).1 k).1 hkmem).1
  have hkl := hk
  have rk : c.nmem ztjsl = k := by
    rw [hCl, hkdef]; exact (hN.2.2.2.2.2.2.2.1 r hrl).2.2.2.2 _ hT
  obtain ⟨wh, wl, wr, -, -⟩ := hN.2.2.2.2.2.1 k hkl
  have b1 : ztdaq := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  have b2 := robust_addr3 (b := B + 7) (o := 5 * r + 3) (t := c.nreg sT) (v := k)
    (fun m' hm' => by
      have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 _ hT
      grind) b1.1 by_omega
  have b3 := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.1 k hkl).2.2.1)
  zuc
  have hhk := hhlt k hk
  zvmxg at hhk
  have hW3 := hS.hW3
  zqbcd
  zqbbz
  have hb : c.nreg sCl + c.nreg sT ≤ W := by_grind
  have hb2 : c.nreg sC3 + 5 * c.nmem ztjsl + 2 ≤ W := by_omega
  have hb3 : c.nmem (c.nreg sC3 + 5 * c.nmem ztjsl) + 1 ≤ W := by
    grind
  have hok := scanReadL_ok c.nmem c.nreg hk1 hb hb2 hb3
  unfold scanBody
  refine IRS.seq (K₂ := scanTestK + 1) zteei ?_ |>.mono
    by_rfl ztb
  zqbcb
  have kk : ∀ q, ¬ RSet q → c₁.nreg q = c.nreg q := fun q hq => by
    zvmwl; exact scanReadL_other' _ _ hq
  have hA1 := kk ALLOC (by unfold RSet sX sY sK sCh sLp sRp sH1 ALLOC sw; omega)
  obtain ⟨v1, v2, v3⟩ := scanReadL_val c.nmem c.nreg hk1
  have vLp : c₁.nreg sLp = (N.chord k).lp := by
    simp_all
  have vRp : c₁.nreg sRp = (N.chord k).rp := by
    simp_all
  have vH1 : c₁.nreg sH1 = (N.chord k).h + 1 := by
    simp_all
  have hS₁ := hS.transport (fun q hq => kk q (by
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [RSet, sX, sY, sK, sCh, sLp, sRp, sH1, lCD, lT, lN, lE, lH, lD, sw] <;> omega))
    by_simp_all hA1.ge
  have hacc₁ := hacc.transport (fun j hj => kk _ (by
    unfold RSet sX sY sK sCh sLp sRp sH1 accA sw; omega))
  refine IRS.seq (scanTest_irs hI₁ hK hS₁ hk hacc₁ vLp vRp vH1
    (by zvnhf; unfold scanBodyK at hroom; omega)) ?_
  rintro c₂ hI₂ - - ⟨hst, fr2⟩
  have t2 : c₂.nreg sT = c.nreg sT := by
    rw [fr2.1 sT ztmr
      by_decide by_decide by_decide
      by_decide by_decide]
    exact kk sT (by unfold RSet sX sY sK sCh sLp sRp sH1 sT sw; omega)
  have k12 := (hK.fix hI₂).2.1
  have hok3 : okB W c₂.nmem [.addN sT sT K1] c₂.nreg :=
    ⟨⟨iscr_sw by_decide by_decide, by
      omega⟩, trivial⟩
  refine (IRS.block _ hI₂ hok3).mono le_rfl ?_
  intro c₃ hc3
  have r3 : ∀ q, q ≠ sT → c₃.nreg q = c₂.nreg q := by
    intro q hq; zvnar; show regB c₂.nmem [.addN sT sT K1] c₂.nreg q = _
    zuie
  have t3 : c₃.nreg sT = c₂.nreg sT + 1 := by
    zvnar; show regB c₂.nmem [.addN sT sT K1] c₂.nreg sT = _
    zvmzj; rw [k12]
  zuyu
  refine ⟨hst.transport (fun j hj => r3 _ (by unfold sT accA sw; omega)), by_omega, ?_,
    ?_, ?_⟩
  · intro q hq hX hqa hqo hqo1 hqA
    rw [r3 q by_omega, fr2.1 q hq (fun h => hX (Or.inl ztbho)) hqa hqo hqo1 hqA]
    exact kk q (fun h => hX (Or.inl zteg))
  · rw [r3 ALLOC by_decide, ← hA1]; exact fr2.2.1
  · zuge
    rw [hm3, fr2.2.2 a by_omega, hm1]

/-! ## The head of the loop over the chords of a region -/

/-- The registers written by the head. -/
def HdSet (q : ℕ) : Prop := q = sX ∨ q = sY ∨ q = sNc ∨ q = sCl ∨ q = sT

/-- The registers written by the scan of one region. -/
def ScanW (q : ℕ) : Prop := WSet q ∨ HdSet q
theorem scanW_sset {q : ℕ} (h : ScanW q) : SSet q := by
  rcases h with ((h | h | h | h | h | h | h) | h | h) | (h | h | h | h | h) <;> subst h <;>
    simp only [SSet, sX, sY, sK, sCh, sLp, sRp, sH1, sFe, sFh, sNc, sCl, sT, sw] <;> omega
theorem scanHeadL_other (m f : ℕ → ℕ) (rr : ℕ) {q : ℕ} (h : ¬ HdSet q) :
    regB m ztglu f q = f q :=
  regB_other m ztglu f (fun i hi => by
    simp only [scanHeadL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> apply h <;> simp [HdSet])
theorem scanHeadL_val (m f : ℕ → ℕ) {rr : ℕ} (hrr : ¬ SSet rr) (hk2 : f K2 = 2)
    (hk3 : f K3 = 3) :
    regB m ztglu f sNc = m (f sR5 + 5 * f rr + 2) ∧
    regB m ztglu f sCl = m (f sR5 + 5 * f rr + 3) ∧
    regB m ztglu f sT = 0 := by
  zqbca
  zqbcc
  simp only [scanHeadL, regB, regI, upd, sX, sY, sR5, sNc, sCl, sT, K2, K3, sw]
  grind
theorem scanHeadL_ok (m f : ℕ → ℕ) {rr : ℕ} (hrr : ¬ SSet rr) (hk2 : f K2 = 2)
    (hk3 : f K3 = 3) (hb : f sR5 + 5 * f rr + 3 ≤ W) : okB W m ztglu f := by
  zqbca
  have hb' : f 241142 + 5 * f rr + 3 ≤ W := hb
  zqbcc
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [scanHeadL, okB, okI, regI, upd, sX, sY, sR5, sNc, sCl, sT, K2, K3, sw]
  grind
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The head of the scan of region `r`**: its number of chords, the start of its chord list
(when there is one) and the place `0`. -/
theorem scanHead_irs (hrr : ¬ SSet rr) {N : NF} (hI : IInv W c₀ c) (hK : Consts c₀)
    {B E r : ℕ} (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC) (hAW : c.nreg ALLOC ≤ W)
    (hr : r < N.nRegions) (hrv : c.nreg rr = r) (hR5 : c.nreg sR5 = c.nmem zter)
    (hL7 : c.nreg sL7 = c.nmem ztlw) :
    IRS P W c₀ ztwdh c 12 (fun c' =>
      c'.nreg sNc = (N.region r).chords.length ∧
      (0 < (N.region r).chords.length →
        c'.nreg sCl = c.nmem ztlw + c.nmem ztwrt) ∧
      c'.nreg sT = 0 ∧ (∀ q, ¬ HdSet q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zuiwo
  zuese
  zuhx
  have hk2 := hKc.2.2.2.2.2.1
  have hk3 := hKc.2.2.2.2.2.2
  have b1 : ztdaq := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  have hok := scanHeadL_ok (W := W) c.nmem c.nreg hrr hk2 hk3 by_omega
  obtain ⟨v1, v2, v3⟩ := scanHeadL_val c.nmem c.nreg hrr hk2 hk3
  unfold scanHead
  refine IRS.seq (K₂ := 3) zteei ?_ |>.mono
    by_rfl ztb
  zqbcb
  have kk : ∀ q, ¬ HdSet q → c₁.nreg q = c.nreg q := fun q hq => by
    zvmwl; exact scanHeadL_other _ _ _ hq
  have w1 : c₁.nreg sNc = (N.region r).chords.length := by
    zvmwl; show regB c.nmem _ c.nreg sNc = _
    rw [v1, hR5, hrv]; exact (hN.2.2.2.2.2.2.2.1 r hrl).2.1
  have w2 : c₁.nreg sCl = c.nmem ztwrt := by
    simp_all
  have w3 : c₁.nreg sT = 0 := by
    simp_all
  zuibb
  by_cases hpos : c₁.nreg K0 < c₁.nreg sNc
  · have hn0 : ztphl := by_omega
    have b2 := robust_addr3 (o := 5 * r + 3)
      (fun m' hm' => by
        have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 0 hn0
        omega) b1.1 by_omega
    zqbbz
    have l7 : ztzpt := by
      rw [kk sL7 (by simp only [HdSet, sX, sY, sNc, sCl, sT, sL7, sw]; omega), hL7]
    have hok2 : okI W c₁.nreg ztlde :=
      ⟨iscr_sw by_decide by_decide, by
        grind⟩
    refine (IRS.ifT hpos (IRS.instr1 hI₁ hok2)).mono le_rfl ?_
    zufxk
    have r' : ∀ q, q ≠ sCl → c'.nreg q = c₁.nreg q := by
      intro q hq; zumyg; show regI c₁.nmem (.addN sCl sCl sL7) c₁.nreg q = _
      zuua
    refine ⟨by rw [r' sNc by_decide, w1], fun _ => ?_,
      by rw [r' sT by_decide, w3], fun q hq => ?_, by_simp_all⟩
    · zumyg; show regI c₁.nmem ztlde c₁.nreg sCl = _
      zubzz
    · rw [r' q ztwix, kk q hq]
  · refine (IRS.ifF hpos (IRS.skip hI₁ ?_)).mono le_rfl ztb
    simp_all

/-! ## The loop over the chords of a region -/

/-- The cost of the scan of a region with `n` chords. -/
def scanRK (n : ℕ) : ℕ := 12 + ((scanBodyK + 2) * n + 2)
theorem XFr.of_regs {c c' : Config} (hr : ∀ q, ¬ X q → c'.nreg q = c.nreg q)
    (hX : ¬ X ALLOC) (hm : c'.nmem = c.nmem) : XFr X c c' :=
  ⟨by_simp_all, by_simp_all, by_simp_all⟩
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The scan of the exit chords of the region `r`** (register `rr`). -/
theorem scanR_irs (hrr : ¬ SSet rr) {C : Chain} {N : NF} {Mod : ℕ → Chain} {R₀ : ℝ}
    {x : WPos} {d : ℕ} (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c)
    {r B E : ℕ} (hr : r < N.nRegions) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    (hrv : c.nreg rr = r) (hR5 : c.nreg sR5 = c.nmem zter) (hL7 : c.nreg sL7 = c.nmem ztlw)
    (hC3 : c.nreg sC3 = c.nmem ztkh) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ztwjd ztwf L c)
    (hroom : c.nreg ALLOC + scanRK (N.region r).chords.length ≤ W) :
    IRS P W c₀ (scanR rr) c (scanRK (N.region r).chords.length) (fun c' =>
      AccStep P C N Mod R₀ x d (N.region r).chords L c' ∧ XFr ScanW c c') := by
  obtain ⟨n, hn⟩ : ∃ n, n = (N.region r).chords.length := by_simp_all
  zuinn
  zuese
  have b1 : ztdaq := NFLoc.robust_addr2 (fun m' hm' => by
    simpa only [Nat.add_assoc] using ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.1)
  zqbcd
  unfold scanR
  refine IRS.seq
    (scanHead_irs hrr hI hK hNW hEA hAW hr hrv hR5 hL7) ?_
  rintro c₁ hI₁ - - ⟨w1, w2, w3, kk, hm1⟩
  zvocr at w1 w2
  have fr1 : XFr ScanW c c₁ := XFr.of_regs (fun q hq => kk q (fun h => hq ztbho))
    (by simp only [ScanW, WSet, RSet, HdSet, sX, sY, sK, sCh, sLp, sRp, sH1, sFe, sFh, sNc, sCl, sT,
      ALLOC, sw]; omega) hm1
  have hA1 :=
    kk ALLOC (by simp only [HdSet, sX, sY, sNc, sCl, sT, ALLOC, sw]; omega)
  have c31 :=
    kk sC3 (by simp only [HdSet, sX, sY, sNc, sCl, sT, sC3, sw]; omega)
  have hS₁ := hS.keep (fr1.mono fun q h => scanW_sset h)
  have hacc₁ := hacc.transport (fun j hj => kk _ (by
    simp only [HdSet, sX, sY, sNc, sCl, sT, accA, sw]; omega))
  have hreg : ∀ c', XFr ztdoa c₁ c' → ∀ q, q = sNc ∨ q = sCl ∨ q = sC3 →
      c'.nreg q = c₁.nreg q := by
    intro c' fr q hq
    refine fr.1 q ztods ?_ ?_ ?_ ?_ ?_ <;> rcases hq with rfl | rfl | rfl <;>
      simp only [WSet, RSet, sX, sY, sK, sCh, sLp, sRp, sH1, sFe, sFh, sNc, sCl, sC3, sT, accA, lO,
        ALLOC, sw] <;> omega
  have hmem : ∀ c', XFr ztdoa c₁ c' → ∀ a, a < c.nreg ALLOC →
      c'.nmem a = c.nmem a := by
    intro c' fr a ha; rw [fr.2.2 a by_omega, hm1]
  have hsub : ∀ q, (WSet q ∨ q = sT) → ScanW q := fun q h =>
    h.elim Or.inl (fun e => Or.inr ztbh)
  let I : Config → Prop := fun c' => XFr ztdoa c₁ c' ∧ c'.nreg sT ≤ n ∧
    AccStep P C N Mod R₀ x d ((N.region r).chords.take (c'.nreg sT)) L c'
  have hW := IRS.while (a := sT) (b := sNc) I
    (fun c' => n - c'.nreg sT) scanBodyK
    by_grind
    (fun c' hI' hc ht hroom' => by
      obtain ⟨fr, hle, hst⟩ := hc
      rw [hreg c' fr sNc ztp, w1] at ht
      zucmj
      have hn0' : ztphl := by_omega
      have b2 := robust_addr3 (o := 5 * r + 3)
        (fun m' hm' => by
          have := ((hNW m' hm').2.2.2.2.2.2.2.1 r hrl).2.2.2.2 0 hn0'
          omega) b1.1 by_omega
      have m' := hmem c' fr
      have hS' :=
        hS₁.keep (fr.mono fun q h => scanW_sset by_simp_all)
      have hNW' : NFWithin c'.nmem B E N := hNW.transport by_grind
      have hEA' : E ≤ c'.nreg ALLOC := by have := fr.2.1; omega
      zqbbz
      have hC3' : c'.nreg sC3 = c'.nmem ztkh := by
        grind
      have hCl' : c'.nreg sCl = c'.nmem ztlw + c'.nmem (c'.nmem zter + 5 * r + 3) := by
        grind
      obtain ⟨L', a', s', g', d'⟩ := hst
      refine (scanBody_irs hI' hK hS' hr hNW' hEA' hC3' hCl' by_omega a'
        hroom').mono le_rfl ?_
      rintro c'' ⟨hst2, t2, fr2⟩
      refine ⟨⟨fr.trans fr2, by_omega, ?_⟩, by_omega⟩
      rw [t2, take_succ_getD by_omega]
      exact AccStep.trans s' g' d' hst2)
    hI₁ ⟨XFr.refl _ _, by_omega, by zupbo; exact AccStep.init hacc₁⟩ (by
      rw [w3, hA1, Nat.sub_zero]; unfold scanRK at hroom; omega)
  rw [w3, Nat.sub_zero] at hW
  refine hW.mono le_rfl ?_
  rintro c' ⟨⟨fr, hle, hst⟩, hnot⟩
  rw [hreg c' fr sNc ztp, w1] at hnot
  have ht : c'.nreg sT = n := by_omega
  rw [ht, hn, List.take_length] at hst
  exact ⟨hst, fr1.trans (fr.mono hsub)⟩

/-! ## The scan of the three regions -/
theorem robust_addr1 {b v : ℕ} (h : Robust E m fun m' => m' b = v) :
    b < E := by
  zucux
  have := h (Function.update m b ztsp) ztjwq
  simp_all

/-- The registers written by the initialisation of the scan. -/
def ISet (q : ℕ) : Prop := q = sX ∨ q = sR5 ∨ q = sL7 ∨ q = sC3
theorem scanInitL_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ ISet q) : regB m scanInitL f q = f q :=
  regB_other m scanInitL f (fun i hi => by
    simp only [scanInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro he <;> subst he <;> apply h <;> simp [ISet])
theorem scanInitL_val (m f : ℕ → ℕ) (hk2 : f K2 = 2) (hk3 : f K3 = 3) (hk5 : f K5 = 5) :
    regB m scanInitL f sR5 = m (f lNF + 5) ∧ regB m scanInitL f sL7 = m (f lNF + 7) ∧
    regB m scanInitL f sC3 = m (f lNF + 3) := by
  zqbca
  have e5 : ztuuk := hk5
  simp only [scanInitL, regB, regI, upd, sX, sR5, sL7, sC3, lNF, K2, K3, K5, sw]
  simp_all
theorem scanInitL_ok (m f : ℕ → ℕ) (hk2 : f K2 = 2) (hk3 : f K3 = 3) (hk5 : f K5 = 5)
    (hb : f lNF + 7 ≤ W) : okB W m scanInitL f := by
  zqbca
  have e5 : ztuuk := hk5
  have hb' : f 241102 + 7 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [scanInitL, okB, okI, regI, upd, sX, sR5, sL7, sC3, lNF, K2, K3, K5, sw]
  grind
theorem XFr.scanKeep {c c' : Config} (fr : XFr ScanW c c') {q : ℕ}
    (hq : q = sR5 ∨ q = sL7 ∨ q = sC3 ∨ q = lR0 ∨ q = lR1 ∨ q = lR2) : c'.nreg q = c.nreg q := by
  refine fr.1 q ztods ?_ ?_ ?_ ?_ ?_ <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ScanW, WSet, RSet, HdSet, sX, sY, sK, sCh, sLp, sRp, sH1, sFe, sFh, sNc, sCl, sT,
      sR5, sL7, sC3, lR0, lR1, lR2, accA, lO, ALLOC, sw] <;> omega

/-- The cost of the scan of the three regions. -/
def lhScanK (n0 n1 n2 : ℕ) : ℕ := 6 + (scanRK n0 + (scanRK n1 + scanRK n2))
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The scan of the exit chords of the three regions** `lR0, lR1, lR2`. -/
theorem lhScan_irs
    (hI : IInv W c₀ c) (hK : Consts c₀) (hS : SEnv P W C N Mod R₀ x d c) {B E : ℕ}
    (hB : c.nreg lNF = B) (hNW : NFWithin c.nmem B E N) (hEA : E ≤ c.nreg ALLOC)
    {r0 r1 r2 : ℕ} (h0 : c.nreg lR0 = r0) (h1 : c.nreg lR1 = r1) (h2 : c.nreg lR2 = r2)
    (hr0 : r0 < N.nRegions) (hr1 : r1 < N.nRegions) (hr2 : r2 < N.nRegions) {L : Set ℝ}
    (hacc : AccOK P accA Mod R₀ ztwjd ztwf L c)
    (hroom : c.nreg ALLOC + lhScanK (N.region r0).chords.length (N.region r1).chords.length
      (N.region r2).chords.length ≤ W) :
    IRS P W c₀ lhScan c (lhScanK (N.region r0).chords.length (N.region r1).chords.length
      (N.region r2).chords.length) (fun c' =>
      AccStep P C N Mod R₀ x d
        ((N.region r0).chords ++ ((N.region r1).chords ++ (N.region r2).chords)) L c' ∧
      XFr SSet c c') := by
  zuhx
  have hB11 := robust_addr1 (fun m' hm' => (hNW m' hm').2.2.2.2.1)
  zqbcd
  have hok : okB W c.nmem scanInitL c.nreg := scanInitL_ok c.nmem c.nreg hKc.2.2.2.2.2.1
    hKc.2.2.2.2.2.2 hKc.2.2.2.2.1 by_omega
  obtain ⟨v1, v2, v3⟩ := scanInitL_val c.nmem c.nreg hKc.2.2.2.2.2.1 hKc.2.2.2.2.2.2
    hKc.2.2.2.2.1
  unfold lhScan
  refine IRS.seq zteei ?_ |>.mono
    by_rfl ztb
  zqbcb
  have kk : ∀ q, ¬ ISet q → c₁.nreg q = c.nreg q := fun q hq => by
    zvmwl; exact scanInitL_other _ _ hq
  have fr1 : XFr SSet c c₁ := XFr.of_regs (fun q hq => kk q (fun h => hq (by
      rcases h with rfl | rfl | rfl | rfl <;> simp only [SSet, sX, sR5, sL7, sC3, sw] <;> omega)))
    (by simp only [SSet, ALLOC, sw]; omega) hm1
  have hA1 := kk ALLOC (by
    simp only [ISet, sX, sR5, sL7, sC3, ALLOC, sw]; omega)
  have w5 : c₁.nreg sR5 = c.nmem zter := by
    simp_all
  have w7 : ztzpt := by
    simp_all
  have w3 : c₁.nreg sC3 = c.nmem ztkh := by
    simp_all
  have hS₁ := hS.keep fr1
  have hacc₁ := hacc.transport (fun j hj => kk _ (by
    simp only [ISet, sX, sR5, sL7, sC3, accA, sw]; omega))
  have nr : ∀ q, q = lR0 ∨ q = lR1 ∨ q = lR2 → ¬ SSet q := by
    intro q hq; rcases hq with rfl | rfl | rfl <;> simp only [SSet, lR0, lR1, lR2, sw] <;> omega
  have g0 : c₁.nreg lR0 = r0 := by
    rw [kk lR0 (by simp only [ISet, sX, sR5, sL7, sC3, lR0, sw]; omega), h0]
  have g1 : c₁.nreg lR1 = r1 := by
    rw [kk lR1 (by simp only [ISet, sX, sR5, sL7, sC3, lR1, sw]; omega), h1]
  have g2 : c₁.nreg lR2 = r2 := by
    rw [kk lR2 (by simp only [ISet, sX, sR5, sL7, sC3, lR2, sw]; omega), h2]
  -- region `r0`
  refine IRS.seq
    (scanR_irs by_simp_all hI₁ hK hS₁ hr0
      (hNW.transport by_simp_all) by_omega g0 by_simp_all
      by_simp_all by_simp_all hacc₁
      (by zvnhf; unfold lhScanK at hroom; omega)) ?_
  rintro c₂ hI₂ hA2 hA2' ⟨hst2, fr2⟩
  obtain ⟨L₁, a₁, s₁, gg₁, d₁⟩ := hst2
  have m2 : ztux := fun a ha => by
    rw [fr2.2.2 a by_omega, hm1]
  have hS₂ := hS₁.keep (fr2.mono fun q h => scanW_sset h)
  refine IRS.seq
    (scanR_irs by_simp_all hI₂ hK hS₂ hr1
      ztvtn by_omega
      (by rw [fr2.scanKeep by_simp, g1])
      (by rw [fr2.scanKeep by_simp, w5, m2 _ by_omega])
      (by rw [fr2.scanKeep by_simp, w7, m2 _ by_omega])
      (by rw [fr2.scanKeep by_simp, w3, m2 _ by_omega]) a₁
      ztnvy) ?_
  rintro c₃ hI₃ hA3 hA3' ⟨hst3, fr3⟩
  obtain ⟨L₂, a₂, s₂, gg₂, d₂⟩ := hst3
  have m3 : ztblg := fun a ha => by
    rw [fr3.2.2 a by_omega, m2 a ha]
  have hS₃ := hS₂.keep (fr3.mono fun q h => scanW_sset h)
  refine (scanR_irs by_simp_all hI₃ hK hS₃ hr2
      ztvtn by_omega
      (by rw [fr3.scanKeep by_simp, fr2.scanKeep by_simp, g2])
      (by rw [fr3.scanKeep by_simp, fr2.scanKeep by_simp, w5, m3 _ by_omega])
      (by rw [fr3.scanKeep by_simp, fr2.scanKeep by_simp, w7, m3 _ by_omega])
      (by rw [fr3.scanKeep by_simp, fr2.scanKeep by_simp, w3, m3 _ by_omega]) a₂
      ztnvy).mono le_rfl ?_
  rintro c₄ ⟨hst4, fr4⟩
  refine ⟨AccStep.trans s₁ gg₁ d₁ (AccStep.trans s₂ gg₂ d₂ hst4), ?_⟩
  exact fr1.trans ((fr2.mono fun q h => scanW_sset h).trans
    ((fr3.mono fun q h => scanW_sset h).trans (fr4.mono fun q h => scanW_sset h)))
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

/-- **The local hit.** -/
def localHit (sh : Stmt) : Stmt :=
  .seq lh1 (.seq lhGather (.seq lhHoles (.seq ztvyg lhScan)))

/-- The registers the local hit writes (besides the allocator and the oracle bands):
`sw 1000 … sw 2199` (the accumulator `accA = sw 2000 … sw 2012` included) and `sw 3000 … sw 3199`. -/
def LHW (r : ℕ) : Prop := (sw 1000 ≤ r ∧ r < sw 2200) ∨ ztfut

/-- **The geometric conditions of completeness**: a positive height code naming the height of the
point, the ray in the left sector, the point not above the top. -/
def LHGeo (P : Polygon) (C : Chain) (x : WPos) (d : ℕ) : Prop :=
  ∃ h, x.hgt = h + 1 ∧ h < P.n ∧ ((Qof P).vtx h).2 = ((chainModel C).pos zta x).2 ∧
    sideLeft (chainModel C).W x.edge ztwte
      (rayPt ztwjd ztwf 1) ∧
    ((chainModel C).pos zta x).2 ≤ C.top.2

/-- The cost of the local hit: `T` the length of the table of powers, `Fg` the shooter's cost,
`Da` and `Dc` bounds on the numbers of arcs and exit chords of a region. -/
def localK (T Fg Da Dc : ℕ) : ℕ :=
  lh1K T + ((3 + (11 + 3 * ztiaj)) +
    (11200 + (shotOfferK Fg (3 * Da) + lhScanK Dc Dc Dc)))

/-! ## Cost bounds -/
variable {N : NF} {rs : List ℕ} {Da : ℕ} {C : Chain}
theorem gatherK_le
    (h : ∀ r ∈ rs, (N.region r).arcs.length ≤ Da) :
    gatherK N rs ≤ 11 + rs.length * ztiaj := by
  unfold gatherK
  have := List.sum_le_length_nsmul (rs.map fun r => regK (N.region r).arcs.length + 2)
    ztiaj (by
      zusy
      zufza
      have := h r hr
      unfold regK
      simp_all)
  simp_all
theorem regArcs_length_le
    (h : ∀ r ∈ rs, (N.region r).arcs.length ≤ Da) :
    (regArcs N rs).length ≤ rs.length * Da := by
  unfold regArcs
  zugtt
  have := List.sum_le_length_nsmul (rs.map fun r => (N.region r).arcs.length) Da (by
    simp_all)
  simp_all
theorem shotOfferK_mono {Fg K K' : ℕ} (h : K ≤ K') : shotOfferK Fg K ≤ shotOfferK Fg K' := by
  unfold shotOfferK ShotList.shotCost
  simp_all
theorem scanRK_mono {n n' : ℕ} (h : n ≤ n') : scanRK n ≤ scanRK n' := by
  unfold scanRK
  simp_all
theorem lhScanK_mono {a b d a' b' d' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hd : d ≤ d') :
    lhScanK a b d ≤ lhScanK a' b' d' := by
  unfold lhScanK
  have := scanRK_mono ha
  have := scanRK_mono hb
  have := scanRK_mono hd
  omega

/-! ## The regions around the spine position -/
theorem nbrRegs_lt {N : NF} (hNF : IsNF ztc zta N) {j : ℕ}
    (hj : j < N.arcs.length) : ∀ r ∈ Sweep.nbrRegs N j, r < N.nRegions := by
  zugls
  obtain ⟨-, -, -, reg, -, -, hArcs, -⟩ := hNF'
  have hreg : ∀ p, p < N.arcs.length → (N.arc ztmh).reg < N.nRegions := fun p hp =>
    (hArcs.1 _ (NFLoc.seq_lt hNF hp)).1
  zuz
  zufbd
  zuiee
  · exact hreg _ ztqbf
  · simp_all
  · exact hreg _ ztqbg
theorem regArcs_lt {N : NF} (hNF : IsNF ztc zta N) {rs : List ℕ}
    (hrs : ∀ r ∈ rs, r < N.nRegions) : ∀ a ∈ regArcs N rs, a < N.arcs.length := by
  zuge
  zucsf
  zufyx
  exact ((hArcs.2.2.2 r by_simp_all a).1 har).1

/-- The gathered arcs list the arcs of the regions, up to the keys. -/
theorem gathered_keys {N : NF} (hNF : IsNF ztc zta N) {rs : List ℕ}
    (hrs : ∀ r ∈ rs, r < N.nRegions) {m : ℕ → ℕ} {AB : ℕ}
    (harcs : ∀ k, k < (regArcs N rs).length → ShotList.arcAt m AB k =
      nArc ztc zta N ztdxx) :
    ∀ r ∈ rs, ∀ a ∈ (N.region r).arcs, ∃ i < (regArcs N rs).length,
      (chainModel C).key zta (ShotList.arcAt m AB i).1 =
        (chainModel C).key zta (N.arc a).s ∧
      (chainModel C).key zta (ShotList.arcAt m AB i).2 =
        (chainModel C).key zta (N.arc a).e := by
  intro r hr a ha
  zugls
  obtain ⟨-, -, -, reg, -, -, hArcs, -, -, -, hpp⟩ := hNF'
  have hal := ((hArcs.2.2.2 r by_simp_all a).1 ha).1
  have hmem : a ∈ regArcs N rs := List.mem_flatMap.2 by_grind
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 hmem
  zuifc
  have hg : (regArcs N rs).getD i 0 = a := by_simp_all
  rw [harcs i hi, hg]
  zujqr
  exact ⟨(Restore.normOf_facts (hpp a hal).1).2.2.2.1, (Restore.normOf_facts (hpp a hal).2).2.2.2.1⟩

/-! ## The local hit -/
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The local hit.** -/
theorem localHit_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {Mod : ℕ → Chain} {R₀ : ℝ} {L : Set ℝ}
    {Da Dc : ℕ} {x : WPos} {d : ℕ}
    (hI : IInv W c₀ c) (hK : Consts c₀) (hL : LCtx P W C N E c)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztc)
    (hsg : (chainModel C).Semigranular ztwjq ztq)
    (hAr : ∀ r, r < N.nRegions → (N.region r).arcs.length ≤ Da)
    (hCh : ∀ r, r < N.nRegions → (N.region r).chords.length ≤ Dc)
    (hxE : c.nreg lE = x.edge) (hxH : c.nreg lH = x.hgt) (hxD : c.nreg lD = d)
    (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n x)
    (hy : |((chainModel C).pos zta x).2| < C.radius)
    (hloc : ztdiq ∨
      (6 ≤ x.edge ∧ (chainModel C).pos zta x ∈ C.set))
    (hacc : AccOK P accA Mod R₀ ztwjd ztwf L c)
    (htag : c.nreg lT ≤ 2) (hMod : Mod ztjsj = C) (hR : C.radius = R₀)
    (hn : c.nreg lN = 2 * C.m + 7)
    (hroom : c.nreg ALLOC + localK zterd ztwiu Da Dc ≤ W) :
    IRS P W c₀ ztkak c (localK zterd ztwiu Da Dc) (fun c' =>
      (∃ L', AccOK P accA Mod R₀ ztwjd ztwf L' c' ∧ L ⊆ L' ∧
        (∀ τ ∈ L', τ ∈ L ∨
          ztbajy) ∧
        (LHGeo P C x d → Merge.FreeAt C ztwjd ztwf ∧
          C.hitParam ztwjd ztwf ∈ L')) ∧
      ztcfn ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuebn
  simp only at hxE hxH he hloc
  subst hxE hxH hxD
  have hσ' : dirOf _ = 1 ∨ dirOf ztcuy = -1 := dirOf_cases _
  zuc
  -- the input registers
  let LIn : ℕ → Prop := fun r => r = lMD ∨ r = lCD ∨ r = lNF ∨ r = lE ∨ r = lH ∨ r = lD ∨
    r = lN ∨ r = lT
  have lin : ∀ r, LIn r → 241100 ≤ r ∧ r ≤ 241107 := by
    zuz
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [lMD, lCD, lNF, lE, lH, lD, lN, lT, sw] <;> omega
  have linO : ∀ r, LIn r → bandOf r ∉ oracleBands := fun r hr =>
    not_oracle_sw (by have := lin r hr; omega) (by have := lin r hr; omega)
  -- 1. the spine position and the regions
  refine IRS.seq
    (lh1_irs hI hK hL he hpp zteqp) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨hj1, hl1, hl2, hLL, hA1, hlist1, hm1, fr1, hR0, hR1, hR2⟩
  have k1 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => fr1 r h1 (fun h => h2 (by unfold LSet sw at h; unfold LHW sw; omega)) h3
  have i1 : ∀ r, LIn r → c₁.nreg r = c.nreg r := fun r hr =>
    fr1 r by_grind (fun h => by have := lin r hr; unfold LSet sw at h; omega)
      (by have := lin r hr; unfold ALLOC; omega)
  have hL₁ := hL.transport (fun r hr => by
      zukx
      · grind
      · grind
      · grind
      · exact hI₁.hin _ by_trivial |>.trans (hI.hin _ by_trivial).symm
      · exact hI₁.hin _ by_trivial |>.trans (hI.hin _ by_trivial).symm)
    hm1 hA₁
  zujmz
  have hrsl := nbrRegs_lt hL.hNF hj1
  have hrs3 : (Sweep.nbrRegs N j).length = 3 := by_rfl
  have hGl : gatherK N ztnpo ≤ 11 + 3 * ztiaj := by
    have := gatherK_le
      ztjwl
    grind
  have hKl : (regArcs N ztnpo).length ≤ 3 * Da := by
    have := regArcs_length_le
      ztjwl
    grind
  -- 2. the gather
  refine IRS.seq
    ((lhGather_irs hI₁ hK hL₁ hrs3 hrsl
      ztbmx by_omega
      zteqp).mono
      by_omega ztb) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨g1, g2, g3, g4, hm2, fr2⟩
  have k2 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => fr2 r h1 (fun h => h2 (by unfold GCall sw at h; unfold LHW sw; omega)) h3
  have i2 : ∀ r, LIn r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [← i1 r hr]
    exact fr2 r by_grind (fun h => by have := lin r hr; unfold GCall sw at h; omega)
      by_grind
  have hL₂ := hL₁.transport (fun r hr => by
      zukx
      · rw [i2 _ ztp, i1 _ ztp]
      · zugvt
      · zugvt
      · exact hI₂.hin _ by_trivial |>.trans (hI₁.hin _ by_trivial).symm
      · exact hI₂.hin _ by_trivial |>.trans (hI₁.hin _ by_trivial).symm)
    hm2 hA₂
  have e2 : c₂.nreg lE = c.nreg lE := i2 _ by_omega
  have h2 : c₂.nreg lH = c.nreg lH := i2 _ by_omega
  -- 3. the holes
  refine IRS.seq
    (lhHoles_irs hI₂ hK hL₂.hctx by_omega by_grind
      by_grind by_grind
      zteqp) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨hho, fr3, hA3, hm3⟩
  rw [e2, h2] at hho
  have k3 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => fr3 r h1 (fun h => h2 (by
      unfold HSet lO sw at h; unfold LHW sw; omega)) h3
  have i3 : ∀ r, LIn r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [← i2 r hr]
    exact fr3 r by_grind (fun h => by have := lin r hr; unfold HSet lO sw at h; omega)
      (by have := lin r hr; unfold ALLOC; omega)
  have kG : ∀ r, GCall r → c₃.nreg r = c₂.nreg r := fun r hr =>
    fr3 r (not_oracle_sw ztmek ztmek)
      (fun h => by unfold GCall sw at hr; unfold HSet lO sw at h; omega)
      (by unfold GCall sw at hr; unfold ALLOC; omega)
  have hL₃ := hL₂.transport (fun r hr => by
      zukx
      · rw [i3 _ ztp, i2 _ ztp]
      · zugvu
      · zugvu
      · exact hI₃.hin _ by_trivial |>.trans (hI₂.hin _ by_trivial).symm
      · exact hI₃.hin _ by_trivial |>.trans (hI₂.hin _ by_trivial).symm)
    by_grind hA3.ge
  have e3 : c₃.nreg lE = c.nreg lE := i3 _ by_omega
  have h3 : c₃.nreg lH = c.nreg lH := i3 _ by_omega
  have d3 : c₃.nreg lD = c.nreg lD := i3 _ by_omega
  have n3 : c₃.nreg lN = c.nreg lN :=
    i3 _ by_omega
  have t3 : c₃.nreg lT = c.nreg lT :=
    i3 _ by_omega
  have gB3 : c₃.nreg gBase = c₁.nreg ALLOC := by rw [kG _ by_trivial, g1]
  have gK3 : c₃.nreg gK = (regArcs N ztnpo).length := by rw [kG _ by_trivial, g2]
  -- the accumulator is untouched so far
  have hacc₃ : AccOK P accA Mod R₀ _
      _ L c₃ := hacc.transport (fun i hi => by
    have o : bandOf (accA + i) ∉ oracleBands :=
      not_oracle_sw zthk zthk
    rw [fr3 _ o (by unfold HSet lO accA sw; omega) ztbjo,
      fr2 _ o (by unfold GCall accA sw; omega) ztbjo]
    exact fr1 _ o (by unfold LSet accA sw; omega) ztbjo)
  have hW3 : ztmd := by have := hL.hWh; unfold hostWords at this; omega
  have hD : ztxpn := (goodShear_epsOf hL.hG.2).2.1
  -- 4. the shot and its offer
  refine IRS.seq
    ((lhShotOffer_irs hsh hBs hXl hI₃ hK hL₃ hX hcap hOk hsg
      by_omega by_grind by_grind
      (regArcs_lt hL.hNF hrsl) gK3 by_omega ztksy
      by_grind (by rw [e3, h3, d3]; omega) by_omega
      by_grind hR by_omega
      (by
        have := shotOfferK_mono (Fg := F ztq) hKl
        unfold localK at hroom; omega)).mono (shotOfferK_mono hKl) (fun _ h => h)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨L₁, a₁, hL₁, comp₁, fr4, hA4, hm4⟩
  rw [e3, h3, d3] at a₁ hL₁ comp₁
  have k4 : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c₄.nreg r = c₃.nreg r :=
    fun r h1 h2 h3 => fr4 r h1 (fun h => h2 (by unfold RS at h; unfold LHW sw; omega))
      ztise ztbuv
      ztbuv h3
  have keep4 : ∀ r, 241100 ≤ r → r ≤ 241111 → c₄.nreg r = c₃.nreg r := fun r h1 h2 =>
    fr4 r ztbet zteqn zthk
      ztozq ztozq ztu
  have i4 : ∀ r, LIn r → c₄.nreg r = c.nreg r := fun r hr => by
    have := lin r hr
    rw [keep4 r by_omega by_omega, i3 r hr]
  have hL₄ := hL₃.transport (fun r hr => by
      zukx
      · rw [i4 _ ztp, i3 _ ztp]
      · rw [i4 _ ztwiz, i3 _ ztwiz]
      · rw [i4 _ ztbajm, i3 _ ztbajm]
      · exact hI₄.hin _ by_trivial |>.trans (hI₃.hin _ by_trivial).symm
      · exact hI₄.hin _ by_trivial |>.trans (hI₃.hin _ by_trivial).symm)
    hm4 hA4
  have e4 := i4 _ ztbaje
  have h4 : c₄.nreg lH = c.nreg lH := i4 _ by_omega
  have d4 : c₄.nreg lD = c.nreg lD := i4 _ by_omega
  have n4 : c₄.nreg lN = c.nreg lN :=
    i4 _ by_omega
  have t4 : c₄.nreg lT = c.nreg lT :=
    i4 _ by_omega
  -- the region registers
  have kR : ∀ r, 241109 ≤ r → r ≤ 241111 → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [keep4 r by_omega by_omega,
      fr3 r ztbet (by unfold HSet lO sw; omega) ztu,
      fr2 r ztbet (by unfold GCall sw; omega) ztu]
  have r0 : ztyuk := by
    rw [kR lR0 by_rfl by_decide, hR0]
  have r1 : ztyul := by
    rw [kR lR1 by_decide by_decide, hR1]
  have r2 : ztyum := by
    rw [kR lR2 by_decide by_rfl, hR2]
  have hr0 : (N.arc ztcay).reg < N.nRegions :=
    hrsl _ ztjql
  have hr1 : (N.arc ztbhb).reg < N.nRegions := hrsl _ ztjql
  have hr2 : (N.arc ztcaz).reg < N.nRegions :=
    hrsl _ ztjql
  have hS₄ : SEnv P W C N Mod R₀ zthj _ c₄ :=
    ⟨hL.hG, hW3, hL₄.hctx, hL.hNF, by_omega, by rw [t4]; omega, hR,
      by omega, e4, h4, d4, by rw [← hR]; exact hy⟩
  have hsc := lhScanK_mono (hCh _ hr0) (hCh _ hr1) (hCh _ hr2)
  -- 5. the chords
  refine (lhScan_irs hI₄ hK hS₄ rfl hL₄.hNW hL₄.hE r0 r1 r2 hr0 hr1 hr2 a₁
    zteqp).mono hsc ?_
  rintro c₅ ⟨⟨L₂, a₂, s₂, g₂, d₂⟩, fr5⟩
  have hLL₁ : L ⊆ L₁ := by
    rcases hL₁ with rfl | ⟨τ, rfl, -⟩
    · simp
    simp
  refine ⟨⟨L₂, a₂, hLL₁.trans s₂, fun τ hτ => ?_, fun hgeo => ?_⟩, fun r h1 h2 h3 => ?_, ?_, ?_⟩
  · rcases g₂ τ hτ with h | h
    · rcases hL₁ with rfl | ⟨τ', rfl, hτ', hg'⟩
      · zueou
      · rcases h with rfl | h
        · exact Or.inr ⟨hτ', hg'⟩
        · zueou
    · zuhcq
  · obtain ⟨h, hxh, hhn, hyz, hsec, hzt⟩ := hgeo
    obtain ⟨hfree, hmem⟩ := Sweep.local_hit_mem C hL.hP hD hL.hNF hxh by_omega he hpp.1 hpp.2.1 hyz hsec hy
      hzt hj1 hl1 hl2 (gathered_keys hL.hNF hrsl (m := c₃.nmem) (AB := c₃.nreg gBase)
        ztksy) hho.2.2.2
    zuknu
    rcases hmem with hlo | ⟨r, hr, k, hk, hca, hpos⟩
    · exact s₂ (comp₁ hfree hzt hlo)
    · have hk' : k ∈ (N.region (N.arc ztcay).reg).chords ++
          ((N.region (N.arc ztbhb).reg).chords ++
            (N.region (N.arc ztcaz).reg).chords) := by
        zufbd
        rcases hr with rfl | rfl | rfl <;> zupay
      obtain ⟨τ, hτ, hτpos⟩ := d₂ hzt k hk' hca
      have hne : dirOf ztcuy ≠ 0 := by rcases hσ' with h | h <;> zvmwc <;> norm_num
      have := Chazelle.Visibility.rayPt_injective _ hne (hτpos.symm.trans hpos)
      zvnnr; exact hτ
  · have hS : ¬ SSet r := fun h => h2 (by unfold SSet sw at h; unfold LHW sw; omega)
    rw [fr5.1 r h1 hS ztise
      ztbuv
      ztbuv h3,
      k4 r h1 h2 h3, k3 r h1 h2 h3, k2 r h1 h2 h3, k1 r h1 h2 h3]
  · have := fr5.2.1; omega
  · zuge
    rw [fr5.2.2 a by_omega, hm4 a by_omega, hm3, hm2 a by_omega, hm1 a ha]
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The mathematics -/

/-- Agreeing walk points give agreeing edge ends. -/
theorem wab_of_sidePt {W W' : Polygon} {p p' : ℕ} (h : ∀ t, sidePt W p t = sidePt W' p' t) :
    W.vtx p = W'.vtx p' ∧ W.vtx ztwjb = W'.vtx ztgwe := by
  constructor
  · have := h 0; rwa [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero] at this
  · have := h 1; rwa [Restore.sidePt_one', Restore.sidePt_one'] at this

/-- Positions on edges with the same ends have the same parameter and point. -/
theorem param_pos_of_wab {M M' : Model} {p p' : ℕ} (ha : M.wa p = M'.wa p')
    (hb : M.wb p = M'.wb p') (Q : Polygon) (h : ℕ) :
    M.param Q ztnk = M'.param Q ztcfq ∧ M.pos Q ztnk = M'.pos Q ztcfq := by
  have hp : M.param Q ztnk = M'.param Q ztcfq := by
    zudcl
  exact ⟨hp, by unfold Model.pos; simp_all⟩

/-- **A side of a junction for the conversion**: the side model `M'` of the chain `C'`, the
constants of its correspondence with the model `M` of `C` (with the three cases of the lengths),
and the agreement of the vertical box sides. -/
structure SideConv (M M' : Model) (C' : Chain) (g g' L1 L2 δ : ℕ) : Prop where
  hM' : M' = chainModel C'
  hτ : ∃ τ, g' = 6 + τ ∧ τ < 2 * C'.m ∧ ((L1 = 2 * C'.m + 7 ∧ L2 = 0 ∧ δ = 0) ∨
    (τ = 0 ∧ L1 = 2 * C'.m ∧ L2 = 0 ∧ δ = 0) ∨ (0 < τ ∧ L1 = 2 * C'.m - τ ∧ L2 = τ ∧ δ = 7))
  hg : g < M.W.n
  hMn : 6 < M.W.n
  hL : L1 + L2 ≤ M.W.n
  corr : ∀ d, d < L1 + L2 → ∀ t,
    sidePt M.W ztwje t = sidePt M'.W ((g' + Sweep.dq L1 δ d) % M'.W.n) t
  box : ∀ e, zthgo → M.wa e = M'.wa e ∧ M.wb e = M'.wb e
variable (J : Merge.Junction)
/-- The side of `C₂`. -/
theorem sideConvR (hP : J.P.Simple) :
    SideConv ztbm ztj J.right ztve
      ztbrv ztvds (Sweep.rL2 J) ztvdt := by
  have hC := Sweep.corr_right0 J hP ztjmt Set.finite_empty
  zubau
  zunc
  refine ⟨rfl, ⟨tpos J.right 0, rfl, hτ, ?_⟩, hC.hg, by zvokr; omega, hC.hL,
    fun d hd t => corrR_sidePt J hP hd t,
    fun e he => ?_⟩
  · unfold Sweep.rL1 Sweep.rL2 Sweep.rδ
    grind
  · obtain ⟨ha, hb, -, -⟩ := boxTwin_pos (FuseMath.radius_of_P J (C' := J.right) rfl) he
      ⟨[]⟩ 0
    simp_all

/-- The side of `C₁`. -/
theorem sideConvL (hP : J.P.Simple) :
    SideConv ztbm ztbw J.left ztxfw
      ztgcv ztvdq (Sweep.lL2 J) ztvdr := by
  have hC := Sweep.corr_left0 J hP ztjmt Set.finite_empty
  zucmz
  zufd
  refine ⟨rfl, ⟨tpos J.left J.m₁, rfl, hτ, ?_⟩, hC.hg, by zvokr; omega, hC.hL,
    fun d hd t => corrL_sidePt J hP hd t,
    fun e he => ?_⟩
  · unfold Sweep.lL1 Sweep.lL2 Sweep.lδ
    grind
  · obtain ⟨ha, hb, -, -⟩ := boxTwin_pos (FuseMath.radius_of_P J (C' := J.left) rfl) he
      ⟨[]⟩ 0
    simp_all

/-- The offset in `M` of the tour edge `x` of the side model (inverse of `dq`). -/
def convD (g' L1 δ n' x : ℕ) : ℕ :=
  if ztdba < L1 then ztdba
  else ztdba - δ

/-- The edge `(g + d) mod n`. -/
def convM (g n d : ℕ) : ℕ := if d < n - g then g + d else d - ztodp

/-- **The converted edge.** -/
def convVal (g g' L1 δ n' n e : ℕ) : ℕ :=
  if e < 6 then e else convM g n (convD g' L1 δ n' (if e + 1 = n' then 6 else e))

/-- The tour vertex `6` of a chain model is its top, as is the vertex `2m + 6`. -/
theorem slit_start_pos (C : Chain) (Q : Polygon) {h : ℕ}
    (h0 : (chainModel C).param Q ztoln = 0) :
    (chainModel C).param Q ztolu = 0 ∧
      (chainModel C).pos Q ztolu = (chainModel C).pos Q ztoln := by
  have hv6 : (chainModel C).wa 6 = C.top := C.sideWalk_vtx_six _
  have hvt : ztytp := by
    show (C.sideWalk C.sideBeta).vtx _ = C.top
    rw [show 2 * C.m + 6 = 2 * C.m + 6 by rfl, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]
  have hwb : (chainModel C).wb _ = C.slitTop := C.sideWalk_vtx_wrap _
  zueqq
  have hp6 : (chainModel C).param Q ztolu = 0 := by
    zukkl
    · rfl
    · have hk : (Q.vtx k).2 = C.top.2 := by
        unfold Model.param at h0; simp only at h0
        rw [hvt, hwb] at h0
        have hne : C.slitTop.2 - C.top.2 ≠ 0 := by
          positivity
        grind
      zudcl
  refine ⟨hp6, ?_⟩
  zueew
  simp_all

/-- The index arithmetic of a tour edge. -/
theorem conv_arith {m τ L1 L2 δ x : ℕ} (hτ : τ < 2 * m)
    (hc : (L1 = 2 * m + 7 ∧ L2 = 0 ∧ δ = 0) ∨ (τ = 0 ∧ L1 = 2 * m ∧ L2 = 0 ∧ δ = 0) ∨
      (0 < τ ∧ L1 = 2 * m - τ ∧ L2 = τ ∧ δ = 7)) (hx6 : 6 ≤ x) (hx : x < 2 * m + 6) :
    convD ztckx L1 δ ztfk x < L1 + L2 ∧
      (6 + τ + Sweep.dq L1 δ (convD ztckx L1 δ ztfk x)) % ztfk = x := by
  have key : ∀ v, v = x ∨ v = x + ztfk → v % ztfk = x := by
    rintro v (rfl | rfl)
    · zudgs
    · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt by_omega
  unfold Sweep.dq convD
  constructor
  · grind
  · apply key
    grind
theorem add_mod_cases {g d n : ℕ} (hg : g < n) (hd : d < n) : ztbe % n = convM g n d := by
  unfold convM
  zus
  · zudgs
  · rw [show g + d = (d - ztodp) + n by omega, Nat.add_mod_right]
    zudgs

/-- **The converted position has the same point.** -/
theorem conv_pos {M M' : Model} {C' : Chain} {g g' L1 L2 δ : ℕ}
    (hS : SideConv M M' C' g g' L1 L2 δ) (Q : Polygon) {e h : ℕ}
    (hv : zthgo ∨ (6 ≤ e ∧ e < 2 * C'.m + 6) ∨
      (e = 2 * C'.m + 6 ∧ M'.param Q ztcq = 0)) :
    convVal g g' L1 δ M'.W.n M.W.n e < M.W.n ∧
      M.param Q ztkyi = M'.param Q ztcq ∧
      M.pos Q ztkyi = M'.pos Q ztcq := by
  obtain ⟨hM', ⟨τ, hg', hτ, hc⟩, hg, hMn, hL, hcorr, hbox⟩ := hS
  subst hM' hg'
  zuhfj
  -- the tour case for an edge `x`
  have tour : ∀ x, 6 ≤ x → x < 2 * C'.m + 6 →
      convM g M.W.n ztxbk < M.W.n ∧
      M.param Q ztbaow =
        (chainModel C').param Q zthnu ∧
      M.pos Q ztbaow =
        (chainModel C').pos Q zthnu := by
    intro x hx6 hx
    rw [hn']
    obtain ⟨hdL, hmod⟩ := conv_arith hτ hc hx6 hx
    have hdn : convD ztckx L1 δ ztjes x < M.W.n := by_omega
    rw [← add_mod_cases hg hdn]
    have hs : ∀ t, sidePt M.W ((g + convD ztckx L1 δ ztjes x) % M.W.n) t =
        sidePt (chainModel C').W x t := by
      simp_all
    obtain ⟨ha, hb⟩ := wab_of_sidePt hs
    zufjx
    exact ⟨Nat.mod_lt _ by_omega, hp, hq⟩
  unfold convVal
  rcases hv with he | ⟨he6, he⟩ | ⟨rfl, h0⟩
  · have he6 : e < 6 := by_omega
    rw [ite_eq_left he6]
    obtain ⟨ha, hb⟩ := hbox e he
    zufjx
    grind
  · grind
  · rw [ite_eq_right by_simp_all,
      ite_eq_left by_omega]
    obtain ⟨h6, hpos⟩ := slit_start_pos C' Q h0
    grind

/-! ## The RAM -/
def cX : ℕ := sw 3300
def cT : ℕ := sw 3301
def cDd : ℕ := sw 3302

/-- **The conversion** of the edge in `pe` to the edge `po` of `M`, with the constants of the
correspondence at `b … b + 4` (`g, g', L1, L2, δ`) and the walk length of the side model in `nr`
(scratch `cX, cT, cDd`). -/
def convS (b nr pe po : ℕ) : Stmt :=
  .ifLtN pe K6 (.instr (.copyN po pe))
    (.seq (block [.copyN cX pe, .addN cT pe K1])
    (.seq ztjuu
    (.seq (.ifLtN cX ztds ztxsa
        ztyob)
    (.seq (.ifLtN cT ztub ztovw ztjdn)
    (.seq (.instr (.subN cT zthg b))
      (.ifLtN cDd cT (.instr ztrhz) (.instr (.subN po cDd cT))))))))

/-- The registers `convS` writes. -/
def CvSet (po r : ℕ) : Prop := r = po ∨ r = cX ∨ r = cT ∨ r = cDd
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The conversion on the RAM.** -/
theorem convS_irs {b nr pe po : ℕ} (hbr : b = sw 40 ∨ b = sw 45) (hnr : nr = sw 33 ∨ nr = sw 34)
    (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd) (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd)
    (hI : IInv W c₀ c) (hK : Consts c₀)
    (hpn : c.nreg pe < c.nreg nr) (hg' : c.nreg ztds < c.nreg nr) (hnW : c.nreg nr ≤ W)
    (hg : c.nreg b < c.nreg zthg) (hnW' : c.nreg zthg ≤ W) :
    IRS P W c₀ (convS b nr pe po) c 22 (fun c' =>
      c'.nreg po = convVal ztfgv ztxni ztwzr ztcyz
        zthvj ztwru ztqiy ∧
      ztcjo ∧ c'.nmem = c.nmem) := by
  zuhx
  zucww
  have k6 := hKc.2.2.1
  have hbl : 240040 ≤ b ∧ b ≤ 240045 := by rcases hbr with rfl | rfl <;> zupdg
  have hnl : 240033 ≤ nr ∧ nr ≤ 240034 := by rcases hnr with rfl | rfl <;> zupdg
  have eX : cX = 243300 := rfl
  have eT : cT = 243301 := rfl
  have eD : cDd = 243302 := rfl
  have e6 : K6 = 240612 := rfl
  have e1 : K1 = 240611 := rfl
  have e35 : sw 35 = 240035 := rfl
  have scX : IScr cX := iscr_sw by_omega by_omega
  have scT : IScr cT := iscr_sw by_omega by_omega
  have scD : IScr cDd := iscr_sw by_omega by_omega
  have hpoX := hpo.2.1
  have hpoT := hpo.2.2.1
  have hpoD := hpo.2.2.2
  unfold convS
  zuhsx
  · refine (IRS.ifT hbox (IRS.instr1 (i := .copyN po pe) hI hpo.1)).mono by_norm_num ?_
    zuu
    zuflx
    · show upd c.nreg po _ po = _
      rw [upd_same]; unfold convVal; simp_all
    · show upd c.nreg po _ r = _
      exact upd_other _ _ _ ztwnm
  refine IRS.mono (K := 21) ztsyc by_norm_num ztb
  -- the box test failed: `6 ≤ e`
  set e := c.nreg pe with he
  have he6 : 6 ≤ e := by_omega
  -- step 1
  have ok1 : okB W c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg :=
    ⟨scX, ⟨scT, by
      simp only [regI, upd]
      grind⟩, trivial⟩
  refine (IRS.seq (K₂ := 17) ztrjo ?_).mono by_simp ztb
  zugn
  have v1X : c₁.nreg cX = e := by
    zubuz
  have v1T : c₁.nreg cT = e + 1 := by
    zvmwl; show regB c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg cT = _
    zuie
  have k1r : ∀ r, r ≠ cX → r ≠ cT → c₁.nreg r = c.nreg r := by
    intro r h1 h2; zvmwl; show regB c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg r = _
    zuie
  zull
  have fx : ∀ r, 240000 ≤ r → r < 240700 → c₁.nreg r = c.nreg r := by_grind
  -- step 2: `x := 6` at the end of the walk
  have hnr1 : c₁.nreg nr = c.nreg nr := by_grind
  have k6' : ztpmz := by_simp_all
  have st2 : IRS P W c₀ ztjuu c₁ 6 (fun c' =>
      c'.nreg cX = ztjyu ∧
      (∀ r, r ≠ cX → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem) := by
    zumso
    by_cases h1 : c₁.nreg cT < c₁.nreg nr
    · zudff
      grind
    refine IRS.mono (K := 6) ztfnr by_norm_num ztb
    by_cases h2 : c₁.nreg nr < c₁.nreg cT
    · omega
    refine (IRS.ifF h2 (IRS.instr1 (i := .copyN cX K6) hI₁ scX)).mono by_norm_num ?_
    zuu
    zuflx
    · show upd c₁.nreg cX (c₁.nreg K6) cX = _
      rw [v1T, hnr1] at h1 h2
      rw [upd_same, k6', ite_eq_left by_grind]
    · show upd c₁.nreg cX _ r = _
      simp_all
  refine (IRS.seq (K₂ := 11) st2 ?_).mono by_norm_num ztb
  rintro c₂ hI₂ - - ⟨v2X, k2r, hm2⟩
  set x := ztjyu with hx
  have fx2 : ∀ r, 240000 ≤ r → r < 240700 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    grind
  have hxn : x < c.nreg nr := by_grind
  -- step 3: `d₂`
  have g2 : c₂.nreg _ = c.nreg ztds := fx2 _ by_omega by_omega
  have n2 : c₂.nreg nr = c.nreg nr := by_grind
  have st3 : IRS P W c₀ (.ifLtN cX ztds ztxsa
      ztyob) c₂ 4 (fun c' =>
      c'.nreg cT = (if x < c.nreg ztds then x + ztzdx
        else x - c.nreg ztds) ∧
      (∀ r, r ≠ cT → c'.nreg r = c₂.nreg r) ∧ c'.nmem = c₂.nmem) := by
    by_cases h1 : c₂.nreg cX < c₂.nreg ztds
    · have ok3 : okB W c₂.nmem [.subN cT nr ztds, .addN cT cX cT] c₂.nreg := by
        refine ⟨scT, ⟨scT, ?_⟩, trivial⟩
        show ztrxv cX +
          ztrxv cT ≤ W
        rw [upd_other _ _ _ by_grind, upd_same, n2, g2, v2X]
        omega
      refine (IRS.ifT h1 (IRS.block _ hI₂ ok3)).mono by_norm_num ?_
      zuu
      zuflx
      · show regB c₂.nmem [.subN cT nr _, .addN cT cX cT] c₂.nreg cT = _
        zudj
        rw [upd_same, upd_other _ _ _ by_omega, upd_same, n2, g2, v2X]
        grind
      · show regB c₂.nmem [.subN cT nr _, .addN cT cX cT] c₂.nreg r = _
        zumxi; rw [upd_other _ _ _ hr, upd_other _ _ _ hr]
    · refine (IRS.ifF h1 (IRS.instr1 (i := .subN cT cX _) hI₂ scT)).mono by_norm_num ?_
      zuu
      zuflx
      · show upd c₂.nreg cT (c₂.nreg cX - c₂.nreg _) cT = _
        rw [upd_same, v2X, g2]; grind
      · show upd c₂.nreg cT _ r = _
        zuclj
  refine (IRS.seq (K₂ := 7) st3 ?_).mono by_norm_num ztb
  rintro c₃ hI₃ - - ⟨v3T, k3r, hm3⟩
  set d₂ := (if x < c.nreg ztds then x + ztzdx else x - c.nreg ztds)
    with hd₂
  have hd₂n : d₂ < c.nreg nr := by_grind
  have fx3 : ∀ r, 240000 ≤ r → r < 240700 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    grind
  -- step 4: `d`
  have l3 : c₃.nreg _ = c.nreg ztub := fx3 _ by_omega by_omega
  have δ3 : c₃.nreg _ = c.nreg (b + 4) := fx3 _ by_omega by_omega
  have st4 : IRS P W c₀ (.ifLtN cT ztub ztovw
      ztjdn) c₃ 3 (fun c' =>
      c'.nreg cDd = convD ztxni ztwzr ztcyz zthvj x ∧
      (∀ r, r ≠ cDd → c'.nreg r = c₃.nreg r) ∧ c'.nmem = c₃.nmem) := by
    by_cases h1 : c₃.nreg cT < c₃.nreg ztub
    · refine (IRS.ifT h1 (IRS.instr1 (i := .copyN cDd cT) hI₃ scD)).mono by_norm_num ?_
      zuu
      zuflx
      · show upd c₃.nreg cDd (c₃.nreg cT) cDd = _
        rw [upd_same, v3T]; rw [v3T, l3] at h1; unfold convD; grind
      · show upd c₃.nreg cDd _ r = _
        zuclj
    · refine (IRS.ifF h1 (IRS.instr1 (i := .subN cDd cT _) hI₃ scD)).mono by_norm_num ?_
      zuu
      zuflx
      · show upd c₃.nreg cDd (c₃.nreg cT - c₃.nreg _) cDd = _
        rw [upd_same, v3T, δ3]; rw [v3T, l3] at h1; unfold convD; grind
      · show upd c₃.nreg cDd _ r = _
        zuclj
  refine (IRS.seq (K₂ := 4) st4 ?_).mono by_norm_num ztb
  rintro c₄ hI₄ - - ⟨v4D, k4r, hm4⟩
  set d := convD ztxni ztwzr ztcyz zthvj x with hd
  have fx4 : ∀ r, 240000 ≤ r → r < 240700 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    grind
  -- step 5: `n - g`
  have b4 : c₄.nreg b = c.nreg b := by_grind
  have n4 : c₄.nreg _ = c.nreg zthg := fx4 _ by_omega by_omega
  refine (IRS.seq (K₂ := 3) (IRS.instr1 (i := .subN cT _ b) hI₄ scT) ?_).mono by_norm_num
    ztb
  zugbc
  have v5T : ztxbo cT = c.nreg zthg - c.nreg b := by
    rw [upd_same, b4, n4]
  have v5D : ztxbo cDd = d := by
    tauto
  have v5b : ztxbo b = c.nreg b := by
    rw [upd_other _ _ _ by_omega, b4]
  -- step 6: the edge
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b) } with hc5
  have hpost : ∀ c' : Config, c'.nreg po = convVal ztfgv ztxni ztwzr
      ztcyz zthvj ztwru e →
      (∀ r, r ≠ po → c'.nreg r = c₅.nreg r) → c'.nmem = c₅.nmem →
      c'.nreg po = convVal ztfgv ztxni ztwzr ztcyz
        zthvj ztwru ztqiy ∧
      ztcjo ∧ c'.nmem = c.nmem := by
    intro c' h1 h2 h3
    refine ⟨h1, fun r hr => ?_, by_grind⟩
    rw [h2 r ztwnm]
    show upd c₄.nreg cT _ r = _
    rw [upd_other _ _ _ ztwkw,
      k4r r ztwkw,
      k3r r ztwkw,
      k2r r ztbake,
      k1r r ztbake ztwkw]
  have hval : convVal ztfgv ztxni ztwzr ztcyz zthvj
      ztwru e = convM ztfgv ztwru d := by
    unfold convVal; grind
  by_cases h6 : c₅.nreg cDd < c₅.nreg cT
  · have ok6 : okI W c₅.nreg ztrhz := ⟨hpo.1, by
      grind⟩
    refine (IRS.ifT h6 (IRS.instr1 hI₅ ok6)).mono by_norm_num ?_
    zuu
    zuknl
    · show upd c₅.nreg po _ po = _
      zubso

      simp only [hc5]; rw [v5b, v5D]; unfold convM; grind
    · show upd c₅.nreg po _ r = _
      zuclj
  · refine (IRS.ifF h6 (IRS.instr1 (i := .subN po cDd cT) hI₅ hpo.1)).mono by_norm_num ?_
    zuu
    zuknl
    · show upd c₅.nreg po _ po = _
      zubso

      simp only [hc5]; rw [v5D, v5T]; unfold convM; grind
    · show upd c₅.nreg po _ r = _
      zuclj
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc sideLeftOf sideCcw sideCross sidePrev sideNext)
@[expose] public section
theorem absy_lt (C : Chain) {p : Point} (hp : p ∈ C.set) : |p.2| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius

/-- **The positions converted to the model of `C`.** -/
def PosClass (C : Chain) (Q : Polygon) (x : WPos) : Prop :=
  ztdiq ∨ ztbxz ∨
    ztgmw
theorem pos_eq_sidePt' (C : Chain) (Q : Polygon) (x : WPos) :
    (chainModel C).pos Q x = sidePt (chainModel C).W x.edge ztuy := rfl
variable {C : Chain} {Q : Polygon} {x : WPos}
/-- **Points of the chain or of the box on a ray strictly inside the height band** have positions
of the class. -/
theorem posClass_of (he : x.edge < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (hy : |((chainModel C).pos Q x).2| < C.radius)
    (hc : ((chainModel C).pos Q x).2 ≤ C.top.2 ∨ |((chainModel C).pos Q x).1| = C.radius) :
    PosClass C Q x := by
  zukk
  zubo
  zugne
  have htx := C.abs_top_fst_lt_radius
  zucew
  rw [pos_eq_sidePt' C Q x, ← ht] at hy hc
  zuxj
  zucn
  rw [hW] at hy hc
  unfold PosClass
  rcases (show x.edge < 6 ∨ ztbxz ∨ x.edge = 2 * C.m + 6 by
    omega) with hlt | hmid | hend
  · rcases (show x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨ x.edge = 5 by
      omega) with h | h | h | h | h | h
    · grind
    · omega
    · grind
    · omega
    · grind
    · exfalso
      rw [h, b5] at hy hc; simp only at hy hc
      zunk
      · nlinarith
      simp_all
  · omega
  · refine Or.inr (Or.inr ⟨hend, ?_⟩)
    rw [hend, b6] at hc; simp only at hc
    zunk
    · zukkn
      · nlinarith
      simp_all
    simp_all

/-- **The points of the class** are points of the chain or of a vertical side of the box. -/
theorem posClass_pt (hx : PosClass C Q x)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (hy : |((chainModel C).pos Q x).2| < C.radius) :
    (chainModel C).pos Q x ∈ C.set ∨
      (|((chainModel C).pos Q x).1| = C.radius ∧ |((chainModel C).pos Q x).2| < C.radius) := by
  zubo
  zucew
  rw [pos_eq_sidePt' C Q x, ← ht] at hy ⊢
  zuxj
  zucn
  zujim
  rcases hx with (h | h) | ⟨h6, hlt⟩ | ⟨hend, hz⟩
  · grind
  · grind
  · left
    have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := t) by_omega
      ztczk h0 h1
    simp_all
  · left
    rw [hend, ht, hz]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl ztdnl le_rfl
      one_pos

/-- **The bottom corners of the box have no horizontal direction in their left sector.** -/
theorem not_sideLeft_bottom (C : Chain) {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    (hp : p = 2 ∨ p = 3) :
    ¬ sideLeft (chainModel C).W p 0 (rayPt ztcwj σ 1) := by
  zubo
  zukk
  zucn
  unfold sideLeft sideLeftOf sidePrev sideNext sideCcw
  rw [hW, Chazelle.Chain.sidePt_zero, ite_eq_left rfl]
  rw [hW] at hn
  zugaa
  · rw [show (2 + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = 1 by
        rw [hn, show 2 + ztz - 1 = 1 + ztz by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega],
      show ztssp % (C.sideWalk C.sideBeta).n = 3 by zvmxq; exact Nat.mod_eq_of_lt by_omega,
      C.sideWalk_vtx_one, C.sideWalk_vtx_two, C.sideWalk_vtx_three]
    zufca
    zuq
    rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith
  · rw [show (3 + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = 2 by
        rw [hn, show 3 + ztz - 1 = 2 + ztz by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega],
      show ztjfq % (C.sideWalk C.sideBeta).n = 4 by zvmxq; exact Nat.mod_eq_of_lt by_omega,
      C.sideWalk_vtx_two, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
    zufca
    zuq
    rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith

/-- **A query point lies strictly inside the height band of the box.** -/
theorem query_abs (he : x.edge < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (htop : ((chainModel C).pos Q x).2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft (chainModel C).W x.edge ztuy
      (rayPt ztte σ 1)) :
    |((chainModel C).pos Q x).2| < C.radius := by
  zukk
  zubo
  zugne
  have htm : |C.top.2| < C.radius := absy_lt C C.top_mem_set
  have htl := (abs_lt.1 htm).1
  zucew
  rw [pos_eq_sidePt' C Q x, ← ht] at htop hsec ⊢
  zuxj
  zucn
  rcases (show x.edge < 6 ∨ ztbxz ∨ x.edge = 2 * C.m + 6 by
    omega) with hlt | hmid | hend
  · rcases (show x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨ x.edge = 5 by
      omega) with h | h | h | h | h | h
    · grind
    · rw [hW, h, b1]; simp only
      rw [hW, h, b1] at htop; simp only at htop
      zuigx
    · exfalso
      have ht0 : ztbhh := by
        zukkn
        · exfalso
          apply Sweep.not_sideLeft_horizontal h0 h1 (W := (chainModel C).W) (p := 2) _ σ
          · simp_all
          rfl
        simp_all
      rw [h, ht0] at hsec
      exact not_sideLeft_bottom C hσ ztp hsec
    · rcases h0.lt_or_eq with h0' | h0'
      · rw [hW, h, b3]; simp only
        zuigx
      · exfalso
        rw [h, ← h0'] at hsec
        exact not_sideLeft_bottom C hσ ztbt hsec
    · grind
    · rw [hW, h, b5] at htop; simp only at htop; nlinarith
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := t) by_omega
      ztczk h0 h1
    rw [show x.edge - 6 + 6 = x.edge by omega] at this
    exact absy_lt C by_simp_all
  · rw [hW, hend, b6] at htop ⊢; simp only at htop ⊢
    have : t * ztox ≤ 0 := by_linarith
    have ht0 : ztbhh := by_nlinarith
    grind
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Mathematics -/
variable (C : Chain)
/-- **A free direction at a point of a chain or of a vertical side of the box has a departure
position** in the walk of the chain model. -/
theorem arrival_of_freeC (hPC : C.P.Simple) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ C.set ∨ (|z.1| = C.radius ∧ |z.2| < C.radius))
    (hf : FreeAt C z σ) : ∃ p t, Sweep.Arrival (chainModel C).W z (-σ) p t := by
  zublc

  zubat
  have hee : ztrhf := by
    zuq
    zuegg

  have hopen : ztxjb := by
    zugg
    rw [show Geometry.lerp z _ s = rayPt z σ ztohf by
      apply Geometry.point_ext <;> zuokw; ring]
    zukam
    exact hsub ⟨by_simp_all, by have := hs.2; zuoxz; nlinarith⟩
  obtain ⟨p, t, hp, ht0, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hPC C.sideBeta hee by_simp hopen hz
  zukev
  have hl' : sideLeft (chainModel C).W p t _ := hl
  refine ztiom
  zuduy
  have h1 : ztxrq := by
    simp_all
  have := (Sweep.sideLeft_rayPt_iff _ p t σ hT one_pos).1 h1
  simp_all

/-- **The flag from `arrivalPos`**: free iff an arrival position exists. -/
theorem freeAt_iff_arr (hPC : C.P.Simple) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ C.set ∨ (|z.1| = C.radius ∧ |z.2| < C.radius)) :
    FreeAt C z σ ↔ ∃ p t, Sweep.Arrival (chainModel C).W z (-σ) p t := by
  constructor
  · exact arrival_of_freeC C hPC hσ hz
  · rintro ⟨p, t, hp, ht0, ht1, hpt, hl⟩
    rw [neg_neg] at hl
    exact Sweep.freeAt_of_leave C hPC hσ hp ht0 ht1 hpt hl

/-! ## Registers of an answer -/
def qE : ℕ := sw 3210
def qH : ℕ := sw 3211
def qD : ℕ := sw 3212
def zE : ℕ := sw 3213
def zF : ℕ := sw 3214
def zP : ℕ := sw 3215
def zPh : ℕ := sw 3216
def yE : ℕ := sw 3217
def yH : ℕ := sw 3218
def wF : ℕ := sw 3219
def wP : ℕ := sw 3220
def wPh : ℕ := sw 3221
def rL : ℕ := sw 3222
def rR : ℕ := sw 3223
def rho : ℕ := sw 3224

/-! ## The flag -/

/-- `arrivalPos` at the query point (position `(zE, qH)` of `M`, direction code `qD`). -/
def flagS : Stmt := callArr ztjl zE qH qD zF

/-- **The flag.** -/
theorem flagS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hP : J.P.Simple)
    (hctx : ChainCtx P W c ztjl J.whole) {z : Point}
    (he : c.nreg zE < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztdqo)
    (hz : (chainModel J.whole).pos zta ztdqo = z)
    (hzR : |z.2| < J.whole.radius)
    (hzC : z ∈ J.whole.set ∨ (|z.1| = J.whole.radius ∧ |z.2| < J.whole.radius))
    (hroom : c.nreg ALLOC + 35007 ≤ W) :
    IRS P W c₀ flagS c 35007 (fun c' =>
      c'.nreg zF ≤ 1 ∧ (c'.nreg zF = 1 ↔ FreeAt J.whole z ztba) ∧
      (c'.nreg zF = 1 → c'.nreg zP < (chainModel J.whole).W.n ∧
        ProperPos ztbm zta P.n ztrbd ∧
        Sweep.Arrival (chainModel J.whole).W z ztwtj (c'.nreg zP)
          ((chainModel J.whole).param zta ztrbd)) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ zF → r ≠ zP → r ≠ zPh → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hσ := dirOf_cases ztql
  refine (callArr_irs hI hctx ⟨by_decide, by_decide, by_decide,
    by decide, by_decide, by_decide,
    by decide, by_decide⟩ ⟨by_decide,
    by decide⟩ he hpp by_simp_all hroom).mono le_rfl ?_
  rintro c' ⟨⟨hf1, hf2, hf3⟩, hfr, hA, hm⟩
  zvncr at hf2 hf3
  have e1 : zF + 1 = zP := rfl
  have e2 : zF + 2 = zPh := rfl
  zvmws at hf2 hfr
  refine ⟨hf1, ?_, by_omega, hfr, hA, hm⟩
  rw [freeAt_iff_arr J.whole hP hσ hzC]
  grind

/-! ## The record -/

/-- `arrivalPos` at the hit point (position `(yE, yH)`, reversed direction), and the record. -/
def recS : Stmt :=
  .seq (block [.constN rho 1]) (.seq ztjuv
    (.seq (callArr ztjl yE yH rho wF)
      (.seq (block [.copyN rL wP, .copyN rR zP]) (eqT qD K1 (block [.copyN rL zP, .copyN rR wP])))))

/-- The cost of the record. -/
def recK : ℕ := 35030
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The record of the answer.** -/
theorem recS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c₀) (hP : J.P.Simple)
    (hctx : ChainCtx P W c ztjl J.whole) {z : Point} {T : ℝ}
    (hzt : z.2 ≤ J.whole.top.2) (hfree : FreeAt J.whole z ztba)
    (hT : J.whole.hitParam z ztba = T)
    (hAz : Sweep.Arrival (chainModel J.whole).W z ztwtj ztdmx
      ztwmc)
    (he : c.nreg yE < (chainModel J.whole).W.n)
    (hpp : ProperPos ztbm zta P.n ztrbn)
    (hw : (chainModel J.whole).pos zta ztrbn = rayPt z ztba T)
    (hzR : |z.2| < J.whole.radius) {h : ℕ} (hh : ((Qof P).vtx h).2 = z.2)
    (hroom : c.nreg ALLOC + recK ≤ W) :
    IRS P W c₀ recS c recK (fun c' =>
      Sweep.RecordData J zta z ztba T h ztdmx ztvha ztvgx
        ztvgy ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ rL → r ≠ rR →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  set σ := dirOf ztql with hσd
  zuizy
  zudzd
  obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole hzt hσ hfree
  zvncs at hT0
  have hgen : Sweep.Genuine J.whole z σ T :=
    (Sweep.genuine_iff J.whole hzt hσ).2 by_simp_all
  have hsr : ztcrm := fun r h1 h2 => iscr_sw h1 h2
  have hW1 : ztbla := by have := hctx.2.1; unfold hostWords at this; omega
  have hrho : IScr rho := hsr _ by_decide by_decide
  have hq1 : σ = 1 ↔ c.nreg qD = 1 := by
    rw [hσd]; unfold dirOf; grind
  -- `rho := flip qD`
  refine (IRS.seq (K₂ := recK - 1) (IRS.block [.constN rho 1] hI ⟨⟨hrho, hW1⟩, trivial⟩) ?_).mono
    by_rfl ztb
  zugn
  have r1 : c₁.nreg rho = 1 := by zvmwl; rfl
  have k1 : ∀ r, r ≠ rho → c₁.nreg r = c.nreg r := fun r hr => by
    zvmwl; show upd c.nreg rho 1 r = _; simp_all
  zull
  have hA1 : ztdc := k1 _ by_decide
  have q1 : ztizm := k1 _ by_decide
  have kk1 : ztcpf := by_grind
  have st2 : IRS P W c₀ ztjuv c₁ 5 (fun c' =>
      c'.nreg rho = (if c.nreg qD = 1 then 0 else 1) ∧ (∀ r, r ≠ rho → c'.nreg r = c₁.nreg r) ∧
      c'.nmem = c₁.nmem) := by
    zumso
    by_cases h1 : c₁.nreg qD < c₁.nreg K1
    · zudff
      simp_all
    refine IRS.mono (K := 5) ztfnr by_norm_num ztb
    by_cases h2 : c₁.nreg K1 < c₁.nreg qD
    · refine (IRS.ifT h2 (IRS.skip (K := 0) hI₁ ?_)).mono by_norm_num ztb
      grind
    refine (IRS.ifF h2 (IRS.instr1 (i := .constN rho 0) hI₁ ⟨hrho, by_omega⟩)).mono by_norm_num ?_
    zuu
    rw [q1, kk1] at h1 h2
    zuflx
    · show upd c₁.nreg rho 0 rho = _; rw [upd_same, ite_eq_left by_omega]
    · show upd c₁.nreg rho 0 r = _; simp_all
  refine (IRS.seq (K₂ := 35024) st2 ?_).mono by_rfl ztb
  rintro c₂ hI₂ hA₂ - ⟨r2, k2, hm2⟩
  have ff : ∀ r, r ≠ rho → c₂.nreg r = c.nreg r := by_simp_all
  have hA2 : ztbae := by_grind
  have y2 : c₂.nreg yE = c.nreg yE := ff _ by_decide
  have h2' : c₂.nreg yH = c.nreg yH := ff _ by_decide
  have hctx₂ : ChainCtx P W c₂ _ J.whole := hctx.transport
    (ff _ by_decide) by_simp_all (by rw [hA2])
  have hwR : |((chainModel J.whole).pos zta ⟨c₂.nreg yE, c₂.nreg yH⟩).2| < J.whole.radius := by
    simp_all
  refine (IRS.seq (K₂ := 17) (callArr_irs hI₂ hctx₂ ⟨by_decide, by_decide,
    by decide, by_decide, by_decide,
    by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide⟩ by_omega
    by_simp_all hwR (by rw [hA2]; unfold recK at hroom; omega)) ?_).mono le_rfl
    ztb
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨hf1, hf2, hf3⟩, fr3, hA3, hm3⟩
  rw [y2, h2', hw, r2] at hf2 hf3
  have hflip : -dirOf _ = σ := neg_dirOf_flip _
  rw [hflip] at hf2 hf3
  have e1 : wF + 1 = wP := rfl
  have e2 : wF + 2 = wPh := rfl
  zvmws at hf2 fr3
  have hf : c₃.nreg wF = 1 := by
    zuct
    obtain ⟨p, t, hA'⟩ := Sweep.arrival_exists J.whole hP hzt hσ hgen
    grind
  obtain ⟨-, -, hAw⟩ := hf2 hf
  have hRD := Sweep.recordData_of_arrival J _ hσ hT0 hh hAz hAw
  have k3 : ∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ ALLOC →
      c₃.nreg r = c.nreg r := by_grind
  have zp3 : c₃.nreg zP = c.nreg zP := k3 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide by_decide
  have q3 : c₃.nreg qD = c.nreg qD := k3 _ (not_oracle_sw by_decide
    by_decide) by_decide by_decide
    by_decide by_decide by_decide
  have kk3 := (hK.fix hI₃).2.1
  -- the default order, then the swap for `σ = 1`
  refine (IRS.seq (K₂ := 15) (IRS.block [.copyN rL wP, .copyN rR zP] hI₃
    ⟨hsr _ by_decide by_decide,
      hsr _ by_decide by_decide, trivial⟩) ?_).mono
    by_simp ztb
  zudsw
  have v4L : c₄.nreg rL = c₃.nreg wP := by
    zumyv; rfl
  have v4R : c₄.nreg rR = c.nreg zP := by
    zumyv; trivial
  have k4 : ∀ r, r ≠ rL → r ≠ rR → c₄.nreg r = c₃.nreg r := fun r h1 h2 => by
    zumyv; show regB c₃.nmem [.copyN rL wP, .copyN rR zP] c₃.nreg r = _
    zucks
  have hm4 : ztmvj := by zumyv
  have q4 : c₄.nreg qD = c.nreg qD := by rw [k4 _ by_decide
    by_decide, q3]
  have kk4 := (hK.fix hI₄).2.1
  have w4 : c₄.nreg wP = c₃.nreg wP := k4 _ by_decide by_decide
  have zp4 : c₄.nreg zP = c.nreg zP := by
    rw [k4 _ by_decide by_decide, zp3]
  have hfin : ∀ c' : Config, c'.nreg rL = (if σ = 1 then c.nreg zP else c₃.nreg wP) →
      c'.nreg rR = (if σ = 1 then c₃.nreg wP else c.nreg zP) → c'.nreg wP = c₃.nreg wP →
      (∀ r, r ≠ rL → r ≠ rR → c'.nreg r = c₄.nreg r) → c'.nmem = c₄.nmem →
      c'.nreg ALLOC = c₄.nreg ALLOC →
      Sweep.RecordData J zta z σ T h ztdmx ztvha ztvgx ztvgy ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ rL → r ≠ rR →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth := by
    intro c' hl hr hwp hk hm hA
    refine ⟨by_grind, fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, fun a ha => ?_⟩
    · rw [hk r h5 h6, k4 r h5 h6]; grind
    · rw [hA, k4 _ by_decide by_decide]
      omega
    grind
  have hA4 : ztmvk := k4 _ by_decide
    by_decide
  zumso
  by_cases h1 : c₄.nreg qD < c₄.nreg K1
  · refine (IRS.ifT h1 (IRS.skip (K := 0) hI₄ ?_)).mono by_norm_num ztb
    rw [q4, kk4] at h1
    zudzo

  refine IRS.mono (K := 15) ztfnr by_norm_num ztb
  by_cases h2 : c₄.nreg K1 < c₄.nreg qD
  · refine (IRS.ifT h2 (IRS.skip (K := 0) hI₄ ?_)).mono by_norm_num ztb
    rw [q4, kk4] at h2
    zudzo

  rw [q4, kk4] at h1 h2
  have hs : ztgbc := by_grind
  refine (IRS.ifF by_omega
    (IRS.block [.copyN rL zP, .copyN rR wP] hI₄
      ⟨hsr _ by_decide by_decide,
        hsr _ by_decide by_decide, trivial⟩)).mono
    by_simp ?_
  zuu
  refine hfin _ ?_ ?_ ?_ ztpbv rfl ?_
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg rL = _
    zudj
    rw [upd_other _ _ _ by_decide, upd_same, zp4, ite_eq_left hs]
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg rR = _
    zudj
    rw [upd_same, upd_other _ _ _ by_decide, w4, ite_eq_left hs]
  · trivial
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg r = _
    zucks
  rfl
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc sideE)
@[expose] public section
variable (C : Chain)
/-- **The walk positions of a chain vertex.** -/
theorem vtx_pos_iff (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p : ℕ}
    (hp : p < (chainModel C).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    sidePt (chainModel C).W p t = C.vertex k ↔
      t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  constructor
  · exact SweepPrim.vertex_positions C hP hk hp ht0 ht1
  · rintro ⟨rfl, i, hi, rfl, hidx⟩
    zudti
    show (C.sideWalk C.sideBeta).vtx ztcy = _
    zukot
    unfold Chain.sideTour; simp_all

/-- A residue of a number below `3 n`. -/
theorem mod_three {a n : ℕ} (_hn : 0 < n) (ha : a < 3 * n) :
    a % n = if a < n then a else if a < 2 * n then a - n else a - 2 * n := by
  zupi
  · exact Nat.mod_eq_of_lt h1
  · zul
  · rw [Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
    omega

/-- **The tour positions of an end vertex.** -/
theorem endIdx {k : ℕ} (hk : k = 0 ∨ k = C.m) {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideIdx C.sideBeta i = k ↔ i = tpos C k ∨ (i = 2 * C.m ∧ tpos C k = 0) := by
  zuec
  zubt
  zujys
  zuewl
  unfold tpos bS sideE
  zuhof
  rw [mod_three h2m (show S + i < 3 * ztbb by omega),
    mod_three h2m (show k + 2 * C.m - S < 3 * ztbb by omega)]
  rcases hk with rfl | rfl <;> split_ifs <;> omega

/-- The middle visit of the top in the tour. -/
noncomputable def midT (C : Chain) : ℕ :=
  if C.sideBeta then 2 * C.m - 2 * C.topIdx else if C.topIdx < C.m then 2 * C.topIdx else 0

/-- **The tour positions of the top vertex.** -/
theorem topIdx_iff {i : ℕ} (hi : i ≤ 2 * C.m) :
    C.sideIdx C.sideBeta i = C.topIdx ↔ i = 0 ∨ i = 2 * C.m ∨ i = midT C := by
  zuwi
  zubt
  zujys
  zuewl
  unfold midT sideE Chain.sideS
  cases hβ : C.sideBeta
  · zuma
    rw [mod_three h2m (show 2 * C.m - C.topIdx + i < 3 * ztbb by omega)]
    grind
  · zuwa
    rw [mod_three h2m (show C.topIdx + i < 3 * ztbb by omega)]
    grind

/-! ## Positions -/

/-- The normalised height code is `0` iff the parameter is `0` (proper positions). -/
theorem nhgt_eq_zero_iff (M : Model) (Q : Polygon) (u : WPos) :
    nhgt M Q u = 0 ↔ M.param Q u = 0 := by
  zulur
  zus
  · zugyx
  · simp only [h, iff_false]
    zubww
    zuhrs
    obtain ⟨e, hh⟩ := u
    simp_all

/-- **A position is at an end vertex** (`k = 0` or `k = m`) iff its parameter is `0` and its edge
is `6 + tpos C k`, or `2m + 6` when `tpos C k = 0`. -/
theorem atEnd_iff (hP : C.P.Simple) {k : ℕ} (hk : k = 0 ∨ k = C.m) (Q : Polygon)
    {x : WPos} (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x = C.vertex k ↔ (chainModel C).param Q x = 0 ∧
      (x.edge = 6 + tpos C k ∨ (x.edge = 2 * C.m + 6 ∧ tpos C k = 0)) := by
  have hkm : ztidw := by_omega
  rw [pos_eq_sidePt' C Q x, vtx_pos_iff C hP hkm hx h0 h1]
  zukk
  constructor
  · zuekt

    rcases (endIdx C hk hi).1 hidx with h | ⟨h, h'⟩
    · omega
    omega
  · rintro ⟨ht, h | ⟨h, h'⟩⟩
    · zufwx
      refine ⟨ht, tpos C k, by_omega, by_omega, (endIdx C hk by_omega).2 ztp⟩
    · refine ⟨ht, 2 * C.m, le_rfl, by_omega, (endIdx C hk le_rfl).2 (Or.inr ⟨rfl, h'⟩)⟩

/-- **A position is at the top** iff its parameter is `0` and its edge is `6`, `2m + 6` or
`6 + midT`. -/
theorem atTop_iff (hP : C.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x = C.top ↔ (chainModel C).param Q x = 0 ∧
      (x.edge = 6 ∨ x.edge = 2 * C.m + 6 ∨ x.edge = 6 + midT C) := by
  zukk
  have hmid : midT C ≤ 2 * C.m := by
    zujqq
  show _ = C.vertex C.topIdx ↔ _
  rw [pos_eq_sidePt' C Q x, vtx_pos_iff C hP C.topIdx_le hx h0 h1]
  constructor
  · zuekt

    rcases (topIdx_iff C hi).1 hidx with h | h | h <;> omega
  · rintro ⟨ht, h | h | h⟩
    · exact ⟨ht, 0, by_omega, by_omega, (topIdx_iff C by_omega).2 ztp⟩
    · exact ⟨ht, 2 * C.m, le_rfl, by_omega, (topIdx_iff C le_rfl).2 ztwiz⟩
    · exact ⟨ht, midT C, hmid, by_omega, (topIdx_iff C hmid).2 ztwrm⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Chain (sideE sideLeft sidePt)
@[expose] public section
def SymOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
    sp.eval zta = (chainModel C).pos zta ztbce

/-- The input of the symbolic point: that of `absKey`, and a tour or top position. -/
def SymIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  AbsKeyIn P W C c ∧ ((6 ≤ c.nreg 50201 ∧ c.nreg 50201 < 2 * C.m + 6) ∨
    (c.nreg 50201 = 2 * C.m + 6 ∧
      (chainModel C).param zta ztbce = 0))
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
theorem symVtx_exec
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param zta ztev = 0) :
    ∃ c' k, Exec P W absVtx c c' k ∧ k ≤ 27 * H.length + 45 ∧
      c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
        sp.eval zta = (chainModel C).pos zta ztev := by
  zuiu
  have hE₁ : ztrfh := hE.step e₁ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    zteqd by_omega (dst := 50211) by_norm_num
  have e₃ := Exec.constN (P := P) e₂.wb_right 50210 1 (by have := hE.hW; omega)
  have hv : ztwnq := by
    rw [SweepPrim.pos_eq_sidePt, hpar, Chazelle.Chain.sidePt_zero, show e - 6 + 6 = e by omega]
  refine ⟨_, _, .seq e₁ ztcr, by_omega, by_simp, sp,
    symPtIn_of_eq isp fun j h1 h2 => by zunxc, lsp, ?_⟩
  simp_all
theorem symInt_exec
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 6)
    (ht : 0 < (chainModel C).param zta ztev) (ht1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      c'.nreg 50210 = 1 ∧ ∃ sp : SymPt, SymPtIn c' 50211 sp ∧ sp.Lt P.n ∧
        sp.eval zta = (chainModel C).pos zta ztev := by
  zuol
  zubb
  zudym

  zubnw
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    zuyv
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; zunqk, by config_simp; zunkz; ring,
        fun r h1 h2 => by_simp_all⟩
  zucxx
  have hE₁ : ztrfi := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) by_decide).2.2.1
    ztwxf
  have hlt : ztgau := by_omega
  zuckk
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c₁ hE₁ (i := i) q20
    hlt.le (dst := 50130) by_norm_num
  zue
  have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
    ztdtz
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50120 + c₂.nreg 50032) }
    with hc₃
  have hE₃ : ztrfj := hE₂.step e₃ by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
    ztbtw
    by_omega (dst := 50136) by_norm_num
  have i₁' : SymPtIn c₄ 50130 s₁ := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
    zumwr; zunbj) f₄
    by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right by_omega
    hE₄.r32 i₁' i₂ l₁ l₂
  have q02 : ztlyi := by
    zuwy
    zubi
    zudar
  have q32 : ztlyh := by
    zubqc
  obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂
    (hc := hc) by_grind
  have hc1 : ztixw := by
    zuzn
    · simp_all
    omega
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
      (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 ztyoc) := by
    zumtu
    zudpp
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp, by config_simp; exact v₅, ?_⟩
    config_simp; omega
  zucie
  have ex : Exec P W absInt c c₆ (k₁ + (k₂ + (1 + (k₄ + zttrj)) + 1)) :=
    .seq e₁ (.ifLtN_true by_omega (.seq e₂ (.seq e₃ (.seq e₄
      ztcsd))))
  refine ⟨c₆, _, ex, by_omega, q10, _, q11, ztonu, ?_⟩
  zubkn
  have hy : ztwrc := by
    rw [Model.pos_snd (Q := Qof P) (x := ztev) hne]
    zucnu

  zujrv
  · grind
  · rw [hy]; rfl

/-- **Contract of `absKey` for tour and top positions: the symbolic point of the position.** -/
theorem symKey_meets : Meets absKey primBands ztvcu ztvct
    ztqnc := by
  refine prim_meets (K := 15900) ztng wr_absKey ?_
  intro P W H C c₀ c hC hE ⟨⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hreg⟩, hcls⟩ hinp
  zudpd
  zuet
  zubgf
  obtain ⟨c', k, ex, hk, hr⟩ := classify_exec (Kb := 27 * H.length + 50)
    (Kv := 27 * H.length + 45) (Ki := 60 * H.length + 200) (R := SymOut P C c₀) c₀ c hE hinp hen
    hp0 hp1 hhn hy
    (fun c₂ hE₂ g₂ d₂ he hpos => by_omega)
    (fun c₂ hE₂ g₂ h6 hpar => symVtx_exec c₂ hE₂ ztdop h6
      by_omega hpar)
    (fun c₂ hE₂ g₂ _ h6 hpos => symInt_exec c₂ hE₂ hregH ztdop
      ztlpk h6 (by
        grind) hpos hp1 hhn)
  exact ztlvn
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim SignK
open Chazelle.Visibility (rayPt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The symbolic point of a position -/

/-- `absKey` on the descriptor `dsc` and the position `(re, rh)`, outputs into `o … o + 3`. -/
def callSym (dsc re rh o : ℕ) : Stmt :=
  callP [ztcso, ztdsq, ztdsr] absKey
    [ztcnz, ztbsv, ztciw, ztglc]
theorem symPtIn_copy {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : SymPtIn c' r' s := by
  cases s with
  | vtx i => obtain ⟨a, b⟩ := h; exact ⟨h0.trans a, h1.trans b⟩
  | onEdge e hh => obtain ⟨a, b, d⟩ := h; exact ⟨h0.trans a, h1.trans b, h2.trans d⟩
set_option maxRecDepth 20000 in
/-- **The symbolic point of a tour or top position.** -/
theorem callSym_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztcbr)
    (hy : |((chainModel C).pos zta ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hcls : (6 ≤ c.nreg re ∧ c.nreg re < 2 * C.m + 6) ∨
      (c.nreg re = 2 * C.m + 6 ∧ (chainModel C).param zta ztcbr = 0))
    (hroom : c.nreg ALLOC + 16707 ≤ W) :
    IRS P W c₀ ztqjn c 16707
      (fun c' => ∃ sp : SymPt, SymPtIn c' ztbql sp ∧ sp.Lt P.n ∧
          sp.eval zta = (chainModel C).pos zta ztcbr ∧
        (∀ r, bandOf r ∉ oracleBands → ztlsd → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [ztcso, ztdsq, ztdsr])
    (outs := [ztcnz, ztbsv, ztciw, ztglc]) symKey_meets
    primBands_oracle hI
    (nodup3 by_norm_num by_norm_num by_norm_num)
    by_grind
    (by zvmwt
        decide)
    (nodup4 by_omega by_omega by_omega by_omega by_omega by_omega)
    by_grind
    by_grind
    (fun c₁ hm hA e1 e2 => by
      zuej
      zuqr
      have hctx₁ := hctx.transport g0 ztdnr ztchd
      refine primPre_of hctx₁ ⟨ztbabl, ?_⟩
      · omega
      · simp_all
      · simp_all
      · zunqs; exact hctx.hostReg
      simp_all)
    by_omega
  zuo

  zuqr
  zufkh
  zujd

  obtain ⟨-, sp, hsp, hlt, hev⟩ := hpost H C hC₁
  rw [g1, g2] at hev
  refine ⟨sp, symPtIn_copy hsp k1 by_omega
    by_omega, hlt, hev, fun r hr h0 hra => hk r hr
    ztyo
    hra, hA, hm'⟩

/-! ## One sign test -/

/-- The precondition of a kernel bit at the slots `10500`, `10503`, `10506`. -/
def KbPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ P.n + 3 ≤ W ∧ ∃ sa sb sd : SymPt, SymPtIn c 10500 sa ∧ SymPtIn c 10503 sb ∧
    SymPtIn c 10506 sd ∧ sa.Lt P.n ∧ sb.Lt P.n ∧ sd.Lt P.n

/-- The postcondition of a kernel bit. -/
def KbPost (op : ℕ) (_P : Polygon) (c c' : Config) : Prop :=
  c'.nreg 10520 ≤ 1 ∧ ∀ sa sb sd : SymPt, SymPtIn c 10500 sa → SymPtIn c 10503 sb →
    SymPtIn c 10506 sd → (c'.nreg 10520 = 1 ↔ SignTest op (sa.eval ztqbs) (sb.eval ztqbs)
      (sd.eval ztqbs))

/-- **Contract of one kernel bit** (at most `241` steps). -/
theorem kbit_meets {op : ℕ} (hop : op ≤ 3) :
    Meets (kbit 10500 10503 10506 op 10520) {bSign} KbPre (KbPost op) (fun _ _ => 241) := by
  intro P W c hw ⟨hG, hW, sa, sb, sd, ha, hb, hd, la, lb, ld⟩ _
  obtain ⟨c', k, ex, hk, hfr, hle, hiff⟩ := kbit_exec (a := 10500) (b := 10503) (d := 10506)
    (op := op) (dst := 10520) hG hW c hw by_norm_num by_norm_num
    by_norm_num by_norm_num hop la lb ld ha hb hd
  refine ⟨c', k, ex, hk, ⟨hle, fun sa' sb' sd' ha' hb' hd' => ?_⟩, NFLoc.frame_of_frameB hfr
    ztez k⟩
  · rw [symPtIn_unique ha' ha, symPtIn_unique hb' hb, symPtIn_unique hd' hd]; omega
  · simp only [Bkb, WalkKey.Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
    zujx
    · zuhdm
      zuvs
    · unfold ALLOC; omega

/-- The sign test `op` of the symbolic points at `a` and `b` into `o`. -/
def callKb (a b op o : ℕ) : Stmt :=
  callP [ztsqu, ztpsm, ztpsn, ztsqv, ztpso, ztpsp,
    ztsqw, ztpsq, ztpsr] (kbit 10500 10503 10506 op 10520) [(o, 10520)]
theorem bSign_oracle {r : ℕ} (h1 : 10000 ≤ r) (h2 : r < 20000) : bandOf r ∈ oracleBands := by
  zuhdm
  zuvs
set_option maxRecDepth 20000 in
/-- **One sign test.** -/
theorem callKb_irs {a b op o : ℕ} (hop : op ≤ 3) (hI : IInv W c₀ c) (hG : GoodEnv P)
    (hW : P.n + 3 ≤ W) (ha : 240000 ≤ a ∧ a + 2 < 250000) (hb : 240000 ≤ b ∧ b + 2 < 250000)
    (ho : 240700 ≤ o ∧ o < 250000) {sa sb : SymPt} (hsa : SymPtIn c a sa)
    (hsb : SymPtIn c b sb) (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hroom : c.nreg ALLOC + 251 ≤ W) :
    IRS P W c₀ (callKb a b op o) c 251 (fun c' =>
      c'.nreg o ≤ 1 ∧
      (c'.nreg o = 1 ↔ SignTest op ztxhi ztxoq ztxhi) ∧
      ztcfm ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have h := callP_irs (P := P) (c₀ := c₀) (c := c)
    (ins := [ztsqu, ztpsm, ztpsn, ztsqv, ztpso,
      ztpsp, ztsqw, ztpsq, ztpsr])
    (outs := [(o, 10520)]) (kbit_meets hop) by_decide hI
    by_simp
    ztdau
    (by zvmwt
        decide)
    by_simp
    by_grind
    by_simp_all
    (fun c₁ hm hA e1 e2 => by
      zuej
      zuchv
      exact ⟨hG, hW, sa, sb, sa, symPtIn_copy hsa g0 g1 g2, symPtIn_copy hsb g3 g4 g5,
        symPtIn_copy hsa g6 g7 g8, hla, hlb, hla⟩)
    by_omega
  zuo

  zuchv
  obtain ⟨hle, hiff⟩ := hpost
  have := hiff sa sb sa (symPtIn_copy hsa g0 g1 g2) (symPtIn_copy hsb g3 g4 g5)
    (symPtIn_copy hsa g6 g7 g8)
  refine ⟨by_omega, by_grind, fun r hr h0 hra => hk r hr
    (by simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        exact h0) hra, hA, hm'⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)
@[expose] public section
def bL : ℕ := sw 3225

/-- The bit `bR`: `1` iff the query point is not above the top of `C₂`. -/
def bR : ℕ := sw 3226

/-- The index of the query in the query list. -/
def qJ : ℕ := sw 3227

/-- The symbolic point of the query point (three registers `sw 3231 … 3233`; `callSym` with
output register `sw 3230` writes it). -/
def sO : ℕ := sw 3231

/-- **The chain of an accumulator tag** under the bits `l = bL`, `r = bR`: tag `0` is `C₁` when
`l = 1`, tag `1` is `C₂` when `r = 1`, every other case is `C`.  (A candidate of `C₁` (`C₂`) is
offered only for a query point not above the top of `C₁` (`C₂`); then the winner of the
accumulator is a tour, top or box-wall position of its model, which converts to the walk of `C`.)
-/
def ModB (J : Merge.Junction) (l r t : ℕ) : Chain :=
  if t = 0 ∧ l = 1 then J.left else if t = 1 ∧ r = 1 then J.right else J.whole

/-- **The origin of a stop record** `(e, h, kind, k, b)`: the shared vertex (`kind = 0`), the end
of chord `k` of `N₂` (`kind = 1`, the left end for the direction east), or the top of `C₂`. -/
noncomputable def stopOrig (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) : Point :=
  if kind = 0 then J.shared
  else if kind = 1 then endOrigin J Q N ztxul
  else J.right.top

/-- **The environment of the answer phase** at its base configuration `c₀`: the facts of the
precondition of `SweepSpecH` (without the queries), the stage-0 state of side `0`, the outputs of
stages 2 and 3 (`SweepEv.Out`, arrays below the allocator), and the initialisation of the
answers (constants `K0 … K6`, the table of powers at `TBR` of length `TLR`, large enough for the
arcs of `N₁`, `N₂` and for the stops, the log and the table). -/
structure AEnv (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (J : Merge.Junction) (H : Host) (N₁ N₂ : NF) (E : ℕ) (c₀ : Config) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hX : X.holds P c₀.nmem ztxj ztdq
  hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj
  hP : J.P.Simple
  hOk₁ : Ok P ztbw
  hOk₂ : Ok P ztj
  hN₁ : NFWithin c₀.nmem ztxnx E N₁
  hN₂ : NFWithin c₀.nmem ztyja E N₂
  hNF₁ : IsNF ztbw zta N₁
  hNF₂ : IsNF ztj zta N₂
  hdeg₁ : (chainModel J.left).DegLe ztwjx zto
  hdeg₂ : (chainModel J.right).DegLe ztwis zto
  hsg₁ : (chainModel J.left).Semigranular ztwjx ztq
  hsg₂ : (chainModel J.right).Semigranular ztwis ztq
  hst : SweepEv.St0S P c₀ H J
  hE : E ≤ c₀.nreg ALLOC
  hWm : 2 * J.whole.m + 7 ≤ W
  hK : Consts c₀
  htab : ∀ j, j < c₀.nreg TLR → c₀.nmem zthwa = 2 ^ j
  hbig₁ : N₁.arcs.length < 2 ^ c₀.nreg TLR
  hbig₂ : N₂.arcs.length < 2 ^ c₀.nreg TLR
  hbigE : rd c₀ bSweep 201 + rd c₀ bSweep 301 + 2 * N₂.nChords < 2 ^ c₀.nreg TLR
  hTB : E ≤ c₀.nreg TBR
  hTW : c₀.nreg TBR + c₀.nreg TLR ≤ c₀.nreg ALLOC
  hout : SweepEv.Out P J N₂ c₀
  hstops : rd c₀ bSweep 200 + 5 * rd c₀ bSweep 201 ≤ c₀.nreg ALLOC
  hlog : rd c₀ bSweep 300 + 7 * rd c₀ bSweep 301 ≤ c₀.nreg ALLOC
  htabw : rd c₀ bSweep 302 + 3 * ztbxu ≤ c₀.nreg ALLOC
  hK₁ : c₀.nmem ztxnx = N₁.nChords
  hK₂ : c₀.nmem ztyja = N₂.nChords
  /-- The model descriptors at `sw 30`, `sw 31` hold copies of the chain descriptors at `sw 20`,
  `sw 21` (stage 0, `mdBlk`). -/
  hmd₁ : ∀ j, j < 5 → c₀.nmem (c₀.nreg ztbbz + 1 + j) = c₀.nmem (c₀.nreg ztiw + j)
  hmd₂ : ∀ j, j < 5 → c₀.nmem (c₀.nreg ztqm + 1 + j) = c₀.nmem (c₀.nreg zted + j)

/-- **The frame of a part** (`BruteSpec`, `S0CandSpec`, `Lab0Spec`): registers outside the oracle
bands, outside `sw 1000 … sw 3199`, `sw 3300 … sw 3399` and `sw 4000 … sw 4799`, other than the
allocator, are kept; the allocator grows; memory below it is kept. -/
def PartFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ ztdpo → ¬ (sw 3300 ≤ r ∧ r < sw 3400) →
    ¬ (sw 4000 ≤ r ∧ r < sw 4800) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth

/-- **The frame of a candidate step** (`Cand0Spec`, `Cand1Spec`): registers outside the oracle
bands, outside `sw 1000 … sw 3199`, `sw 3230 … sw 3399` and `sw 4000 … sw 4999`, other than the
allocator, are kept; the allocator grows; memory below it is kept. -/
def CandFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ ztdpo → ¬ ztdpq →
    ¬ ztbwg → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth

/-- **The state of a query at the candidate step** (side `i`, query point `z`): the query
`(qE, qH, qD)` is a valid query of side `i` (in the model of `C₁` for `i = 0`, of `C₂` for
`i = 1`) with its height code naming its height, `(zE, qH)` is a position of `z` in the walk of
`C`, the direction is free for `C` at `z`, `(zP, zPh)` is the arrival position of `z` in the walk
of `C` (the ray in its left sector), and the bits `bL`, `bR` say whether `z` is not above the top
of `C₁`, `C₂`. -/
structure QState (P : Polygon) (J : Merge.Junction) (i : ℕ) (z : Point) (c : Config) : Prop where
  hq : QueryOK J zta i ztccw
  hht : ((chainModel ztgi).pos zta zthz).2 =
    ((Qof P).vtx ztbmn).2
  hz : (chainModel ztgi).pos zta zthz = z
  hzE : c.nreg zE < (chainModel J.whole).W.n
  hzpp : ProperPos ztbm zta P.n ztdqo
  hzM : (chainModel J.whole).pos zta ztdqo = z
  hfree : FreeAt J.whole z ztba
  hzP : c.nreg zP < (chainModel J.whole).W.n
  hzPp : ProperPos ztbm zta P.n ztlo
  harr : Arrival (chainModel J.whole).W z ztwtj ztdmx
    ztwmc
  hbL : c.nreg bL ≤ 1 ∧ (c.nreg bL = 1 ↔ z.2 ≤ J.left.top.2)
  hbR : c.nreg bR ≤ 1 ∧ (c.nreg bR = 1 ↔ z.2 ≤ J.right.top.2)

/-- **The output of a candidate step**: the accumulator (tags under the bits, `ModB`) holds
candidates of the ray from `z`, all of them hits of `C` or of the box at positive parameters,
among them the first hit of `C`. -/
def CandOut (P : Polygon) (J : Merge.Junction) (z : Point) (c c' : Config) : Prop :=
  ∃ L, AccOK P accA ztdm J.whole.radius z ztba L c' ∧
    ztbalv ∧
    J.whole.hitParam z ztba ∈ L

/-- The key of the log entry `i` (its offset is compared with the offset of a position). -/
noncomputable def logKey (J : Merge.Junction) (Q : Polygon) (N : NF)
    (ls : List ztck) (i : ℕ) : ℝ :=
  ((logOf J Q N ls).getD i ztfj).1 + ((logOf J Q N ls).getD i ztfj).2.1

/-- The label set of the log entry `i`. -/
noncomputable def logLab (J : Merge.Junction) (Q : Polygon) (N : NF)
    (ls : List ztck) (i : ℕ) : Set ztf :=
  ((logOf J Q N ls).getD i ztfj).2.2

/-- **`i` is the log entry of the key `x`**: the last log key whose offset is not after it. -/
def LogIdx (J : Merge.Junction) (Q : Polygon) (N : NF) (ls : List ztck)
    (x : ℝ) (i : ℕ) : Prop :=
  i < ls.length ∧ oW J ztpcq ≤ oW J x ∧
    (i + 1 < ls.length → oW J x < oW J (logKey J Q N ls ztg))

/-! ## Contract 1: the cases of a side-0 query (mathematics) -/

/-- **The cases of the first hit of a side-0 query** `z` (a point of `C₁` other than the shared
vertex, not above the top of `C₂`, with a free direction `σ` for `C`), from its arrival position
`(pz, tz)` in the walk of `C` (the ray in its left sector), the event log `ls`, the stop records
`rs` and the endpoint table `T` of stages 2/3.  The position is on the `C₁` part (offset at least
`Lst`), and for the log entry `i` of the position the first hit `J.whole.hitParam z σ` is

* (C1) the first hit of `C₁` (the local hit in the model of `C₁` finds it), or
* (C2) the first hit of `C₂`, and the ray starts in a region `V` of `S₂` with a label of the log
  entry `i` or `i - 1`, or a gap label (the shot at the arcs of `V` finds it), or
* (C3) the origin of a stop record at the position, the stop chord running along the ray back to
  `z`, or
* (C4) the origin of a regular endpoint query whose table entry is the position, in the direction
  opposite to the ray. -/
def Side0MathSpec : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs : List ztcf)
    (ls : List ztck) (T : ℕ → Option zthlt),
    GoodEnv P → J.P.Simple → IsNF ztj zta N₂ →
    LogOK J ztwis ztxxq →
    StopsOK J ztwis ztwoy →
    TabOK J zta N₂ T →
    ∀ (z : Point) (σ : ℝ), ztdd → z ∈ J.left.set → z ≠ J.shared →
      z.2 ≤ J.right.top.2 → FreeAt J.whole z σ →
      ∀ (pz : ℕ) (tz : ℝ), Arrival (chainModel J.whole).W z (-σ) pz tz →
      (Lst J : ℝ) ≤ oW J zthe ∧
      ∀ i, LogIdx J zta N₂ ls zthe i →
        -- (C1)
        J.left.hitParam z σ = J.whole.hitParam z σ ∨
        -- (C2)
        (J.right.hitParam z σ = J.whole.hitParam z σ ∧
          ∃ V ∈ (chainModel J.right).regions ztwis,
            (V ∈ logLab J zta N₂ ls i ∨ ztwxq ∨
              GapLab J ztwis V) ∧
            ∀ᶠ s in nhdsWithin (0 : ℝ) ztqcp, rayPt z σ s ∈ V) ∨
        -- (C3)
        (∃ r ∈ rs, r.1 = pz ∧ (chainModel J.whole).param zta ztbhg = tz ∧
          dirOf r.2.2.2.2 = -σ ∧
          stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 = rayPt z σ ztbyn) ∨
        -- (C4)
        (∃ j, j < 2 * N₂.nChords ∧ T j = some ztoes ∧ endDir j = -σ ∧
          endOrigin J zta N₂ j ∈ J.right.set ∧ endOrigin J zta N₂ j ≠ J.shared ∧
          endOrigin J zta N₂ j ≠ J.right.top ∧
          endOrigin J zta N₂ j = rayPt z σ ztbyn)

/-! ## Contract 2: endpoint queries at the top of `C₂` (mathematics) -/

/-- **At most two endpoint queries start at the top of `C₂`** (one per direction: two chords of a
normal form starting at one point in one direction are equal). -/
def TopCountSpec : Prop :=
  ∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF), GoodEnv P → J.P.Simple →
    IsNF ztj zta N₂ →
    ((List.range ztbxu).filter
      ztxqw).length ≤ 2

/-! ## Contract 3: the brute-force shot in the model of `C₁` (RAM) -/

/-- **The brute-force shot** at all arcs of `N₁`, in the model of `C₁` (model descriptor `sw 30`,
normal form `sw 3`), from the point `z` of the symbolic point in `sO` (not a point of `C₁`,
strictly inside the box, not above the top of `C₁`, so `bL = 1`), in the direction of code `qD`,
offering the hit (if any) to the accumulator `accA` with tag `0`.  Every new candidate is a point
of `C₁` or of the box on the ray at a positive parameter; the first hit of `C₁` is offered.  Cost
`κB (A₁ + 1) (F γ + 1)` (`A₁` the number of arcs of `N₁`). -/
def BruteSpec : Prop :=
  ∃ (bruteS : Stmt → Stmt) (κB : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (L : Set ℝ) (s : SymPt) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c →
      SymPtIn c sO s → s.Lt P.n → s.eval zta = z → z ∉ J.left.set →
      |z.1| < J.whole.radius → |z.2| < J.whole.radius → z.2 ≤ J.left.top.2 → c.nreg bL = 1 →
      AccOK P accA ztdm J.whole.radius z ztba L c →
      c.nreg ALLOC + κB * ztyz * ztwju ≤ W →
      IRS P W c₀ ztqek c ztbaps
        (fun c' =>
          (∃ L', AccOK P accA ztdm J.whole.radius z
              ztba L' c' ∧ L ⊆ L' ∧
            ztbakr ∧
            (FreeAt J.left z ztba →
              J.left.hitParam z ztba ∈ L')) ∧
          PartFr c c')

/-! ## Contract 4: the stop and table candidates of a side-0 query (RAM) -/

/-- **The initialisation contract** of a side-0 procedure: from a configuration satisfying `AEnv`,
`init` writes only `sw 620 … 659` among `sw 0 … 699` (besides fresh memory, scratch and the
oracle bands) and establishes `Aux`, within `κ (S + E + 2 K₂ + 1) (TLR + 1)` steps (`S` the
number of stop records, `E` of log records); `Aux` survives a write of `sw 11`. -/
def InitSpec (init : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ) :
    Prop :=
  (∀ (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (J : Merge.Junction)
    (H : Host) (N₁ N₂ : NF) (E : ℕ) (c : Config), WordsBounded W c →
    AEnv P W X Ok J H N₁ N₂ E c →
    c.nreg ALLOC + κ ztxgn * ztbbd *
      ztuc ≤ W →
    ∃ c' k, Exec P W init c c' k ∧
      k ≤ κ ztxgn * ztbbd *
        ztuc ∧
      Frame ztdwg c c' k ∧
      (∀ j, j < 700 → ztoca → c'.nreg ztgc = c.nreg ztgc) ∧
      Aux P J N₂ c') ∧
  (∀ (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c : Config) (v : ℕ), Aux P J N₂ c →
    Aux P J N₂ { c with nreg := upd c.nreg (sw 11) v })

/-- **The stop and table candidates of a side-0 query.**  An initialisation `initC` (`InitSpec`)
establishes a fact `Aux`, robust along `IInv` from the base of the answer phase; then, for a query
point `z` of `C₁` (not the shared vertex, not above the top of `C₂`, so `bR = 1`) with its arrival
position `(zP, zPh)` in the walk of `C` and direction code `qD`, the procedure `candC` offers to the
accumulator the origins of the stop records at the position whose direction is opposite to the
ray, and the origins of the regular endpoint queries whose table entry is the position, in the
direction opposite to the ray.  Every new candidate is a point of `C` or of the box on the ray at
a positive parameter.  Cost of a query `κ D (TLR + 1)`. -/
def S0CandSpec : Prop :=
  ∃ (initC candC : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ : ℕ → ℕ),
    InitSpec initC Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧
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
            -- the stop records at the position
            (∀ (rs : List ztcf), rs.length = rd c₀ bSweep 201 →
              StopRecsAt c₀.nmem ztdpi rs →
              ∀ r ∈ rs, r.1 = c.nreg zP →
                (chainModel J.whole).param zta ztbhg =
                  (chainModel J.whole).param zta ztlo →
                dirOf r.2.2.2.2 = -dirOf ztql →
                ∀ τ, 0 < τ → stopOrig J zta N₂ r.2.2.1 r.2.2.2.1 r.2.2.2.2 =
                  rayPt z ztba τ → τ ∈ L') ∧
            -- the table entries at the position
            (∀ j, j < 2 * N₂.nChords →
              tabOf J zta c₀.nmem ztdaf j =
                some ztxbi →
              endDir j = -dirOf ztql → endOrigin J zta N₂ j ∈ J.right.set →
              endOrigin J zta N₂ j ≠ J.shared → endOrigin J zta N₂ j ≠ J.right.top →
              ∀ τ, 0 < τ → endOrigin J zta N₂ j = rayPt z ztba τ →
                τ ∈ L')) ∧
          PartFr c c')

/-! ## Contract 5: the label candidates of a side-0 query (RAM) -/

/-- **The label candidates of a side-0 query.**  For a query point `z` of `C₁` (not the shared
vertex, not above the top of `C₂`, so `bR = 1`) with its arrival position `(zP, zPh)` in the walk
of `C`, its symbolic point in `sO` and direction code `qD`, the procedure finds the log entry `i`
of the position (binary search in the log, `LogIdx`) and shoots, in the model of `C₂`, from `z` at
the arcs of every region of `S₂` with a label of the log entries `i` and `i - 1` and of the gap
regions (`GapLab`), offering the hits to the accumulator with tag `1`.  Every new candidate is a
point of `C₂` or of the box on the ray at a positive parameter; for every such region in which
the ray starts, the first hit of `C₂` is offered.  Cost `κ D (F γ + TLR + 1)`. -/
def Lab0Spec : Prop :=
  ∃ (lab0 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
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

/-! ## Contracts 6, 7: the candidate steps of the two sides (RAM drivers) -/

/-- **The candidate step of side `0`** (queries in the model of `C₁`): an initialisation
`init0` (`InitSpec`, e.g. that of `S0CandSpec`) and the per-query procedure `cand0`, from a
cleared accumulator to `CandOut` (the first hit of `C` among good candidates).  Cost of a query
`κ D (F γ + TLR + 1)`.

Plan: classes of the query point `z` (with `bL = 1` always): a box wall (edges `1`, `3`): local
hits in the models of `C₁` and (if `bR = 1`) of `C₂`; the shared vertex: local hits in the model of
`C₁` and in the model of `C₂` at the arrival position of the shared vertex; a point of `C₁` above
the top of `C₂` (`bR = 0`): the local hit in the model of `C₁`; otherwise the local hit in the
model of `C₁`, `Lab0Spec` (symbolic point by `callSym` into `sO`) and `S0CandSpec`, complete by
`Side0MathSpec`. -/
def Cand0Spec : Prop :=
  ∃ (init0 : Stmt) (cand0 : Stmt → Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop)
    (κ : ℕ → ℕ),
    InitSpec init0 Aux κ ∧
    (∀ (P : Polygon) (W : ℕ) (J : Merge.Junction) (N₂ : NF) (c₀ c : Config),
      Aux P J N₂ c₀ → IInv W c₀ c → Aux P J N₂ c) ∧
    ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
      (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → Aux P J N₂ c₀ → IInv W c₀ c → QState P J 0 z c →
      c.nreg accA = 0 →
      c.nreg ALLOC + κ zto * ztwit ≤ W →
      IRS P W c₀ ztvky c ztbajz
        ztio

/-- **A brute-force query of side `1`**: a point query (index at least `2 K₂`) or an endpoint
query from the top of `C₂`. -/
def BruteQ (J : Merge.Junction) (N₂ : NF) (j : ℕ) (z : Point) : Prop :=
  2 * N₂.nChords ≤ j ∨ z = J.right.top
open Classical in
/-- **The candidate step of side `1`** (queries in the model of `C₂`; the query of index `qJ` below
`2 K₂` is the endpoint query `qJ` of `N₂`).  Cost of a query `κ D (F γ + TLR + 1)`, plus
`κ D (A₁ + 1) (F γ + 1)` for a brute-force query (`BruteQ`).

Plan: classes of the query point `z` (with `bR = 1` always): a box wall: local hits in the models
of `C₂` and (if `bL = 1`) of `C₁`; the shared vertex: local hits in the model of `C₂` and in the
model of `C₁` at the arrival position of the shared vertex; a regular endpoint query (index below
`2 K₂`, origin not the top of `C₂`): the local hit in the model of `C₂` and the table entry of the
query (`TabOK`: the far attachment, a position of the walk of `C`, tag `2`); a brute-force query:
the local hit in the model of `C₂` and (if `bL = 1`) `BruteSpec` (symbolic point by `callSym` into
`sO`). -/
def Cand1Spec : Prop :=
  ∃ (cand1 : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop), ShooterOK sh Bs F X Ok → Bs ⊆ oracleBands → X.CapLocal →
    ∀ (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction) (H : Host) (N₁ N₂ : NF)
      (E : ℕ) (z : Point),
      AEnv P W X Ok J H N₁ N₂ E c₀ → IInv W c₀ c → QState P J 1 z c →
      (c.nreg qJ < 2 * N₂.nChords →
        ztccw = (sweepEndQ N₂.chords).getD ztccx ztt) →
      c.nreg accA = 0 →
      c.nreg ALLOC + (κ zto * ztwit +
        (if BruteQ J N₂ ztccx z then
          κ zto * ztyz * ztwju else 0)) ≤ W →
      IRS P W c₀ ztvkz c
        (κ zto * ztwit +
          (if BruteQ J N₂ ztccx z then
            κ zto * ztyz * ztwju else 0))
        ztio
open Set Filter Topology
open Chazelle.Visibility (rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
variable (C : Chain)
/-- **Every positive walk key lies in the closed arc of an arc record** of a valid normal form of
a chain model. -/
theorem key_in_arc (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztc Q N) {p : ℕ} {t : ℝ} (hkey : 0 < (p : ℝ) + t) :
    ∃ j < N.arcs.length, ShotList.CIn ztjcg
      ztjcf ztk := by
  set M := chainModel C with hMd
  set F := N.F M Q with hFd
  zubqs

  zuhwt
  zuzj
  have ofArc : ∀ U ∈ M.regions F, ∀ a b, M.IsArc F U a b →
      ∃ j < N.arcs.length, M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
    intro U hU a b harc
    obtain ⟨r, hr, hrU⟩ := hRC.2.2 U hU
    rw [← hrU] at harc
    obtain ⟨j, hj, -, hs, he⟩ := hArcs.2.2.1 r hr a b harc
    grind
  zujtc
  · obtain ⟨c, hc, p', t', hAc, hk⟩ := hcut
    obtain ⟨U, -, -, r, hU, -, -, harc, -, -⟩ := hM.attach_face hFam.2.1 hFam.1 hc hAc
    obtain ⟨j, hj, hs, -⟩ := ofArc U hU _ _ harc
    refine ⟨j, hj, Or.inr ztenp⟩
    simp_all
  · obtain ⟨U, hU, l, r, harc, hin⟩ := exists_arc_around hGM hFam hkey hcut
    obtain ⟨j, hj, hs, he⟩ := ofArc U hU _ _ harc
    exact ⟨j, hj, Or.inl by_simp_all⟩

/-- **The exit point of a free ray** (at a height not above the top) is a walk point whose key
lies in the closed arc of an arc record. -/
theorem exit_in_arcs (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF ztc Q N) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hz : z.2 ≤ C.top.2) (hf : FreeAt C z σ) :
    ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (∃ j < N.arcs.length, ShotList.CIn ztjcg
        ztjcf ztk) ∧
      lerp ztbkd ztbke t = rayPt z σ ztbtm := by
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hz hσ hf
  zuckj
  zuhom
  -- the height is inside the box
  have hzR : ztmxi := by
    have := C.dom_subset_box ztxoe
    zugie
  -- the hit point is on the chain or on a vertical side of the box
  have he : ztdea := by
    zudjj
    · zulpb

      · zuum

        zueek
        zusv
        zuesq

        have h1 : |(rayPt z σ ztbpt).1| < C.radius := hbox.1
        have h2 : ztxpx := by
          zuega
          zui
          zuxs

        grind
      · zube

        tauto
    simp_all
  -- a walk position at the hit point
  zufua
  have hee : ztwym := by
    zuq
    have := congrArg Prod.fst h
    zudv
    grind
  have hopen : ztbajt := by
    zugg
    have e : ztbann := by
      zubvk
    zui
    zuhct
  obtain ⟨p, t, hp, ht, ht1, hpt, -⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee by_simp hopen he
  zukeu
  have hkey : ztmsh := by
    zuks

    have hp0 : ztidy := by
      zuhdi
      simp_all
    have ht0 : ztbhh := by
      grind
    zultd
    have h0 : ztdxs := by
      zudtj
    have := congrArg Prod.snd (hpt'.symm.trans h0)
    zufpr

  obtain ⟨j, hj, hin⟩ := key_in_arc C hP hN (Q := Q) hkey
  exact ⟨p, t, hp, ht, ht1.le, ⟨j, hj, hin⟩, hpt'⟩

/-! ## A point strictly inside the box -/

/-- A point strictly inside the box, not above the top and off the chain is in the domain. -/
theorem mem_dom_of (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) (h1 : |z.1| < C.radius)
    (h2 : |z.2| < C.radius) (hzC : z ∉ C.set) : z ∈ C.dom := by
  zumv
  rcases (Merge.not_mem_dom_iff C hz).1 h with h' | h'
  · tauto
  simp_all

/-- A point of the domain is not a walk point. -/
theorem walk_ne_of_dom (hP : C.P.Simple) {z : Point} (hz : z ∈ C.dom) {p : ℕ}
    (hp : p < (chainModel C).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lerp ztbkd ztbke t ≠ z := fun h =>
  (FactsChain.walkAx C hP).trace p hp t ht0 ht1
    (by rw [show sidePt (chainModel C).W p t = z from h]; exact hz)

/-- **A point strictly inside the box is an inner point** of the chain model. -/
theorem innerPt_box {z : Point} (h1 : |z.1| < C.radius) (h2 : |z.2| < C.radius) :
    (chainModel C).InnerPt z := by
  have hx := abs_lt.1 h1
  have hy := abs_lt.1 h2
  zuet
  zubbq

  refine ztbrc
  · simp_all
  · simp_all
  · grind
  grind

/-- **A walk position not above the top** is a point of the chain or of the box. -/
theorem walk_hit_onCB (Q : Polygon) {n : ℕ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos ztc Q n x)
    (hy : ((chainModel C).pos Q x).2 ≤ C.top.2) : OnCB C ztte := by
  refine walk_pos_good C Q he hp (fun h5 => ?_) (fun h6 => ?_)
  · exact absurd hy (not_le.2 (slit_above C Q hp ztmbw))
  · zuccr
    exact absurd hy (not_le.2 (slit_above C Q hp (Or.inr ⟨h6, lt_of_le_of_ne hp.1 ztval⟩)))

/-! ## Descriptors of the answer phase -/
section Env
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

/-- The host of the junction is regular. -/
theorem AEnv.hostReg (hA : AEnv P W X Ok J H N₁ N₂ E c₀) : HostRegular P.n H := by
  obtain ⟨-, -, -, -, hJ, hwf, -⟩ := hA.hst
  exact hwf.2.2.2 H hJ.2.2.1

/-- **The chain descriptor of `C₁`** at `sw 20`. -/
theorem AEnv.ctxL (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    ChainCtx P W c ztiw J.left := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -⟩ := hA.hst
  zuegs

  have h0 : ChainCtx P W c₀ ztiw J.left :=
    ⟨hA.hG, hA.hWh, w20, ⟨H, d20, hA.hostReg⟩, hA.hP, by change 2 * J.m₁ + 7 ≤ W; omega⟩
  zuhcs

/-- **The chain descriptor of `C₂`** at `sw 21`. -/
theorem AEnv.ctxR (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    ChainCtx P W c zted J.right := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -⟩ := hA.hst
  zuegs

  have h0 : ChainCtx P W c₀ zted J.right :=
    ⟨hA.hG, hA.hWh, w21, ⟨H, d21, hA.hostReg⟩, hA.hP, by change 2 * J.m₂ + 7 ≤ W; omega⟩
  zuhcs

/-- The facts about a copied model descriptor at a run configuration. -/
def MdFacts (P : Polygon) (c : Config) (B : ℕ) (H : Host) (C : Chain) : Prop :=
  c.nmem B = 0 ∧ ChainDescAt c.nmem ztvf zta H C ∧
    ModelDescWF P ztm c.nmem B ∧ ModelDescAt c.nmem B zta ztc

/-- A model descriptor copied from a chain descriptor, transported to a run configuration. -/
theorem mdFacts_of {B d : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hd : ChainDescAt c₀.nmem d zta H C) (hwf : ChainWF P ztdq c₀.nmem d)
    (hmd : ModelDescAt c₀.nmem B zta ztc)
    (hmw : ModelDescWF P ztdq c₀.nmem B)
    (hcp : ∀ j, j < 5 → c₀.nmem (B + 1 + j) = c₀.nmem ztfqu) : MdFacts P c B H C := by
  obtain ⟨h0, -⟩ := Restore.chainDesc_of hmd rfl
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hd
  have hC : ChainDescAt c₀.nmem ztvf zta H C :=
    MergeAsm.chainDescAt_copy hd hEb ztcj hcp
  obtain ⟨hmd', hmw', hC', h0'⟩ := MergeAsm.modelDesc_agree hmw h0 hC hI.hm
  exact ⟨h0', hC', hmw'.mono hI.hA, hmd'⟩

/-- **The model descriptor of `C₁`** at `sw 30`. -/
theorem AEnv.mdL (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    MdFacts P c ztxwc H J.left := by
  zuqp
  zubuy
  exact mdFacts_of hI d20 w20 d30 w30 hA.hmd₁

/-- **The model descriptor of `C₂`** at `sw 31`. -/
theorem AEnv.mdR (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) :
    MdFacts P c ztxgo H J.right := by
  zuqo
  zubuy
  exact mdFacts_of hI d21 w21 d31 w31 hA.hmd₂
