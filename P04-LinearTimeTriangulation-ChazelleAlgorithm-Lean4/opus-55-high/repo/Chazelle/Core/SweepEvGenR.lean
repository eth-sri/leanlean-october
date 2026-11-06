module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepEvPrep
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepIoLHit3
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Core.SweepEvWinM2
public import Chazelle.Core.SweepEvBatch

namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The inputs of the local hit -/

/-- The inputs of the local hit: the descriptors and the normal form of `C₁`, the arrival
position, the reverse direction, the walk length, the tag `0`, the empty accumulator. -/
def gSetL : List Instr :=
  [.copyN lMD MD₁, .copyN lCD CD₁, .copyN lNF ztea, .copyN lE ztle, .copyN lH zthq,
    .subN lD K1 oD, .copyN lN cN1, .constN lT 0, .constN accA 0]
variable (m f : ℕ → ℕ) {C : Chain}
theorem gSet_val :
    regB m gSetL f lMD = f MD₁ ∧ regB m gSetL f lCD = f CD₁ ∧ regB m gSetL f lNF = f ztea ∧
    regB m gSetL f lE = f ztle ∧ regB m gSetL f lH = f zthq ∧
    regB m gSetL f lD = f K1 - f oD ∧ regB m gSetL f lN = f cN1 ∧ regB m gSetL f lT = 0 ∧
    regB m gSetL f accA = 0 ∧
    (∀ q, ztoex → q ≠ accA → regB m gSetL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hq' => regB_other _ _ _ (fun i hi => by
    simp only [gSetL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI, lMD, lCD, lNF, lE, lH, lD, lN, lT, sw] <;>
      first | omega)⟩ <;>
  · rfl
theorem gSet_ok (hW : 0 ≤ W) : okB W m gSetL f := by
  simp only [gSetL, okB, okI]
  tauto

/-! ## A positive height code -/

/-- **The vertex fix**: the edge (`2m + 6 ↦ 6`, the other copy of the top), its symbolic point,
the height code `i + 1` (vertex `i`) or `h + 1` (a point of an edge at the height of vertex `h`). -/
def gFix : Stmt :=
  .seq ztyqc
    (.seq (.ifLtN ztfiv cN1 ztdkf ztdke)
      (.seq (callSym CD₁ ztwgm lH ztibh)
        (.ifLtN ztibh K1 ztyny
          ztynz)))

/-- **A positive height code**: normalise; at a vertex, fix the code. -/
def gHgt : Stmt := .seq (normS CD₁ lE lH ztwgl) (.ifLtN lH K1 gFix .skip)
set_option maxRecDepth 20000 in
theorem gFix_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c CD₁ C)
    (hn : c.nreg cN1 = 2 * C.m + 7) {e : ℕ} (hE : c.nreg lE = e) (hH : c.nreg lH = 0)
    (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) (hroom : c.nreg ALLOC + 31013 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ gFix c 31013 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos zta ztjy).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpe → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  zucid

  unfold gFix
  -- 1. `e + 1`
  refine IRS.seq (K₂ := 31012)
    ((IRS.block [.addN _ lE K1] hI ⟨⟨iscr_sw by_decide by_decide,
      by omega⟩, trivial⟩).mono le_rfl (fun _ h => h)) ?_
  zubun
  have q22 : ztzjf := by
    zuduc
  have q1 : ztjbj := fun r hr => by
    zuelv
  zugnu
  have qN : ztoqs := by zuooh; exact hn
  -- 2. the edge `e'`
  have hstep2 : IRS P W c₀ (.ifLtN ztfiv cN1 ztdkf
      ztdke) c₁ 3 (fun c' => ∃ e', c'.nreg (sw 723) = e' ∧ 6 ≤ e' ∧
        e' < 2 * C.m + 6 ∧ (chainModel C).pos zta ztugh = (chainModel C).pos zta ztjy ∧
        ztina ∧ c'.nmem = c₁.nmem) := by
    zugsk
    · refine (IRS.instr1 hI₁ (i := .copyN _ lE) (iscr_sw by_decide
        by_decide)).mono by_omega ?_
      zuu
      zugwz

      · zubiv
        zuhne
      · zuua
    · refine (IRS.instr1 hI₁ (i := .copyN _ K6) (iscr_sw by_decide
        by_decide)).mono by_omega ?_
      zuu
      zuxv

      · zubiv
        zuhnf
      · zukua
      · zuua
  zubln

  have hH₂ : zturq := by
    zuezd
  have hctx₂ : ChainCtx P W c₂ CD₁ C := hctx.transport
    (by rw [q2 _ by_decide, q1 _ by_decide])
    by_simp_all by_omega
  have hA₂e : ztbae := by
    zugwy
  -- 3. the symbolic point
  refine IRS.seq (K₂ := 3) (callSym_irs hI₂ hctx₂
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide⟩ ⟨by_decide, by_decide⟩
    by_omega by_omega
    ztyau
    by_simp_all by_omega) ?_
  zuft

  -- 4. the code
  have hfin : ∀ (j : ℕ), ztilj → c₃.nreg j = k →
      IRS P W c₀ ztnbb c₃ 1 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos zta ztjy).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpe → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    zumha
    refine (IRS.instr1 hI₃ (i := .addN lH j K1) ⟨iscr_sw by_decide
      by_decide, by_omega⟩).mono le_rfl ?_
    zuu
    refine ztegz
    · zubzz
    · zuwc
      rw [upd_other _ _ _ hr2, q3 r hr1 ztcco hr4,
        q2 _ ztcco, q1 _ ztcco]
    · zuwc
      zuhnp

    grind
  zuekc
  · grind
  grind
set_option maxRecDepth 20000 in
/-- **A positive height code** naming the height of the arrival position, with the same
parameter and point. -/
theorem gHgt_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c CD₁ C)
    (hn : c.nreg cN1 = 2 * C.m + 7) {x : WPos} (hE : c.nreg lE = x.edge)
    (hH : c.nreg lH = x.hgt) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n x) (hcl : PosClass C zta x)
    (hy : |((chainModel C).pos zta x).2| < C.radius)
    (hroom : c.nreg ALLOC + 42030 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ gHgt c 42030 (fun c' => ∃ k, c'.nreg lE = x.edge ∧ c'.nreg lH = k + 1 ∧ k < P.n ∧
      ((Qof P).vtx k).2 = ((chainModel C).pos zta x).2 ∧
      (chainModel C).param zta ztcjw = (chainModel C).param zta x ∧
      (chainModel C).pos zta ztcjw = (chainModel C).pos zta x ∧
      ProperPos ztc zta P.n ztcjw ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpd → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  zubo
  unfold gHgt
  zukhd
  -- 1. normalise
  refine IRS.seq (K₂ := 31015) (normS_irs hI hKc hctx
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    by_omega by_simp_all by_simp_all
    by_omega) ?_
  zufs

  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpd → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    q1 r h1 h2 ztbsm ztbsm h4
  zuekd
  · -- a vertex: fix the code
    zujxy
    have hpar0 : ztxir := by
      grind
    have hposv : ztxpl := by
      grind
    zucn
    have he6 : ztkzt := by
      zudsb
      · zuhcy

        simp only [show (chainModel C).param _ ztkng = 0 from rfl,
          Chazelle.Chain.sidePt_zero, hW] at hy
        zuevj
        · zuiga
        · zuigb
      · omega
      omega
    have hctx₁ := hctx.transport
      (keep1 CD₁ by_decide
        by_decide ztbuo by_decide)
      qm1 hA₁''
    have hn₁ : ztoqs := by
      rw [keep1 cN1 by_decide
        by_decide ztbuo
        by_decide]; exact hn
    refine (gFix_irs hI₁ hK hctx₁ hn₁ hE₁ by_omega he6.1 he6.2 by_omega hPW).mono
      le_rfl ?_
    zucby

    obtain ⟨vpar, vpos⟩ := vtx_fix (M := chainModel C) (Q := Qof P) (e := x.edge) (h' := k)
      by_grind
    refine ⟨k, ?_, hk1, hkl, hkh, by_grind, by_grind,
      ⟨by_grind, by_grind, by_grind⟩,
      fun r h1 h2 h3 h4 => ?_, by_omega, fun a ha => ?_⟩
    · rw [hk2 lE by_decide
        by_decide ztbcz by_decide]
      omega
    · zuguz

    grind
  · -- inside an edge: the code is positive
    zuddi

    have hparne : ztixd := fun h =>
      hpos0 ztvvu
    zudhs

    refine IRS.skip hI₁ ⟨k, hE₁, by_omega, by
      have := hpp₁.2.2; grind, hkh, by_grind,
      by grind, by_grind, keep1, hA₁'', qm1⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
def gCmp : Stmt :=
  .ifLtN oD K1 (callAbsCmp oAbsA zthdm cG) (callAbsCmp zthdm oAbsA cG)

/-- **The genuineness check.** -/
def mkG (sh : Stmt) : Stmt := .seq (block gSetL) (.seq gHgt (.seq ztkak gCmp))

/-- The cost of the check. -/
def genK (Fg D T : ℕ) : ℕ := 9 + (42030 + (localK T Fg ztef D + ztssv))

/-- The constant of the cost bound. -/
def κGen (D : ℕ) : ℕ := localK 0 0 ztef D + 16 * ztzbb + 50000
theorem localK_lin (T Fg Da Dc : ℕ) :
    localK T Fg Da Dc = localK 0 0 Da Dc + 5500 * T + ztpub * ztjem := by
  zulbx
theorem genK_le (Fg D T : ℕ) : genK Fg D T ≤ κGen D * ztbbs := by
  unfold genK κGen
  rw [localK_lin]
  grind
theorem dirOf_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  zubqi

/-! ## The contract -/
section exec
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- **The genuineness check meets its contract.** -/
theorem genOK_mkG (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) :
    GenOK P W c₀ J ztqtq (κGen zto * ztwit) := by
  intro c₁ a σ τ hI₁ hroom hD hσ habs haR hav ha₁ hτ he hpp harr
  zujmo
  set D := c₀.nreg _ with hDd
  zujmt
  have hgk : 9 + (42030 + (localK T Fg _ D + ztssv)) ≤ κGen D * ztbbs :=
    genK_le Fg D T
  have hσ' : ztim := by zungf; exact dirOf_pm _
  zudod
  -- the geometry of the hit
  zujzy
  have hay : ztsnt := by
    zumms
    zudxk
  set x : WPos := ztxzm with hxd
  set w := rayPt a σ τ with hwd
  have hw2 : w.2 = a.2 := rfl
  obtain ⟨hposx, hcl, hloc, hwD⟩ := arr_facts (N := P.n) (x := x) he hpp harr
    by_simp_all by_simp_all
  have haD := origin_mem_left_dom E.hP haR hav ha₁
  have hrev : dirOf ztldg = -σ := by
    rw [hσ, ← dirOf_rev hD, neg_neg]
  -- 1. the inputs of the local hit
  refine (IRS.seq (K₁ := 9)
    ((IRS.block gSetL hI₁ (gSet_ok _ _ ztbg)).mono by_rfl
      ztb) ?_).mono by_omega (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' hc₂
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, vo⟩ := gSet_val c₁.nmem c₁.nreg
  have g2 : ∀ q, ztoex → q ≠ accA → c₂.nreg q = c₁.nreg q := by_simp_all
  have m₂ : ztpna := by zumxp
  have r2 : ∀ r, ∀ v, regB c₁.nmem gSetL c₁.nreg r = v → c₂.nreg r = v := by_simp_all
  zubke
  have s2E : c₂.nreg lE = x.edge := by_simp_all
  have s2H : c₂.nreg lH = x.hgt := by_simp_all
  have s2D : c₂.nreg lD = 1 - c₁.nreg oD := by rw [r2 _ _ v6, hK₁.2.1]
  have s2N : c₂.nreg lN = 2 * J.left.m + 7 := by
    rw [r2 _ _ v7, (E.hM.fix hI₁).n1, WalkEmbed.cm_n]
  have s2T : zturr := by_simp_all
  have s2A : ztpnl := by_simp_all
  have s2MD : c₂.nreg lMD = c₁.nreg MD₁ := by_simp_all
  have s2CD : c₂.nreg lCD = c₁.nreg CD₁ := by_simp_all
  have s2NF : c₂.nreg lNF = c₁.nreg _ := r2 _ _ v3
  -- 2. a positive height code
  have hctx₂ := E.ctx1' hI₂
  have hn₂ : c₂.nreg cN1 = 2 * J.left.m + 7 := by
    rw [(E.hM.fix hI₂).n1, WalkEmbed.cm_n]
  refine IRS.seq
    (gHgt_irs hI₂ E.hK hctx₂ hn₂ s2E s2H he hpp hcl
      by_grind by_omega by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨k, s3E, s3H, hkl, hkh, hkpar, hkpos, hkpp, k3, hA₃'', m₃⟩
  zuioo
  have k3' := fun r h1 h2 h3 h4 =>
    k3 r ztbet h1 h4 ztu
  have s3D : c₃.nreg lD = 1 - c₁.nreg oD := by
    rw [k3' lD by_decide by_decide by_decide
      ztbcz]; omega
  have s3N : c₃.nreg lN = 2 * J.left.m + 7 := by
    rw [k3' lN by_decide by_decide by_decide
      ztbcz]; omega
  have s3T : c₃.nreg lT = 0 := by
    rw [k3' lT by_decide by_decide by_decide
      ztbcz]; omega
  have s3A : c₃.nreg accA = 0 := by
    rw [k3' accA by_decide by_decide
      by_decide ztbcz]; omega
  have s3MD : c₃.nreg lMD = c₃.nreg MD₁ := by
    rw [k3' lMD by_decide by_decide by_decide
      ztbcz, s2MD, hI₁.hin _ by_trivial,
      hI₃.hin _ by_trivial]
  have s3CD : c₃.nreg lCD = c₃.nreg CD₁ := by
    rw [k3' lCD by_decide by_decide by_decide
      ztbcz, s2CD, hI₁.hin _ by_trivial,
      hI₃.hin _ by_trivial]
  have s3NF : c₃.nreg lNF = c₀.nreg ztea := by
    rw [k3' lNF by_decide by_decide by_decide
      ztbcz, s2NF, hI₁.hin _ by_trivial]
  -- 3. the local hit
  have hTBR₃ : c₃.nreg TBR = c₀.nreg TBR := hI₃.hin _ by_trivial
  have hTLR₃ : ztshp := hI₃.hin _ by_trivial
  zuixa
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI₃
  have hL₃ : LCtx P W J.left N₁ _ c₃ :=
    { hG := E.hG
      hWh := E.hWh
      hctx := (E.ctx1' hI₃).transport s3CD by_omega le_rfl
      hcd := by_omega
      hmd := by_grind
      hmwf := by_grind
      hm0 := by_grind
      hP := E.hP
      hNW := by
        rw [s3NF]
        exact E.hNT₁.transport (fun b hb => hI₃.hm b by_omega)
      hE := by have := hI₃.hA; omega
      hNF := E.hNF₁
      htab := fun j hj => by
        rw [hTLR₃] at hj
        rw [hTBR₃, hI₃.hm _ by_omega]
        exact E.htab j hj
      hbig := by rw [hTLR₃]; exact E.hbig₁
      hTB := by_omega
      hTW := by rw [hTBR₃, hTLR₃]; have := hI₃.hA; omega }
  obtain ⟨hAr, hCh⟩ := region_bounds E.hP E.hNF₁ E.hdeg₁
  have hposxs : (chainModel J.left).pos _ xs = w := hkpos.trans hposx
  have hlocs : ztoke ∨
      (6 ≤ xs.edge ∧ (chainModel J.left).pos zta xs ∈ J.left.set) := by
    grind
  have hacc : AccOK P accA ztrpq J.left.radius
      ((chainModel J.left).pos zta xs) (dirOf ztldg) ∅ c₃ :=
    accOK_init accA _ _ _ _ s3A
  refine IRS.seq
    ((localHit_irs (x := xs)
      E.hsh E.hBs E.hXl hI₃ E.hK hL₃ E.hX E.hcap E.hOk₁ E.hsg₁ hAr hCh s3E s3H s3D he hkpp
      by_grind hlocs hacc by_omega rfl rfl s3N
      by_grind).mono
        by_grind ztb) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨L', hacc', -, hL', hgeo⟩, k4, hA₄'', m₄⟩
  -- the reverse hit
  have hgeo' : LHGeo P J.left xs ztldg := by
    refine ztkme
    rw [hposxs, hrev]
    show sideLeft (chainModel J.left).W x.edge _ _
    rw [hkpar]
    exact harr.2.2.2.2
  obtain ⟨hfree, hmem⟩ := hgeo hgeo'
  rw [hposxs, hrev] at hfree hmem hacc' hL'
  obtain ⟨hf1, hf0, hf⟩ := hacc'
  have hflag : c₄.nreg accA = 1 := by
    zuct
    have h0 : c₄.nreg accA = 0 := by_omega
    rw [hf0 h0] at hmem
    exact hmem
  obtain ⟨τm, hτm, hmin, -, -, -, -, habsH⟩ := hf hflag
  have hσ'' : ztjh := by rcases hσ' with h | h <;> zvmwc <;> norm_num
  have hτeq : τm = J.left.hitParam w _ :=
    lh_min hσ'' by_grind (fun t ht => by
      rcases hL' t ht with h | h
      · exact absurd h (Set.notMem_empty t)
      omega) hfree hmem hτm hmin
  rw [hτeq] at habsH
  obtain ⟨gp, gn⟩ := genuine_iff_abs hσ' haD hwD hτ ha₁ hfree
  -- the registers of `c₁` at `c₄`
  have keep : ∀ r, bandOf r ∉ oracleBands → ¬ GR r → r ≠ ALLOC → c₄.nreg r = c₁.nreg r := by
    zuete
    have hGR : ¬ (ztgz ∨ r = cG ∨ ztph) := h2
    rw [k4 r h1 (fun h => hGR (by unfold LHW at h; unfold cG; unfold sw at h ⊢; omega)) h3,
      k3 r h1 ztzez
        (by unfold sw at hGR ⊢; omega) h3,
      g2 r (by unfold sw at hGR; omega) ztzez]
  have hD4 :=
    keep oD ztmr
      (by unfold GR oD cG sw; omega) by_decide
  have kA : ∀ i, i < 4 → c₄.nreg _ = c₁.nreg (oAbsA + i) := fun i hi =>
    keep _ (not_oracle_sw ztozr ztozr)
      (by unfold GR oAbsA cG sw; omega) (by unfold oAbsA ALLOC sw; omega)
  have habs4 :=
    absRec_transport habs (kA 0 by_norm_num) (kA 1 by_norm_num) (kA 2 by_norm_num)
      (kA 3 by_norm_num)
  have hk1₄ := (E.hK.fix hI₄).2.1
  -- the frame
  have hfin : ∀ c', (∀ r, bandOf r ∉ oracleBands → r ≠ cG → r ≠ ALLOC → c'.nreg r = c₄.nreg r) →
      c₄.nreg ALLOC ≤ c'.nreg ALLOC → (∀ b, b < c₄.nreg ALLOC → c'.nmem b = c₄.nmem b) →
      EFr GR c₁ c' := fun c' h1 h2 h3 => by
    refine ⟨fun r hr1 hr2 hr3 => ?_, by_omega, fun b hb => ?_⟩
    · rw [h1 r hr1 (fun h => hr2 ztwkb) hr3]; exact keep r hr1 hr2 hr3
    · rw [h3 b by_omega, m₄ b by_omega, m₃ b by_omega, m₂]
  unfold gCmp
  zugsk
  · -- code `0`: `σ = -1`
    have hd0 : c₁.nreg oD = 0 := by_omega
    have hsn : ztgbb := by rw [hσ, hd0]; rfl
    refine (callAbsCmp_irs hI₄ E.hG hW3
      ⟨by_decide, by_decide, by_decide,
        by decide⟩ ⟨by_decide, by_decide⟩ habs4 habsH
      by_omega).mono le_rfl ?_
    zuewe

  · -- code `1`: `σ = 1`
    have hd1 : c₁.nreg oD = 1 := by_omega
    have hsp : ztgbc := by rw [hσ, hd1]; rfl
    refine (callAbsCmp_irs hI₄ E.hG hW3
      ⟨by_decide, by_decide, by_decide,
        by decide⟩ ⟨by_decide, by_decide⟩ habsH habs4
      by_omega).mono le_rfl ?_
    zuewe
end exec

/-- **Task A: the genuineness check.** -/
theorem genTask : GenTask :=
  ⟨mkG, κGen, fun _ _ _ _ _ _ _ _ _ _ _ E => genOK_mkG E⟩
theorem regArcsTask : RegArcsTask := fun _ _ _ _ hP hNF hdeg =>
  (region_bounds hP hNF hdeg).1
end
end SweepEv
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace SweepStop
open Sweep
variable {C : Chain}

/-- **The far end of the chord seen from `a`** in the direction `σ`. -/
noncomputable def farPt (C : Chain) (a : Point) (σ : ℝ) : Point := rayPt a σ (C.hitParam a σ)
theorem dirOf_cases' (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  zubqi
theorem neg_cases {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : -σ = 1 ∨ -σ = -1 := by
  grind

/-- The points of the ray up to the first hit lie on the chord. -/
theorem rayPt_mem_shoot (C : Chain) (a : Point) (σ : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ C.hitParam a σ) : rayPt a σ s ∈ Merge.shoot C a σ := by
  unfold Merge.shoot
  zuewp
  zugac
  · have hT : 0 < C.hitParam a σ := lt_of_lt_of_le hs0 hs
    refine ⟨s / C.hitParam a σ, div_nonneg hs0.le hT.le, (div_le_one hT).2 hs, ?_⟩
    zufqm
    · zunkt; grind
    simp
  · zumkq
    simp

/-- The chord seen from `a` is the segment of the ray points up to the first hit. -/
theorem mem_shoot_iff (C : Chain) (a : Point) {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    (hT : 0 ≤ C.hitParam a σ) {x : Point} :
    x ∈ Merge.shoot C a σ ↔ ∃ s, 0 ≤ s ∧ s ≤ C.hitParam a σ ∧ x = rayPt a σ s := by
  constructor
  · zuetb
    unfold Merge.shoot at hx
    zueuw
    refine ⟨u * C.hitParam a σ, mul_nonneg hu0 hT, by_nlinarith, ?_⟩
    zufqm
    · zuhpd
    simp
  · rintro ⟨s, hs0, hs, rfl⟩
    exact rayPt_mem_shoot C a σ hs0 hs

/-- **The points of the chord off the domain** are its two ends. -/
theorem shoot_off_dom (C : Chain) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {x : Point} (hx : x ∈ Merge.shoot C a σ)
    (hxD : x ∉ C.dom) : x = a ∨ x = farPt C a σ := by
  zueim
  obtain ⟨s, hs0, hs, rfl⟩ := (mem_shoot_iff C a hσ hT.le).1 hx
  zugac
  · rcases hs.lt_or_eq with hs | rfl
    · simp_all
    tauto
  simp

/-- **The sector of an attachment** contains the direction of the chord from the position's point. -/
theorem sideLeft_of_attach {W : Polygon} {e : Set Point} {p : ℕ} {t : ℝ}
    (hA : SideAttach W e p t) {δ : ℝ} (hδ : δ = 1 ∨ δ = -1) {ε : ℝ} (hε : 0 < ε)
    (hin : ∀ s, 0 < s → s < ε → rayPt ztia δ s ∈ e) :
    sideLeft W p t (rayPt ztia δ 1) := by
  obtain ⟨-, -, -, -, r, hr, hsec⟩ := hA
  set s := min ztzr ztfvo with hsdef
  have hs : ztxx := lt_min zteta (half_pos hε)
  have hsr : ztmwr := min_le_left _ _
  have hsε : s ≤ ε / 2 := min_le_right _ _
  have hd : dist (rayPt ztia δ s) ztia = s :=
    Sweep.dist_rayPt _ hδ hs.le
  have hne : rayPt ztia δ s ≠ sidePt W p t := by
    intro h; rw [h, dist_self] at hd; linarith
  have hsl := hsec _ (hin s hs by_linarith) hne by_grind
  exact (Sweep.sideLeft_rayPt_iff W p t δ one_pos hs).2 hsl
variable (hP : C.P.Simple)
include hP
variable {a : Point} {c c' : Set Point}
/-- **The arrival position of the origin** (direction `-σ`) is an attachment of the chord. -/
theorem attach_of_origin (ha : a.2 ≤ C.top.2) (haD : a ∉ C.dom) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : Arrival (chainModel C).W a (-σ) p t) : SideAttach (chainModel C).W ztlfi p t := by
  zuwq
  zubvb
  zuhev
  zubrm
  refine sideAttach_of_along C hP he hp ht0 ht1 hσ by_simp_all ?_
  zubil
  zunv
  exact rayPt_mem_shoot C a σ hs.1.le hs.2.le

/-- **The arrival position of the far end** (direction `σ`) is an attachment of the chord. -/
theorem attach_of_far (ha : a.2 ≤ C.top.2) (haD : a ∉ C.dom) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : Arrival (chainModel C).W zthwq σ p t) :
    SideAttach (chainModel C).W ztlfi p t := by
  zuwq
  zuhev
  zubrm
  refine sideAttach_of_along C hP he hp ht0 ht1 ztvzt by_simp_all ?_
  zubil
  zunv
  zulbs

  exact rayPt_mem_shoot C a σ by_grind by_grind

/-- **Every attachment of the chord** is the arrival position of its origin or of its far end. -/
theorem attach_cases (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel C).W ztlfi p t) :
    (sidePt (chainModel C).W p t = a ∧ Arrival (chainModel C).W a (-σ) p t) ∨
      (sidePt (chainModel C).W p t = farPt C a σ ∧
        Arrival (chainModel C).W zthwq σ p t) := by
  zubkf
  zubrm
  have hxD : sidePt (chainModel C).W p t ∉ C.dom := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  rcases shoot_off_dom C ha hσ hf hA.2.2.2.1 hxD with h | h
  · refine Or.inl ztklf
    zuduy
    have := sideLeft_of_attach hA hσ hT (fun s hs0 hs => by
      zvmwc; exact rayPt_mem_shoot C a σ hs0.le hs.le)
    simp_all
  · refine Or.inr ztklf
    have := sideLeft_of_attach hA ztvzt hT (fun s hs0 hs => by
      zvmwc; unfold farPt; rw [Sweep.rayPt_back]
      exact rayPt_mem_shoot C a σ by_linarith by_linarith)
    simp_all
omit hP in
/-- The ends of the chord seen in the direction `1`. -/
theorem ends_shoot_pos (C : Chain) {a : Point} (hT : 0 ≤ C.hitParam a 1) :
    Merge.lend ztrjy = a ∧ Merge.rend ztrjy = farPt C a 1 := by
  unfold Merge.shoot farPt
  rw [Merge.segment_rayPt_pos a hT, Merge.lend_hseg by_linarith, Merge.rend_hseg by_linarith]
  exact ⟨rfl, by apply Geometry.point_ext <;> zvmxf⟩
omit hP in
/-- The ends of the chord seen in the direction `-1`. -/
theorem ends_shoot_neg (C : Chain) {a : Point} (hT : 0 ≤ C.hitParam a (-1)) :
    Merge.lend ztnmz = farPt C a (-1) ∧ Merge.rend ztnmz = a := by
  unfold Merge.shoot farPt
  rw [Merge.segment_rayPt_neg a hT, Merge.lend_hseg by_linarith, Merge.rend_hseg by_linarith]
  refine ⟨by apply Geometry.point_ext <;> zunob, rfl⟩
omit hP in
/-- **Two augmented chords with the same left end are equal.** -/
theorem aug_eq_of_lend (hc : c ∈ Merge.augChords C)
    (hc' : c' ∈ Merge.augChords C) (h : Merge.lend c = Merge.lend c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, hl, -⟩ := Merge.augChords_spec hc
  obtain ⟨y', a', b', hH', -, rfl, hl', -⟩ := Merge.augChords_spec hc'
  rw [hl, hl'] at h
  zuhia
  rcases lt_trichotomy b b' with hb | rfl | hb
  · exact absurd (hH'.open_mem b hH.lt hb) hH.right_not
  · rfl
  · exact absurd (hH.open_mem b' hH'.lt hb) hH'.right_not
omit hP in
/-- **Two augmented chords with the same right end are equal.** -/
theorem aug_eq_of_rend (hc : c ∈ Merge.augChords C)
    (hc' : c' ∈ Merge.augChords C) (h : Merge.rend c = Merge.rend c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, -, hr⟩ := Merge.augChords_spec hc
  obtain ⟨y', a', b', hH', -, rfl, -, hr'⟩ := Merge.augChords_spec hc'
  rw [hr, hr'] at h
  zuhia
  rcases lt_trichotomy a a' with ha | rfl | ha
  · exact absurd (hH.open_mem a' ha hH'.lt) hH'.left_not
  · rfl
  · exact absurd (hH'.open_mem a ha hH.lt) hH.left_not
omit hP in
/-- The ends of an augmented chord are distinct. -/
theorem lend_ne_rend {c : Set Point} (hc : c ∈ Merge.augChords C) : Merge.lend c ≠ Merge.rend c := by
  obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec hc
  zukuv
  zuq
  have := congrArg Prod.fst h
  zugzu
  linarith [hH.lt]
end SweepStop
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace SweepStop
open Sweep SweepIo
variable {J : Merge.Junction}

/-- **The origin of a stop record.** -/
noncomputable def stOrig (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) : Point :=
  if kind = 0 then J.shared
  else if kind = 1 then endOrigin J Q N ztxul
  else J.right.top
theorem stopSet_eq (J : Merge.Junction) (Q : Polygon) (N : NF) (kind k b : ℕ) :
    stopSet J Q N kind k b = Merge.shoot J.whole (stOrig J Q N kind k b) ztkz := by
  unfold stopSet stOrig
  grind
theorem dirOf_one : dirOf 1 = 1 := by_rfl
theorem dirOf_zero : dirOf 0 = -1 := by_rfl

/-- The end index of a wall record. -/
theorem wall_j {k b : ℕ} (hb : b ≤ 1) :
    2 * k + ztcno = 2 * k + ztlp := by
  rw [show ztcno = 1 - b by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> norm_num [dirOf]]

/-- **The admissible codes** of a stop record. -/
def StOK (_P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : Prop :=
  kind ≤ 2 ∧ b ≤ 1 ∧ (kind = 1 → k < N.nChords ∧ (endPos N k ztlp).edge < 6) ∧
    (kind = 2 → J.right.topIdx ≠ 0)
variable {M : Model} {Q : Polygon} {a : Point}
/-- The chord records of a normal form are chords of its family. -/
theorem chord_mem {N : NF} {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).toSet M Q ∈ N.F M Q := by
  zuno

/-- A position on a vertical side of the box has the abscissa `±R`. -/
theorem wall_abs (C : Chain) (Q : Polygon) {x : WPos} (h : x.edge = 1 ∨ x.edge = 3) :
    |((chainModel C).pos Q x).1| = C.radius := by
  show |(sidePt (chainModel C).W x.edge _).1| = _
  zucsg
  zugue
  zuy
  · rw [h, b1]; simp only; rw [abs_neg, abs_of_pos C.radius_pos]
  · rw [h, b3]; simp only; rw [abs_of_pos C.radius_pos]

/-- A point with abscissa `±R` is off the chain. -/
theorem not_mem_set_of_abs (C : Chain) {z : Point} (h : |z.1| = C.radius) : z ∉ C.set := by
  zujbb
  have := (C.abs_le_coordBound_of_mem_set hm).1
  have := C.coordBound_lt_radius
  linarith

/-- **The end of a chord record off `C₂`**: its walk edge is below `6` (a vertical side of the
box), and conversely; the end is a position of the class of `convS`. -/
theorem end_off_iff (_hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF ztj zta N) {k s : ℕ} (hk : k < N.nChords) :
    PosClass J.right zta ztcdc ∧
    ((chainModel J.right).pos zta ztcdc ∉ J.right.set ↔ (endPos N k s).edge < 6) := by
  zuiwy
  have hc : (N.chord k).toSet _ _ ∈ N.F ztj zta :=
    chord_mem hk
  zuftf
  have hatt : SideAttach (chainModel J.right).W ztwyr
      (endPos N k s).edge ((chainModel J.right).param zta ztcdc) := by
    zuhan
    · exact hA.1
    · exact hA.2
  obtain ⟨y, l, r, hH, hy, heq, -, -⟩ := Merge.augChords_spec ztgkd
  have hpt : (chainModel J.right).pos _ _ ∈
      (N.chord k).toSet _ _ := hatt.2.2.2.1
  zufnm

  have hboxy : ztsnw := by
    zuerl

  have hcl := posClass_of hatt.1 hatt.2.1 hatt.2.2.1 by_simp_all
    by_simp_all
  refine ⟨hcl, ⟨fun hn => ?_, fun h6 => ?_⟩⟩
  · rcases hcl with (h | h) | ⟨h6, hlt⟩ | ⟨h6, hz⟩
    · omega
    · omega
    · zumaf
      have hm := J.right.sideWalk_tour_pt_mem J.right.sideBeta (i := (endPos N k s).edge - 6) by_omega
        by_grind hatt.2.1 hatt.2.2.1
      rwa [show (endPos N k s).edge - 6 + 6 = (endPos N k s).edge by omega] at hm
    · zumaf
      have hm := J.right.sideWalk_tour_pt_mem J.right.sideBeta
        le_rfl by_simp_all le_rfl one_pos
      show sidePt (chainModel J.right).W _ _ ∈ _
      zuihe
      exact hm
  · rcases hcl with (h | h) | ⟨h6', -⟩ | ⟨h6', -⟩
    · exact not_mem_set_of_abs J.right (wall_abs J.right _ zteg)
    · exact not_mem_set_of_abs J.right (wall_abs J.right _ ztbho)
    · omega
    · omega

/-! ## The origins -/

/-- The radius of the box of `C₂` is that of `C`. -/
theorem radius_right : J.right.radius = J.whole.radius := rfl

/-- The origin of a wall record is the end `1 - b` of the chord `k`. -/
theorem stOrig_wall {N : NF} (hN : IsNF ztj Q N) {k b : ℕ}
    (hk : k < N.nChords) (hb : b ≤ 1) :
    stOrig J Q N 1 k b = (chainModel J.right).pos Q ztxoa ∧
      ((b = 1 ∧ stOrig J Q N 1 k b = Merge.lend ztwyq) ∨
        (b = 0 ∧ stOrig J Q N 1 k b = Merge.rend ztwyq)) := by
  have hj : 2 * k + ztlp < 2 * N.nChords := by_omega
  zufyb
  have e1 : ztxum / 2 = k := by_omega
  have e2 : ztxum % 2 = 1 - b := by_omega
  zvmws at hEO
  have hs : stOrig J Q N 1 k b = endOrigin J Q N ztxum := by
    unfold stOrig; rw [ite_eq_right by_norm_num, ite_eq_left rfl, wall_j hb]
  refine ⟨hs.trans hEO, ?_⟩
  zubqb
  zulbr
  grind

/-- **The facts of an origin**: off the domain of `C`, not above the top of `C₂`, strictly inside
the height band of the box, a point of `C` (shared vertex, top) or of a vertical side of the box
(wall ends). -/
theorem stOrig_facts (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF ztj zta N) {kind k b : ℕ} (hok : StOK P J N kind k b) :
    stOrig J zta N kind k b ∉ J.whole.dom ∧
      (stOrig J zta N kind k b).2 ≤ J.right.top.2 ∧
      |(stOrig J (Qof P) N kind k b).2| < J.whole.radius ∧
      (kind ≠ 1 → stOrig J zta N kind k b ∈ J.right.set) ∧
      (kind = 1 → |(stOrig J zta N kind k b).1| = J.whole.radius) := by
  zufju
  have hset : ∀ z ∈ J.right.set, z ∉ J.whole.dom ∧ z.2 ≤ J.right.top.2 ∧
      |z.2| < J.whole.radius := fun z hz =>
    ⟨fun hd => J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset hz),
      J.right.snd_le_top_of_mem_set hz, by
        rw [← radius_right]
        exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set hz).2
          J.right.coordBound_lt_radius⟩
  zubsx
  · zucuj
    zuhhs
    obtain ⟨hcl, hiff⟩ := end_off_iff hP hN hkN
    obtain ⟨hpos, -⟩ := stOrig_wall hN hkN hb
    zudul
    have hwall : (endPos N k ztlp).edge = 1 ∨ (endPos N k ztlp).edge = 3 := by
      rcases hcl with h | ⟨h, -⟩ | ⟨h, -⟩
      · zubh
      · omega
      · omega
    have hx := wall_abs J.right zta hwall
    -- the end lies on the chord: its height
    zudhm
    have hA := hN.2.2.1 k hkN
    have hatt : SideAttach (chainModel J.right).W ztwyr
        (endPos N k ztlp).edge ((chainModel J.right).param zta ztxoa) := by
      zuhan
      · exact hA.1
      · exact hA.2
    obtain ⟨y, l, r, hH, hy, heq, -, -⟩ := Merge.augChords_spec ztvtm
    have hpt : (chainModel J.right).pos _ _ ∈
        (N.chord k).toSet _ _ := hatt.2.2.2.1
    zufnm

    have hboxy : ztsnw := by
      zuerl

    refine ⟨fun hd => ?_, by_simp_all, by rw [hyy, ← radius_right]; omega,
      by omega, fun _ => by_tauto⟩
    have hb' := (J.whole.dom_subset_box hd).1
    rw [← radius_right, hx] at hb'
    simp_all
  · have hmem : stOrig J zta N kind k b ∈ J.right.set := by
      unfold stOrig
      split_ifs
      · exact J.shared_mem_right
      · exact J.right.top_mem_set
    grind

/-- **The chord of an admissible code with a free direction** is a stop chord of `F₂⁺`. -/
theorem stop_mem (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF ztj zta N) {kind k b : ℕ} (hok : StOK P J N kind k b)
    (hf : FreeAt J.whole ztwjf ztkz) :
    stopSet J zta N kind k b ∈ F₂plus J ztwrl ∧
      StopChord2 J ztwrl ztwjv := by
  zuezm
  zufju
  zudia
  zufqu
  · zubvi
    have hv : stOrig J zta N 0 k b = J.whole.vertex J.m₁ := by
      rfl
    zvmyq at hf ⊢
    refine ⟨Or.inl (Or.inr ⟨dirOf b, hσ, (Merge.freeAt_vertex _ _ _).1 hf, rfl⟩),
      Or.inl (Or.inl ⟨dirOf b, hσ, hf, rfl⟩)⟩
  zubsx
  · zucuj
    zuhhs
    obtain ⟨-, hiff⟩ := end_off_iff hP hN hkN (s := 1 - b)
    obtain ⟨hpos, hcase⟩ := stOrig_wall hN hkN hb
    zudhm
    have hoff : stOrig J zta N 1 k b ∉ J.right.set := by_simp_all
    have ha : (dirOf b = 1 ∧ stOrig J zta N 1 k b =
          Merge.lend ztwyr) ∨
        (dirOf b = -1 ∧ stOrig J zta N 1 k b =
          Merge.rend ztwyr) := by
      zueju
      · exact Or.inl ⟨dirOf_one, h⟩
      · exact Or.inr ⟨dirOf_zero, h⟩
    exact ⟨shoot_end_mem hc ha hf, Or.inl ztbmd⟩
  · have h2 : kind = 2 := by_omega
    zuhqi
    have hv : stOrig J zta N 2 k b = J.whole.vertex ztrw := by
      unfold stOrig; rw [ite_eq_right by_norm_num, ite_eq_right by_norm_num, Merge.Junction.whole_vertex_add]
      rfl
    have hf' := hf
    zvmyq at hf'
    refine ⟨Or.inr ⟨dirOf b, hσ, (Merge.freeAt_vertex _ _ _).1 hf', by zvmyq; rfl⟩,
      Or.inr ⟨dirOf b, hσ, ?_, ?_⟩⟩
    · tauto
    rfl

/-- A code `b ≤ 1` for a direction. -/
theorem code_of_dir {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ b, b ≤ 1 ∧ dirOf b = σ := by
  zur
  · tauto
  · exact ⟨0, zero_le_one, dirOf_zero⟩

/-- A chord of a normal form is a chord record. -/
theorem chord_of_mem {N : NF} {c : Set Point} (hc : c ∈ N.F M Q) :
    ∃ k, k < N.nChords ∧ c = (N.chord k).toSet M Q := by
  zugqq
  zubhj
  zulow
  zudly
  simp_all

/-- **Every stop chord is the chord of an admissible code** with a free direction. -/
theorem stop_complete (hP : J.P.Simple) {P : Polygon} {N : NF}
    (hN : IsNF ztj zta N) {e : Set Point}
    (hs : StopChord2 J ztwrl e) :
    ∃ kind k b, StOK P J N kind k b ∧ FreeAt J.whole ztwjf ztkz ∧
      e = stopSet J zta N kind k b := by
  rcases hs with (⟨σ, hσ, hf, rfl⟩ | ⟨c, hc, a, σ, ha, hoff, hf, rfl⟩) | ⟨σ, hσ, hf, rfl⟩
  · zucnn
    refine ztxzh
    · tauto
    rfl
  · obtain ⟨k, hk, rfl⟩ := chord_of_mem hc
    zune
    zucnn
    obtain ⟨hpos, hcase⟩ := stOrig_wall hN hk hb
    have hab : stOrig J zta N 1 k b = a := by
      rcases hcase with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp_all
      · rw [dirOf_one] at h1; grind
      · rw [dirOf_zero] at h1; grind
      simp_all
    obtain ⟨-, hiff⟩ := end_off_iff hP hN hk
    refine ⟨1, k, b, ⟨by_norm_num, hb, fun _ => ⟨hk, hiff.1 by_simp_all⟩,
      by omega⟩, by_simp_all, ?_⟩
    rw [stopSet_eq, hab]
  · zucnn
    by_cases ht : J.right.topIdx = 0
    · have hv : J.right.top = J.shared := by
        show J.right.vertex J.right.topIdx = _
        rw [ht, ← Merge.Junction.whole_vertex_add, Nat.add_zero]; rfl
      refine ztxzh
      · unfold stOrig; simp_all
      · rw [stopSet_eq]; tauto
    · refine ⟨2, 0, b, ⟨le_rfl, hb, by_omega, by_omega⟩, ?_, ?_⟩
      · tauto
      rfl

/-! ## The first hit of `C` -/

/-- **Freeness for `C`** gives freeness for `C₁` (not above its top). -/
theorem free_left {σ : ℝ} (hf : FreeAt J.whole a σ) (ha : a.2 ≤ J.left.top.2) :
    FreeAt J.left a σ := by
  zuiuc
  exact J.mem_left_dom_of_whole by_simp_all ht

/-- **Freeness for `C`** gives freeness for `C₂` (not above its top). -/
theorem free_right {σ : ℝ} (hf : FreeAt J.whole a σ) (ha : a.2 ≤ J.right.top.2) :
    FreeAt J.right a σ := by
  zuiuc
  exact J.mem_right_dom_of_whole by_simp_all ht

/-- **The first hit of `C`** is that of `C₂`, or (not above the top of `C₁`) that of `C₁`. -/
theorem hit_cases (ha : a.2 ≤ J.right.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam a σ = J.right.hitParam a σ ∨
      (a.2 ≤ J.left.top.2 ∧ J.whole.hitParam a σ = J.left.hitParam a σ) := by
  rw [whole_hitParam_eq_min J (le_trans ha J.right_top_le) hσ, right_hitParam_eq J ha]
  zufrp
  · zuoog
    grind
  · zujcf
    left
    rw [rayHit_eq_empty_of_above J.left h₁, ← right_hitParam_eq J ha]
    apply min_eq_right
    exact csInf_le_csInf (Merge.rayHitSet_bddBelow _ _ _ _) ztqag
      (fun t ht => ⟨ht.1, by rcases ht.2 with h | h; exact Or.inl h; simp_all⟩)

/-- **The least candidate is the first hit**: candidates are positive parameters of points off
the domain of `C`, and the first hit is a candidate. -/
theorem hit_min {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : a.2 ≤ J.whole.top.2)
    (hf : FreeAt J.whole a σ) {L : Set ℝ} (hL : ∀ τ ∈ L, 0 < τ ∧ rayPt a σ τ ∉ J.whole.dom)
    (hmem : J.whole.hitParam a σ ∈ L) {τm : ℝ} (hτm : τm ∈ L) (hmin : ∀ τ' ∈ L, τm ≤ τ') :
    τm = J.whole.hitParam a σ := by
  obtain ⟨-, -, hin⟩ := Merge.hit_of_freeAt J.whole ha hσ hf
  grind
end SweepStop
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace SweepStop
open Sweep SweepEv

/-! ## Lexicographic keys -/

/-- The lexicographic order of keys `(offset, code)`. -/
def KLe (a b : ℝ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- The strict lexicographic order. -/
def KLt (a b : ℝ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)
theorem KLe.trans {a b c : ℝ × ℕ} (h1 : KLe a b) (h2 : KLe b c) : KLe a c := by
  unfold KLe at *
  grind
theorem KLe.total (a b : ℝ × ℕ) : KLe a b ∨ KLe b a := by
  unfold KLe
  grind
variable {a b : ℝ × ℕ}
theorem KLt.of_le_ne (h : KLe a b) (hne : a ≠ b) : KLt a b := by
  zulv
  · tauto
  · refine Or.inr by_grind
theorem KLt.ne (h : KLt a b) : a ≠ b := by
  zunq
  rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h
theorem KLt.le (h : KLt a b) : KLe a b := by
  zulv
  · tauto
  · zufsb
theorem KLt.fst_le (h : KLt a b) : a.1 ≤ b.1 := by
  rcases h with h | ⟨h1, -⟩
  · grind
  simp_all

/-! ## The dedupe pass -/
variable {α : Type*} (key : α → ℝ × ℕ)

/-- **The invariant of the dedupe pass** over the sorted list `L` after `i` items: the kept list
`O` consists of items of `L`, has strictly increasing keys, covers the keys of the first `i`
items, and (for `i > 0`) its last key is that of item `i - 1`. -/
structure DInv (L : List α) (i : ℕ) (O : List α) : Prop where
  sub : ∀ y ∈ O, y ∈ L
  inc : O.Pairwise (fun x y => KLt ztbhv ztbnb)
  cov : ∀ j, j < i → ∀ x, L[j]? = some x → ∃ y ∈ O, key y = key x
  last : ∀ x, 0 < i → L[i - 1]? = some x → ∃ y, O.getLast? = some y ∧ key y = key x
  nil : i = 0 → O = []
variable {key}
theorem DInv.start (L : List α) : DInv key L 0 [] :=
  ⟨by_simp_all, List.Pairwise.nil, by_omega,
    by omega, by_simp_all⟩

/-- **A step of the dedupe pass**: item `i` is kept iff it is the first or its key differs from
that of item `i - 1`. -/
theorem DInv.step {L : List α} (hs : L.Pairwise (fun x y => KLe ztbhv ztbnb)) {i : ℕ}
    {O : List α} (h : DInv key L i O) {x : α} (hx : L[i]? = some x) :
    ((i = 0 ∨ ∀ x', L[i - 1]? = some x' → key x' ≠ key x) → DInv key L ztg (O ++ [x])) ∧
      ((0 < i ∧ ∀ x', L[i - 1]? = some x' → key x' = key x) → DInv key L ztg O) := by
  have hi : ztsjb := by
    grind
  have hxL := List.mem_of_getElem? hx
  constructor
  · intro hcase
    -- the last kept key is below the key of `x`
    have hlast : ∀ y ∈ O, KLt ztbnb ztbhv := by
      zusy
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h.nil h0] at hy; cases hy
      · obtain ⟨x', hx'⟩ : ztjbw :=
          ⟨L[i - 1], List.getElem?_eq_getElem by_omega⟩
        obtain ⟨yl, hyl, hkl⟩ := h.last x' hpos hx'
        have hne : key x' ≠ key x := by
          grind
        -- `key x' ≤ key x` by sortedness
        have hle : KLe (key x') ztbhv := by
          have := List.pairwise_iff_getElem.1 hs ztei i by_omega hi by_omega
          grind
        have hlt : KLt _ _ := KLt.of_le_ne hle hne
        -- every kept key is at most the last one
        rcases List.getLast?_eq_some_iff.1 hyl with ⟨O', rfl⟩
        zujcm
        · have := List.pairwise_append.1 h.inc
          have h2 := this.2.2 y hy yl by_simp
          rw [hkl] at h2
          rcases h2 with h2 | ⟨h2, h2'⟩ <;> rcases hlt with h3 | ⟨h3, h3'⟩
          · exact Or.inl (h2.trans h3)
          · zudxj
          · zudxj
          · zufsb
        simp_all
    refine ⟨fun y hy => ?_, ?_, fun j hj x'' hx'' => ?_, fun x'' _ hx'' => ?_, by_simp_all⟩
    · zujcm
      · exact h.sub y hy
      simp_all
    · zumlm
      exact ⟨h.inc, by_simp_all, by_simp_all⟩
    · zuknc
      · obtain ⟨y, hy, hk⟩ := h.cov j hj x'' hx''
        grind
      simp_all
    simp_all
  · rintro ⟨hpos, heq⟩
    obtain ⟨x', hx'⟩ : ztjbw :=
      ⟨L[i - 1], List.getElem?_eq_getElem by_omega⟩
    refine ⟨h.sub, h.inc, fun j hj x'' hx'' => ?_, fun x'' _ hx'' => ?_, by_simp_all⟩
    · zuknc
      · exact h.cov j hj x'' hx''
      · zuhmb
        obtain ⟨y, hy, hk⟩ := h.cov _ by_omega x' hx'
        grind
    · simp only [Nat.add_sub_cancel] at hx''
      zuhmb
      obtain ⟨y, hy, hk⟩ := h.last x' hpos hx'
      simp_all

/-! ## Raw stop records -/
section Raw
variable (P : Polygon) (J : Merge.Junction) (N : NF)

/-- The key of a raw record `(e, h, kind, k, b)` with leaving direction code `d`. -/
noncomputable def rKey (r : ℕ × ℕ × ℕ × ℕ × ℕ) (d : ℕ) : ℝ × ℕ := (offK P J r.1 r.2.1, d)

/-- The parameter of the position of a record. -/
noncomputable abbrev rPar (r : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (chainModel J.whole).param zta ztbhg

/-- The chord of a record. -/
noncomputable abbrev rSet (r : ℕ × ℕ × ℕ × ℕ × ℕ) : Set Point :=
  stopSet J zta N r.2.2.1 r.2.2.2.1 r.2.2.2.2

/-- **A valid raw record**: admissible codes with a free direction, the chord attached at the
position on the `C₁` part, which is its left end (`d = 1`) or its right end (`d = 0`). -/
def RawOK (r : ℕ × ℕ × ℕ × ℕ × ℕ) (d : ℕ) : Prop :=
  StOK P J N r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧
    FreeAt J.whole (stOrig J zta N r.2.2.1 r.2.2.2.1 r.2.2.2.2) ztqmb ∧
    SideAttach (chainModel J.whole).W ztkdu r.1 zthzk ∧
    (Lst J : ℝ) ≤ oW J (r.1 + rPar P J r) ∧ d ≤ 1 ∧
    sidePt (chainModel J.whole).W r.1 zthzk =
      (if d = 1 then Merge.lend ztkdu else Merge.rend ztkdu)
end Raw
theorem offK_eq (P : Polygon) (J : Merge.Junction) (e h : ℕ) :
    offK P J e h = oW J ztyeo := rfl
variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- Two valid raw records with the same key have the same position and chord. -/
theorem raw_eq_of_key (hP : J.P.Simple) (hN : IsNF ztj zta N)
    {r r' : ℕ × ℕ × ℕ × ℕ × ℕ} {d d' : ℕ} (h : RawOK P J N r d) (h' : RawOK P J N r' d')
    (hk : rKey P J r d = rKey P J r' d') :
    r.1 = r'.1 ∧ rPar P J r = rPar P J r' ∧ rSet P J N r = rSet P J N r' := by
  zuiwy
  obtain ⟨hok, hf, hA, -, hd, hend⟩ := h
  obtain ⟨hok', hf', hA', -, hd', hend'⟩ := h'
  unfold rKey at hk
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hk
  zufct
  rw [offK_eq, offK_eq] at h1
  obtain ⟨he, ht⟩ := pos_eq_of_oW hP hS₂.2.1 hS₂.1 hA.1 hA'.1 hA.2.1 hA.2.2.1 hA'.2.1
    hA'.2.2.1 h1
  refine ⟨he, ht, ?_⟩
  zufvk
  have hm' := (stop_mem hP hN hok' hf').1
  zuixk
  have ha' := F₂plus_subset J hS₂.2.1 hm'
  have hpt : sidePt (chainModel J.whole).W r.1 zthzk =
      sidePt (chainModel J.whole).W r'.1 ztruu := by_simp_all
  rw [hend, hend', h2] at hpt
  split_ifs at hpt
  · exact aug_eq_of_lend ha ha' hpt
  · exact aug_eq_of_rend ha ha' hpt

/-- The leaving direction code is determined by the position and the chord. -/
theorem raw_dc_eq (hP : J.P.Simple) (hN : IsNF ztj zta N)
    {r r' : ℕ × ℕ × ℕ × ℕ × ℕ} {d d' : ℕ} (h : RawOK P J N r d) (h' : RawOK P J N r' d')
    (he : r.1 = r'.1) (ht : rPar P J r = rPar P J r') (hs : rSet P J N r = rSet P J N r') :
    rKey P J r d = rKey P J r' d' := by
  zuiwy
  obtain ⟨hok, hf, -, -, hd, hend⟩ := h
  obtain ⟨-, -, -, -, hd', hend'⟩ := h'
  zufvk
  zuixk
  have hpt : sidePt (chainModel J.whole).W r.1 zthzk =
      sidePt (chainModel J.whole).W r'.1 ztruu := by_simp_all
  rw [hend, hend', ← hs] at hpt
  have hne := lend_ne_rend ha
  have hdd : d = d' := by
    grind
  unfold rKey
  rw [offK_eq, offK_eq, hdd]
  grind

/-- **The stop list from the deduped raw records** (a list `O` of raw items with strictly
increasing keys covering the keys of all raw items). -/
theorem stopsOK_of' {α : Type*} (hP : J.P.Simple) (hN : IsNF ztj zta N)
    {RS O : List α} {rec : α → ℕ × ℕ × ℕ × ℕ × ℕ} {dc : α → ℕ}
    (hok : ∀ x ∈ RS, RawOK P J N ztkea ztqlw)
    (hcomp : ∀ e ∈ F₂plus J ztwrl,
      StopChord2 J ztwrl e → ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J ztk →
      ∃ x ∈ RS, (rec x).1 = p ∧ rPar P J ztkea = t ∧ rSet P J N ztkea = e)
    (hsub : ∀ y ∈ O, y ∈ RS)
    (hinc : O.Pairwise (fun x y => KLt (rKey P J ztkea ztqlw) (rKey P J ztmnj ztvoy)))
    (hcov : ∀ x ∈ RS, ∃ y ∈ O, rKey P J ztmnj ztvoy = rKey P J ztkea ztqlw) :
    StopsOK J ztwrl (stopsOf J zta N ztvbt) := by
  have hO : ∀ y ∈ O, RawOK P J N _ _ := fun y hy => hok y by_simp_all
  have hst : stopsOf J zta N ztvbt =
      O.map (fun y => ((rec y).1, rPar P J ztmnj, rSet P J N ztmnj)) := by
    unfold stopsOf; simp
  rw [hst]
  zudfi
  · zugg
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hk, hf, hA, hL, -, -⟩ := hO y hy
    obtain ⟨hm, hsc⟩ := stop_mem hP hN hk hf
    simp_all
  · zuibp
    obtain ⟨x, hx, h1, h2, h3⟩ := hcomp e he hsc p t hA hL
    obtain ⟨y, hy, hky⟩ := hcov x hx
    obtain ⟨e1, e2, e3⟩ := raw_eq_of_key hP hN by_simp_all by_simp_all hky
    grind
  · zuczn
    exact hinc.imp fun {a b} h => by
      have := KLt.fst_le h
      tauto
  · rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb h heq => ?_) hinc
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 heq
    obtain ⟨h2, h3⟩ := Prod.ext_iff.1 h2
    exact KLt.ne h (raw_dc_eq hP hN by_simp_all by_simp_all h1 h2 h3)
end SweepStop
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace SweepStop
open Sweep SweepEv
variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- The data of an admissible code with a free direction. -/
structure OrgD (P : Polygon) (J : Merge.Junction) (N : NF) (kind k b : ℕ) : Prop where
  ok : StOK P J N kind k b
  free : FreeAt J.whole ztwjf ztkz
variable (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N)
include hP hN
variable {kind k b : ℕ}
/-- **The attachments of a stop chord.** -/
theorem orig_attach (hD : OrgD P J N kind k b) :
    (∀ p t, Arrival (chainModel J.whole).W ztwjf ztcrx p t →
      SideAttach (chainModel J.whole).W ztwjv p t ∧
      sidePt (chainModel J.whole).W p t = (if b = 1 then Merge.lend ztwjv
        else Merge.rend ztwjv)) ∧
    (∀ p t, Arrival (chainModel J.whole).W
        ztbakp ztkz p t →
      SideAttach (chainModel J.whole).W ztwjv p t ∧
      sidePt (chainModel J.whole).W p t = (if 1 - b = 1 then
        Merge.lend ztwjv else Merge.rend ztwjv)) ∧
    (∀ p t, SideAttach (chainModel J.whole).W ztwjv p t →
      Arrival (chainModel J.whole).W ztwjf ztcrx p t ∨
      Arrival (chainModel J.whole).W
        ztbakp ztkz p t) := by
  zuics
  obtain ⟨haD, ha2, -, -, -⟩ := stOrig_facts hP hN hok
  zuhxx
  have hb := hok.2.1
  zudia
  zuezm
  set a := stOrig J zta N kind k b
  zubrn
  have hends : (if b = 1 then Merge.lend ztxmx
        else Merge.rend ztxmx) = a ∧
      (if 1 - b = 1 then Merge.lend ztxmx
        else Merge.rend ztxmx) = farPt J.whole a (dirOf b) := by
    zubhr
    · rw [dirOf_zero] at hT ⊢
      obtain ⟨h1, h2⟩ := ends_shoot_neg J.whole hT.le
      simp_all
    · rw [dirOf_one] at hT ⊢
      obtain ⟨h1, h2⟩ := ends_shoot_pos J.whole hT.le
      simp_all
  refine ⟨fun p t hA => ⟨attach_of_origin hP ha haD hσ hf hA, by rw [hends.1]; exact hA.2.2.2.1⟩,
    fun p t hA => ⟨attach_of_far hP ha haD hσ hf hA, by rw [hends.2]; exact hA.2.2.2.1⟩,
    fun p t hA => ?_⟩
  rcases attach_cases hP ha hσ hf hA with ⟨-, h⟩ | ⟨-, h⟩
  · simp_all
  simp_all

/-- **The two attachments** of a stop chord: any attachment is the arrival position of the
origin or that of the far end. -/
theorem attach_two (hD : OrgD P J N kind k b) {p₀ p₁ : ℕ} {t₀ t₁ : ℝ}
    (h₀ : Arrival (chainModel J.whole).W ztwjf ztcrx p₀ t₀)
    (h₁ : Arrival (chainModel J.whole).W
      ztbakp ztkz p₁ t₁)
    {q : ℕ} {s : ℝ} (hA : SideAttach (chainModel J.whole).W ztwjv q s) :
    (q = p₀ ∧ s = t₀) ∨ (q = p₁ ∧ s = t₁) := by
  obtain ⟨i1, i2, i3⟩ := orig_attach hP hN hD
  zugb
  have hm := (stop_mem hP hN hD.ok hD.free).1
  have ha : stopSet J zta N kind k b ∈ (chainModel J.whole).Adm :=
    F₂plus_subset J hN.1.2.1 hm
  rcases i3 q s hA with h | h
  · exact Or.inl (hM.attach_unique ha hA (i1 p₀ t₀ h₀).1 by_simp_all)
  · exact Or.inr (hM.attach_unique ha hA (i2 p₁ t₁ h₁).1 by_simp_all)

/-- **Anchored, pocket**: from the offsets of the two attachments. -/
theorem anc_pocket_iff (hD : OrgD P J N kind k b) {p₀ p₁ : ℕ} {t₀ t₁ : ℝ}
    (h₀ : Arrival (chainModel J.whole).W ztwjf ztcrx p₀ t₀)
    (h₁ : Arrival (chainModel J.whole).W
      ztbakp ztkz p₁ t₁) :
    (¬ EvBrk J ztwjv ↔
      oW J zthw < Lst J ∨ oW J ztdhz < Lst J) ∧
    ((∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W ztwjv q s →
      oW J ztej ≠ 0) ↔ oW J (p₀ + t₀) ≠ 0 ∧ oW J (p₁ + t₁) ≠ 0) := by
  zueuj
  have hA₀ := (i1 p₀ t₀ h₀).1
  have hA₁ := (i2 p₁ t₁ h₁).1
  refine ⟨⟨fun h => ?_, fun h hb => ?_⟩, ⟨fun h => ⟨h _ _ hA₀, h _ _ hA₁⟩, fun h q s hA => ?_⟩⟩
  · unfold EvBrk at h
    zubpo
    obtain ⟨q, s, hA, hlt⟩ := h
    zuctg
    · simp_all
    simp_all
  · zuy
    · exact absurd (hb _ _ hA₀) ztmmp
    · exact absurd (hb _ _ hA₁) ztmmp
  · zuctg
    · simp_all
    simp_all

/-- The origin and the far end of a stop chord are distinct points of it. -/
theorem orig_far_ne (hD : OrgD P J N kind k b) :
    stOrig J zta N kind k b ≠ farPt J.whole ztwjf ztkz ∧
      stOrig J zta N kind k b ∈ stopSet J zta N kind k b ∧
      farPt J.whole ztwjf ztkz ∈ stopSet J zta N kind k b := by
  zuics
  obtain ⟨-, ha2, -, -, -⟩ := stOrig_facts hP hN hok
  zuhxx
  zudia
  zubrn
  zuezm
  refine ⟨fun h => ?_, ?_, rayPt_mem_shoot _ _ _ hT.le le_rfl⟩
  · have := congrArg Prod.fst h
    unfold farPt at this
    zudv
    rcases hσ with h' | h' <;> zvmxl at this hT <;> linarith
  · have := rayPt_mem_shoot J.whole ztwjf ztkz le_rfl hT.le
    simp_all

/-- **At most one parent**: two chords of `S₂` containing a stop chord are equal. -/
theorem parent_eq (hD : OrgD P J N kind k b) {c c' : Set Point}
    (hc : c ∈ N.F ztj zta) (hc' : c' ∈ N.F ztj zta)
    (h : stopSet J zta N kind k b ⊆ c) (h' : stopSet J zta N kind k b ⊆ c') : c = c' := by
  obtain ⟨hne, h1, h2⟩ := orig_far_ne hP hN hD
  exact parent_unique hN.1.2.1 hc hc' hne (h h1) (h h2) (h' h1) (h' h2)
omit hP hN in
/-- **The parent of a wall piece** is its chord. -/
theorem parent_wall (_hP : J.P.Simple) (hN : IsNF ztj zta N) {k b : ℕ}
    (hD : OrgD P J N 1 k b) :
    stopSet J zta N 1 k b ⊆ (N.chord k).toSet ztj zta := by
  obtain ⟨-, hb, hw, -⟩ := hD.ok
  obtain ⟨hk, -⟩ := hw rfl
  obtain ⟨-, hcase⟩ := stOrig_wall (Q := Qof P) hN hk hb
  zuezm
  refine shoot_sub_end hN.1.2.1 ztvlj ?_
  zueju
  · tauto
  tauto
omit hP in
omit hN in
/-- **The parent of a shared or top chord**: a chord `c` of `S₂` contains it iff its end in the
direction `σ` is the origin. -/
theorem parent_vt_iff (_hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    {a : Point}
    (haR : a ∈ J.right.set) {b : ℕ} (hb : b ≤ 1)
    (hf : FreeAt J.whole a ztkz) {c : Set Point} (hc : c ∈ S₂) :
    Merge.shoot J.whole a ztkz ⊆ c ↔
      (b = 1 ∧ Merge.lend c = a) ∨ (b = 0 ∧ Merge.rend c = a) := by
  zudia
  have ha : ztlal := le_trans (J.right.snd_le_top_of_mem_set haR) J.right_top_le
  zubrn
  constructor
  · intro hsub
    obtain ⟨y, l, r, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec ztbac
    have ha0 : a ∈ Visibility.hseg y l r := hsub (by
      have := rayPt_mem_shoot J.whole a ztkz le_rfl hT.le
      simp_all)
    zueqv
    obtain ⟨hay, hal, har⟩ := ha0
    -- `a` is an end of the chord
    have hend : a.1 = l ∨ a.1 = r := by
      zuct
      zumip
      exact haD (by
        have := hH.open_mem a.1 (lt_of_le_of_ne hal ztvbk) (lt_of_le_of_ne har hne.2)
        grind)
    -- the points just after `a` along the ray are in the chord
    set s : ℝ := min (J.whole.hitParam a ztkz) ztxyo with hs
    have hs0 : ztxx := lt_min hT ztbzj
    have hmem := hsub (rayPt_mem_shoot J.whole a ztkz hs0.le ztff)
    obtain ⟨-, h1, h2⟩ := hmem
    zvogc at h1 h2
    zubhr
    · rw [dirOf_zero] at h1 h2
      grind
    · rw [dirOf_one] at h1 h2
      grind
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact shoot_sub_end hS₂ hc (Or.inl ⟨dirOf_one, h.symm⟩)
    · exact shoot_sub_end hS₂ hc (Or.inr ⟨dirOf_zero, h.symm⟩)
end SweepStop
end
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The registers allowed as descriptor or length registers: fixed, or of stage 2. -/
def DR (r : ℕ) : Prop := ztnga ∨ (244000 ≤ r ∧ r < 246000)

/-! ## A positive height code -/

/-- **The vertex fix**: the edge (`2m + 6 ↦ 6`, the other copy of the top), its symbolic point,
the height code `i + 1` (vertex `i`) or `h + 1` (a point of an edge at the height of vertex `h`). -/
def hFix (dsc nr : ℕ) : Stmt :=
  .seq ztyqc
    (.seq (.ifLtN ztfiv nr ztdkf ztdke)
      (.seq (callSym dsc ztwgm lH ztibh)
        (.ifLtN ztibh K1 ztyny
          ztynz)))

/-- **A positive height code**: normalise; at a vertex, fix the code. -/
def hHgt (dsc nr : ℕ) : Stmt := .seq (normS dsc lE lH ztwgl) (.ifLtN lH K1 zttmf .skip)
variable {dsc nr : ℕ}
set_option maxRecDepth 20000 in
theorem hFix_irs (hdr : DR dsc) (hnr : DR nr) {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hn : c.nreg nr = 2 * C.m + 7) {e : ℕ} (hE : c.nreg lE = e) (hH : c.nreg lH = 0)
    (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) (hroom : c.nreg ALLOC + 31013 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ zttmf c 31013 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos zta ztjy).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpe → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  zucid

  unfold hFix
  -- 1. `e + 1`
  refine IRS.seq (K₂ := 31012)
    ((IRS.block [.addN _ lE K1] hI ⟨⟨iscr_sw by_decide by_decide,
      by omega⟩, trivial⟩).mono le_rfl (fun _ h => h)) ?_
  zubun
  have q22 : ztzjf := by
    zuduc
  have q1 : ztjbj := fun r hr => by
    zuelv
  zugnu
  have qN : ztidv := by rw [q1 _ ztiiu]; exact hn
  -- 2. the edge `e'`
  have hstep2 : IRS P W c₀ (.ifLtN ztfiv nr ztdkf
      ztdke) c₁ 3 (fun c' => ∃ e', c'.nreg (sw 723) = e' ∧ 6 ≤ e' ∧
        e' < 2 * C.m + 6 ∧ (chainModel C).pos zta ztugh = (chainModel C).pos zta ztjy ∧
        ztina ∧ c'.nmem = c₁.nmem) := by
    zugsk
    · refine (IRS.instr1 hI₁ (i := .copyN _ lE) (iscr_sw by_decide
        by_decide)).mono by_omega ?_
      zuu
      zugwz

      · zubiv
        zuhne
      · zuua
    · refine (IRS.instr1 hI₁ (i := .copyN _ K6) (iscr_sw by_decide
        by_decide)).mono by_omega ?_
      zuu
      zuxv

      · zubiv
        zuhnf
      · zukua
      · zuua
  zubln

  have hH₂ : zturq := by
    zuezd
  have hctx₂ : ChainCtx P W c₂ dsc C := hctx.transport
    (by rw [q2 _ ztdub, q1 _ ztdub])
    by_simp_all by_omega
  have hA₂e : ztbae := by
    zugwy
  -- 3. the symbolic point
  refine IRS.seq (K₂ := 3) (callSym_irs hI₂ hctx₂
    ⟨by unfold DR at hdr; omega, by unfold DR at hdr; omega, by_decide, by_decide,
      by decide, by_decide⟩ ⟨by_decide, by_decide⟩
    by_omega by_omega
    ztyau
    by_simp_all by_omega) ?_
  zuft

  -- 4. the code
  have hfin : ∀ (j : ℕ), ztilj → c₃.nreg j = k →
      IRS P W c₀ ztnbb c₃ 1 (fun c' => ∃ k, c'.nreg lH = k + 1 ∧ k < P.n ∧
        ((Qof P).vtx k).2 = ((chainModel C).pos zta ztjy).2 ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpe → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
    zumha
    refine (IRS.instr1 hI₃ (i := .addN lH j K1) ⟨iscr_sw by_decide
      by_decide, by_omega⟩).mono le_rfl ?_
    zuu
    refine ztegz
    · zubzz
    · zuwc
      rw [upd_other _ _ _ hr2, q3 r hr1 ztcco hr4,
        q2 _ ztcco, q1 _ ztcco]
    · zuwc
      zuhnp

    grind
  zuekc
  · grind
  grind
set_option maxRecDepth 20000 in
/-- **A positive height code** naming the height of the arrival position, with the same
parameter and point. -/
theorem hHgt_irs (hdr : DR dsc) (hnr : DR nr) {C : Chain} (hI : IInv W c₀ c) (hK : Consts c₀) (hctx : ChainCtx P W c dsc C)
    (hn : c.nreg nr = 2 * C.m + 7) {x : WPos} (hE : c.nreg lE = x.edge)
    (hH : c.nreg lH = x.hgt) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n x) (hcl : PosClass C zta x)
    (hy : |((chainModel C).pos zta x).2| < C.radius)
    (hroom : c.nreg ALLOC + 42030 ≤ W) (hPW : P.n + 1 ≤ W) :
    IRS P W c₀ (hHgt dsc nr) c 42030 (fun c' => ∃ k, c'.nreg lE = x.edge ∧ c'.nreg lH = k + 1 ∧ k < P.n ∧
      ((Qof P).vtx k).2 = ((chainModel C).pos zta x).2 ∧
      (chainModel C).param zta ztcjw = (chainModel C).param zta x ∧
      (chainModel C).pos zta ztcjw = (chainModel C).pos zta x ∧
      ProperPos ztc zta P.n ztcjw ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpd → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuhx
  zubo
  unfold hHgt
  zukhd
  -- 1. normalise
  refine IRS.seq (K₂ := 31015) (normS_irs hI hKc hctx
    ⟨by unfold DR at hdr; omega, by unfold DR at hdr; omega, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    by_omega by_simp_all by_simp_all
    by_omega) ?_
  zufs

  have keep1 : ∀ r, bandOf r ∉ oracleBands → r ≠ lH → ztdpd → r ≠ ALLOC →
      c₁.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    q1 r h1 h2 ztbsm ztbsm h4
  zuekd
  · -- a vertex: fix the code
    zujxy
    have hpar0 : ztxir := by
      grind
    have hposv : ztxpl := by
      grind
    zucn
    have he6 : ztkzt := by
      zudsb
      · zuhcy

        simp only [show (chainModel C).param _ ztkng = 0 from rfl,
          Chazelle.Chain.sidePt_zero, hW] at hy
        zuevj
        · zuiga
        · zuigb
      · omega
      omega
    have hctx₁ := hctx.transport
      (keep1 dsc (by exact not_oracle_sw ztnve ztnve)
        (by unfold DR at hdr; unfold lH sw; omega) ztdub (by unfold DR at hdr; unfold ALLOC; omega))
      qm1 hA₁''
    have hn₁ : ztidv := by
      rw [keep1 nr (by exact not_oracle_sw ztnvf ztnvf)
        (by unfold DR at hnr; unfold lH sw; omega) ztiiu
        (by unfold DR at hnr; unfold ALLOC; omega)]; exact hn
    refine (hFix_irs hdr hnr hI₁ hK hctx₁ hn₁ hE₁ by_omega he6.1 he6.2 by_omega hPW).mono
      le_rfl ?_
    zucby

    obtain ⟨vpar, vpos⟩ := vtx_fix (M := chainModel C) (Q := Qof P) (e := x.edge) (h' := k)
      by_grind
    refine ⟨k, ?_, hk1, hkl, hkh, by_grind, by_grind,
      ⟨by_grind, by_grind, by_grind⟩,
      fun r h1 h2 h3 h4 => ?_, by_omega, fun a ha => ?_⟩
    · rw [hk2 lE by_decide
        by_decide ztbcz by_decide]
      omega
    · zuguz

    grind
  · -- inside an edge: the code is positive
    zuddi

    have hparne : ztixd := fun h =>
      hpos0 ztvvu
    zudhs

    refine IRS.skip hI₁ ⟨k, hE₁, by_omega, by
      have := hpp₁.2.2; grind, hkh, by_grind,
      by grind, by_grind, keep1, hA₁'', qm1⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The context of a model for the local hit, at registers `md, cd, nf` (`LCtx` with
these registers). -/
structure MCtx (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (E : ℕ) (md cd nf : ℕ) (c : Config) :
    Prop where
  hctx : ChainCtx P W c cd C
  hcd : c.nreg cd = c.nreg md + 1
  hmd : ModelDescAt c.nmem zthvi zta ztc
  hmwf : ModelDescWF P ztm c.nmem zthvi
  hm0 : c.nmem zthvi = 0
  hNW : NFWithin c.nmem ztvjt E N
  hE : E ≤ c.nreg ALLOC
  htab : ∀ j, j < c.nreg TLR → c.nmem ztllh = 2 ^ j
  hbig : N.arcs.length < 2 ^ c.nreg TLR
  hTB : E ≤ c.nreg TBR
  hTW : c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC

/-- The setup of the local hit. -/
def lhSetL (md cd nf nr : ℕ) : List Instr :=
  [.copyN lMD md, .copyN lCD cd, .copyN lNF nf, .copyN lN nr, .constN lT 0, .constN accA 0]

/-- **A local hit** in the model of the registers `md, cd, nf, nr`. -/
def lhRun (sh : Stmt) (md cd nf nr : ℕ) : Stmt :=
  .seq (block ztbsu) (.seq (hHgt cd nr) ztkak)

/-- The registers of the local-hit run (besides the oracle bands and the allocator). -/
def LHR (r : ℕ) : Prop := ztgz ∨ ztfut

/-- The cost of the local-hit run. -/
def lhRunK (T Fg D : ℕ) : ℕ := 6 + (42030 + localK T Fg ztef D)
theorem lhSet_val (m f : ℕ → ℕ) {md cd nf nr : ℕ} (_hd : DR md) (hc : DR cd) (hn : DR nf)
    (hr : DR nr) :
    regB m ztbsu f lMD = f md ∧ regB m ztbsu f lCD = f cd ∧
    regB m ztbsu f lNF = f nf ∧ regB m ztbsu f lN = f nr ∧
    regB m ztbsu f lT = 0 ∧ regB m ztbsu f accA = 0 ∧
    (∀ q, q ≠ lMD → q ≠ lCD → q ≠ lNF → q ≠ lN → q ≠ lT → q ≠ accA →
      regB m ztbsu f q = f q) := by
  unfold DR at _hd hc hn hr
  have e1 : lMD = 241100 := rfl
  have e2 : lCD = 241101 := rfl
  have e3 : lNF = 241102 := rfl
  have e4 : lN = 241106 := rfl
  have e5 : lT = 241107 := rfl
  have e6 : accA = 242000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 => ?_⟩ <;>
    simp only [lhSetL, regB, regI, upd, e1, e2, e3, e4, e5, e6] at * <;>
    simp (disch := omega) only [ite_false, ite_eq_right, ite_eq_left, *]

/-- **The local-hit run.** -/
theorem lhRun_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {md cd nf nr : ℕ}
    (hd : DR md) (hc : DR cd) (hn : DR nf) (hr : DR nr)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hM : MCtx P W C N E md cd nf c) (hPs : C.P.Simple) (hNF : IsNF ztc zta N)
    (hX : X.holds P c₀.nmem ztxj ztdq)
    (hcap : c₀.nreg ztbcb ≤ X.cap P c₀.nmem ztxj)
    (hOk : Ok P ztc)
    (hsg : (chainModel C).Semigranular ztwjq ztq)
    (hdeg : (chainModel C).DegLe ztwjq zto)
    (hnr : c.nreg nr = 2 * C.m + 7) {x : WPos} (hxE : c.nreg lE = x.edge)
    (hxH : c.nreg lH = x.hgt) (_hxD : c.nreg lD ≤ 1) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n x) (hcl : PosClass C zta x)
    (hy : |((chainModel C).pos zta x).2| < C.radius)
    (hon : (chainModel C).pos zta x ∈ C.set ∨
      |((chainModel C).pos (Qof P) x).1| = C.radius)
    (hroom : c.nreg ALLOC + lhRunK ztdg ztwiu zto ≤ W) :
    IRS P W c₀ ztpco c
      (lhRunK ztdg ztwiu zto) (fun c' =>
      ∃ L', AccOK P accA ztlnv C.radius ztwjd
          ztmk L' c' ∧
        (∀ τ ∈ L', 0 < τ ∧ OnCB C (rayPt ztwjd ztmk τ)) ∧
        ((sideLeft (chainModel C).W x.edge ztwte
            ztbaqi ∧
          ((chainModel C).pos zta x).2 ≤ C.top.2) →
          Merge.FreeAt C ztwjd ztmk ∧
            C.hitParam ztwjd ztmk ∈ L') ∧
      EFr LHR c c') := by
  zujmo
  set D := c₀.nreg ztbey with hDd
  zujmt
  unfold lhRun lhRunK at *
  have hDR : ∀ r, DR r → bandOf r ∉ oracleBands ∧ r ≠ ALLOC ∧ ¬ LHR r ∧ 240000 ≤ r ∧ r < 250000 :=
    fun r h => by
      zumqs
      refine ⟨not_oracle_sw by_omega by_omega, by unfold ALLOC; omega, ?_, by_omega, by_omega⟩
      unfold LHR sw; omega
  -- 1. the setup
  have hok : okB W c.nmem ztbsu c.nreg := by
    simp only [lhSetL, okB, okI]
    exact ⟨iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide,
      iscr_sw by_decide by_decide,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩, trivial⟩
  refine IRS.seq
    ((IRS.block _ hI hok).mono by_rfl ztb) ?_
  zubun
  obtain ⟨v1, v2, v3, v4, v5, v6, vo⟩ := lhSet_val c.nmem c.nreg hd hc hn hr
  have r1 : ∀ r v, regB c.nmem ztbsu c.nreg r = v → c₁.nreg r = v :=
    by simp_all
  zucwy
  have hA1 : ztdc := r1 _ _ (vo _ by_decide
    by_decide by_decide by_decide
    by_decide by_decide)
  have keep1 : ∀ q, q ≠ lMD → q ≠ lCD → q ≠ lNF → q ≠ lN → q ≠ lT → q ≠ accA →
      c₁.nreg q = c.nreg q := by_simp_all
  have kD : ∀ r, DR r → c₁.nreg r = c.nreg r := fun r h => by
    zumqs
    exact keep1 r (by unfold lMD sw; omega) (by unfold lCD sw; omega) (by unfold lNF sw; omega)
      (by unfold lN sw; omega) (by unfold lT sw; omega) zthk
  have s1E : c₁.nreg lE = x.edge := by
    rw [keep1 lE by_decide by_decide
      by_decide by_decide by_decide
      by_decide]; omega
  have s1H : c₁.nreg lH = x.hgt := by
    rw [keep1 lH by_decide by_decide
      by_decide by_decide by_decide
      by_decide]; omega
  have s1D := keep1 lD by_decide
    by_decide by_decide by_decide
    by_decide by_decide
  have hctx₁ : ChainCtx P W c₁ cd C := hM.hctx.transport by_grind by_grind
    ztqew
  have hnr₁ : ztidv := by_grind
  have hPW : P.n + 1 ≤ W := by unfold hostWords at hWh; omega
  -- 2. the height code
  refine IRS.seq
    (hHgt_irs hc hr hI₁ hK hctx₁ hnr₁ s1E s1H he hpp hcl hy by_omega hPW) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨k, s2E, s2H, hkl, hkh, hkpar, hkpos, hkpp, k2, hA₂'', m2⟩
  zuioo
  have keep2 := k2
  have k2s := fun r h1 h2 h3 h4 =>
    keep2 r ztsg h3 h4 ztu
  have s2D : ztshj := by
    rw [k2s lD by_decide by_decide by_decide
      ztbcz, s1D]
  have s2N : c₂.nreg lN = 2 * C.m + 7 := by
    rw [k2s lN by_decide by_decide by_decide
      ztbcz, r1 _ _ v4, hnr]
  have s2T : zturr := by
    rw [k2s lT by_decide by_decide by_decide
      ztbcz, r1 _ _ v5]
  have s2A : ztpnl := by
    rw [k2s accA by_decide by_decide
      by_decide ztbcz, r1 _ _ v6]
  have s2MD : c₂.nreg lMD = c.nreg md := by
    rw [k2s lMD by_decide by_decide by_decide
      ztbcz, r1 _ _ v1]
  have s2CD : c₂.nreg lCD = c.nreg cd := by
    rw [k2s lCD by_decide by_decide by_decide
      ztbcz, r1 _ _ v2]
  have s2NF : c₂.nreg lNF = c.nreg nf := by
    rw [k2s lNF by_decide by_decide by_decide
      ztbcz, r1 _ _ v3]
  have hTBR₂ : c₂.nreg TBR = c.nreg TBR := by
    zugup
  have hTLR₂ : c₂.nreg TLR = c.nreg TLR := by
    zugup
  have hTLRc : c.nreg TLR = T := hI.hin _ by_trivial
  have mem2 : ztux := fun a ha => by
    rw [m2 a by_omega, m1]
  have hA2 : zteia := by_omega
  have hL₂ : LCtx P W C N E c₂ :=
    { hG := hG
      hWh := hWh
      hctx := by
        refine hM.hctx.transport by_omega mem2 hA2
      hcd := by rw [s2CD, s2MD]; exact hM.hcd
      hmd := by
        zuccd

        · obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hM.hmwf hM.hm0 hC' mem2 hA2
          exact Or.inl ztfwz
        · have := hM.hm0; omega
      hmwf := by
        zuccd

        · exact (ShotList.modelDesc_keep hM.hmwf hM.hm0 hC' mem2 hA2).1
        · have := hM.hm0; omega
      hm0 := by rw [s2MD, mem2 _ (by have := hM.hmwf.1; omega)]; exact hM.hm0
      hP := hPs
      hNW := by rw [s2NF]; exact (hM.hNW.transport fun b hb => mem2 b (by
        have := hM.hE; omega))
      hE := le_trans hM.hE hA2
      hNF := hNF
      htab := fun j hj => by
        rw [hTLR₂] at hj
        rw [hTBR₂, mem2 _ (by have := hM.hTW; omega)]
        exact hM.htab j hj
      hbig := by rw [hTLR₂]; exact hM.hbig
      hTB := by rw [hTBR₂]; exact hM.hTB
      hTW := by rw [hTBR₂, hTLR₂]; have := hM.hTW; omega }
  obtain ⟨hAr, hCh⟩ := region_bounds hPs hNF hdeg
  have hposxs : (chainModel C).pos _ xs = (chainModel C).pos _ x := hkpos
  have hlocs : ztoke ∨
      (6 ≤ xs.edge ∧ (chainModel C).pos zta xs ∈ C.set) := by
    rw [hposxs]
    rcases hcl with h | ⟨h6, h6'⟩ | ⟨h6, hz⟩
    · grind
    · zuklv
      · grind
      · exfalso
        have hm := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) by_omega by_grind hpp.1 hpp.2.1
        rw [show x.edge - 6 + 6 = x.edge by omega] at hm
        zulep
    · zuklv
      · grind
      · exfalso
        have hm := C.sideWalk_tour_pt_mem C.sideBeta
          le_rfl by_grind le_rfl one_pos
        have : (chainModel C).pos zta x = sidePt ztcs ztcc 0 := by
          show sidePt (chainModel C).W _ _ = _
          zuihe
        zukyv
        zulep
  have hacc : AccOK P accA ztlnv C.radius
      ((chainModel C).pos zta xs) (dirOf (c₂.nreg lD)) ∅ c₂ :=
    accOK_init accA _ _ _ _ s2A
  refine (localHit_irs (x := xs)
      hsh hBs hXl hI₂ hK hL₂ hX hcap hOk hsg hAr hCh s2E s2H rfl he hkpp
      by_grind hlocs hacc by_omega rfl rfl s2N
      by_grind).mono
        by_grind ?_
  rintro c' ⟨⟨L', hacc', -, hL', hgeo⟩, k3, hA₃, m3⟩
  rw [hposxs, s2D] at hacc' hL' hgeo
  refine ⟨L', hacc', fun τ hτ => ?_, fun ⟨hsl, htop⟩ => hgeo ?_, ?_⟩
  · rcases hL' τ hτ with h | h
    · tauto
    omega
  · refine ztkme
    grind
  · refine ⟨fun r h1 h2 h3 => ?_, by_omega, fun a ha => ?_⟩
    · have hr2 : ¬ (ztgz ∨ ztfut) := h2
      rw [k3 r h1 (fun h => hr2 (by unfold LHW sw at h; unfold sw; omega)) h3,
        keep2 r h1 ztwsa (by unfold sw at hr2 ⊢; omega)
          h3, keep1 r ztwsa
          ztwsa
          ztwsa
          ztwsa
          ztwsa
          ztwsa]
    · zugwc
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Registers -/
def gRB : ℕ := sw 4000
def gRC : ℕ := sw 4001
def gMD2 : ℕ := sw 4002
def gCD2 : ℕ := sw 4003
def gTP : ℕ := sw 4005
def gTV : ℕ := sw 4006

/-! ## The model contexts -/
theorem MCtx.transport {C : Chain} {N : NF} {E md cd nf : ℕ} {c c' : Config}
    (h : MCtx P W C N E md cd nf c)
    (hr : ∀ r, r = md ∨ r = cd ∨ r = nf ∨ r = TBR ∨ r = TLR → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    MCtx P W C N E md cd nf c' := by
  obtain ⟨hctx, hcd, hmd, hmwf, hm0, hNW, hE, htab, hbig, hTB, hTW⟩ := h
  have rMD := hr md ztp
  have rCD := hr cd ztwiz
  have rNF := hr nf ztbajm
  have rTB := hr TBR ztbaje
  have rTL := hr TLR ztbakw
  zucou

  · omega
  zuebm
  refine ⟨hctx.transport rCD hm hA, by_omega,
    by zupct; exact Or.inl ztfwz, by_simp_all, by_simp_all,
    by zupcu; exact hNW.transport fun b hb => hm b by_omega, le_trans hE hA,
    fun j hj => by
      grind,
    by simp_all, by_omega, by_omega⟩
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- **The context of the model of `C₁`.** -/
theorem mctx1 (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    MCtx P W J.left N₁ ztbmp MD₁ CD₁ ztea c := by
  have hTBR : ztgug := hI.hin _ by_trivial
  have hTLR : ztguh := hI.hin _ by_trivial
  have h3 : c.nreg ztea = c₀.nreg ztea := hI.hin _ by_trivial
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI
  zuixa
  refine ⟨E.ctx1' hI, md4, md1, md2, md3, ?_, by have := hI.hA; omega, fun j hj => ?_,
    by rw [hTLR]; exact E.hbig₁, by_omega, by zunqq; have := hI.hA; omega⟩
  · zvncq; exact E.hNT₁.transport fun b hb => hI.hm b by_omega
  · rw [hTLR] at hj; rw [hTBR, hI.hm _ by_omega]; exact E.htab j hj

/-! ## The model descriptor of `C₂` -/

/-- **A model descriptor of `C₂`** in fresh memory: `0` and a copy of the chain descriptor of
`C₂` (`sw 21`). -/
def md2Init : Stmt :=
  block [.copyN 244002 9999, .storeN 9999 240610, .addN 9999 9999 240611,
    .copyN 244005 240021,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .loadN 244006 244005, .storeN 9999 244006, .addN 9999 9999 240611, .addN 244005 244005 240611,
    .addN 244003 244002 240611]

/-- The registers `md2Init` writes. -/
def MD2W (r : ℕ) : Prop := r = gMD2 ∨ r = gCD2 ∨ r = gTP ∨ r = gTV
set_option maxHeartbeats 4000000 in
theorem md2Init_exec (c : Config) (hw : WordsBounded W c) (k0 : c.nreg 240610 = 0)
    (k1 : c.nreg 240611 = 1) (hroom : c.nreg 9999 + 6 ≤ W) (hB : c.nreg 240021 + 5 ≤ c.nreg 9999) :
    ∃ c' k, Exec P W md2Init c c' k ∧ k = 25 ∧
      c'.nreg 9999 = c.nreg 9999 + 6 ∧ c'.nreg 244002 = c.nreg 9999 ∧
      c'.nreg 244003 = c.nreg 9999 + 1 ∧
      (∀ r, r ≠ 9999 → r ≠ 244002 → r ≠ 244003 → r ≠ 244005 → r ≠ 244006 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem zterc = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg 9999 + 1 + j) = c.nmem (c.nreg 240021 + j)) ∧
      (∀ a, a < c.nreg 9999 → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold md2Init
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, by config_simp; omega, by config_simp, by config_simp; omega, fun r h1 h2 h3 h4 h5 => ?_,
    ?_, fun j hj => ?_, fun a ha => ?_, rfl, rfl, rfl⟩
  · config_simp; simp [upd, h1, h2, h3, h4, h5]
  · config_simp; simp only [upd]; grind
  · config_simp
    zuby
    grind
  · config_simp; simp only [upd]; grind

/-- **The model descriptor of `C₂`** as a run step: the context of the model of `C₂` at
`gMD2, gCD2, sw 4`. -/
theorem md2Init_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + 25 ≤ W) :
    IRS P W c₀ md2Init c 25 (fun c' => MCtx P W J.right N₂ ztbmp gMD2 gCD2 ztbz c' ∧
      (∀ r, ¬ MD2W r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      zth) := by
  zuiw
  have k0 : c.nreg 240610 = 0 := hK.1
  zubgn
  zuljx
  obtain ⟨hG, hWh, hwf, ⟨H, hC, hreg⟩, hPs, hWm⟩ := hctx
  have hB : c.nreg 240021 + 5 ≤ c.nreg 9999 := hwf.1
  obtain ⟨c', k, ex, hk, a1, a2, a3, hreg', m0, mc, mlo, rr, rm, ro⟩ :=
    md2Init_exec (P := P) c hI.hw k0 k1 (by unfold ALLOC at hroom; omega) hB
  have a1' : c'.nreg ALLOC = c.nreg ALLOC + 6 := a1
  have a2' : c'.nreg gMD2 = c.nreg ALLOC := a2
  have a3' : c'.nreg gCD2 = c.nreg ALLOC + 1 := a3
  have m0' : c'.nmem ztm = 0 := m0
  have mc' : ∀ j, j < 5 → c'.nmem ztijb = c.nmem (c.nreg zted + j) := mc
  have mlo' : zteih := mlo
  have hwf' : ChainWF P ztm c.nmem ztxnj := hwf
  have hC' : ChainDescAt c.nmem ztxnj zta H J.right := hC
  obtain ⟨hMD, hMWF, hCD⟩ := SweepRam.modelDesc_of_copy (E' := c'.nreg ALLOC) hwf' hC'
    le_rfl mlo' m0' mc' (by rw [a1'])
  have hTBR : c'.nreg TBR = c₀.nreg TBR := by
    rw [hreg' _ by_decide by_decide by_decide
      by_decide by_decide]
    zugkg
  have hTLR : c'.nreg TLR = c₀.nreg TLR := by
    rw [hreg' _ by_decide by_decide by_decide
      by_decide by_decide]
    zugkg
  have h4 : c'.nreg ztbz = c₀.nreg ztbz := by
    rw [hreg' _ by_decide by_decide by_decide
      by_decide by_decide]
    zugkg
  have hA : c.nreg ALLOC ≤ c'.nreg ALLOC := by_omega
  zuixa
  have hmem : ∀ a, a < c₀.nreg ALLOC → c'.nmem a = c₀.nmem a := fun a ha => by
    rw [mlo a (by have := hI.hA; show a < c.nreg 9999; unfold ALLOC at *; omega)]; exact hI.hm a ha
  have hI' : IInv W c₀ c' := by
    refine ⟨ex.wb_right, fun q hq => ?_, le_trans hI.hA hA, hmem, fun a ha => by zupas; exact hI.hrm a ha⟩
    zujpt
    rw [hreg' q by_omega by_omega by_omega by_omega by_omega]
    exact hI.hin q by_tauto
  refine ⟨c', k, ex, by_omega, hI', ⟨fun r hr hra => ?_, fun r _ => by zuofy, ro, hA,
    by omega⟩, ?_, fun r hr hra => ?_, hA, fun a ha => mlo' a ha⟩
  · have : ¬ ztngb := fun h => hr (scr_band (iscr_sw (by
      by_contra h'; exact hr (by
        unfold ioBands sweepBands; rw [band_sw h.1 h.2]; decide)) h.2))
    zuhuh
  · refine ⟨⟨hG, hWh, ?_, ⟨H, ?_, hreg⟩, hPs, hWm⟩, by_omega, by_grind,
      by grind, by_grind, by rw [h4]; exact E.hNT₂.transport (fun b hb =>
        hmem b by_omega), by have := hI.hA; omega, fun j hj => ?_, by rw [hTLR]; exact E.hbig₂,
      by omega, by zunqq; have := hI.hA; omega⟩
    · rw [a3']; exact hMWF.2 m0'
    · grind
    · rw [hTLR] at hj; rw [hTBR, hmem _ by_omega]; exact E.htab j hj
  · unfold MD2W gMD2 gCD2 gTP gTV sw at hr
    zuhuh
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)
@[expose] public section
def rawRec (m : ℕ → ℕ) (RB i : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m ztqcg, m ztnon, m (RB + 11 * i + 3), m (RB + 11 * i + 4),
    m (RB + 11 * i + 5))

/-- The leaving direction code of the raw record `i`. -/
def rawDc (m : ℕ → ℕ) (RB i : ℕ) : ℕ := m (RB + 11 * i + 2)

/-- The auxiliary record `(anc, nl, l₀, l₁, par)` of the raw record `i`. -/
def rawAux (m : ℕ → ℕ) (RB i : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m (RB + 11 * i + 6), m (RB + 11 * i + 7), m (RB + 11 * i + 8), m (RB + 11 * i + 9),
    m (RB + 11 * i + 10))

/-! ## Sort and dedupe (RAM) -/

/-- The registers the sort may write (besides the oracle bands and the allocator). -/
def SoR (r : ℕ) : Prop :=
  ztgz ∨ ztltt ∨ ztph ∨
    ztbgd

/-- **The post of the sort**: a list `O` of raw record indices with strictly increasing keys
`(offK, dc)` covering the keys of all raw records; the stop records (`sB`, count `sC`) and the
auxiliary records (`aB`) are those of `O`, in fresh arrays. -/
def SortOut (P : Polygon) (J : Merge.Junction) (c c' : Config) : Prop :=
  ∃ O : List ℕ, (∀ i ∈ O, i < c.nreg gRC) ∧
    O.Pairwise (fun i j => KLt (rKey P J ztznn ztznj)
      (rKey P J ztzno ztznk)) ∧
    (∀ i, i < c.nreg gRC → ∃ j ∈ O,
      rKey P J ztzno ztznk =
        rKey P J ztznn ztznj) ∧
    c'.nreg sC = O.length ∧
    StopRecsAt c'.nmem ztqhe (O.map (rawRec c.nmem ztbsp)) ∧
    AuxRecsAt c'.nmem ztvgs (O.map (rawAux c.nmem ztbsp)) ∧
    c.nreg ALLOC ≤ c'.nreg sB ∧ c'.nreg sB + 5 * O.length ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ c'.nreg aB ∧ c'.nreg aB + 5 * O.length ≤ c'.nreg ALLOC ∧
    zth ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ SoR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task S: sort and dedupe** the `S = gRC` raw records at `gRB` (positions `PosW`, codes
`dc ≤ 1`, below the allocator), at cost `κ (S + 1) (⌈log₂ (S + 1)⌉ + 1)`. -/
def SortTask : Prop :=
  ∃ (srt : Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      (∀ i, i < c.nreg gRC → PosW P J (c.nmem (c.nreg gRB + 11 * i))
        (c.nmem (c.nreg gRB + 11 * i + 1)) ∧ rawDc c.nmem ztbsp i ≤ 1) →
      c.nreg gRB + 11 * c.nreg gRC ≤ c.nreg ALLOC →
      c.nreg ALLOC + κ * zteer * ztzci ≤ W →
      IRS P W c₀ srt c (κ * zteer * ztzci)
        (SortOut P J c)

/-! ## The labels (mathematics) -/

/-- The position of the walk of `C₂` corresponding to the offset `d` of the right stretch, just
after the position (`dq d`). -/
noncomputable def cpA (J : Merge.Junction) (d : ℕ) : ℕ :=
  ztfw % (chainModel J.right).W.n

/-- The position of the walk of `C₂` just before the vertex at offset `d` of the right stretch
(`dq (d - 1) + 1`: the end of the previous edge; it differs from `cpA d` only at the split
vertex). -/
noncomputable def cpB (J : Merge.Junction) (d : ℕ) : ℕ :=
  ztwlf % (chainModel J.right).W.n

/-- **Task L (mathematics): the side labels of an anchored stop chord** `e` (not a pocket),
attached on the `C₁` part, with an attachment at the position `(gW + d, t)` of the open right
stretch:
* if `e` lies in a chord `c ∈ S₂`, the regions of `S₂` above and below `c` are side labels;
* otherwise the regions of `S₂` faced just after (`cpA d`, parameter `t`) and just before
  (`cpA d` for `t > 0`, `cpB d` at a vertex) the counterpart position are side labels. -/
def LabTask : Prop :=
  ∀ (J : Merge.Junction) (Q : Polygon) (S₂ : Set ztf) (e : Set Point), J.P.Simple →
    (chainModel J.right).ChordFamily Q S₂ → (chainModel J.whole).ChordFamily Q ztbi →
    e ∈ F₂plus J S₂ → StopChord2 J S₂ e →
    ztwnd →
    ztwly →
    ∀ (d : ℕ) (t : ℝ), d < Lst J → 0 ≤ t → t < 1 → ztevv →
    SideAttach (chainModel J.whole).W e ztfq t →
    (∀ c ∈ S₂, e ⊆ c → ∀ Vu ∈ (chainModel J.right).regions S₂,
      ∀ Vd ∈ (chainModel J.right).regions S₂, SideOf ztj 1 c Vu →
      SideOf ztj (-1) c Vd → EvSideLab J S₂ {Vu, Vd} e) ∧
    (ztluu → ∀ Va ∈ (chainModel J.right).regions S₂,
      ∀ Vb ∈ (chainModel J.right).regions S₂, AfterFaces ztj ztbcq t Va →
      (0 < t → BeforeFaces ztj ztbcq t Vb) →
      (t = 0 → BeforeFaces ztj zterj 0 Vb) →
      EvSideLab J S₂ {Va, Vb} e)

/-! ## The faced regions (RAM) -/
def fpE : ℕ := sw 4110
def fpH : ℕ := sw 4111
def fqE : ℕ := sw 4112
def fqH : ℕ := sw 4113
def frA : ℕ := sw 4114
def frB : ℕ := sw 4115

/-- The registers the faced-region procedure may write. -/
def FRR (r : ℕ) : Prop :=
  ztgz ∨ r = frA ∨ r = frB ∨ ztph ∨
    ztbgd

/-- **The post of the faced regions**: `frA` is a region of `N₂` faced just after the position
`(fpE, fpH)` of the walk of `C₂`, `frB` one faced just before `(fqE, fqH)`. -/
def FaceROut (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c c' : Config) : Prop :=
  c'.nreg frA < N₂.nRegions ∧ c'.nreg frB < N₂.nRegions ∧
    AfterFaces ztj ztvjl
      ztync
      ztxhh ∧
    BeforeFaces ztj ztvjm
      ztynd
      ztwva ∧
    zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ FRR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task F: the faced regions** at two proper positions of the walk of `C₂` (the position is a
vertex or not a cut of `S₂`), cost `κ D (TLR + 1)`. -/
def FaceRTask : Prop :=
  ∃ (fr : Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      c.nreg fpE < (chainModel J.right).W.n →
      ProperPos ztj zta P.n ztcbp →
      ((chainModel J.right).param zta ztcbp = 0 ∨
        ¬ (chainModel J.right).IsCut ztwis
          ztymz) →
      c.nreg fqE < (chainModel J.right).W.n →
      ProperPos ztj zta P.n ztcbq →
      ((chainModel J.right).param zta ztcbq = 0 ∨
        ¬ (chainModel J.right).IsCut ztwis
          ztyna) →
      c.nreg ALLOC + κ zto * ztgf ≤ W →
      IRS P W c₀ fr c ztxen (FaceROut P J N₂ c)

/-! ## The brute-force shot at `N₁` (RAM) -/
def brOS : ℕ := sw 4080
def brOD : ℕ := sw 4083
def brF : ℕ := sw 4084

/-- The registers the brute-force shot may write. -/
def BrR (r : ℕ) : Prop :=
  ztgz ∨ (sw 4084 ≤ r ∧ r ≤ sw 4090) ∨ ztph ∨
    ztbgd

/-- **The post of the brute-force shot** from the point `z` in the direction `σ`: the flag `brF`;
if set, a proper walk position `(brF + 1, brF + 2)` of the model of `C₁` of a point of `C₁` or of
the box on the ray at a positive parameter, with its abscissa record at `brF + 3 … brF + 6`; if the
direction is free for `C₁`, the flag is set and the parameter is the first hit of `C₁`. -/
def BruteOut (P : Polygon) (J : Merge.Junction) (z : Point) (σ : ℝ) (c c' : Config) : Prop :=
  c'.nreg brF ≤ 1 ∧
    (c'.nreg brF = 1 → ∃ τ, 0 < τ ∧ OnCB J.left ztdpf ∧
      c'.nreg ztepo < (chainModel J.left).W.n ∧
      ProperPos ztbw zta P.n ztzid ∧
      (chainModel J.left).pos zta ztzid = rayPt z σ τ ∧
      AbsRec P c' ztnso (rayPt z σ τ).1 J.left.radius ∧
      (FreeAt J.left z σ → τ = J.left.hitParam z σ)) ∧
    (FreeAt J.left z σ → c'.nreg brF = 1) ∧
    zth ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ BrR r → r ≠ ALLOC → c'.nreg r = c.nreg r)

/-- **Task B: the brute-force shot** in the model of `C₁` at all arcs of `N₁` from the
symbolic point `s` in `brOS … brOS + 2` (off `C₁`, strictly inside the box, not above the top of
`C₁`) in the direction of code `brOD ≤ 1`, cost `κ (K₁ + 1) (F γ + 1)`. -/
def BruteTask : Prop :=
  ∃ (br : Stmt → Stmt) (κ : ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx)
    (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c₀ c : Config) (J : Merge.Junction)
    (N₁ N₂ : NF), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ → IInv W c₀ c →
      ∀ s : SymPt, SymPtIn c brOS s → s.Lt P.n → s.eval zta ∉ J.left.set →
      |(s.eval (Qof P)).1| < J.whole.radius → |(s.eval (Qof P)).2| < J.whole.radius →
      (s.eval zta).2 ≤ J.left.top.2 → c.nreg brOD ≤ 1 →
      c.nreg ALLOC + κ * ztfok * ztwju ≤ W →
      IRS P W c₀ ztqej c ztbapr
        ztbaoq
def stbSv : ℕ := sw 3990

/-- Save, inputs, clear the accumulator. -/
def stbPre : List Instr :=
  [.copyN stbSv ztwgg, .copyN ztuay ztwgh, .copyN ztuaz ztwgi,
    .copyN ztuba ztwgj, .copyN ztubb ztwgk,
    .copyN sO brOS, .copyN ztkep ztthc, .copyN ztkeq ztthd, .copyN qD brOD,
    .constN accA 0]

/-- Restore, outputs. -/
def stbPost : List Instr :=
  [.copyN ztwgg stbSv, .copyN ztwgh ztuay, .copyN ztwgi ztuaz,
    .copyN ztwgj ztuba, .copyN ztwgk ztubb,
    .copyN brF accA, .copyN ztepo ztbef, .copyN ztfpg ztcma,
    .copyN ztnso zthdm, .copyN zttgz ztnre, .copyN zttha ztnrf,
    .copyN ztthb ztnrg]

/-- **The brute-force shot of stage 2.** -/
def stbProg (sh : Stmt) : Stmt :=
  .seq (block stbPre) (.seq bLoop (.seq (symShot sh MD₁ SweepIo.bBase SweepIo.bN CD₁ K0) (block stbPost)))

/-- The cost constant. -/
def stbK : ℕ := 3 * bruteK + 100

/-- The registers written by `stbPre`. -/
def StbPreW (q : ℕ) : Prop :=
  (sw 3990 ≤ q ∧ q ≤ sw 3994) ∨ (sw 3231 ≤ q ∧ q ≤ sw 3233) ∨ q = qD ∨ q = accA
variable (m f : ℕ → ℕ) {W : ℕ}
theorem stbPre_val :
    (∀ i, i < 5 → regB m stbPre f ztubc = f ztrxg) ∧
    regB m stbPre f sO = f brOS ∧ regB m stbPre f ztkep = f ztthc ∧
    regB m stbPre f ztkeq = f ztthd ∧ regB m stbPre f qD = f brOD ∧
    regB m stbPre f accA = 0 ∧
    (∀ q, ¬ StbPreW q → regB m stbPre f q = f q) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · interval_cases i <;> simp [stbPre, regB, regI, upd, stbSv, sO, qD, accA, brOS, brOD, sw]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  zunn
  simp only [stbPre, List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold StbPreW at hq
  simp only [qD, accA, sw] at hq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dstI, stbSv, sO, qD, accA, sw] <;> omega
theorem stbPre_ok (m f : ℕ → ℕ) : okB W m stbPre f := by
  have s : ztwrf := fun j h1 h2 =>
    iscr_sw ztce ztce
  simp only [stbPre, okB, okI]
  refine ⟨s 3990 by_norm_num by_norm_num, s 3991 by_norm_num by_norm_num,
    s 3992 by_norm_num by_norm_num, s 3993 by_norm_num by_norm_num,
    s 3994 by_norm_num by_norm_num, s 3231 by_norm_num by_norm_num,
    s 3232 by_norm_num by_norm_num, s 3233 by_norm_num by_norm_num,
    s 3212 by_norm_num by_norm_num, ⟨s 2000 by_norm_num by_norm_num, Nat.zero_le _⟩,
    trivial⟩

/-- The registers written by `stbPost`. -/
def StbPostW (q : ℕ) : Prop := (sw 4001 ≤ q ∧ q ≤ sw 4005) ∨ (brF ≤ q ∧ q ≤ brF + 6)
theorem stbPost_val :
    (∀ i, i < 5 → regB m stbPost f ztrxg = f ztubc) ∧
    regB m stbPost f brF = f accA ∧ regB m stbPost f ztepo = f ztbef ∧
    regB m stbPost f ztfpg = f ztcma ∧
    (∀ j, j < 4 → regB m stbPost f (brF + 3 + j) = f (accA + 4 + j)) ∧
    (∀ q, ¬ StbPostW q → regB m stbPost f q = f q) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, fun j hj => ?_, fun q hq => ?_⟩
  · interval_cases i <;> zuneu
  · rfl
  · rfl
  · rfl
  · interval_cases j <;> zuneu
  zunn
  simp only [stbPost, List.mem_cons, List.not_mem_nil, or_false] at hi
  unfold StbPostW at hq
  simp only [brF, sw] at hq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dstI, brF, sw] <;> omega
theorem stbPost_ok (m f : ℕ → ℕ) : okB W m stbPost f := by
  have s : ztwrf := fun j h1 h2 =>
    iscr_sw ztce ztce
  simp only [stbPost, okB, okI]
  refine ⟨s 4001 by_norm_num by_norm_num, s 4002 by_norm_num by_norm_num,
    s 4003 by_norm_num by_norm_num, s 4004 by_norm_num by_norm_num,
    s 4005 by_norm_num by_norm_num, s 4084 by_norm_num by_norm_num,
    s 4085 by_norm_num by_norm_num, s 4086 by_norm_num by_norm_num,
    s 4087 by_norm_num by_norm_num, s 4088 by_norm_num by_norm_num,
    s 4089 by_norm_num by_norm_num, s 4090 by_norm_num by_norm_num, trivial⟩

/-- The cost bound. -/
theorem stb_cost (A K Fg : ℕ) (hA : A ≤ 3 * K + 1) :
    10 + (bLoopK A + (symShotK Fg A + 12)) ≤ stbK * ztbr * ztclk := by
  have h := brute_cost A Fg
  have h2 : bruteK * ztbo * ztclk ≤ bruteK * ztzst * ztclk :=
    Nat.mul_le_mul ztdfv le_rfl
  have e : stbK * ztbr * ztclk =
      bruteK * ztzst * ztclk + 100 * (ztbr * ztclk) := by
    unfold stbK; ring
  have h3 : 1 ≤ ztbr * ztclk := Nat.one_le_iff_ne_zero.2 by_positivity
  omega
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **Task B: the brute-force shot at `N₁`.** -/
theorem bruteTask : BruteTask := by
  refine ⟨stbProg, stbK, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI s hs hsl hzC hz1 hz2 hzt hd hroom
  have hP : J.left.P.Simple := E.hP
  have hNF := E.hNF₁
  have hAr := arcsTask J.left zta N₁ hP hNF
  have hcost := stb_cost N₁.arcs.length N₁.nChords ztwiu hAr
  zufxc
  obtain ⟨pv, p1, p2, p3, p4, p5, po⟩ := stbPre_val c.nmem c.nreg
  unfold stbProg
  refine (IRS.seq (K₁ := 10) (K₂ := bLoopK N₁.arcs.length +
      (symShotK ztwiu N₁.arcs.length + 12))
    ((IRS.block stbPre hI (stbPre_ok _ _)).mono by_rfl ztb) ?_).mono
    hcost ztb
  zufg
  simp only at hA₁ hA₁'
  have eA1 : regB c.nmem stbPre c.nreg ALLOC = c.nreg ALLOC :=
    po _ (by unfold StbPreW; decide)
  -- the chain context of `C₁` at `sw 20`
  obtain ⟨H₀, hJ₀, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, d20, w20, -⟩ := hst
  have hctx20 : ChainCtx P W { c with nreg := regB c.nmem stbPre c.nreg } (sw 20) J.left :=
    (chainCtx_of E.hG E.hWh hP hJ₀ E.hJWF d20 w20).transport
      zttml ztnyl hI₁.hA
  have hNW : NFWithin ({ c with nreg := regB c.nmem stbPre c.nreg } : Config).nmem
      ztxnx ztdq N₁ :=
    E.hNW₁.transport ztnyl
  refine IRS.seq (bLoop_irs hI₁ E.hK hctx20 hP hNF hNW zttml
    hI₁.hA by_linarith) ?_
  rintro c₂ hI₂ hA₂ hA₂' hBW
  zucig
  simp only at w1 w6 w7 w8 w9 hA₂ hA₂'
  rw [eA1] at w1 w6 w7 w8 hA₂ hA₂'
  have keep : ∀ j, j < 10000 → ¬ BSet ztgc →
      c₂.nreg ztgc = regB c.nmem stbPre c.nreg ztgc := fun j hj hb =>
    w9 _ zttua hb ztbpx
  have hs2 : SymPtIn c₂ sO s := by
    refine symPtIn_copy hs ?_ ?_ ?_
    · rw [show sO = sw 3231 from rfl, keep 3231 by_norm_num ztbfz]
      exact p1
    · rw [show sO + 1 = sw 3232 from rfl, keep 3232 by_norm_num ztbfz]
      exact p2
    · rw [show sO + 2 = sw 3233 from rfl, keep 3233 by_norm_num ztbfz]
      exact p3
  have d2 : c₂.nreg qD = c.nreg brOD := by
    rw [show qD = sw 3212 from rfl, keep 3212 by_norm_num ztbfz]
    exact p4
  have a2 : ztpnl := by
    rw [show accA = sw 2000 from rfl, keep 2000 by_norm_num ztbfz]
    exact p5
  have hacc : AccOK P accA ztrpq J.left.radius ztwpu
      ztjty ∅ c₂ := accOK_init _ _ _ _ _ a2
  zuhef
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI₂
  obtain ⟨-, -, -, ⟨H, hCD, hreg⟩, -, -⟩ := E.ctx1' hI₂
  have hmd : MdFacts P c₂ (c₂.nreg MD₁) H J.left := ⟨md3, by_simp_all, md2, md1⟩
  have hzD : s.eval zta ∈ J.left.dom := mem_dom_of J.left hzt hz1 hz2 hzC
  have hN1 : c₂.nreg SweepIo.bN = N₁.arcs.length := w4
  have harcs : ∀ j, j < c₂.nreg SweepIo.bN →
      ShotList.PieceOK ztbw zta P.n (ShotList.arcAt c₂.nmem ztmie j) ∧
      (chainModel J.left).arcWt
        ((chainModel J.left).key zta (ShotList.arcAt c₂.nmem ztmie j).1)
        ((chainModel J.left).key zta (ShotList.arcAt c₂.nmem ztmie j).2) ≤
        c₀.nreg ztbcb := by
    zun
    zuels

    exact nArc_piece hP hNF E.hsg₁ hj
  have hss := symShot_irs (C := J.left) (H := H) (md := MD₁) (base := SweepIo.bBase)
    (cnt := SweepIo.bN) (dsc := CD₁) (tg := K0) (Mod := fun _ => J.left) (R₀ := J.left.radius)
    (L := ∅) (s := s) (z := s.eval zta) E.hsh E.hBs E.hXl hI₂ E.hK E.hG E.hWh E.hX E.hcap E.hOk₁
    hmd hreg ztuxu harcs by_omega hs2 hsl rfl hzD hz1 hz2 hzt
    hacc (by rw [hK2.1]; omega) rfl rfl
    ⟨sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num,
      sregOK_sw by_norm_num by_norm_num by_norm_num⟩
    (by rw [hN1]; omega)
  rw [hN1] at hss
  refine IRS.seq (K₁ := symShotK ztwiu N₁.arcs.length) (K₂ := 12) hss ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨L', hacc', hL', hcomp, k3, hA3, hm3⟩
  rw [d2] at hacc' hL' hcomp
  refine (IRS.block stbPost hI₃ (stbPost_ok _ _)).mono by_rfl ?_
  zuu
  obtain ⟨qv, q0, q1, q2, q3, qo⟩ := stbPost_val c₃.nmem c₃.nreg
  unfold BruteOut
  zubi
  set σ := dirOf ztqip with hσ
  set z := s.eval zta with hzd
  -- the exit point lies on the arcs
  have hexit : FreeAt J.left z σ → rayPt z σ ztnlt ∈
      ShotList.loSet ztbw zta c₂.nmem ztmie N₁.arcs.length [] := by
    zuhgo
    obtain ⟨p, t, hp, ht0, ht1, ⟨j, hj, hin⟩, hpt⟩ :=
      exit_in_arcs J.left hP hNF (Q := Qof P) (SweepPrim.dirOf_cases _) hzt hf
    refine ⟨p, t, hp, ht0, ht1, ztdqs, fun g hg => absurd hg
      (List.not_mem_nil), hpt.symm⟩
    zupl

  have hmem : FreeAt J.left z σ → J.left.hitParam z σ ∈ L' := fun hf => hcomp hf (hexit hf)
  obtain ⟨f1, f0, fs⟩ := hacc'
  have hA3' : regB c₃.nmem stbPost c₃.nreg ALLOC = c₃.nreg ALLOC :=
    qo _ (by unfold StbPostW ALLOC brF sw; omega)
  refine ⟨by_omega, fun h1 => ?_, fun hf => ?_, fun a ha => ?_, ?_, ?_⟩
  · rw [q0] at h1
    obtain ⟨τ, hτ, hmin, -, hpp, he, hpos, hrec⟩ := fs h1
    rcases hL' with rfl | ⟨τ₀, rfl, hτ0, hon⟩
    · exact absurd hτ (Set.notMem_empty _)
    · have eτ : τ = τ₀ := by simpa using hτ
      subst eτ
      refine ⟨τ, hτ0, hon, by_grind, by_grind,
        by grind, ?_, fun hf => ?_⟩
      · zujex
        · rfl
        · rfl
        · rfl
        rfl
      · have := hmem hf
        simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at this
        grind
  · rw [q0]
    have hne : L' ≠ ∅ := fun h => by zvmwc at hmem; exact Set.notMem_empty _ (hmem hf)
    grind
  · rw [hm3 a by_omega, w8 a by_omega]
  · omega
  · intro r hr hb hra
    unfold BrR at hb
    by_cases hp : StbPostW r
    · have hr4 : 244001 ≤ r ∧ r ≤ 244005 := by
        unfold StbPostW brF at hp; unfold sw at hp hb; omega
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < 5 ∧ r = sw 4001 + i :=
        ⟨r - 244001, by_omega, by unfold sw; omega⟩
      have esv : stbSv + i = sw ztngg := by unfold stbSv sw; omega
      rw [qv i hi, k3 _ (by rw [esv]; exact nb ztngg by_omega)
        (by unfold RS stbSv sw; omega) (by unfold accA stbSv sw; omega)
        (by unfold ALLOC stbSv sw; omega)]
      rw [esv, keep ztngg by_omega ztbfz, ← esv]
      exact pv i hi
    · zuixn
      unfold sw at hb'
      have e1 : ¬ ztbmg := by unfold RS; omega
      have e2 : r < accA ∨ accA + 12 < r := by unfold accA sw; omega
      have e3 : ¬ BSet r := by unfold BSet; unfold StbPostW brF at hp; unfold sw at hb hp ⊢; omega
      rw [qo r hp, k3 r hr e1 e2 hra, w9 r hr e3 hra]
      exact po r (by unfold StbPreW qD accA; unfold sw at hb ⊢; omega)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
section Math
variable {J : Merge.Junction}
theorem stp_gW_lt : gW J < (chainModel J.whole).W.n := by
  have := tpos_lt J.whole J.m₁
  rw [cm_n J.whole]; unfold gW; omega

/-- **The chord seen from a point of `C₂` is attached on the `C₁` part only at its far end.** -/
theorem attach_far (hP : J.P.Simple) {a : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hfree : FreeAt J.whole a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W ztxc p t)
    (hoff : (Lst J : ℝ) ≤ oW J ztk) :
    sidePt (chainModel J.whole).W p t = rayPt a σ zton := by
  zunw
  have ha2 := J.whole.snd_le_top_of_mem_set ztmbj
  obtain ⟨hτ, -, hint⟩ := Merge.hit_of_freeAt J.whole ha2 hσ hfree
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1,
      lerp a _ s ∈ (chainModel J.whole).D := fun s hs => by
    zugwa
    exact hint _ ztttt by_simp_all
  zuebs
  · exfalso
    have := off_right_pt J hP ztzi finite_empty hA.1 hA.2.1 hA.2.2.1
      by_simp_all by_simp_all
    zudbd
    grind
  omega

/-- **A non-stop chord from an end of a chord of `S₂` on `C₂`, attached beyond the start, ends
strictly before the far end of that chord.** -/
theorem whole_lt_right (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hfree : FreeAt J.whole a σ)
    (hns : ¬ StopChord2 J S₂ ztxc) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W ztxc p t)
    (hoff : (Lst J : ℝ) < oW J ztk) :
    J.whole.hitParam a σ < J.right.hitParam a σ := by
  zune
  obtain ⟨-, ha₂, -, hR, hl2, hr2⟩ := right_hit_end ztbac ha
  have hle : J.whole.hitParam a σ ≤ J.right.hitParam a σ := by
    rw [whole_hitParam_eq_min J ztoct hσ, right_hitParam_eq J ha₂]
    simp
  zujfc
  have ha2 := le_trans ha₂ J.right_top_le
  obtain ⟨hτ, hwD, -⟩ := Merge.hit_of_freeAt J.whole ha2 hσ hfree
  have hpt := attach_far hP hσ haR hav hfree hA hoff.le
  have hAdm :=
    F₂plus_subset J hS₂ (shoot_end_mem hc ha hfree)
  set τ := J.whole.hitParam a σ with hτd
  -- the far end of `c`
  obtain ⟨b, σ', hσ', hb, hwb⟩ : ∃ (b : Point) (σ' : ℝ), σ' = -σ ∧
      ((σ' = 1 ∧ b = Merge.lend c) ∨ (σ' = -1 ∧ b = Merge.rend c)) ∧ rayPt a σ τ = b := by
    zuht
    · refine ⟨Merge.rend c, -1, rfl, by_simp_all, point_ext ?_ ?_⟩
      · simp_all
      rfl
    · refine ⟨Merge.lend c, 1, by_norm_num, by_simp_all, point_ext ?_ ?_⟩
      · simp_all
      rfl
  have hbmem : ztrfx := by
    rw [← hwb]; exact Chazelle.Geometry.right_mem_segment _ _
  have hbD : b ∉ J.whole.dom := by_simp_all
  by_cases hbR : b ∈ J.right.set
  · by_cases hbv : b = J.shared
    · rw [hbv] at hbmem hbD
      zudru
      exact hns ztzco
    · have := off_right_pt J hP ztzi finite_empty hA.1 hA.2.1 hA.2.2.1
        by_simp_all by_simp_all
      zudbd
      grind
  · zudru
    -- the direction from `b` is back towards `a`
    have hb2 : b.2 ≤ J.whole.top.2 := by_grind
    obtain ⟨hτ'', -, -⟩ := Merge.hit_of_freeAt J.whole hb2 hσ'' hfr
    have haIn := he ▸ origin_mem J
    unfold Merge.shoot at haIn
    obtain ⟨s, hs0, hs1, has⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 haIn
    rw [lerp_rayPt] at has
    have hx := congrArg Prod.fst has
    rw [rayPt_fst] at hx
    have hb1 : b.1 = a.1 + σ * τ := by_grind
    generalize J.whole.hitParam b σ'' = τ'' at hx hτ''
    have hσσ : σ'' = σ' := by
      rw [hσ']
      rcases hσ with rfl | rfl <;> rcases hσ'' with rfl | rfl
      · zukkc
      · norm_num
      · norm_num
      · zukkc
    rw [hσσ] at hfr he
    exact hns (Or.inl ztbmd)
end Math
section Iter
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- The registers kept by the window computation. -/
theorem stp_win_keep (hregW : ∀ r, bandOf r ∉ oracleBands → ¬ WR r → r ≠ ALLOC → cw.nreg r = c.nreg r)
    {k : ℕ} (hk : ztcky ∨ ztgys ∨ ztgyv ∨
      ztdfa) : cw.nreg (sw k) = c.nreg (sw k) :=
  hregW _ ztzdj (by unfold WR sw; omega)
    ztbpx

/-- The registers kept by the reset and the batch of origins. -/
theorem stp_batch_keep (hR : ResetRel cw cs)
    (hregB : ∀ r, bandOf r ∉ oracleBands → ¬ OrgR r → ¬ LR r → r ≠ ALLOC → co.nreg r = cs.nreg r)
    {k : ℕ} (hk : ztcky ∨ (2400 ≤ k ∧ k ≤ 2409) ∨ (2418 ≤ k ∧ k ≤ 2459) ∨
      ztdfa) : cs.nreg (sw k) = cw.nreg (sw k) ∧ co.nreg (sw k) = cw.nreg (sw k) := by
  have h1 : cs.nreg _ = cw.nreg ztcbe :=
    hR.2.2.2 _ ztozh ztozj
  refine ⟨h1, (hregB _ ztzdj ?_ ?_
    ztbpx).trans h1⟩
  · unfold OrgR CandR BestR LblR bF bE bH bN bL sw; omega
  · unfold LR oK oS sw; omega

/-- **No cut before the candidates (core)**: a chord of `F₂⁺` attached beyond the key of `c`, with
no cut strictly between the key and it, is a stop not yet passed, or is accepted (so the best
candidate is at or before it), or lies beyond the window end. -/
theorem no_cut_core (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs)
    (hB : BatchInv P J N₂ cs
      ztwro
      zthib co)
    {e : Set Point} (he : e ∈ F₂plus J ztwis) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J ztk)
    (hgap : ∀ e' ∈ F₂plus J ztwis, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e' q s →
        ¬ ztxij) :
    (∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i = oW J ztk) ∨
    ztxnp ∨
    ztxnr := by
  zuxz

  -- a stop chord at the position is a stop not yet passed
  have stopCase : ∀ s ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W s p t → StopChord2 J S₂ s →
      ∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i = oW J ztk := by
    intro s hs hsA hss
    obtain ⟨rs, ax, hlen, -, hrec, -, hok, -⟩ := L.stops
    have hmem := hok.2.1 s hs hss p t hsA hLst.le
    zucod
    zuep
    simp only [Prod.mk.injEq] at hreq
    obtain ⟨h1, h2, -⟩ := hreq
    zutg

    have hoff : ztyly := by
      show offK P J ztggy ztggy = _
      zucpp
      show oW J ztxfr = _
      simp_all
    have hic : ztizv := by_omega
    refine ⟨i, ?_, hic, hoff⟩
    by_contra hlt'
    push Not at hlt'
    have := (L.ptrL i hic).1 hlt'
    grind
  by_cases hst : StopChord2 J S₂ e
  · grind
  obtain ⟨ch, hch, a, σ, ha, haR, hav, hat, hfree, rfl, hsrc⟩ :=
    nonstop_found hP hS₂ hF L.keyL L.inv hA.1 hA.2.1 hA.2.2.1 hlt hgap he hA hst
  rcases hsrc with ⟨V, hV, hVΛ, hT⟩ | ⟨s, hs, hsA, hss, -⟩
  swap
  · grind
  by_cases hwin : cw.nreg wX = 0 ∧ offK P J ztjsz ztjta < oW J ztk
  · grind
  zuhl
  zune
  zubwl

  have hnv : ztlyt := by
    zuq
    zukdp
    have hvD := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd ztffl
    zucyf

  have ha₁ : a.2 ≤ J.left.top.2 := by
    zuevg
    · grind
    grind
  zuboo
  -- the endpoint query
  obtain ⟨i, hi, hci⟩ := Restore.mem_F_iff hch
  obtain ⟨j, hj, hji, hjO, hjD⟩ : ∃ j, j < 2 * N₂.nChords ∧ (∃ s, s ≤ 1 ∧ j = 2 * i + s) ∧
      endOrigin J _ N₂ j = a ∧ endDir j = σ := by
    unfold endOrigin endDir
    zuht
    · refine ⟨2 * i, by_omega, by_grind, ?_, ?_⟩
      · rw [ite_eq_left by_omega, show 2 * i / 2 = i by omega, ← hci]
      simp
    · refine ⟨2 * i + 1, by_omega, by_grind, ?_, ?_⟩
      · rw [ite_eq_right by_omega, show ztmj / 2 = i by omega, ← hci]
      simp
  -- the registers through the window, the reset and the batch
  obtain ⟨rs₁, -, -, hgk, -, -, -, -, -, hcov, -, hregW⟩ := hW
  zuni

  have ekE : ztizg := (kB by_omega).1.trans zteah
  have ekH : ztizh := (kB by_omega).1.trans zteah
  have ekN : ztmuy := (kB by_omega).1.trans zteah
  have ekL : ztkpd := fun u hu => by
    have := (kB (k := 2403 + u) by_omega).1.trans zteah
    zudgg
  have egN : ztmux := (kB by_omega).1.trans zteah
  have egR : ztkpc := fun u hu => by
    have := (kB (k := 2441 + u) by_omega).1.trans zteah
    zudgf
  have eGB : ztsft := (kB by_omega).1
  have eGK : ztsfu := (kB by_omega).1
  -- the query is tried in this iteration
  zuhxi
  have hreg : ∀ l, l < N₂.nRegions → regOf ztj zta N₂ l = V →
      j ∈ regO N₂ l := by
    zumhe
    refine ⟨i, ((hRO l hl).1 i).2 ztfwp, hji⟩
    grind
  have hjO' : ztsju := by
    zuflm
    · obtain ⟨u, hu, hu4, rfl⟩ : ztfxp := by
        zucyr
        · exact ⟨0, h.1, by_norm_num, by_grind⟩
        · exact ztoll
        · exact ztolq
        · exact ztolr
      zueke

    · zuxp

  -- the hit is on the gathered arcs
  have hoffd : ztxmk := by
    zucjz

  have hlo : rayPt a σ zton ∈
      ShotList.loSet ztbw zta cs.nmem ztcpv ztdzq [] := by
    have hin := hcov d t hMV hA.2.1 hA.2.2.1 ztntx (fun h0 => by
      grind)
    zudfv

  -- accepted, so the best candidate is at or before it
  obtain ⟨h, hh, hmA⟩ := hBA.comp j hjO' hj ⟨by_grind, by_grind,
    by grind⟩ p t by_grind by_grind hLst
    hnv by_grind by_grind
  have hoT : offT P J ztjzc = oW J ztk := by
    show oW J (p + (chainModel J.whole).param _ ztnk) = _
    zumnh
  obtain ⟨hbF, hle⟩ := hBA.bMin _ hmA ztjqd
  zubfo

/-- **No cut before the candidates**: every chord of `F₂⁺` attached beyond the key of `c` is
attached at or after a stop not yet passed, or at or after the best candidate, or strictly after
the window end. -/
theorem no_cut_between (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs)
    (hB : BatchInv P J N₂ cs
      ztwro
      zthib co)
    {e : Set Point} (he : e ∈ F₂plus J ztwis) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J ztk) :
    (∃ i, c.nreg sP ≤ i ∧ i < c.nreg sC ∧ stopOff P J c i ≤ oW J ztk) ∨
    ztxnp ∨
    ztxnr := by
  classical
  zuinz
  have hM : ztezg := FactsChain.walkAx J.whole E.hP
  have hF := F₂plus_chordFamily E
  set K := {x : ℝ | (chainModel J.whole).IsCut _ x ∧ keyOff P J c < oW J x} with hK
  have hKf : K.Finite := (hM.finite_cuts hF.2.1 hF.1).subset fun x hx => hx.1
  have hKm : ztdj ∈ K := ⟨zteyg, hlt⟩
  obtain ⟨x, ⟨⟨e', he', p', t', hA', rfl⟩, hx⟩, hmin⟩ := Set.exists_min_image K (oW J) hKf ⟨_, hKm⟩
  have hle : oW J _ ≤ oW J _ := hmin _ hKm
  have hgap : ∀ e'' ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e'' q s →
      ¬ (keyOff P J c < oW J ztej ∧ oW J ztej < oW J ztjg) := by
    rintro e'' he'' q s hq ⟨h1, h2⟩
    exact absurd (hmin _ ⟨⟨e'', he'', q, s, hq, rfl⟩, h1⟩) ztquc
  rcases no_cut_core E L hW hR hB he' hA' hx hgap with ⟨i, h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · grind
  · grind
  · grind

/-- The facts of an iteration seen at the configuration after the origins: the stop pointer and
the stops, the window. -/
theorem iter_stops (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') :
    co.nreg sP = c.nreg sP ∧ co.nreg sC = c.nreg sC ∧
    (∀ i, i < c.nreg sC → stopOff P J co i = stopOff P J c i) ∧
    co.nreg wX = cw.nreg wX ∧ co.nreg wE = cw.nreg wE ∧ co.nreg wH = cw.nreg wH := by
  zueio
  zubpi
  zuni

  have esP : ztsfm := (kB by_omega).2.trans zteah
  have esC : ztsfl := (kB by_omega).2.trans zteah
  have esB : ztmuw := (kB by_omega).2.trans zteah
  have eTB : ztguj := (kB by_omega).1.trans zteah
  have eAs : ztfkw := hR.2.2.2 _ by_decide
    by_decide
  have hmem : ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x → co.nmem x = c.nmem x := by
    zueth
    rw [hBA.memT x by_omega by_omega, hR.1, hmW x hx]
  zufgv

  refine ⟨esP, esC, fun i hi => ?_, (kB by_omega).2,
    (kB by_omega).2, (kB by_omega).2⟩
  unfold stopOff stopE stopH
  grind

/-- **No cut strictly between the key of an iteration and the next key** (Task L1, step 1). -/
theorem no_cut_iter (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') :
    NoCutIn J ztwis ztbnc ztcnt := by
  rintro x ⟨e, he, p, t, hA, rfl⟩ - - ⟨h1, h2⟩
  obtain ⟨esP, esC, est, ewX, ewE, ewH⟩ := iter_stops L hI
  zubro
  zufif
  rcases no_cut_between E L hW hR hB he hA h1 with ⟨i, hi1, hi2, hi3⟩ | ⟨hbF, hb⟩ | ⟨hwX, hw⟩
  · obtain ⟨-, -, -, hKs, -⟩ := hK4 by_omega
    have h3 := hKs by_omega
    rw [esP] at h3
    change keyOff P J c' ≤ stopOff P J co _ at h3
    rw [est _ by_omega] at h3
    have h4 := L.sorted _ i hi1 hi2
    grind
  · obtain ⟨-, -, hKb, -⟩ := hK4 (Or.inl hbF)
    exact absurd ((hKb hbF).trans hb) ztquc
  · obtain ⟨-, -, -, -, hKw, -⟩ := hK4 by_omega
    have h3 := hKw by_omega
    rw [ewE, ewH] at h3
    exact absurd (h3.trans hw.le) ztquc

/-- **No cut after the last key** (Task L2, `DoneNoCut`): when the iteration finishes, no cut lies
beyond the key. -/
theorem no_cut_done (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 1) :
    NoCutIn J ztwis ztbnc (chainModel J.whole).W.n := by
  rintro x ⟨e, he, p, t, hA, rfl⟩ - - ⟨h1, -⟩
  obtain ⟨esP, esC, -, ewX, -, -⟩ := iter_stops L hI
  zubro
  zufif
  have hnone : ¬ (co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0) := by_grind
  rcases no_cut_between E L hW hR hB he hA h1 with ⟨i, hi1, hi2, -⟩ | ⟨hbF, -⟩ | ⟨hwX, -⟩
  · omega
  · omega
  omega
end Iter
theorem doneNoCut : DoneNoCut := by
  zucnj
  exact no_cut_done E hL hIt hd

/-- **Task L2: the last iteration.** -/
theorem doneTask : DoneTask := doneTask_of doneNoCut
theorem sweepEvSpec_of_rest (hStop : StopTask) (hWin : WinTask) (hKey : KeyTask)
    (hL0 : LoopStartTask) (hL1 : StepTask) : SweepEvSpec :=
  sweepEvSpec_of asmTask initTask genTask hStop hWin orgsTask hKey prepTask hL0 hL1 doneTask
    regArcsTask countTask
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- **The window and the reset** keep the loop registers and the memory below the allocator. -/
theorem stp_pre_frame (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) :
    (∀ k, ztcky ∨ ztgys ∨ ztgyv ∨
      ztdfa → cs.nreg ztcbe = c.nreg ztcbe) ∧
    (∀ x, x < c.nreg ALLOC → cs.nmem x = c.nmem x) ∧
    cs.nreg wGB = cw.nreg wGB ∧ cs.nreg wGK = cw.nreg wGK := by
  zubpi
  refine ⟨fun k hk => ?_, fun x hx => by rw [hR.1, hmW x hx], ?_, ?_⟩
  · rw [hR.2.2.2 _ ztozh ztozj]
    exact stp_win_keep hregW hk
  · zulfh
  · zulfh

/-- **A stop chord attached on the `C₁` part is a stop record.** -/
theorem stp_stop_at (L : LoopInv P J N₁ N₂ c₀ c) {s : Set Point}
    (hs : s ∈ F₂plus J ztwis)
    (hss : StopChord2 J ztwis s) {p : ℕ} {t : ℝ}
    (hsA : SideAttach (chainModel J.whole).W s p t) (hL : (Lst J : ℝ) ≤ oW J ztk) :
    ∃ rs ax, StopData P J N₂ c rs ax ∧ ∃ i, ∃ hi : i < rs.length, rs[i].1 = p ∧
      (chainModel J.whole).param zta ztcyg = t ∧
      stopSet J zta N₂ rs[i].2.2.1 rs[i].2.2.2.1 rs[i].2.2.2.2 = s ∧
      i < c.nreg sC ∧ stopOff P J c i = oW J ztk := by
  zucxz
  obtain ⟨hlen, -, hrec, -, hok, -⟩ := id hD
  have hmem := hok.2.1 s hs hss p t hsA hL
  zucod
  zuep
  zudlk

  zutg

  have hoff : ztyly := by
    show offK P J ztggy ztggy = _
    zucpp
    show oW J ztxfr = _
    simp_all
  grind

/-- **Every stop record is a cut** of `F₂⁺` on the `C₁` part. -/
theorem stp_stop_cut (L : LoopInv P J N₁ N₂ c₀ c) {i : ℕ} (hi : i < c.nreg sC) :
    ∃ e ∈ F₂plus J ztwis, ∃ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W e p t ∧ stopOff P J c i = oW J ztk ∧
      StopChord2 J ztwis e := by
  zucxz
  obtain ⟨hlen, -, hrec, -, hok, -⟩ := hD
  zufuv
  have hmem : (stopsOf J _ N₂ rs)[i]'(by simpa [stopsOf] using hi') ∈
      stopsOf J zta N₂ rs := List.getElem_mem _
  obtain ⟨h1, h2, h3, -⟩ := hok.1 _ hmem
  obtain ⟨e0, e1, -⟩ := hrec i hi'
  rw [List.getD_eq_getElem _ _ hi'] at e0 e1
  refine ⟨_, h1, _, _, h3, ?_, h2⟩
  show offK P J ztggy ztggy = _
  zucpp
  zumpo
  rfl

/-- **The stops at the first cut beyond the key** are the stops `sP` and `sP + 1`. -/
theorem stp_stop_near (L : LoopInv P J N₁ N₂ c₀ c) {o : ℝ} (ho : keyOff P J c < o)
    (hgap : ∀ e ∈ F₂plus J ztwis, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ ztxof)
    {i : ℕ} (hi : i < c.nreg sC) (hio : stopOff P J c i = o) :
    i = c.nreg sP ∨ i = c.nreg sP + 1 := by
  have hpi : c.nreg sP ≤ i := by
    zumv
    have := (L.ptrL i hi).1 by_omega
    linarith
  -- every stop from `sP` to `i` is at `o`
  have hat : ∀ i', c.nreg sP ≤ i' → i' ≤ i → stopOff P J c i' = o := by
    intro i' h1 h2
    have hi' : i' < c.nreg sC := by_omega
    have hgt : keyOff P J c < stopOff P J c i' := by
      zumv
      have := (L.ptrL i' hi').2 ztmmq
      omega
    have hle := hio ▸ L.sorted i' i h2 hi
    obtain ⟨e, he, q, s, hA, hq, -⟩ := stp_stop_cut L hi'
    grind
  zuct
  have h2 : c.nreg sP + 2 ≤ i := by_omega
  have := L.two ztccy by_omega
  simp_all

/-- **The chord of `S₂` of a non-stop chord at the first cut beyond the key is tried** in the
iteration: it touches a region of the label set or a gap region (`regO`), or contains a stop chord
at the cut, the stop `sP` or `sP + 1` (`parO`). -/
theorem stp_query_tried (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) {o : ℝ} (ho : keyOff P J c < o)
    (hgap : ∀ e ∈ F₂plus J ztwis, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e q s → ¬ ztxof)
    {pK : ℕ} {tK : ℝ} (hoK : oW J ztkm = o) {ch : Set Point}
    (hch : ch ∈ N₂.F ztj zta)
    (hsrc : (∃ V ∈ (chainModel J.right).regions ztwis,
        (V ∈ curLab P J N₂ c ∨ GapLab J ztwis V) ∧
          Chazelle.Chain.TouchesIn (chainModel J.right).D ch V) ∨
      (∃ s ∈ F₂plus J ztwis,
        SideAttach (chainModel J.whole).W s pK tK ∧
          StopChord2 J ztwis s ∧ s ⊆ ch)) :
    ∃ k, k < N₂.nChords ∧ (N₂.chord k).toSet ztj zta = ch ∧
      ∀ s, s ≤ 1 → 2 * k + s ∈ iterO N₂ cs := by
  zueiq
  have ekN : ztmuy := hkp 2402 by_omega
  have ekL : ztkpd := fun u hu => by
    have := hkp (2403 + u) by_omega
    zudgg
  have egN : ztmux := hkp 2440 by_omega
  have egR : ztkpc := fun u hu => by
    have := hkp ztssu by_omega
    zudgf
  rcases hsrc with ⟨V, -, hVΛ, hT⟩ | ⟨s₀, hs₀, hsA, hss, hsub⟩
  · obtain ⟨k, hk, hci⟩ := Restore.mem_F_iff hch
    refine ⟨k, hk, hci.symm, fun s hs => ?_⟩
    zuhxi
    have hreg : ∀ l, l < N₂.nRegions → regOf ztj zta N₂ l = V →
        2 * k + s ∈ regO N₂ l := by
      zumhe
      refine ⟨k, ((hRO l hl).1 k).2 ztuhq, s, hs, rfl⟩
      simp_all
    zuflm
    · obtain ⟨u, hu, hu4, rfl⟩ : ztfxp := by
        zucyr
        · exact ⟨0, h.1, by_norm_num, by_simp_all⟩
        · exact ztoll
        · exact ztolq
        · exact ztolr
      zueke

    · zuxp

  · -- the parent of a stop at the cut
    have hL : (Lst J : ℝ) ≤ oW J ztkm := by rw [hoK]; linarith [L.keyL]
    obtain ⟨rs, ax, hD, i, hi, -, -, hset, hic, hio⟩ := stp_stop_at L hs₀ hss hsA hL
    have hnear := stp_stop_near L ho hgap hic (hio.trans hoK)
    obtain ⟨-, hax, -, hrecA, -, -, hauxOK, -⟩ := hD
    have hiA : i < ax.length := by_omega
    have hok := hauxOK i hi
    rw [List.getD_eq_getElem _ _ hi, hset, List.getD_eq_getElem _ _ hiA] at hok
    obtain ⟨-, -, -, -, -, -, hparle, hpar, -⟩ := hok
    obtain ⟨hpar0, hpch⟩ := hpar ch hch hsub
    obtain ⟨-, -, -, -, e4⟩ := hrecA i hiA
    rw [List.getD_eq_getElem _ _ hiA] at e4
    have esP : ztsfs := hkp 2450 by_omega
    have esC : ztsfr := hkp 2601 by_omega
    have eaB : ztsfq := hkp 2602 by_omega
    have hlay5 := L.lay5
    have hpo : parOf cs i = ax[i].2.2.2.2 := by
      unfold parOf
      grind
    refine ⟨ax[i].2.2.2.2 - 1, by_omega, hpch, fun s hs => Or.inr ⟨i, by_omega,
      by omega, by_omega, s, hs, by rw [hpo]⟩⟩

/-- **A non-stop chord at the first cut beyond the key, not beyond the window end, is accepted**
by the batch of origins (at its far end, from a valid origin). -/
theorem stp_accepted_of_found (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hW : WinOut P J N₁ c cw) (hR : ResetRel cw cs) {A : Set zte}
    (hBA : BatchA P J N₂ cs
      ztwro
      zthib co A)
    {e : Set Point} (he : e ∈ F₂plus J ztwis) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hlt : keyOff P J c < oW J ztk)
    (hgap : ∀ e' ∈ F₂plus J ztwis, ∀ (q : ℕ) (s : ℝ),
      SideAttach (chainModel J.whole).W e' q s →
        ¬ ztxij)
    (hst : ¬ StopChord2 J ztwis e)
    (hwin : cw.nreg wX = 0 → oW J ztk ≤ offK P J ztjsz ztjta) :
    ∃ k, k < N₂.nChords ∧ ∃ (a : Point) (σ : ℝ),
      ((σ = 1 ∧ a = Merge.lend ztwyu) ∨
        (σ = -1 ∧ a = Merge.rend ztwyu)) ∧
      a ∈ J.right.set ∧ a ≠ J.shared ∧ a ≠ J.right.top ∧ FreeAt J.whole a σ ∧
      e = Merge.shoot J.whole a σ ∧ J.whole.hitParam a σ < J.right.hitParam a σ ∧
      ∃ j, j < 2 * N₂.nChords ∧ j / 2 = k ∧ endOrigin J zta N₂ j = a ∧ endDir j = σ ∧
        ∃ h, (chainModel J.whole).param zta ztnk = t ∧ ztjzc ∈ A := by
  zuxz

  obtain ⟨ch, hch, a, σ, ha, haR, hav, hat, hfree, rfl, hsrc⟩ :=
    nonstop_found hP hS₂ hF L.keyL L.inv hA.1 hA.2.1 hA.2.2.1 hlt hgap he hA hst
  obtain ⟨k, hk, hkch, htried⟩ := stp_query_tried E L hW hR hlt hgap rfl hch hsrc
  zune
  zubwl

  have hnv : ztlyt := by
    zuq
    zukdp
    have hvD := fun hd =>
      J.whole.not_mem_set_of_mem_dom hd ztffl
    zucyf

  have ha₁ : a.2 ≤ J.left.top.2 := by
    zuevg
    · simp_all
    simp_all
  zuboo
  rw [← hkch] at ha
  -- the endpoint query
  obtain ⟨j, hj, hjk, hji, hjO, hjD⟩ : ∃ j, j < 2 * N₂.nChords ∧ j / 2 = k ∧
      (∃ s, s ≤ 1 ∧ j = 2 * k + s) ∧ endOrigin J zta N₂ j = a ∧ endDir j = σ := by
    unfold endOrigin endDir
    zuht
    · refine ⟨2 * k, by_omega, by_omega, by_simp_all, ?_, ?_⟩
      · simp
      simp
    · refine ⟨2 * k + 1, by_omega, by_omega, by_simp_all, ?_, ?_⟩
      · rw [ite_eq_right by_omega, show ztekz / 2 = k by omega]
      simp
  have hjO' : ztsju := by
    obtain ⟨s, hs, rfl⟩ := hji
    simp_all
  -- the hit is on the gathered arcs
  obtain ⟨-, -, eGB, eGK⟩ := stp_pre_frame hW hR
  obtain ⟨rs₁, -, -, hgk, -, -, -, -, -, hcov, -, -⟩ := hW
  have hoffd : ztxmk := by
    zucjz

  have hlo : rayPt a σ zton ∈
      ShotList.loSet ztbw zta cs.nmem ztcpv ztdzq [] := by
    have hin := hcov d t hMV hA.2.1 hA.2.2.1 ztntx (fun h0 => by
      grind)
    zudfv

  obtain ⟨h, hh, hmA⟩ := hBA.comp j hjO' hj ⟨by_grind, by_grind,
    by grind⟩ p t by_grind by_grind hLst
    hnv by_grind by_grind
  exact ⟨k, hk, a, σ, ha, haR, hav, hat, hfree, rfl, hlt', j, hj, hjk, hjO, hjD, h, hh, hmA⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config}

/-- The registers kept from the start of the iteration to the configuration after the origins. -/
theorem stp_co_keep (hI : IterRel P J N₁ N₂ c cw cs co c') {k : ℕ}
    (hk : ztcky ∨ ztgys ∨ ztgyv ∨
      ztdfa) : co.nreg (sw k) = c.nreg (sw k) := by
  obtain ⟨hW, -, hR, hB, -⟩ := hI
  zubrq
  obtain ⟨hregB, -, -⟩ := hB
  have h := stp_batch_keep hR hregB (k := k) by_omega
  simp_all

/-- The registers kept by the next-key step. -/
theorem stp_key_keep (hK : KeyOut P J co c') {k : ℕ}
    (hk : ztcky ∨ k = 2430 ∨ ztngc ∨ (2452 ≤ k ∧ k ≤ 2479) ∨
      (2500 ≤ k ∧ k ≤ 2699)) : c'.nreg (sw k) = co.nreg (sw k) :=
  hK.1 _ ztzdj
    (by unfold KR kE kH kN kL sP dF lC sw; omega) ztbpx

/-- The registers kept by the whole iteration. -/
theorem stp_iter_keep (hI : IterRel P J N₁ N₂ c cw cs co c') {k : ℕ}
    (hk : ztcky ∨ k = 2430 ∨ ztngc ∨ (2452 ≤ k ∧ k ≤ 2459) ∨
      ztdfa) : c'.nreg (sw k) = c.nreg (sw k) :=
  (stp_key_keep hI.2.2.2.2 by_omega).trans (stp_co_keep hI by_omega)

/-- The memory beyond the table, below the allocator, up to the configuration after the
origins. -/
theorem stp_co_mem (_L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') :
    ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x → co.nmem x = c.nmem x := by
  zueio
  zueiq
  zufih
  have eTB : ztguj := hkp 661 by_omega
  have eAs : ztfkw := hR.2.2.2 _ by_decide
    by_decide
  zueth
  rw [hBA.memT x by_omega by_omega, hmem x hx]

/-- The allocator grows. -/
theorem stp_alloc_mono (hI : IterRel P J N₁ N₂ c cw cs co c') :
    c.nreg ALLOC ≤ co.nreg ALLOC ∧ co.nreg ALLOC ≤ c'.nreg ALLOC := by
  obtain ⟨-, hAl, hR, hB, hK⟩ := hI
  have eAs : ztfkw := hR.2.2.2 _ by_decide
    by_decide
  exact ⟨by have := hB.2.1; omega, hK.2.1⟩

/-- **Some candidate exists** when the iteration does not finish. -/
theorem stp_key_some (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0 := by
  zubq

  have := (hI.2.2.2.2.2.2.1 by_omega).1
  omega

/-- The memory beyond the table, below the allocator, outside the new log record, through the
iteration. -/
theorem stp_c'_mem (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c')
    (hd : c'.nreg dF = 0) :
    ∀ x, x < c.nreg ALLOC → c.nreg cTB + 6 * N₂.nChords ≤ x →
      ztfcr →
      c'.nmem x = c.nmem x := by
  intro x hx h1 h2
  have hA := stp_alloc_mono hI
  have elB : ztize := stp_co_keep hI by_omega
  zuhvw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmK⟩ :=
    hI.2.2.2.2.2.2.2 ztoio
  rw [hmK x by_omega by_omega, stp_co_mem L hI x hx h1]

/-- The stop offsets after the origins. -/
theorem stp_stopOff_co (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') {i : ℕ}
    (hi : i < c.nreg sC) : stopOff P J co i = stopOff P J c i :=
  ((iter_stops L hI).2.2.1 i hi)

/-- The stop records after the origins. -/
theorem stp_stopEH_co (L : LoopInv P J N₁ N₂ c₀ c) (hI : IterRel P J N₁ N₂ c cw cs co c') {i : ℕ}
    (hi : i < c.nreg sC) : stopE co i = stopE c i ∧ stopH co i = stopH c i := by
  have esB : ztmuw := stp_co_keep hI by_omega
  zufgv

  zujre
  rw [esB, stp_co_mem L hI _ by_omega by_omega, stp_co_mem L hI _ by_omega by_omega]
  omega

/-- **The next key**: beyond the key, a word position, one of the possible keys. -/
theorem stp_next_key (_E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    keyOff P J c < keyOff P J c' ∧ PosW P J ztccp ztdco ∧
      keyOff P J c' ∈ keyS P J N₁ N₂ := by
  zukfs
  obtain ⟨esP, esC, -, ewX, ewE, ewH⟩ := iter_stops L hI
  have hst := fun {i : ℕ} (hi : i < c.nreg sC) => stp_stopEH_co L hI hi
  zubro
  zubrq
  zufih
  obtain ⟨-, hkey, -⟩ := hK.2.2.2 hsome
  zudmy

  rcases hkey with ⟨hbF, h1, h2⟩ | ⟨hsp, h1, h2⟩ | ⟨hwx, h1, h2⟩
  · -- the best candidate
    obtain ⟨⟨j, hj⟩, hlt⟩ := hBA.bAcc hbF
    obtain ⟨-, hmemF, hAt, -, -, hpw, -⟩ := (hBA.acc _ hj).2.2
    have ho' : keyOff P J c' = offK P J ztmhl ztmhm := by
      zumtg
    refine ⟨?_, by_simp_all, ?_⟩
    · rw [ho']; rw [ekE, ekH] at hlt; tauto
    · zueyc
      have hp0 := hpw.2.1.1
      have hp1 := hpw.2.1.2.1
      have hpn := hpw.1
      refine Or.inl ⟨_, ⟨_, hmemF, _, _, hAt, rfl⟩, by_positivity, ?_, rfl⟩
      have : ((co.nreg bE : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hpn
      linarith
  · -- the next stop
    have hi : c.nreg sP < c.nreg sC := by_omega
    obtain ⟨eE, eH⟩ := hst hi
    have ho' : keyOff P J c' = stopOff P J c ztccy := by
      unfold keyOff stopOff; simp_all
    zusk
    · zueyc
      zumv
      have := (L.ptrL _ hi).2 ztmmq
      omega
    · rw [h1, h2, esP, eE, eH]
      obtain ⟨rs, ax, hlen, -, hrec, -, -, hpw, -⟩ := L.stops
      have hi' : c.nreg sP < rs.length := by_omega
      obtain ⟨e0, e1, -⟩ := hrec _ hi'
      zujre
      grind
    · zueyc
      obtain ⟨e, he, p, t, hA, hoff, -⟩ := stp_stop_cut L hi
      zumnw
      refine Or.inl ⟨_, zteyg, by have := hA.2.1; positivity, ?_, rfl⟩
      have : ((p : ℕ) : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hA.1
      zujcb
  · -- the window end
    rw [ewX] at hwx
    obtain ⟨rs₁, -, -, -, -, -, -, -, hwin, -⟩ := hW
    obtain ⟨hpw, hlt, hcut⟩ := hwin hwx
    have ho' : keyOff P J c' = offK P J ztjsz ztjta := by
      zumtg
    refine ⟨by rw [ho']; tauto, by_simp_all, ?_⟩
    zueyc
    right
    rcases hcut with h | ⟨d, t, hv, ht0, ht1, ho, hc⟩
    · zueou
    · exact Or.inr ⟨d, t, hv, ht0, ht1, hc, ho⟩

/-- **The measure decreases** and the log has room. -/
theorem stp_meas_step (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    (keyS P J N₁ N₂ ∩ Ioi ztcnt).ncard < (keyS P J N₁ N₂ ∩ Ioi ztbnc).ncard ∧
    c'.nreg lC + (keyS P J N₁ N₂ ∩ Ioi ztcnt).ncard ≤ (keyS P J N₁ N₂).ncard + 1 ∧
    c.nreg lC + 1 ≤ logCap N₁ N₂ ∧ c'.nreg lC = c.nreg lC + 1 := by
  obtain ⟨hlt, -, hmem⟩ := stp_next_key E L hI hd
  obtain ⟨hfin, hcard⟩ := countTask P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hfin' := hfin
  have hsub : keyS P J N₁ N₂ ∩ Ioi _ ⊂ keyS P J N₁ N₂ ∩ Ioi _ :=
    ⟨by_grind, fun h => lt_irrefl _ (h ⟨hmem, hlt⟩).2⟩
  have hlt' := ncard_lt_ncard hsub ztvvf
  have hpos : 0 < (keyS P J N₁ N₂ ∩ Ioi _).ncard :=
    (ncard_pos ztvvf).2 ⟨_, hmem, hlt⟩
  zuhvw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlC, -⟩ := hI.2.2.2.2.2.2.2 ztoio
  have hm := L.meas
  have hcard' : ztdap := hcard
  refine ⟨hlt', by_omega, ?_, by_omega⟩
  unfold logCap
  omega

/-- The stop and auxiliary arrays at the next key. -/
theorem stp_arrays_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    c'.nreg sB = c.nreg sB ∧ c'.nreg aB = c.nreg aB ∧ c'.nreg sC = c.nreg sC ∧
    (∀ x, c.nreg sB ≤ x → x < c.nreg sB + 5 * c.nreg sC → c'.nmem x = c.nmem x) ∧
    ztvw := by
  have hcap := (stp_meas_step E L hI hd).2.2.1
  have l1 := L.lay1
  have l2 := L.lay2
  have l3 := L.lay3
  have l4 := L.lay4
  have l5 := L.lay5
  refine ⟨stp_iter_keep hI by_omega, stp_iter_keep hI by_omega,
    stp_iter_keep hI by_omega, fun x h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · zuhcw
  · zuhcw

/-- **The stops at the next key.** -/
theorem stp_stops_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    (∃ rs ax, StopData P J N₂ c' rs ax) ∧
    ∀ i, i < c.nreg sC → stopE c' i = stopE c i ∧ stopH c' i = stopH c i ∧
      stopOff P J c' i = stopOff P J c i := by
  obtain ⟨esB, eaB, esC, hmS, hmA⟩ := stp_arrays_c' E L hI hd
  obtain ⟨rs, ax, hlen, hax, hrec, hrecA, hok, hpw, hauxOK, hbd⟩ := L.stops
  have hEH : ∀ i, i < c.nreg sC → stopE c' i = stopE c i ∧ stopH c' i = stopH c i := by
    zug
    zujre
    rw [esB, hmS _ by_omega by_omega, hmS _ by_omega by_omega]
    omega
  refine ⟨⟨rs, ax, by_omega, hax, fun i hi => ?_, fun i hi => ?_, hok, hpw,
    hauxOK, hbd⟩, fun i hi => ⟨by_grind, by_grind, by
      unfold stopOff; grind⟩⟩
  · have hi' := by_omega
    obtain ⟨a0, a1, a2, a3, a4⟩ := hrec i hi
    rw [esB]
    zuflw
    · grind
    · grind
    · grind
    · grind
    grind
  · zubtl

    zuflw
    · grind
    · grind
    · grind
    · grind
    grind

/-- **The stop pointer at the next key.** -/
theorem stp_ptr_c' (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (L : LoopInv P J N₁ N₂ c₀ c)
    (hI : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 0) :
    c.nreg sP ≤ c'.nreg sP ∧ c'.nreg sP ≤ c'.nreg sC ∧
    (∀ i, i < c'.nreg sC → (i < c'.nreg sP ↔ stopOff P J c' i ≤ keyOff P J c')) ∧
    (∀ i, c.nreg sP ≤ i → i < c'.nreg sP → stopOff P J c i = keyOff P J c') := by
  obtain ⟨-, -, esC', -, -⟩ := stp_arrays_c' E L hI hd
  have hso := (stp_stops_c' E L hI hd).2
  have hlt := (stp_next_key E L hI hd).1
  obtain ⟨esP, esC, -, -, -, -⟩ := iter_stops L hI
  have hco := fun {i : ℕ} (hi : i < c.nreg sC) => stp_stopOff_co L hI hi
  obtain ⟨-, -, -, k1, k2, k3, k4, -⟩ := (hI.2.2.2.2.2.2.2 ztoio).2.2
  rw [esP] at k1 k3
  rw [esC] at k2 k4
  rw [esC']
  have k3' : ∀ i, c.nreg sP ≤ i → i < c'.nreg sP → stopOff P J c i = keyOff P J c' := by
    zusx
    rw [← hco by_omega]
    tauto
  refine ⟨k1, k2, fun i hi => ?_, k3'⟩
  rw [(hso i hi).2.2]
  constructor
  · zuq
    by_cases h' : i < c.nreg sP
    · have := (L.ptrL i hi).1 h'
      linarith
    simp_all
  · zuq
    zudxc
    have hlt' : c'.nreg sP < c.nreg sC := by_omega
    have hle : stopOff P J c ztmfk ≤ keyOff P J c' :=
      (L.sorted _ i by_omega hi).trans h
    have hge : keyOff P J c' ≤ stopOff P J c ztmfk := by
      rcases (show c'.nreg sP = c.nreg sP ∨ c.nreg sP < c'.nreg sP by omega) with h0 | h0
      · obtain ⟨-, -, -, hKs, -⟩ := (hI.2.2.2.2.2.2.2 by_omega)
        have := hKs by_omega
        rw [esP, ← h0] at this
        change keyOff P J c' ≤ stopOff P J co _ at this
        simp_all
      · rw [← k3' (c'.nreg sP - 1) by_omega by_omega]
        exact L.sorted _ _ by_omega hlt'
    have := k4 hlt'
    change stopOff P J co _ ≠ keyOff P J c' at this
    grind
theorem addLs_append' (l a b : List ℕ) : addLs l ztrkm = addLs zttez b := by
  zumro

/-- **A full list inside a set of at most four labels holds all of it.** -/
theorem stp_mem_full {l : List ℕ} {U : Finset ℕ} (hnd : l.Nodup) (hl : l.length = 4)
    (hU : ∀ x ∈ l, x ∈ U) (hc : U.card ≤ 4) {x : ℕ} (hx : x ∈ U) : x ∈ l := by
  classical
  have hsub : l.toFinset ⊆ U := fun y hy => hU y (List.mem_toFinset.1 hy)
  have hcard : l.toFinset.card = 4 := by rw [List.toFinset_card_of_nodup hnd, hl]
  have heq : l.toFinset = U := Finset.eq_of_subset_of_card_le hsub by_omega
  zvnbo at hx
  exact List.mem_toFinset.1 hx

/-- **Appending labels from a set of at most four** keeps every label. -/
theorem stp_addLs_all {U : Finset ℕ} (hc : U.card ≤ 4) :
    ∀ (vs l : List ℕ), l.Nodup → l.length ≤ 4 → (∀ x ∈ l, x ∈ U) → (∀ x ∈ vs, x ∈ U) →
      (addLs l vs).Nodup ∧ (addLs l vs).length ≤ 4 ∧ (∀ x ∈ addLs l vs, x ∈ U) ∧
        (∀ x ∈ l, x ∈ addLs l vs) ∧ (∀ x ∈ vs, x ∈ addLs l vs) := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil =>
    intro l hnd hl hU _
    exact ⟨hnd, hl, hU, fun x hx => hx, fun x hx => absurd hx (List.not_mem_nil)⟩
  | append_singleton vs v ih =>
    intro l hnd hl hU hV
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih l hnd hl hU (fun x hx => hV x ztszh)
    rw [addLs_append']
    have hvU : v ∈ U := hV v (List.mem_append_right _ (List.mem_singleton_self v))
    set l' := addLs l vs with hl'
    have hsame : addLs l' [v] = addL l' v := rfl
    rw [hsame]
    refine ⟨addL_nodup h1 v, addL_length_le h2 v, fun x hx => ?_, fun x hx => mem_addL_of_mem (h4 x hx),
      fun x hx => ?_⟩
    · rcases mem_addL hx with h | h
      · grind
      grind
    · zucyj
      · exact mem_addL_of_mem (h5 x h)
      · zugce
        zubst
        unfold addL
        split_ifs with hif
        · rcases hif with hif | hif
          · omega
          · exact stp_mem_full h1 by_omega h3 hc hvU
        simp

/-- **The label set of a key** is the image of its label list. -/
theorem stp_curLab_eq {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config}
    (h4 : c.nreg kN ≤ 4) :
    curLab P J N₂ c = regOf ztj zta N₂ '' {l | l ∈ lblOf c kN kL} := by
  unfold curLab labSet
  zucr
  ext l
  simp only [mem_ofPred_eq, lblOf, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨0, by_omega, by_simp⟩
    · exact ⟨1, by_omega, rfl⟩
    · exact ⟨2, by_omega, rfl⟩
    · exact ⟨3, by_omega, rfl⟩
  grind

/-- The registers of a label list are its entries. -/
theorem stp_mem_lblOf {c : Config} {i : ℕ} (hi : i < c.nreg kN) (h4 : c.nreg kN ≤ 4) :
    c.nreg ztbuc ∈ lblOf c kN kL := by
  zujqo
  grind
