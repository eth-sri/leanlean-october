module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.NFDecompRamRound
public import Chazelle.Core.GranRamBody
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.FactsAttach
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.OracleQueryExec
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.NFBuildArcs
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.SpecNF
public import Chazelle.Core.DownPhaseDrvRPlB

namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open ShotList ShotListG Machine SweepPrim
variable {P : Polygon} {M : Model} {N : NF}
variable {W : ℕ} {c₀ c' : Config}
/-- **The exactness package of a hit.** -/
theorem hit_exact (hE : TGood P W M N c₀) (hTF : TestFacts P M N c₀ c')
    {reg : ℕ → Set Point} (hregs : NFRegs M zta N reg) (h10 : c'.nreg 83010 = 1)
    (h11 : c'.nreg 83011 = 1) :
    ∃ T > (0 : ℝ),
      (∀ t, 0 < t → t < T → rayPt ztwkk ztjs t ∈
        reg ztco) ∧
      rayPt ztwkk ztjs T ∉ M.D ∧
      M.pos zta ztha =
        rayPt ztwkk ztjs T ∧
      c'.nreg 83012 < M.W.n ∧ ProperPos M zta P.n ztha ∧
      chordOf ztwkk ztjs T ∈ M.Adm ∧
      SideAttach M.W ztbalk
        (xOf c₀).edge ztxvl ∧
      SideAttach M.W ztbalk
        ztfgi ztwzk ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N ztwmu
          ztwtq ztwne)
          (N.region ztco).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N ztwtq
          ztwmu ztwne)
          (N.region ztco).chords.length) := by
  obtain ⟨-, hiv, -, -, -, -, h5⟩ := hTF
  have hV := hiv.1 h10
  obtain ⟨m, B, hs, A, harr, hnear, hlo, hhi, hyes, -⟩ := h5 h10
  obtain ⟨t, f₀, hfh, hp0, he0, hpos0, hpp, hpe, hposf, harrv, hint, hcnt, -⟩ := hyes h11
  obtain ⟨hout, hstr, hadm, p', t', hatt, hw'⟩ := hit_math hE.hGM hE.hNF hregs hE.hr hE.hxp hE.hxe
    hV hE.x_top harr hnear hlo hhi hfh
  have hσ := dir_pm ztbkn
  have ht := hfh.1
  have hposf' : M.pos _ ztha =
      rayPt _ _ t := hposf.trans hpos0
  refine ⟨t, ht, hstr, hout, hposf', hpe, hpp, hadm, ?_, ?_, hcnt⟩
  · exact attach_start hE.hxe hE.hxp.1 hE.hxp.2.1 hσ ht hV.2.1
  · zubby
    · have ha := harrv C hM
      rw [hpos0] at ha
      exact attach_end ha.1 ha.2.1 ha.2.2.1 hσ ht ha.2.2.2.1 (by rw [ha.2.2.2.1]; exact ha.2.2.2.2)
    · zufgb
      have hWs : M.W.Simple := by zvmzx; exact (FactsInterior.interiorWalk_spec hQ).1
      exact attach_far_simple hWs hatt hw' hpe hpp.1 hpp.2.1 hposf'

/-- **The chord triple of the test** describes the chord of the hit and is attached. -/
theorem record_ok {Q : Polygon} {x f : WPos} {h σb lp rp : ℕ} {T : ℝ} (_hσb : σb ≤ 1)
    (hT : 0 < T) (hy : (M.pos Q x).2 = (Q.vtx h).2)
    (hf : M.pos Q f = rayPt zteng ztbem T)
    (hA : SideAttach M.W ztzlc x.edge ztbyt)
    (hB : SideAttach M.W ztzlc f.edge (M.param Q f))
    (hlr : (σb = 1 → lp = x.edge ∧ rp = f.edge) ∧ (σb ≠ 1 → lp = f.edge ∧ rp = x.edge)) :
    (recOf ztcvt).toSet M Q = chordOf zteng ztbem T ∧
      (recOf ztcvt).Attached M Q := by
  have hfy : (M.pos Q f).2 = (Q.vtx h).2 := by_simp_all
  have px := pos_code M Q hy
  have pf := pos_code M Q hfy
  have qx := param_code M Q hy
  have qf := param_code M Q hfy
  have hfx : (M.pos Q f).1 = (M.pos Q x).1 + dirOf σb * T := by_simp_all
  by_cases h1 : σb = 1
  · obtain ⟨rfl, rfl⟩ := hlr.1 h1
    have hd : dirOf σb = 1 := by zvmwp; rfl
    have e : (recOf (h, x.edge, f.edge)).toSet M Q = chordOf zteng ztbem T := by
      show Visibility.hseg (Q.vtx h).2 (M.pos Q ztgpv).1 (M.pos Q ztgow).1 = _
      rw [px, pf, chordOf, hfx, hd, hy, min_eq_left by_linarith, max_eq_right by_linarith]
    refine ztrcd
    · show SideAttach M.W _ x.edge ztzue
      simp_all
    · show SideAttach M.W _ f.edge ztzud
      simp_all
  · obtain ⟨rfl, rfl⟩ := hlr.2 h1
    have hd : ztshy := by unfold dirOf; simp_all
    have e : (recOf (h, f.edge, x.edge)).toSet M Q = chordOf zteng ztbem T := by
      show Visibility.hseg (Q.vtx h).2 (M.pos Q ztgow).1 (M.pos Q ztgpv).1 = _
      rw [px, pf, chordOf, hfx, hd, hy, min_eq_right by_linarith, max_eq_left by_linarith]
    refine ztrcd
    · show SideAttach M.W _ f.edge ztzud
      simp_all
    · show SideAttach M.W _ x.edge ztzue
      simp_all

/-- The candidate and a point of its ray at a positive parameter differ. -/
theorem ray_ne {z : Point} {σb : ℕ} {T : ℝ} (hT : 0 < T) : z ≠ rayPt z ztbem T := by
  zuq
  have := congrArg Prod.fst h
  rw [rayPt_fst] at this
  rcases dir_pm σb with h1 | h1 <;> zvmwp at this <;> linarith

/-- **The postcondition of `TestOK`** for the normal form of the run. -/
theorem test_post (hE : TGood P W M N c₀)
    (hTF : TestFacts P M N c₀ c') {reg : ℕ → Set Point} (hregs : NFRegs M zta N reg) :
    (c'.nreg 83014 = 1 →
      (recOf ztdzh).Attached M zta ∧
      c'.nreg 83015 < (Qof P).n ∧
      (recOf ztdzh).toSet M zta ∈ M.Adm ∧
      SplitsWell M ztwiv ztbain
        ((recOf ztdzh).toSet M zta)) ∧
    (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
      ∃ T > (0 : ℝ),
        (∀ t, 0 < t → t < T → rayPt ztwkk ztjs t ∈
          reg ztco) ∧
        M.pos zta ztha =
          rayPt ztwkk ztjs T ∧
        c'.nreg 83012 < M.W.n ∧ ProperPos M zta P.n ztha ∧
        chordOf ztwkk ztjs T ∈ M.Adm ∧
        SideAttach M.W ztbalk
          (xOf c₀).edge ztxvl ∧
        SideAttach M.W ztbalk
          ztfgi ztwzk ∧
        (c'.nreg 83014 = 1 ↔ CountOK M ztwiv ztbain
          ztwmu ztwtq)) ∧
    (sideLeft M.W (xOf c₀).edge ztxvl
        (rayPt ztwkk ztjs 1) →
      (N.region ztco).chords ≠ [] →
      (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T →
          rayPt ztwkk ztjs t ∈ M.D) →
        rayPt ztwkk ztjs T ∉ M.D →
        chordOf ztwkk ztjs T ∈ M.Adm →
        chordOf ztwkk ztjs T ∉ N.F M zta →
        chordOf ztwkk ztjs T ∩ M.D ⊆ reg ztco →
        c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1)) := by
  have hGM := hE.hGM
  zumcd
  zugnb
  zubm
  zuddz
  -- the counts of the test are those of `CountOK`
  have hcount : ∀ f : WPos,
      (2 ≤ cntP (fun t => SideHit M P N _ _
          _) (N.region _).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N _ _
          _) (N.region _).chords.length) ↔
      CountOK M _ _ ztwmu
        ztxke := fun f => by
    unfold CountOK
    rw [sideExits_ncard hGM hNF hregs hr, sideExits_ncard hGM hNF hregs hr]
  refine ⟨fun hs => ?_, fun h10 h11 => ?_, fun hL hch T hT hdom hout hadm hnF hsub => ?_⟩
  · -- soundness
    have h11 := i14 hs
    have h10 := i11 h11
    obtain ⟨T, hT, hstr, -, hposf, hpe, hpp, hadm, hA, hB, hcnt⟩ :=
      hit_exact hE ztdxa hregs h10 h11
    obtain ⟨m, B, hs', A, -, -, -, -, hyes, -⟩ := h5 h10
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, htri⟩ := hyes h11
    obtain ⟨t15, t1, t2⟩ := htri hs
    have hy : (M.pos _ ztfy).2 = ((Qof P).vtx _).2 := hE.hy.symm
    obtain ⟨he, hat⟩ := record_ok hE.hσ hT hy hposf
      hA hB ⟨t1, t2⟩
    rw [t15]
    zuc
    refine ⟨hat, by zvmxg; exact hE.hh, by_grind, ?_⟩
    zucjo
    have hAB : sidePt M.W (xOf c₀).edge ztxvl ≠
        sidePt M.W ztfgi ztwzk := by
      show M.pos _ _ ≠ M.pos _ ztha
      zuikm
    obtain ⟨c1, c2⟩ := (hcount _).1 (hcnt.1 hs)
    exact splitsWell_of_counts hM hNF.1.2.1 hNF.1.1 (hregs.1.1 _ hr) hadm hA hB hAB c1 c2
  · -- exactness
    obtain ⟨T, hT, hstr, -, hposf, hpe, hpp, hadm, hA, hB, hcnt⟩ :=
      hit_exact hE ztdxa hregs h10 h11
    exact ⟨T, hT, hstr, hposf, hpe, hpp, hadm, hA, hB, by_grind⟩
  · -- completeness
    have hV : ztplh :=
      valid_compl hGM hNF hregs hr hE.hxp hE.hxe hch hL hT hdom hadm hnF hsub
    have h10 := hiv.2 hV
    refine ⟨h10, ?_⟩
    by_contra h11
    obtain ⟨m, B, hs', A, harr, hnear, hlo, -, -, hno⟩ := h5 h10
    exact noHit_false hGM hNF hregs hr hE.hxp hE.hxe hV hE.x_top harr hnear hlo hT hout (hno h11)

/-! ## The cost -/

/-- The cost factor of the test for a degree cap `d`. -/
def testκ (d : ℕ) : ℕ := testK ztet d 0 + 16 * ztvq
theorem testK_split (A D Fg : ℕ) : testK A D Fg = testK A D 0 + ztbo * ztjem := by
  simp only [testK, shotAK, shotCostG, nodeG]
  ring
theorem testK_mono {A D A' D' : ℕ} (hA : A ≤ A') (hD : D ≤ D') : testK A D 0 ≤ testK A' D' 0 := by
  simp only [testK, shotAK, shotCostG, nodeG, validK, arcScanK, arcKB, vertexK, exitScanK,
    exitKB, buildK, bodyK, normK, postHitK, countK, countKB, shK]
  nlinarith

/-- **The cost of the test** is at most `testκ d · (F γ + 1)`. -/
theorem testK_le {A D d Fg : ℕ} (hA : A ≤ d + 1) (hD : D ≤ d) :
    testK A D Fg ≤ testκ d * ztclk := by
  rw [testK_split]
  have h1 := testK_mono hA hD
  have h2 : ztbo * ztjem ≤ 16 * ztvq * Fg := by_nlinarith
  unfold testκ
  nlinarith

/-! ## The contract -/

/-- The normal form `N'` with the fields other than chords, arcs and regions taken from `N`. -/
def patch (N N' : NF) : NF :=
  ⟨N'.chords, N'.arcs, N'.regions, N.seq, N.dec, N.root, N.lpar⟩

/-- A normal form at the handle of the run agrees with the run's on chords, arcs and regions. -/
theorem nf_patch {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    patch N N' = N := by
  have hc := NFLoc.nfAt_chords_eq h h'
  have ha := NFLoc.nfAt_arcs_eq h h'
  have hr := DecR.nfAt_regions_eq' h h'
  unfold patch
  simp_all

/-- **The candidate test meets its contract.** -/
theorem testOK {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal)
    (hB8 : bRestore ∉ Bo) (hBo : oracleBands ⊆ Bo) :
    TestOK ztibi testκ F X Ok Bo := by
  zuesx
  dsimp only at hroom ⊢
  obtain ⟨hG, hW, hX, hcap, hwf, hreg, hsimp, hσ, M, N, hMD, hGM, hOk, hNw, hNF, hdeg, hsg, hr,
    hxe, hxp, hxc, hkind, hxC, hh, hy⟩ := pre
  have hE := tgood_of hG hW hMD hwf hreg hsimp hkind hGM hNw hNF hr hxe hxp
    hxc hxC hh hy hσ
  obtain ⟨reg₀, hregs₀⟩ := hE.regs
  have hdg : M.deg _ _ ≤ c.nreg 83009 :=
    hdeg _ (hregs₀.1.1 _ hr)
  have hA := arcs_le_deg hGM hNF hregs₀ hr
  have hD := chords_le_deg hNF hregs₀ hr
  have hK := testK_le (Fg := F ztmgo) (show (N.region ztqii).arcs.length ≤
    c.nreg 83009 + 1 by omega) (show (N.region (c.nreg 83002)).chords.length ≤ c.nreg 83009 by omega)
  obtain ⟨c', k, ex, hk, hI, hrf, hTF⟩ := testS_rsb hsh hBs hXl hB8 hBo hw hE hX hcap hOk hsg
    by_omega
  have hsub : dBands ∪ Bo ⊆ restoreBands ∪ Bo := by
    intro b hb
    simp only [dBands, Finset.mem_union] at hb ⊢
    grind
  refine ⟨c', k, ex, by_omega, ?_, (RF.to_frame hrf).mono hsub le_rfl⟩
  zuddz
  refine ⟨fun q hq hq' => hI.hin q (by unfold bandOf bRestore at hq; omega) by_omega, b10, b11,
    b14, fun M' N' reg hMD' hNA' hNF' hregs' => ?_⟩
  have eM := (NFLoc.modelDesc_unique hMD' hMD).symm
  subst eM
  have hNA : ztpkv := hNw.holds
  have e := nf_patch hNA hNA'
  have hregs : NFRegs M zta N reg := by
    have h : NFRegs M _ zttvs reg := hregs'
    grind
  have hF : N'.F M zta = N.F M zta := by
    have : N'.F M _ = (patch N N').F M zta := rfl
    grind
  have hRg : ∀ r, N'.region r = N.region r := fun r => by
    have : N'.region r = (patch N N').region r := rfl
    grind
  rw [hF, hRg]
  exact test_post hE ztdxa hregs
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open SweepPrim (candIdx)
variable {M : Model}

/-- **A good candidate** of the search for the region `R` of `S`: a walk vertex `X` and a
direction `σ` into its left sector whose ray first leaves the domain at `T`, with an admissible
chord splitting `R` well. -/
def GoodCand (M : Model) (Q : Polygon) (S : Set ztf) (R : Set Point) (X : WPos)
    (σ T : ℝ) : Prop :=
  X.hgt = 0 ∧ X.edge < M.W.n ∧ ztdd ∧ 0 < T ∧
    sideLeft M.W X.edge 0 (rayPt ztjjz σ 1) ∧
    (∀ t, 0 < t → t < T → rayPt ztjjz σ t ∈ M.D) ∧ rayPt ztjjz σ T ∉ M.D ∧
    chordOf ztjjz σ T ∈ M.Adm ∧ SplitsWell M S R ztcvb
theorem iv_iv {Q : Polygon} {i : ℕ} (hi : i < Q.n) : IOrc.iv Q ztsxy = i := by
  unfold IOrc.iv; grind

/-- **A full chord is the chord of the ray from a walk vertex** `p`; every proper position of
the vertex is a vertex position. -/
theorem full_ray (hGM : GoodModel M) {e : Set Point} (he : e ∈ M.Full) :
    ∃ p, p < M.W.n ∧ ∃ σ T : ℝ, ztdd ∧ 0 < T ∧
      (∀ t, 0 < t → t < T → rayPt ztoy σ t ∈ M.D) ∧ rayPt ztoy σ T ∉ M.D ∧
      e = chordOf ztoy σ T ∧
      (∀ p' t', p' < M.W.n → 0 ≤ t' → t' < 1 → sidePt M.W p' t' = M.W.vtx p → t' = 0) ∧
      ∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6 := by
  rcases hGM with ⟨C, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
  · obtain ⟨k, σ, hk, hσ, hfree, rfl⟩ := he
    zuet
    have cv := (SweepPrim.cand_vertex C C.sideBeta hk).1
    have hv : (chainModel C).W.vtx ztyvp = C.vertex k := by
      show (C.sideWalk C.sideBeta).vtx _ = _
      rw [C.sideWalk_vtx_tour _ cv.1, Chain.sideTour, cv.2]
    refine ⟨candIdx C.m ztboi k + 6, by_omega, σ, C.chordParam k σ, hσ,
      C.chordParam_pos hk hσ hfree, fun t h0 h1 => ?_, ?_, ?_, fun p' t' hp' h0 h1 hpt => ?_,
      fun C' hC' => ?_⟩
    · zvmyq; exact C.openChordSet_subset_dom hk hσ hfree ztzio
    · zvmyq; exact C.chordEnd_not_mem_dom hk hσ hfree
    · rw [hv, C.chordSet_eq_hseg, chordOf, Chain.chordEnd, rayPt_fst]
    · zvmyq at hpt
      exact (chain_vertex_positions hP hk hp' h0 h1 hpt).1
    · have e1 : ztdh := C.sideWalk_n _
      have e2 : (chainModel C').W.n = 2 * C'.m + 7 := C'.sideWalk_n _
      simp_all
  · obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := he
    have hn : ztbdm := IOrc.mi_n
    have hp : IOrc.iv Q i < Q.n := IOrc.iv_lt hi
    have hv : (interiorModel Q).W.vtx ztsxy = Q.vtx i := by
      show (interiorWalk Q).vtx _ = _
      rw [IOrc.iw_vtx hp, iv_iv hi]
    refine ⟨IOrc.iv Q i, by_omega, σ, Visibility.chordParam Q i σ, hσ,
      Visibility.chordParam_pos hQ hi hdir, fun t h0 h1 => ?_, ?_, ?_,
      fun p' t' hp' h0 h1 hpt => ?_, fun C hC => ?_⟩
    · zvmyq; exact Visibility.openChordSet_subset_interior hQ hi hdir ztzio
    · zueyk
      exact fun h => h.2 (Visibility.chordEnd_mem_boundary hQ hi hdir)
    · rw [hv, Visibility.chordSet_eq_hseg, chordOf, Visibility.chordEnd, rayPt_fst]
    · have hWs : (interiorModel Q).W.Simple := (FactsInterior.interiorWalk_spec hQ).1
      have := FactsInterior.pos_unique hWs hp' by_omega h0 h1 le_rfl zero_lt_one
        (hpt.trans (Chazelle.Chain.sidePt_zero _ _).symm)
      simp_all
    · have := congrArg (fun M : Model => M.counted 0) hC
      simp [interiorModel, chainModel] at this

/-- **The good candidate of a full chord**, with its attachments and its vertex. -/
theorem good_of_full' (hGM : GoodModel M) {Q : Polygon} {S : Set ztf} {R : Set Point}
    {e : Set Point} (he : e ∈ M.Full) (hsw : SplitsWell M S R e) :
    ∃ X σ T, GoodCand M Q S R X σ T ∧ SideAttach M.W ztcvb X.edge 0 ∧
      (∃ po tq, SideAttach M.W ztcvb po tq ∧
        sidePt M.W X.edge 0 ≠ sidePt M.W po tq) ∧
      ∃ p, (∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6) ∧ M.pos Q X = M.W.vtx p := by
  zubm
  obtain ⟨p, hp, σ, T, hσ, hT, hdom, hout, rfl, hvtx, hrange⟩ := full_ray hGM he
  set v := M.W.vtx p with hvdef
  have hadm : chordOf v σ T ∈ M.Adm := full_subset_adm hGM he
  obtain ⟨a, b, hab, hseg', hy, -, ⟨⟨pa, ta, hA, hpa⟩, -⟩, ⟨⟨pb, tb, hB, hpb⟩, -⟩⟩ := hM.ends _ hadm
  -- the vertex is an end of the segment
  have hw1 : (rayPt v σ T).1 ≠ v.1 := by
    zugff
  have hvab : v = a ∨ v = b := by
    have e1 : chordOf v σ T = hseg a.2 ztttk ztttb := by
      rw [hseg', Visibility.segment_horizontal_eq_hseg hy]
    unfold chordOf at e1
    obtain ⟨ey, emin, emax⟩ := Merge.hseg_inj min_le_max e1
    grind
  -- the attachment at the vertex
  obtain ⟨pv, tv, hAv, hpv, po, tq, hAo, hpo⟩ : ∃ pv tv, SideAttach M.W (chordOf v σ T) pv tv ∧
      sidePt M.W pv tv = v ∧ ∃ po tq, SideAttach M.W (chordOf v σ T) po tq ∧
        sidePt M.W po tq ≠ v := by
    grind
  have htv : tv = 0 := hvtx pv tv hAv.1 hAv.2.1 hAv.2.2.1 hpv
  subst htv
  have hposX : M.pos Q ztopf = v := by
    tauto
  refine ⟨ztopf, σ, T, ⟨rfl, hAv.1, hσ, hT, ?_, by_grind,
    by grind, by_grind, by_grind⟩,
    by grind, ⟨po, tq, by_grind, by_grind⟩,
    p, hrange, hposX⟩
  -- the ray starts into the left sector
  obtain ⟨-, -, -, -, r, hr, hsec⟩ := hAv
  zubfj

  have hmem : rayPt v σ s ∈ chordOf v σ T := (mem_chordOf hσ hT.le).2 ⟨s, hs.le, by_linarith, rfl⟩
  have hd : dist ztrvb v = s := Sweep.dist_rayPt _ hσ hs.le
  have hne : rayPt v σ s ≠ sidePt M.W pv 0 := by
    rw [hpv]; intro h; rw [h, dist_self] at hd; linarith
  zuiak
  show sideLeft M.W pv 0 (rayPt (M.pos Q ztopf) σ 1)
  rw [hposX, ← hpv] at *
  exact (Sweep.sideLeft_rayPt_iff M.W pv 0 σ one_pos hs).2 hsl

/-- **A good candidate exists**, with its attachments and its vertex. -/
theorem exists_good' (hGM : GoodModel M) {Q : Polygon} {D : ℕ} (hfull : M.FullDegLe Q D)
    {S : Set ztf} (hS : M.ChordFamily Q S) {R : Set Point}
    (hR : R ∈ Chazelle.Chain.regionsIn M.D S) (hdeg : D < (Chazelle.Merge.exitsIn M.D S R).ncard) :
    ∃ X σ T, GoodCand M Q S R X σ T ∧ SideAttach M.W ztcvb X.edge 0 ∧
      (∃ po tq, SideAttach M.W ztcvb po tq ∧
        sidePt M.W X.edge 0 ≠ sidePt M.W po tq) ∧
      ∃ p, (∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6) ∧ M.pos Q X = M.W.vtx p := by
  obtain ⟨e, he, hsw⟩ := exists_step hGM hfull hS hR hdeg
  exact good_of_full' hGM he hsw

/-- **The first exit of a ray is unique.** -/
theorem exit_unique {D : Set Point} {z : Point} {σ T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ D) (hout : rayPt z σ T ∉ D)
    (hdom' : ∀ t, 0 < t → t < T' → rayPt z σ t ∈ D) (hout' : rayPt z σ T' ∉ D) : T = T' := by
  grind
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (sidePt SideAttach sideLeft sideLeftOf sideCcw sideCross sideDot sidePrev
  sideNext sideInArc freeIn regionsIn TouchesIn halfDisk mem_halfDisk_iff isPreconnected_halfDisk
  sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset)

/-- **A sector containing both horizontal directions contains an open half-plane.** -/
theorem ccw_half {B A : Point} (hB : B ≠ 0) (hA : A ≠ 0)
    (hE : sideCcw B (ztcei : Point) A) (hW : sideCcw B (ztcyl : Point) A) :
    (∀ X : Point, 0 < X.2 → sideCcw B X A) ∨ (∀ X : Point, X.2 < 0 → sideCcw B X A) := by
  unfold sideCcw sideCross sideDot at *
  simp only at hE hW
  have hB' : B.1 ≠ 0 ∨ B.2 ≠ 0 := by
    grind
  have hA' : A.1 ≠ 0 ∨ A.2 ≠ 0 := by
    by_contra h; simp_all
  rcases lt_trichotomy (B.1 * A.2 - B.2 * A.1) 0 with hc | hc | hc
  · -- a reflex sector
    have e1 : B.2 < 0 ∨ 0 < A.2 := by
      grind
    have e2 : 0 < B.2 ∨ A.2 < 0 := by
      grind
    rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2
    · linarith
    · -- both edges point down: the upper half-plane is in the sector
      left
      zufxi
      zuhl
      zuekk

    · -- both edges point up: the lower half-plane is in the sector
      right
      zufxi
      zuhl
      zuekk

    grind
  · -- a straight or full sector
    rcases lt_trichotomy ztely 0 with hd | hd | hd
    · grind
    · simp_all
    · -- `A`, `B` in the same direction: every direction but theirs is in the sector
      rcases le_or_gt B.2 0 with hb | hb
      · left
        zufxi
        zubef
        zuekj

        · right
          -- `X` parallel to `B`, pointing up while `B` does not: opposite directions
          have key : ztyzl := by
            grind
          rcases hb.lt_or_eq with hb | hb
          · have : B.2 * zteol < 0 :=
              mul_neg_of_neg_of_pos hb by_positivity
            zuhbx
          grind
        simp_all
      · right
        zufxi
        zubef
        zuekj

        · right
          have key : ztyzl := by
            grind
          have : 0 < B.2 * zteol :=
            mul_pos hb (by nlinarith [sq_nonneg X.1, mul_pos ztvzv ztvzv])
          zuhbx
        simp_all
  grind
variable {M : Model}

/-- **An attached admissible chord is a horizontal segment from the attachment point**, whose
other end `o` is a walk point (outside the domain) and whose open part is in the domain. -/
theorem attach_ray (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ o : Point, o ≠ sidePt M.W p t ∧ o.2 = (sidePt M.W p t).2 ∧
      c = Chazelle.segment ztbp o ∧ o ∉ M.D ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztbp o s ∈ M.D := by
  zuchn
  zucgh
  zugdq
  have hout : ztlcb := by
    zucjc

  zucio
  · grind
  · refine ⟨a, by_simp_all, by_simp_all, by rw [hcab, h, Geometry.segment_comm],
      by grind, ?_⟩
    zugg
    rw [h, Geometry.lerp_symm]
    simp_all

/-- A point of the segment `[w, v]` between `w` and `v` on a horizontal line. -/
theorem lerp_hit {w u v : Point} (hu : u.2 = w.2) (hv : v.2 = w.2) {s : ℝ}
    (hs : u.1 = w.1 + s * ztuct) : lerp w v s = u :=
  point_ext by_simp_all by_simp_all

/-- **Two horizontal segments from `w` in the same direction, with open parts in `D` and far ends
outside `D`, are equal.** -/
theorem ray_eq {D : Set Point} {w o o' : Point} (ho : o.2 = w.2) (ho' : o'.2 = w.2)
    (hsame : 0 < ztcwc * ztcan) (hoD : o ∉ D) (ho'D : o' ∉ D)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w o s ∈ D)
    (hopen' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w o' s ∈ D) : o = o' := by
  rcases lt_trichotomy o.1 o'.1 with h | h | h
  · zudmq

    · -- `o` inside `[w, o']`
      have hs : ztycv :=
        ⟨by_simp_all, (div_lt_one h2).2 by_linarith⟩
      zucyy

    · -- `o'` inside `[w, o]`
      have hs : ztycu :=
        ⟨div_pos_of_neg_of_neg h2 h1, (div_lt_one_of_neg h1).2 by_linarith⟩
      zucyx

  · grind
  · zudmq

    · have hs : ztycu :=
        ⟨by_simp_all, (div_lt_one h1).2 by_linarith⟩
      zucyx

    · have hs : ztycv :=
        ⟨div_pos_of_neg_of_neg h1 h2, (div_lt_one_of_neg h2).2 by_linarith⟩
      zucyy

/-- The points of a segment from `w` eventually approach `w`. -/
theorem lerp_near (w o : Point) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ dist ztrto w < r := by
  have hc : Continuous (fun s : ℝ => lerp w o s) := by
    zumti
  have ht : Tendsto (fun s : ℝ => lerp w o s) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have := hc.tendsto 0
    zugcb
    zuhv
  filter_upwards [Ioo_mem_nhdsGT one_pos, ht.eventually (ball_mem_nhds w hr)] with s hs hd
  simp_all

/-- **The direction of an attached chord is in the left sector at its attachment.** -/
theorem attach_ccw (_hM : WalkAx M) {c : Set Point} {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {o : Point} (ho : o ≠ sidePt M.W p t)
    (hco : c = Chazelle.segment ztbp o) :
    sideCcw (sideNext M.W p - sidePt M.W p t) ztpcv
      (sidePrev M.W p t - sidePt M.W p t) := by
  zudds
  obtain ⟨s, ⟨hs1, hd⟩, hs0⟩ := ((lerp_near ztbp o hr).and self_mem_nhdsWithin).exists
  have hs0' := hs0
  have hx : lerp ztbp o s ∈ c := by
    rw [hco]; exact Geometry.mem_segment_iff_lerp.2 by_grind
  have hl := hleft _ hx (Chazelle.Jordan.lerp_ne_left (Ne.symm ho) hs0') hd
  unfold sideLeft sideLeftOf at hl
  have e : lerp ztbp o s - sidePt M.W p t = s • ztpcv := by
    apply point_ext <;> simp [lerp_fst, lerp_snd]
  rw [e, Chazelle.Chain.sideCcw_smul hs0'] at hl
  exact hl

/-- A horizontal direction vector is a positive multiple of `(1, 0)` or `(-1, 0)`. -/
theorem ccw_unit {B A o w : Point} (h : sideCcw B (o - w) A) (ho : o.2 = w.2) :
    (0 < o.1 - w.1 → sideCcw B (ztcei : Point) A) ∧
      (o.1 - w.1 < 0 → sideCcw B (ztcyl : Point) A) := by
  constructor
  · zulmx
    have e : o - w = ztcwc • (ztcei : Point) := by
      zuiqw
    rw [e, Chazelle.Chain.sideCcw_smul hpos] at h
    zubh
  · intro hneg
    have e : o - w = (w.1 - o.1) • (ztcyl : Point) := by
      zuiqw
    rw [e, Chazelle.Chain.sideCcw_smul by_linarith] at h
    zubh

/-- Points level with the centre of a half-disk and inside its square are in its closure. -/
theorem mem_closure_halfDisk' {w z : Point} {r τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hr : 0 < r)
    (hz : z.2 = w.2) (hz1 : |z.1 - w.1| < r) : z ∈ closure ztefh := by
  zujha
  zudik
  set δ := min ε r / 2 with hδ
  have hδ0 : ztcfy := by_simp_all
  have hδε : δ < ε := by_grind
  have hδr : ztsod := by_grind
  have habs : |τ * δ| = δ := by
    zujj
    · grind
    grind
  refine ⟨(z.1, w.2 + τ * δ), ?_, ?_⟩
  · zueyz
    refine ⟨⟨hz1, ?_⟩, ?_⟩
    · simp_all
    · show 0 < τ * (w.2 + τ * δ - w.2)
      rw [add_sub_cancel_left, ← mul_assoc]
      rcases hτ with rfl | rfl <;> norm_num <;> exact hδ0
  · rw [Prod.dist_eq, dist_self, Real.dist_eq, hz, sub_add_cancel_left, abs_neg, habs,
      max_eq_right hδ0.le]
    omega

/-- The point before a position is not its point. -/
theorem sidePrev_ne (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) :
    sidePrev M.W p t ≠ sidePt M.W p t := by
  zukec
  zulcf
  zujpo
  · zucfb
    zudti
    zuiy
    have hq := hM.nd ztcm zthp
    rw [Sweep.prev_succ_mod hp] at hq
    zuito
  · zucky
    exact (Chazelle.Jordan.lerp_ne_left hnd by_grind).symm

/-- **The ends of a new chord lie on closed arcs of its region.**  An admissible chord `e ∉ S`
whose domain part lies in the region `R` of `S`, attached at `(p, t)`, has the key `p + t` on the
closed key interval of an arc of `R`. -/
theorem attach_closedArc (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) (hne : S.Nonempty) {R : Set Point} (hR : R ∈ M.regions S)
    {e : Set Point} (he : e ∈ M.Adm) (heS : e ∉ S) (heR : e ∩ M.D ⊆ R) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W e p t) :
    ∃ a b, M.IsArc S R a b ∧ ClosedArc a b ztk := by
  obtain ⟨hp, ht0, ht1, -, rA, hrA, hleftA⟩ := id hA
  have hsys := hM.sys S hS hfin
  zudnz
  obtain ⟨oe, hoe, hoe2, hes, hoeD, hoeo⟩ := attach_ray hM he hA
  zubla

  -- a point of `e` near the attachment, in `R`
  obtain ⟨se, ⟨hse1, hsed⟩, hse0⟩ := ((lerp_near ztbp oe (lt_min hr₁ hrA)).and
    self_mem_nhdsWithin).exists
  have hse0' := hse0
  set ze := lerp _ oe se with hze
  have hzeD : ze ∈ M.D := by_grind
  have hzee : ze ∈ e := by
    zupau; exact Geometry.mem_segment_iff_lerp.2 by_grind
  have hzeR : ze ∈ R := by_grind
  have hzel :=
    hleftA ze hzee (Chazelle.Jordan.lerp_ne_left (Ne.symm hoe) hse0')
      by_grind
  replace hsed : dist ze ztbp < r₁ := lt_of_lt_of_le hsed ztff
  by_cases hB : ∃ c ∈ S, SideAttach M.W c p t
  · -- **a chord `c` of `S` is attached at the same position**
    obtain ⟨c, hc, hAc⟩ := hB
    obtain ⟨oc, hoc, hoc2, hcs, hocD, hoco⟩ := attach_ray hM ztbkp hAc
    zubzh
    have hdx : ztgqc := by
      grind
    -- `e` and `c` leave in opposite directions
    have hopp : ztftp * zthiy < 0 := by
      rcases lt_trichotomy (ztftp * zthiy) 0 with h | h | h
      · zubh
      · grind
      · have := ray_eq hoe2 hoc2 h hoeD hocD hoeo hoco
        simp_all
    -- so `c` is the only chord of `S` attached there
    have hsole : ∀ c' ∈ S, SideAttach M.W c' p t → c' = c := by
      zujax
      obtain ⟨o', ho', ho'2, hc's, ho'D, ho'o⟩ := attach_ray hM zthxt hA'
      rcases lt_trichotomy ztzzw 0 with h | h | h
      · have hpos : 0 < zthiy * ztcan := by
          have h3 := mul_pos_of_neg_of_neg hopp h
          have h4 : ztftp * zthiy * ztzzw =
              ztftp ^ 2 * (zthiy * ztcan) := by_ring
          zukrz
          exact pos_of_mul_pos_right h3 ztqwr
        rw [hc's, hcs, ray_eq hoc2 ho'2 hpos hocD ho'D hoco ho'o]
      · grind
      · exact absurd (by rw [hes, hc's, ray_eq hoe2 ho'2 h hoeD ho'D hoeo ho'o] : e = c')
          by_grind
    -- the sector contains both horizontal directions, hence a half-plane
    have hse := ccw_unit (attach_ccw hM hA hoe hes) hoe2
    have hsc := ccw_unit (attach_ccw hM hAc hoc hcs) hoc2
    have hE : sideCcw ztqwh (ztcei : Point) ztpeb := by
      zuebw
      · grind
      grind
    have hW : sideCcw ztqwh (ztcyl : Point) ztpeb := by
      zuebw
      · grind
      grind
    obtain ⟨τ, hτ, hhalf⟩ : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ ∀ X : Point, 0 < τ * X.2 →
        sideCcw _ X _ := by
      rcases ccw_half (sub_ne_zero_of_ne hbv) (sub_ne_zero_of_ne hav) hE hW with h | h
      · exact ⟨1, Or.inl rfl, fun X hX => h X by_linarith⟩
      · exact ⟨-1, Or.inr rfl, fun X hX => by_grind⟩
    -- the half-disk is free
    have hH : halfDisk w r₁ τ ⊆ freeIn M.D S := by
      zuh
      have hxl : sideLeft M.W p t x := by
        zuhrd
        exact hhalf _ zthty
      obtain ⟨hxD, hxc⟩ := hfree x hx.1 hxl
      refine ztfwr
      rintro ⟨c', hc', hxc'⟩
      have hc'c := hsole c' hc' (hxc c' hc' hxc')
      rw [hc'c, hcs] at hxc'
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hxc'
      have := hx.2
      simp only [mem_ofPred_eq, lerp_snd, hoc2, sub_self, mul_zero, add_zero] at this
      grind
    have hx1 : ∀ s : ℝ, ∀ o : Point, o.2 = w.2 → dist ztrto w < r₁ →
        |(lerp w o s).1 - w.1| < r₁ := by
      intro s o _ hd
      refine lt_of_le_of_lt ?_ hd
      rw [Prod.dist_eq, ← Real.dist_eq]
      simp
    have hy2 : ∀ s : ℝ, ∀ o : Point, o.2 = w.2 → (lerp w o s).2 = w.2 := by
      simp
    -- the half-disk is in `R`
    have hHR : halfDisk w r₁ τ ⊆ R := by
      refine Chazelle.Chain.subset_regionsIn_of_inter hR ztlqi hH ?_
      have hcl := mem_closure_halfDisk' hτ hr₁ (hy2 se oe hoe2) (hx1 se oe hoe2 hsed)
      obtain ⟨y, hyR, hyH⟩ := mem_closure_iff_nhds.1 hcl R (hRo.mem_nhds hzeR)
      exact ⟨y, hyH, hyR⟩
    -- `R` touches `c`
    obtain ⟨sc, ⟨hsc1, hscd⟩, hsc0⟩ := ((lerp_near w oc hr₁).and
      self_mem_nhdsWithin).exists
    have hsc0' := hsc0
    have htR : TouchesIn M.D c R := by
      refine ⟨lerp w oc sc, ⟨?_, hoco sc ⟨hsc0', hsc1⟩⟩, closure_mono hHR
        (mem_closure_halfDisk' hτ hr₁ (hy2 sc oc hoc2) (hx1 sc oc hoc2 hscd))⟩
      zuoei; exact Geometry.mem_segment_iff_lerp.2 by_grind
    -- the two sides of `c` are the regions faced next to the attachment
    obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ := hM.attach_face hS hfin hc hAc
    obtain ⟨tU, tV⟩ := htouch hsole
    obtain ⟨U₀, V₀, -, -, -, -, hiff⟩ := chordSides_of_system hsys hc
    have h1 := (hiff R hR).1 htR
    have h2 := (hiff U hU).1 tU
    have h3 := (hiff V hV).1 tV
    have hRUV : R = U ∨ R = V := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
        first
        | exact by_grind
        | exact by_grind
        | exact by_grind
    rcases hRUV with rfl | rfl
    · exact ⟨p + t, r, harcU, Or.inr ztp⟩
    · exact ⟨l, p + t, harcV, Or.inr ztbt⟩
  · -- **no chord of `S` is attached there: the key is inside an arc of `R`**
    zugrf
    have hcut : ztyzm := by
      zuekr
      obtain ⟨rfl, rfl⟩ := sideKey_inj ht0 ht1 hA'.2.1 hA'.2.2.1 hk
      grind
    -- the small sector is free, hence in `R`
    obtain ⟨-, hpre, hoff⟩ := Chazelle.Chain.sideSector (S := (freeIn M.D S)ᶜ) hav hbv hr₁ (by
      zuddp

      exact ztiwj)
    set L := ball _ r₁ ∩
      {x | sideLeftOf _ _ _ x} with hL
    have hLfree : ztsbz := by
      zuh
      zufyi
      exact ztiwj
    have hzeL : ze ∈ L := ⟨hsed, hzel⟩
    have hLR :=
      Chazelle.Chain.subset_regionsIn_of_inter hR hpre hLfree ⟨ze, hzeL, hzeR⟩
    -- the arc around the key
    zuxi
    have hscale : Tendsto (fun s : ℝ => s * (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      zuloq
      · have : Tendsto (fun δ : ℝ => δ * (1 - t)) _ (𝓝 (0 * (1 - t))) :=
          (continuous_id.mul continuous_const).tendsto 0
        zudvn
        zuhv
      · exact mul_pos hx by_linarith
    have hfX : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ M.Faces p ztwlx X := by
      zudmr

      refine ⟨hs.2, harc.2.2.2.2.2.2 p _ hp by_nlinarith ztiid ?_⟩
      grind
    obtain ⟨s, hs1, hs2⟩ := (hoff.and hfX).exists
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        offset _ _ _ _ ∈ X :=
      hscale.eventually hs2.2
    zubrw
    have e : offset ztbp ztohw s ztckn =
        offset ztpr ztoa ztwlx ztxlw := by
      zuedr

    have hXR : ztpli := by
      zubba
      · zubh
      · exact absurd (h.le_bot ⟨hδ2, hLR by_grind⟩) zthxd
    zuktl
    exact ⟨l, r, harc, Or.inl hin⟩
variable {N : NF} {d : ℕ}

/-- **Taking the child on the side of the target keeps the target below.** -/
theorem below_lo (hD : IsDecomp N d) {k r : ℕ} (hk : k < N.nChords) (hb : N.Below ztckt r)
    (hs : r ∈ N.lowSide k) : N.Below (N.dnode k).lo r :=
  (hD.2.2.2.1 k hk r hb).2 hs
theorem below_hi (hD : IsDecomp N d) {k r : ℕ} (hk : k < N.nChords) (hb : N.Below ztckt r)
    (hs : r ∈ N.highSide k) : N.Below (N.dnode k).hi r :=
  (hD.2.2.2.2.1 k hk r hb).2 hs

/-- The target is below the root. -/
theorem below_root (hD : IsDecomp N d) {r : ℕ} (hr : r < N.nRegions) : N.Below N.root r :=
  hD.2.2.2.2.2.1 r hr
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
@[expose] public section
open BuildNF (codeLe wposOf tieBit buildNF gapStarts arcRec arcList evs evOf)
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Geometry (point_ext)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Event keys -/

/-- The key of the event at index `i` of the event list. -/
noncomputable def kE (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (i : ℕ) : ℝ :=
  M.key Q ztzyl
variable {m : ℕ} {j : ℕ}
theorem kap_evs (hm : m < E.length) :
    BuildSort.kap ztll m = kE M Q L E m := by
  zuue

/-- **The event keys are nondecreasing** along a `codeLe`-sorted list. -/
theorem kE_mono (hsort : E.Pairwise ztxi) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < E.length) : kE M Q L E i ≤ kE M Q L E i' := by
  zujcr
  · simp
  · zuffq

    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem by_omega, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    zubpp
    · grind
    simp_all

/-! ## The gap starts -/

/-- The start index (in `E`) of gap `j`. -/
noncomputable def gs (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (j : ℕ) : ℕ :=
  (gapStarts M Q L E).getD j 0
theorem mem_gapStarts : m ∈ gapStarts M Q L E ↔ m < E.length ∧
    ztwwi := by
  zumst
  simp
theorem gapStarts_pairwise : (gapStarts M Q L E).Pairwise ztfvn :=
  List.Pairwise.filter _ List.pairwise_lt_range
theorem gs_eq (hj : j < (gapStarts M Q L E).length) :
    gs M Q L E j = ztdon[j] := by
  unfold gs; simp_all
theorem gs_mem (hj : j < (gapStarts M Q L E).length) :
    gs M Q L E j ∈ gapStarts M Q L E := by
  rw [gs_eq hj]; simp
theorem gs_lt_len (hj : j < (gapStarts M Q L E).length) : gs M Q L E j < E.length :=
  (mem_gapStarts.1 (gs_mem hj)).1
theorem gs_lt_gs {j j' : ℕ} (hjj : j < j') (hj' : j' < (gapStarts M Q L E).length) :
    gs M Q L E j < gs M Q L E j' := by
  rw [gs_eq by_omega, gs_eq hj']
  exact List.pairwise_iff_getElem.1 gapStarts_pairwise j j' by_omega hj' hjj

/-- **The last gap starts at the last event.** -/
theorem gs_last (hE : 0 < E.length) :
    0 < (gapStarts M Q L E).length ∧
      gs M Q L E ztdbp = E.length - 1 := by
  have hmem : ztmsy := mem_gapStarts.2 by_omega
  obtain ⟨j₀, hj₀, hj₀e⟩ := List.mem_iff_getElem.1 hmem
  zuhwf

  have h0 : gs M Q L E j₀ = E.length - 1 := by rw [gs_eq hj₀]; omega
  zuct
  have hlt : ztknn := by
    grind
  have h1 := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E) hlt by_omega
  have h2 := gs_lt_len (M := M) (Q := Q) (L := L) (E := E)
    (j := (gapStarts M Q L E).length - 1) by_omega
  omega

/-- **A gap other than the last one** ends at the next event, with a larger key. -/
theorem gs_succ (hE : 0 < E.length) {j : ℕ} (hj : j + 1 < (gapStarts M Q L E).length) :
    gs M Q L E j + 1 < E.length ∧ kE M Q L E ztiku < kE M Q L E ztgjw := by
  obtain ⟨-, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  have h1 := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E)
    (j := j) (j' := (gapStarts M Q L E).length - 1) by_omega by_omega
  rw [hlast] at h1
  zubsc
  rcases (mem_gapStarts.1 (gs_mem (by omega : j <
    (gapStarts M Q L E).length))).2 with h | h
  · omega
  · rwa [kap_evs by_omega, kap_evs by_omega] at h

/-! ## The arcs of `buildNF` -/
theorem arcs_length (hK : 0 < L.length) :
    (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
  zuewm
theorem arc_s (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    ((buildNF M Q L E).arc j).s = wposOf L (E.getD ztiku 0) := by
  zudnb
  unfold NF.arc
  zuzx
  rfl
theorem arc_e (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    ((buildNF M Q L E).arc j).e = wposOf L (E.getD (ztgjw % E.length) 0) := by
  zudnb
  unfold NF.arc
  zuzx
  rfl
theorem key_s (hK : 0 < L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s = kE M Q L E ztiku := by
  rw [arc_s hK hj]; rfl

/-- The end of an arc other than the last one is the next event. -/
theorem key_e (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (hj : j + 1 < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).e = kE M Q L E ztgjw := by
  rw [arc_e hK by_omega, Nat.mod_eq_of_lt (gs_succ hE hj).1]; rfl

/-- **An arc other than the last one does not wrap.** -/
theorem key_s_lt_e (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (hj : j + 1 < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s < M.key Q ((buildNF M Q L E).arc j).e := by
  rw [key_s hK by_omega, key_e hK hE hj]; exact (gs_succ hE hj).2

/-- The last arc ends at the first event. -/
theorem key_e_last (hK : 0 < L.length) (hE : 0 < E.length) :
    M.key Q ((buildNF M Q L E).arc ztdbp).e = kE M Q L E 0 := by
  zucbk
  rw [arc_e hK by_omega, hlast, Nat.sub_add_cancel hE, Nat.mod_self]; rfl

/-- The last arc starts at the last event. -/
theorem key_s_last (hK : 0 < L.length) (hE : 0 < E.length) :
    M.key Q ((buildNF M Q L E).arc ztdbp).s =
      kE M Q L E ztswz := by
  zucbk
  rw [key_s hK by_omega, hlast]

/-! ## Buckets -/

/-- **The bucket condition** of a key `x` for the bucket `b` of the normal form `N` (`A` arcs):
`b = 0`: `x` at most the end of the last arc; `1 ≤ b < A`: `x` on the closed arc `b - 1`;
`b = A`: `x` at least the start of the last arc. -/
def BktKey (M : Model) (Q : Polygon) (N : NF) (x : ℝ) (b : ℕ) : Prop :=
  (b = 0 ∧ x ≤ M.key Q (N.arc ztdfr).e) ∨
  (1 ≤ b ∧ b < N.arcs.length ∧ M.key Q (N.arc zteow).s ≤ x ∧
    x ≤ M.key Q (N.arc zteow).e) ∨
  (b = N.arcs.length ∧ M.key Q (N.arc ztdfr).s ≤ x)
theorem BktKey.le {N : NF} {x : ℝ} {b : ℕ} (h : BktKey M Q N x b) : b ≤ N.arcs.length := by
  rcases h with ⟨rfl, -⟩ | ⟨-, h, -⟩ | ⟨rfl, -⟩ <;> omega

/-- **A smaller bucket has a smaller key**, through an event key of `E`. -/
theorem bktKey_le (hK : 0 < L.length) (hE : 0 < E.length) (hsort : E.Pairwise ztxi)
    {x y : ℝ} {b b' : ℕ} (hx : BktKey M Q ztob x b)
    (hy : BktKey M Q ztob y b') (hbb : b < b') :
    ∃ i, i < E.length ∧ x ≤ kE M Q L E i ∧ kE M Q L E i ≤ y := by
  have hA := arcs_length (M := M) (Q := Q) (E := E) hK
  obtain ⟨hA0, hlast⟩ := gs_last (M := M) (Q := Q) (L := L) hE
  -- the lower bound of `y`'s bucket
  have hlow : ∀ i, (b' < (gapStarts M Q L E).length → i ≤ gs M Q L E (b' - 1)) →
      i ≤ E.length - 1 → 1 ≤ b' → kE M Q L E i ≤ y := by
    intro i hi hi' hb1
    rcases hy with ⟨rfl, -⟩ | ⟨-, hb2, hs, -⟩ | ⟨hbA, hs⟩
    · omega
    · zukse
      rw [key_s hK by_omega] at hs
      exact le_trans (kE_mono hsort (hi hb2) (gs_lt_len by_omega)) hs
    · rw [hA, key_s_last hK hE] at hs
      exact le_trans (kE_mono hsort hi' by_omega) hs
  rcases hx with ⟨rfl, hx⟩ | ⟨hb1, hb2, -, hx⟩ | ⟨hbA, -⟩
  · rw [hA, key_e_last hK hE] at hx
    grind
  · zukse
    have hj : b - 1 + 1 < (gapStarts M Q L E).length := by_omega
    rw [show b - 1 = b - 1 from rfl, key_e hK hE hj] at hx
    have hsucc := gs_succ hE hj
    refine ⟨gs M Q L E _ + 1, hsucc.1, hx, hlow _ ztloe by_omega by_omega⟩
    have := gs_lt_gs (M := M) (Q := Q) (L := L) (E := E) (j := b - 1) (j' := b' - 1)
      by_omega by_omega
    omega
  · exfalso
    have := hy.le
    omega

/-! ## Three chords at one position -/

/-- **Three admissible chords attached at one walk position are not distinct**: each leaves the
position horizontally, to the east or to the west, and two leaving in the same direction are equal
(`Restore.ray_eq`). -/
theorem three_attach (hM : WalkAx M) {c₁ c₂ c₃ : Set Point} (h₁ : c₁ ∈ M.Adm) (h₂ : c₂ ∈ M.Adm)
    (h₃ : c₃ ∈ M.Adm) {p : ℕ} {t : ℝ} (a₁ : SideAttach M.W c₁ p t) (a₂ : SideAttach M.W c₂ p t)
    (a₃ : SideAttach M.W c₃ p t) : c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃ := by
  obtain ⟨o₁, ho₁, ho₁2, hc₁, ho₁D, ho₁o⟩ := Restore.attach_ray hM h₁ a₁
  obtain ⟨o₂, ho₂, ho₂2, hc₂, ho₂D, ho₂o⟩ := Restore.attach_ray hM h₂ a₂
  obtain ⟨o₃, ho₃, ho₃2, hc₃, ho₃D, ho₃o⟩ := Restore.attach_ray hM h₃ a₃
  set w := sidePt M.W p t
  have hd : ztgqc := by_grind
  have d₁ := hd o₁ ho₁ ho₁2
  have d₂ := hd o₂ ho₂ ho₂2
  have d₃ := hd o₃ ho₃ ho₃2
  rcases lt_or_gt_of_ne (mul_ne_zero d₁ d₂) with h12 | h12
  · rcases lt_or_gt_of_ne (mul_ne_zero d₁ d₃) with h13 | h13
    · zulw
      have h23 : 0 < ztodz * ztoea := by
        have := mul_pos_of_neg_of_neg h12 h13
        have e : ztody * ztodz * (ztody * ztoea) =
          ztody ^ 2 * (ztodz * ztoea) := by_ring
        zudtu
        exact pos_of_mul_pos_right this ztqwr
      rw [hc₂, hc₃, Restore.ray_eq ho₂2 ho₃2 h23 ho₂D ho₃D ho₂o ho₃o]
    · zuhl
      rw [hc₁, hc₃, Restore.ray_eq ho₁2 ho₃2 h13 ho₁D ho₃D ho₁o ho₃o]
  · left
    rw [hc₁, hc₂, Restore.ray_eq ho₁2 ho₂2 h12 ho₁D ho₂D ho₁o ho₂o]

/-- **Equal keys of event positions are equal positions** (edge and parameter). -/
theorem pos_eq_of_key (hok : ChordTriplesOK M Q L) {a a' : ℕ} (ha : a < 2 * L.length)
    (ha' : a' < 2 * L.length) (h : M.key Q ztdwl = M.key Q ztudg) :
    (wposOf L a).edge = (wposOf L a').edge ∧ M.param Q ztdwl = M.param Q ztudg := by
  obtain ⟨-, t0, t1, -⟩ := BuildNF.attach_wposOf hok ha
  obtain ⟨-, t0', t1', -⟩ := BuildNF.attach_wposOf hok ha'
  unfold Model.key at h
  have h1 : ((wposOf L a).edge : ℝ) < (wposOf L a').edge + 1 := by_linarith
  have h2 : ((wposOf L a').edge : ℝ) < (wposOf L a).edge + 1 := by_linarith
  have h1' : (wposOf L a).edge < (wposOf L a').edge + 1 := by exact_mod_cast h1
  have h2' : (wposOf L a').edge < (wposOf L a).edge + 1 := by exact_mod_cast h2
  grind

/-- The chords of a valid list are admissible. -/
theorem chordSet_adm (hok : ChordTriplesOK M Q L) {k : ℕ} (hk : k < L.length) :
    BuildOrder.chordSet M Q L k ∈ M.Adm :=
  hok.1.2.1 ⟨L.getD k ztt, BuildOrder.getD_mem hk, rfl⟩

/-- **A smaller bucket means an earlier event** for the codes of new chords `L₂` appended to `L`:
the keys are ordered through an event key of `E`; equal keys would put three distinct chords (or
both ends of one chord) at one walk position. -/
theorem codeLe_of_bkt (hM : WalkAx M) {L₂ : List zte} (hok : ChordTriplesOK M Q ztfi)
    (hK : 0 < L.length) (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztxi) {a a' b b' : ℕ} (ha : 2 * L.length ≤ a)
    (ha2 : a < 2 * (L ++ L₂).length) (ha' : 2 * L.length ≤ a') (ha2' : a' < 2 * (L ++ L₂).length)
    (hx : BktKey M Q ztob (M.key Q ztysc) b)
    (hy : BktKey M Q ztob (M.key Q ztysb) b') (hbb : b < b') :
    codeLe M Q ztfi a a' := by
  zubcn
  obtain ⟨i, hi, hxi, hiy⟩ := bktKey_le hK by_omega hsort hx hy hbb
  rcases lt_or_eq_of_le (hxi.trans hiy) with hlt | heq
  · tauto
  by_cases haa : a = a'
  · subst haa; tauto
  exfalso
  have hlen : ztfkk := List.length_append
  -- the old event
  have hc₀ : E.getD i 0 < 2 * L.length := by
    have hmem : E.getD i 0 ∈ E := by
      simp_all
    grind
  have hc₀' : E.getD i 0 < 2 * (L ++ L₂).length := by_omega
  have hkc : M.key Q ztysd = kE M Q L E i := by
    rw [DownDrv.wposOf_append hc₀]; rfl
  have hxa : M.key Q ztysc = M.key Q ztysd := by
    grind
  have hya : M.key Q ztysb = M.key Q ztysd := by
    simp_all
  obtain ⟨e1, p1⟩ := pos_eq_of_key hok ha2 hc₀' hxa
  obtain ⟨e2, p2⟩ := pos_eq_of_key hok ha2' hc₀' hya
  by_cases hii : a / 2 = a' / 2
  · -- the two ends of one chord are distinct points
    have hpos : M.pos Q ztysc = M.pos Q ztysb := by
      zuckw
    have hlt := BuildNF.pos_lt' hM hok (i := a / 2) by_omega
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · have h1' : a' % 2 = 1 := by_omega
      rw [BuildNF.wposOf_even h0, BuildNF.wposOf_odd h1', ← hii] at hpos
      simp_all
    · have h0' : a' % 2 = 0 := by_omega
      rw [BuildNF.wposOf_odd h1, BuildNF.wposOf_even h0', ← hii] at hpos
      simp_all
  · have A₀ := BuildNF.attach_wposOf hok hc₀'
    have A₁ := BuildNF.attach_wposOf hok ha2
    have A₂ := BuildNF.attach_wposOf hok ha2'
    rw [e1, p1] at A₁
    rw [e2, p2] at A₂
    rcases three_attach hM ztnwz ztnwz
        ztnwz A₀ A₁ A₂ with h | h | h
    · have := BuildOrder.chordSet_inj hok by_omega by_omega h; omega
    · have := BuildOrder.chordSet_inj hok by_omega by_omega h; omega
    · exact hii (BuildOrder.chordSet_inj hok by_omega by_omega h)
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
@[expose] public section
open BuildNF (codeLe wposOf buildNF gapStarts)
open Chazelle.Chain (SideAttach sideInArc)
variable {M : Model} {Q : Polygon}

/-! ## The decision of the arc scan -/

/-- The scan's test on arc `j` of `A` arcs, with `t₁ = [key s ≤ key x]`, `t₂ = [key x ≤ key e]`. -/
def matchB (A j : ℕ) (t₁ t₂ : Bool) : Bool := if j + 1 < A then t₁ && t₂ else t₂ || t₁

/-- The bucket the scan assigns on a match. -/
def bktB (A j : ℕ) (t₂ : Bool) : ℕ := if j + 1 < A then j + 1 else if t₂ then 0 else A

/-- The arc of a bucket. -/
def arcOfB (A b : ℕ) : ℕ := if b = 0 ∨ A ≤ b then A - 1 else b - 1
theorem arcOfB_bktB {A j : ℕ} (hj : j < A) (t₂ : Bool) : arcOfB A (bktB A j t₂) = j := by
  unfold arcOfB bktB
  grind

/-- **A match gives the bucket condition.** -/
theorem bkt_of_match (N : NF) {x : ℝ} {j : ℕ} (hj : j < N.arcs.length) {t₁ t₂ : Bool}
    (h₁ : t₁ = true ↔ M.key Q (N.arc j).s ≤ x) (h₂ : t₂ = true ↔ x ≤ M.key Q (N.arc j).e)
    (hm : matchB N.arcs.length j t₁ t₂ = true) : BktKey M Q N x (bktB N.arcs.length j t₂) := by
  unfold matchB at hm
  unfold bktB
  by_cases h : j + 1 < N.arcs.length
  · zvnbq at hm ⊢
    simp only [Bool.and_eq_true] at hm
    zujga
  · zvnoi at hm ⊢
    have hjA : j = N.arcs.length - 1 := by_omega
    by_cases ht : t₂ = true
    · rw [ite_eq_left ht]
      left
      simp_all
    · zulqk
      have ht1 : t₁ = true := by
        simp_all
      zujga

/-! ## The ends of a new chord lie on arcs of its region -/

/-- **The ends of a chord splitting region `r` lie on closed arcs of `r`.** -/
theorem exists_closedArc (hM : WalkAx M) {N : NF} {reg : ℕ → Set Point} (hNF : IsNF M Q N)
    (hregs : Restore.NFRegs M Q N reg) (hne : (N.F M Q).Nonempty) {r : ℕ} (hr : r < N.nRegions)
    {e : Set Point} (he : e ∈ M.Adm) (hw : Restore.SplitsWell M ztdu ztcz e) {p : ℕ}
    {τ : ℝ} (hA : SideAttach M.W e p τ) :
    ∃ j ∈ (N.region r).arcs, j < N.arcs.length ∧
      Restore.ClosedArc ztbpl ztdfq (p + τ) := by
  obtain ⟨a, b, harc, hcl⟩ := Restore.attach_closedArc hM hNF.1.2.1 hNF.1.1 hne ztobe
    he hw.1 hw.2.1 hA
  obtain ⟨j, hj, hjr, hs, he'⟩ := hregs.2.2.1.2.2.1 r hr a b harc
  refine ⟨j, (hregs.2.2.1.2.2.2 r hr j).2 zthnb, hj, ?_⟩
  simp_all
variable {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- **In `buildNF`, an end on a closed arc matches.** -/
theorem match_of_closedArc (hK : 0 < L.length) (hE : 0 < E.length) {j : ℕ}
    (_hj : j < (buildNF M Q L E).arcs.length) {x : ℝ}
    (hc : Restore.ClosedArc zthrj
      zthri x) {t₁ t₂ : Bool}
    (h₁ : t₁ = true ↔ M.key Q ((buildNF M Q L E).arc j).s ≤ x)
    (h₂ : t₂ = true ↔ x ≤ M.key Q ((buildNF M Q L E).arc j).e) :
    matchB (buildNF M Q L E).arcs.length j t₁ t₂ = true := by
  unfold matchB
  by_cases h : j + 1 < (buildNF M Q L E).arcs.length
  · zueyn
    have hlt := key_s_lt_e (M := M) (Q := Q) hK hE (j := j) (by rw [← arcs_length hK]; exact h)
    zuhos
    zuik
    · zuhaz
      grind
    · grind
    grind
  · zubme
    simp only [Bool.or_eq_true]
    zuik
    · zuhaz
      grind
    · simp_all
    simp_all

/-! ## Bucket sizes -/

/-- **A bucket whose codes all belong to one chord has at most two codes.** -/
theorem bcnt_le_two {bk : ℕ → ℕ} {n b : ℕ}
    (h : ∀ q q', q < n → q' < n → bk q = b → bk q' = b → q / 2 = q' / 2) :
    DrvR.bcnt bk n b ≤ 2 := by
  unfold DrvR.bcnt
  zuho

  set l := DrvR.bfilt bk n b with hl
  have hpw : l.Pairwise ztfvn := List.Pairwise.filter _ List.pairwise_lt_range
  have m0 := (DrvR.mem_bfilt (bk := bk)).1 (List.getElem_mem (l := l) (n := 0) by_omega)
  have m2 := (DrvR.mem_bfilt (bk := bk)).1 (List.getElem_mem (l := l) (n := 2) by_omega)
  have h01 := List.pairwise_iff_getElem.1 hpw 0 1 by_omega by_omega by_omega
  have h12 := List.pairwise_iff_getElem.1 hpw 1 2 by_omega by_omega by_omega
  grind
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
@[expose] public section
open BuildNF (codeLe wposOf buildNF)
open Restore (FoundOK NewOK newSet highList degOf oldL)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The walk position of end `s` (`0` left, `1` right) of a chord triple. -/
def endPos (t : ℕ × ℕ × ℕ) (s : ℕ) : WPos :=
  if s = 0 then ⟨t.2.1, t.1 + 1⟩ else ⟨t.2.2, t.1 + 1⟩

/-- The default pair of `newL`. -/
abbrev dflt : ℕ × zte := ztlt
theorem getD_map_snd {newL : List ztwjg} (i : ℕ) :
    (newL.map Prod.snd).getD i ztt = (newL.getD i dflt).2 := by
  grind

/-- The positions of the new event codes. -/
theorem wposOf_new {L₂ : List zte} {q : ℕ} (_hq : q < 2 * L₂.length) :
    wposOf ztfi ztbhj = endPos (L₂.getD ztbeu ztt) ztkcq := by
  zuffd

  have hg : ztxsw := by
    grind
  unfold wposOf endPos
  zuexi

  rfl

/-- **The buckets of the new events** written by the region loop: for every new code `q` the
bucket condition of its position, on an arc of the region of its chord. -/
structure BktOK (M : Model) (Q : Polygon) (N : NF) (newL : List ztwjg)
    (bk : ℕ → ℕ) : Prop where
  key : ∀ q, q < 2 * newL.length →
    BktKey M Q N (M.key Q ztyje) ztbse
  arc : ∀ q, q < 2 * newL.length →
    arcOfB N.arcs.length ztbse ∈ (N.region (newL.getD ztbeu dflt).1).arcs
theorem getD_mem' {newL : List ztwjg} {i : ℕ} (hi : i < newL.length) :
    newL.getD i dflt ∈ newL := by
  simp_all

/-- The region records of `buildNF`. -/
theorem region_buildNF {r : ℕ} (hr : r < L.length + 1) :
    (buildNF M Q L E).region r =
      ⟨BuildNF.regArcs M Q L E r, BuildNF.regChords M Q L E r, BuildNF.regWt M Q L E r⟩ := by
  unfold NF.region
  zuhjz
  simp [buildNF, hr]

/-- Without chords there are no high regions. -/
theorem newL_nil {reg : ℕ → Set Point} {D : ℕ} {newL : List ztwjg}
    (hnew : NewOK M Q ztob reg D newL) (hK : L.length = 0) : newL = [] := by
  rcases newL with _ | ⟨p, newL⟩
  · rfl
  · exfalso
    have hp : p.1 ∈ (p :: newL).map Prod.fst := by_simp
    rw [hnew.fst, Restore.mem_highList] at hp
    have hr : p.1 < L.length + 1 := by
      have := hp.1; simpa [NF.nRegions, buildNF] using this
    have h0 : degOf ztob p.1 = 0 := by
      unfold degOf
      zulqs
      simp [BuildNF.regChords, hK]
    omega

/-- **The precondition of the splice after the region loop of a round.** -/
theorem round_ok (hGM : GoodModel M) (hok : ChordTriplesOK M Q L)
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztxi)
    {reg : ℕ → Set Point} (hregs : Restore.NFRegs M Q ztob reg) {D : ℕ}
    {newL : List ztwjg} (hnew : NewOK M Q ztob reg D newL)
    {bk : ℕ → ℕ} (hbk : BktOK M Q ztob newL bk) :
    ChordTriplesOK M Q ztbsa ∧
    (∀ q, q < 2 * (newL.map Prod.snd).length → bk q ≤ (buildNF M Q L E).arcs.length) ∧
    (∀ q q', q < 2 * (newL.map Prod.snd).length → q' < 2 * (newL.map Prod.snd).length →
      bk q < bk q' →
      codeLe M Q ztbsa ztbhj ztekx) ∧
    (∀ b, DrvR.bcnt bk (2 * (newL.map Prod.snd).length) b ≤ 2) := by
  zubm
  zucsr

  have hok' : ztbabs := by
    have := Restore.round_list_ok hM hNF hregs hnew
    simp_all
  zujgs
  have hkey : ∀ q, q < 2 * newL.length →
      M.key Q (wposOf ztbsa ztbhj) =
        M.key Q ztyje := by
    zuco
    rw [wposOf_new by_simp_all, getD_map_snd]
  refine ⟨hok', fun q hq => (hbk.key q hq).le, fun q q' hq hq' hbb => ?_, fun b => ?_⟩
  · zujcu
    · rw [newL_nil hnew hK] at hq; simp_all
    · have hlen : (L ++ newL.map Prod.snd).length = L.length + newL.length := by_simp
      refine codeLe_of_bkt hM hok' hK hperm hsort by_omega by_omega by_omega
        by_omega ?_ ?_ hbb
      · zuoir; exact hbk.key q hq
      · zuois; exact hbk.key q' hq'
  · refine bcnt_le_two fun q q' hq hq' hb hb' => ?_
    have hr : ∀ q, q < 2 * newL.length → (newL.getD ztbeu dflt).1 < (buildNF M Q L E).nRegions :=
      fun q hq => hnew.lt (getD_mem' by_omega)
    have ha := hbk.arc q hq
    have ha' := hbk.arc q' hq'
    rw [hb] at ha
    rw [hb'] at ha'
    have e1 := ((hregs.2.2.1.2.2.2 _ (hr q hq) _).1 ha).2
    have e2 := ((hregs.2.2.1.2.2.2 _ (hr q' hq') _).1 ha').2
    have hfst : ztvzw[q / 2]' by_grind =
        ztvzw[q' / 2]' by_grind := by
      zukpm
      have g1 : newL[q / 2]' by_omega = newL.getD ztbeu dflt := by
        zugcd
      have g2 : newL[q' / 2]' by_omega = newL.getD (q' / 2) dflt := by
        zugcd
      simp_all
    exact (hnew.nodup_fst.getElem_inj_iff).1 hfst

/-- **The family after a round.** -/
theorem round_family (hGM : GoodModel M) (hok : ChordTriplesOK M Q L)
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztxi)
    {reg : ℕ → Set Point} (hregs : Restore.NFRegs M Q ztob reg) {D : ℕ}
    {newL : List ztwjg} (hnew : NewOK M Q ztob reg D newL) {d γ : ℕ}
    (hdeg : M.DegLe ztkpi d)
    (hsg : M.Semigranular ztkpi γ) (E' : List ℕ)
    (hperm' : E'.Perm ztihj)
    (hsort' : E'.Pairwise (codeLe M Q ztbsa)) :
    (buildNF M Q L E).F M Q ⊆ (buildNF M Q ztbsa E').F M Q ∧
      M.DegLe ztyag ztzxa ∧
      M.Semigranular ztyag γ ∧
      (L ++ newL.map Prod.snd).length + 1 ≤ 2 * ztkr := by
  zubm
  zucsr

  have hok' : ztbabs := by
    have := Restore.round_list_ok hM hNF hregs hnew
    simp_all
  obtain ⟨-, hmap', -⟩ := BuildNF.isNF_goodModel hGM hok' hperm' hsort'
  have hF' : (buildNF M Q ztbsa E').F M Q =
      (buildNF M Q L E).F M Q ∪ newSet M Q newL := by
    rw [Gran.F_of_map hmap', ← Restore.round_lset (N := buildNF M Q L E), holdL]
  have hSa : (buildNF M Q L E).F M Q ⊆ M.Adm := hNF.1.2.1
  have hSf : ((buildNF M Q L E).F M Q).Finite := hNF.1.1
  have hdata := Restore.round_data hM hNF hregs hnew
  have hdeg' := Restore.round_degLe hM hSa hSf hdata hdeg (Restore.round_all hNF hregs hnew)
  have hlenNew : newL.length ≤ L.length + 1 := by
    have := congrArg List.length hnew.fst
    zubus
    zubk
    zuhit
    zuggb
  zudtz
  refine ⟨Set.subset_union_left, hdeg', Restore.semigranular_mono hM Set.subset_union_left
    zttcy ztvty hsg, ?_⟩
  grind
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
noncomputable def tA (M : Model) (Q : Polygon) (N : NF) (x : WPos) (j : ℕ) : Bool :=
  decide (M.key Q (N.arc j).s ≤ M.key Q x)

/-- The second decision: `x` is not after the end of arc `j`. -/
noncomputable def tB (M : Model) (Q : Polygon) (N : NF) (x : WPos) (j : ℕ) : Bool :=
  decide (M.key Q x ≤ M.key Q (N.arc j).e)

/-- **The result of a scan**: the bucket condition of `x`, on an arc of region `r`. -/
def ScanFound (M : Model) (Q : Polygon) (N : NF) (r : ℕ) (x : WPos) (b : ℕ) : Prop :=
  BktKey M Q N ztbys b ∧ arcOfB N.arcs.length b ∈ (N.region r).arcs

/-- The data of an arc scan: the end `x`, region `r` of `N` (its arc list at `lp`, the arc
records at `AB`, in the memory `m`), the model descriptor at `MD`. -/
structure ScanGood (P : Polygon) (W : ℕ) (M : Model) (N : NF) (r : ℕ) (x : WPos) (m : ℕ → ℕ)
    (MD AB lp : ℕ) : Prop where
  hG : GoodEnv P
  hW : hostWords P.n ≤ W
  hDW : MD + 6 ≤ W
  hCW : NFLoc.LocChainWF P W m MD
  hM : ModelDescAt m MD zta M
  xe : x.edge < M.W.n
  xh : 1 ≤ x.hgt
  xp : ProperPos M zta P.n x
  lpW : lp + (N.region r).arcs.length ≤ W
  ABW : AB + 5 * N.arcs.length ≤ W
  list : ∀ t, t < (N.region r).arcs.length → m zttsm = (N.region r).arcs.getD t 0
  arcs : ∀ j ∈ (N.region r).arcs, j < N.arcs.length ∧
    m ztbph = (N.arc j).s.edge ∧ m ztbpi = (N.arc j).s.hgt ∧
    m ztbyb = (N.arc j).e.edge ∧ m ztbyc = (N.arc j).e.hgt ∧
    ProperPos M zta P.n (N.arc j).s ∧ ProperPos M zta P.n (N.arc j).e ∧
    1 ≤ (N.arc j).e.hgt ∧ (N.arc j).e.edge < M.W.n

/-- The step bound of one arc of the scan. -/
def scanK : ℕ := 11000
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- Loading arc `j`. -/
theorem ldArc_exec (d : Config) (hw : WordsBounded W d) {lp t AB j xe xh : ℕ}
    (h43 : d.nreg 216043 = lp) (h44 : d.nreg 216044 = t) (h14 : d.nreg 216014 = AB)
    (h02 : d.nreg 216002 = 1) (h40 : d.nreg 216040 = xe) (h41 : d.nreg 216041 = xh)
    (hj : d.nmem zttsm = j) (hW : AB + 5 * j + 5 ≤ W) (hW' : lp + t ≤ W) :
    ∃ d' k, Exec P W ldArc d d' k ∧ k = 17 ∧
      d'.nreg 42100 = xe ∧ d'.nreg 42101 = xh ∧
      d'.nreg 42102 = d.nmem ztbph ∧ d'.nreg 42103 = d.nmem ztbpi ∧
      d'.nreg 42104 = d.nmem ztbyb ∧ d'.nreg 42105 = d.nmem ztbyc ∧
      d'.nreg 216045 = j ∧ d'.nreg 216054 = j + 1 ∧ FrameB BldArc d d' := by
  obtain ⟨d', k, ex, hk, q⟩ : ∃ d' k, Exec P W ldArc d d' k ∧ k = 17 ∧
      (d'.nreg 42100 = xe ∧ d'.nreg 42101 = xh ∧
      d'.nreg 42102 = d.nmem ztbph ∧ d'.nreg 42103 = d.nmem ztbpi ∧
      d'.nreg 42104 = d.nmem ztbyb ∧ d'.nreg 42105 = d.nmem ztbyc ∧
      d'.nreg 216045 = j ∧ d'.nreg 216054 = j + 1) := by
    unfold ldArc
    exec_block
    all_goals try (config_simp; simp only [h43, h44, h14, h02, h40, h41, hj]; omega)
    refine ztgpi <;> config_simp <;>
      simp only [h43, h44, h14, h02, h40, h41, hj] <;> (congr 1; ring)
  exact ⟨d', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2, exec_frameB ex wr_ldArc⟩

/-- The decision on arc `j`. -/
theorem decS_exec (d : Config) (hw : WordsBounded W d) {A j : ℕ} {t₁ t₂ : Bool}
    (h54 : d.nreg 216054 = j + 1) (h17 : d.nreg 216017 = A) (h03 : d.nreg 216003 = 0)
    (h07 : d.nreg 42107 = if t₁ then 1 else 0) (h09 : d.nreg 42109 = if t₂ then 1 else 0) :
    ∃ d' k, Exec P W decS d d' k ∧ k ≤ 7 ∧
      d'.nreg 216053 = zthyi ∧
      FrameB ztlos d d' := by
  obtain ⟨d', k, ex, hk, q⟩ : ∃ d' k, Exec P W decS d d' k ∧ k ≤ 7 ∧
      d'.nreg 216053 = zthyi := by
    unfold decS matchB bktB
    have hA := h17 ▸ hw.1 216017
    by_cases hjA : j + 1 < A
    · zudd
      rw [ite_eq_left hjA, ite_eq_left hjA]
      cases t₁
      · refine spec_ifLtN_false by_simp_all ztevs
      · zuek
        cases t₂
        · zulzu
        · refine spec_ifLtN_true by_simp_all
            ztxcs
          simp_all
    · zubv
      rw [ite_eq_right hjA, ite_eq_right hjA]
      cases t₂
      · zudx
        cases t₁
        · zulzu
        · refine spec_ifLtN_true by_simp_all
            ztxcs
          simp_all
      · refine spec_ifLtN_true by_simp_all
          (spec_instr (Exec.constN hw _ _ ztbg) fun _ => zteh)
        simp
  exact ⟨d', k, ex, hk, q, exec_frameB ex wr_decS⟩

/-- The decision bit of `halfS` as a key comparison. -/
theorem keyBit {M : Model} {x s : WPos} (hx : ProperPos M zta P.n x)
    (hs : ProperPos M zta P.n s) (hx1 : 1 ≤ x.hgt) :
    (if keyDec zta P.n x ztjtx s = true then 1 else 0) =
      (if decide (M.key zta s ≤ M.key zta x) = true then 1 else 0) := by
  have h := keyDec_iff hx hs
  unfold KeyPred at h
  grind
set_option maxHeartbeats 4000000 in
/-- **One arc of the scan.** -/
theorem scanBody_exec {M : Model} {N : NF} {r : ℕ} {x : WPos} {m : ℕ → ℕ} {MD AB lp : ℕ}
    (hS : ScanGood P W M N r x m MD AB lp) (d : Config) (hw : WordsBounded W d) (hm : d.nmem = m)
    {t : ℕ} (ht : t < (N.region r).arcs.length)
    (h40 : d.nreg 216040 = x.edge) (h41 : d.nreg 216041 = x.hgt) (h43 : d.nreg 216043 = lp)
    (h44 : d.nreg 216044 = t) (h14 : d.nreg 216014 = AB) (h17 : d.nreg 216017 = N.arcs.length)
    (h02 : d.nreg 216002 = 1) (h03 : d.nreg 216003 = 0) (h4 : d.nreg 40000 = MD) :
    ∃ d' k, Exec P W scanBody d d' k ∧ k ≤ scanK ∧ d'.nreg 216044 = t + 1 ∧
      d'.nreg 216053 = (if matchB N.arcs.length ztml
          (tA M zta N x ztml)
          ztywv
        then bktB N.arcs.length ztml
          ztywv
        else d.nreg 216053) ∧ FrameB Bscan d d' := by
  set j := (N.region r).arcs.getD t 0 with hjd
  have hjm : ztgav := by
    simp_all
  obtain ⟨hjA, ms1, ms2, me1, me2, hps, hpe, he1, hee⟩ := hS.arcs j hjm
  have hW3 : ztmd := by have := hS.hW; unfold hostWords at this; omega
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a05, a45, a54, f₁⟩ := ldArc_exec (P := P) d hw
    h43 h44 h14 h02 h40 h41 (by rw [hm, hS.list t ht]) (by have := hS.ABW; omega)
    (by have := hS.lpW; omega)
  rw [hm, ms1] at a02
  rw [hm, ms2] at a03
  rw [hm, me1] at a04
  rw [hm, me2] at a05
  zud
  zuepx
  have hm₁ : d₁.nmem = m := by zunok
  -- the first decision
  obtain ⟨d₂, k₂, e₂, hk₂, -, b07, f₂⟩ := BuildRam.halfS_exec (P := P) hS.hG hW3 d₁ w₁
    (qe := 42100) (qh := 42101) (se := 42102) (sh := 42103) (dd := 42106) (dst := 42107)
    by_decide by_decide by_decide (by rw [g₁ _ by_decide, h4]; exact hS.hDW)
    (by zunrw; exact hS.hCW) (M := M)
    (by zunrw; exact hS.hM) (by zuodl; exact hS.xe)
    (by rw [a01]; exact hS.xp.2.2)
  rw [a00, a01, a02, a03] at b07
  rw [keyBit hS.xp hps hS.xh] at b07
  zue
  zucgb
  -- the second decision
  obtain ⟨d₃, k₃, e₃, hk₃, -, b09, f₃⟩ := BuildRam.halfS_exec (P := P) hS.hG hW3 d₂ w₂
    (qe := 42104) (qh := 42105) (se := 42100) (sh := 42101) (dd := 42108) (dst := 42109)
    by_decide by_decide by_decide
    (by rw [g₂ _ by_decide, g₁ _ by_decide, h4]; exact hS.hDW)
    (by zunfw; exact hS.hCW) (M := M)
    (by zunfw; exact hS.hM)
    (by rw [g₂ _ by_decide, a04]; omega)
    (by rw [g₂ _ by_decide, a05]; exact hpe.2.2)
  rw [g₂ _ by_decide, g₂ _ by_decide, g₂ _ by_decide, g₂ _ by_decide, a04, a05, a00,
    a01] at b09
  rw [keyBit hpe hS.xp he1] at b09
  zubj
  zuepy
  -- the decision
  have b07' : d₃.nreg 42107 = if tA M zta N x j then 1 else 0 := by
    rw [g₃ _ by_decide, b07]; rfl
  have b09' : d₃.nreg 42109 = if tB M zta N x j then 1 else 0 := by
    rw [b09]; rfl
  obtain ⟨d₄, k₄, e₄, hk₄, v53, f₄⟩ := decS_exec (P := P) d₃ w₃ (A := N.arcs.length) (j := j)
    (by rw [g₃ _ by_decide, g₂ _ by_decide, a54])
    (by rw [g₃ _ by_decide, g₂ _ by_decide, g₁ _ by_decide, h17])
    (by rw [g₃ _ by_decide, g₂ _ by_decide, g₁ _ by_decide, h03]) b07' b09'
  zucc
  -- the increment
  have i44 : d₄.nreg 216044 = t := by
    rw [f₄.1 _ by_decide, g₃ _ by_decide, g₂ _ by_decide, g₁ _ by_decide, h44]
  have i02 : d₄.nreg 216002 = 1 := by
    rw [f₄.1 _ by_decide, g₃ _ by_decide, g₂ _ by_decide, g₁ _ by_decide, h02]
  obtain ⟨d₅, k₅, e₅, hk₅, v44⟩ : ∃ d₅ k₅, Exec P W (block [.addN 216044 216044 216002]) d₄ d₅ k₅ ∧
      k₅ = 1 ∧ d₅ = { d₄ with nreg := upd d₄.nreg 216044 (t + 1) } := by
    exec_block
    · rw [i44, i02]; have := hS.lpW; omega
    simp_all
  have f₅ : FrameB Bscan d₄ d₅ := by
    zumpc
    exact ⟨fun q hq => by
      zubi
      rw [Machine.upd_other _ _ _ (by rintro rfl; simp [Bscan] at hq)], by_simp_all, rfl, rfl,
      rfl⟩
  have F₁ := fbMono f₁ bldArc_scan
  have F₂ := fbMono f₂ zttgu
  have F₃ := fbMono f₃ zttgu
  have F₄ := fbMono f₄ b53_scan
  refine ⟨d₅, k₁ + ztwqm, .seq e₁ ztbq, ?_, ?_, ?_,
    F₁.trans (F₂.trans (F₃.trans (F₄.trans f₅)))⟩
  · unfold scanK; omega
  · simp_all
  · zumpc
    zubi
    rw [Machine.upd_other _ _ _ by_decide, v53, g₃ _ by_decide, g₂ _ by_decide,
      g₁ _ by_decide]
variable {M : Model}
/-- A match gives a scan result. -/
theorem found_of_match {Q : Polygon} {N : NF} {r : ℕ} {x : WPos} {j : ℕ}
    (hj : j ∈ (N.region r).arcs) (hjA : j < N.arcs.length)
    (hm : matchB N.arcs.length j (tA M Q N x j) ztpek = true) :
    ScanFound M Q N r x (bktB N.arcs.length j ztpek) :=
  ⟨bkt_of_match N hjA (by zuovb) (by zuovc) hm, by rw [arcOfB_bktB hjA]; exact hj⟩
set_option maxHeartbeats 4000000 in
/-- **The arc scan**: if some arc of the region matches, the bucket found is a scan result. -/
theorem scanS_exec {N : NF} {r : ℕ} {x : WPos} {m : ℕ → ℕ} {MD AB lp : ℕ}
    (hS : ScanGood P W M N r x m MD AB lp) (d : Config) (hw : WordsBounded W d) (hm : d.nmem = m)
    (h40 : d.nreg 216040 = x.edge) (h41 : d.nreg 216041 = x.hgt)
    (h42 : d.nreg 216042 = (N.region r).arcs.length) (h43 : d.nreg 216043 = lp)
    (h14 : d.nreg 216014 = AB) (h17 : d.nreg 216017 = N.arcs.length)
    (h02 : d.nreg 216002 = 1) (h03 : d.nreg 216003 = 0) (h4 : d.nreg 40000 = MD)
    (hex : ∃ j ∈ (N.region r).arcs,
      matchB N.arcs.length j (tA M zta N x j) (tB M zta N x j) = true) :
    ∃ d' k, Exec P W scanS d d' k ∧ k ≤ ztkes * (N.region r).arcs.length + 3 ∧
      ScanFound M zta N r x (d'.nreg 216053) ∧ FrameB Bscan d d' := by
  have e₀ := Exec.constN (P := P) hw 216044 0 ztbg
  set d₀ : Config := { d with nreg := upd d.nreg 216044 0 } with hd₀
  have f₀ : FrameB Bscan d d₀ := exec_frameB e₀ by_decide
  set nA := (N.region r).arcs.length with hnA
  set lst : ℕ → ℕ := fun t => (N.region r).arcs.getD t 0 with hlst
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 216044 = t ∧
    e.nreg 216042 = nA ∧ FrameB Bscan d e ∧
    ((∃ t', t' < t ∧ matchB N.arcs.length ztqte (tA M zta N x ztqte)
      (tB M zta N x ztqte) = true) → ScanFound M (Qof P) N r x (e.nreg 216053))
  obtain ⟨d', k, ex, ⟨w', -, -, hf', hfound⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 216044) (nr := 216042) Inv scanK nA
    ztfhl
    (fun t e ht ⟨hw, h1, h2, hf, hI⟩ => by
      zugla
      obtain ⟨e', k, ex, hk, h44, h53, hf'⟩ := scanBody_exec hS e hw (by rw [hf.2.2.1, hm]) ht
        (by rw [g _ by_decide, h40]) (by rw [g _ by_decide, h41])
        (by rw [g _ by_decide, h43]) h1 (by rw [g _ by_decide, h14])
        (by rw [g _ by_decide, h17]) (by rw [g _ by_decide, h02])
        (by rw [g _ by_decide, h03]) (by rw [g _ by_decide, h4])
      refine ⟨e', k, ex, ⟨ex.wb_right, h44, by zunya, hf.trans hf',
        fun ⟨t', ht', hmt⟩ => ?_⟩, hk⟩
      have hjm : lst t ∈ (N.region r).arcs := by
        simp_all
      zunrx
      by_cases hmt' : matchB N.arcs.length ztqtf (tA M zta N x ztqtf)
          (tB M zta N x ztqtf) = true
      · rw [ite_eq_left hmt']
        exact found_of_match hjm (hS.arcs _ hjm).1 hmt'
      grind)
    (j := 0) ⟨e₀.wb_right, by_rfl, by_simp_all, f₀,
      fun ⟨t', ht', _⟩ => absurd ht' zthrl⟩ (Nat.zero_le _)
  refine ⟨d', 1 + k, .seq e₀ ex, ?_, ?_, hf'⟩
  · grind
  · obtain ⟨j, hj, hmj⟩ := hex
    obtain ⟨t', ht', hjt⟩ := List.mem_iff_getElem.1 hj
    refine hfound ztrep
    simp_all
end exec
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs
open BuildNF (codeLe wposOf)
@[expose] public section
variable {M : Model} {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The arc list of a region lies below the bound of a robust normal form. -/
theorem arcList_lt {m : ℕ → ℕ} {B E' : ℕ} {N : NF} (h : NFWithin m B E' N) {r : ℕ}
    (hr : r < N.nRegions) {t : ℕ} (ht : t < (N.region r).arcs.length) :
    m ztlw + m ztxhc + t < E' := by
  have hp : m zter + 5 * r + 1 < E' := by
    have := (Gran.nf_areas h).2.2.1 r hr; omega
  have hB : B + 7 < E' := (Gran.nf_areas h).1
  exact Gran.robust_addr3 (b₁ := B + 7) (p₂ := m zter + 5 * r + 1) (t := t)
    (v := (N.region r).arcs.getD t 0) hp (fun m' hm' => by
      zuhvt
      have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.1 t ht
      simp_all)

/-- The ends of a found chord are proper positions of the walk at a vertex height. -/
theorem endPos_props (_hGM : GoodModel M) {N : NF} {reg : ℕ → Set Point} {r : ℕ}
    {t : ℕ × ℕ × ℕ} (hf : Restore.FoundOK M zta N reg r t) {s : ℕ} (hs : s < 2) :
    (endPos t s).edge < M.W.n ∧ 1 ≤ (endPos t s).hgt ∧ ProperPos M zta P.n ztfre ∧
      Chazelle.Chain.SideAttach M.W ztynu (endPos t s).edge
        ztzuf := by
  zuc
  have hA : Chazelle.Chain.SideAttach M.W ztynu (endPos t s).edge
      ztzuf := by
    zuox
    · exact hf.1.1
    · exact hf.1.2
  have hh : (endPos t s).hgt = t.1 + 1 := by unfold endPos; grind
  obtain ⟨he, h0, h1, -⟩ := id hA
  refine ⟨he, by_omega, ⟨h0, h1, ?_⟩, hA⟩
  have := hf.2.1
  omega

/-- **The scan data of an end of a chord of region `r`.** -/
theorem scanGood_of (hGM : GoodModel M) {W : ℕ} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hok : ChordTriplesOK M zta L) (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztwqj) (hK : 0 < L.length) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs M zta ztwni reg) {m : ℕ → ℕ} {H B MD : ℕ}
    (hNW : NFWithin m H B ztwni) (hBW : B ≤ W)
    (hwf : ModelDescWF P B m MD) (hMD : ModelDescAt m MD zta M) {r : ℕ}
    (hr : r < L.length + 1) {x : WPos} (hxe : x.edge < M.W.n) (hx1 : 1 ≤ x.hgt)
    (hxp : ProperPos M zta P.n x) :
    ScanGood P W M ztwni r x m MD (m ztdtf)
      (m ztctc + m (m ztwj + 5 * r + 1)) := by
  zubm
  zuc
  zubrl
  zugyh
  have hR : N.nRegions = L.length + 1 := by simp [hN, NF.nRegions, BuildNF.buildNF]
  have hr' : ztsll := by_omega
  zumcc
  have hne : ztxml := by
    zuciy

  obtain ⟨hnA, -, -⟩ := Restore.region_arc hM hNF hregs hne hr'
  obtain ⟨hDW, hCW⟩ := NFLoc.locChainWF_of hwf hBW hWh
  have hAOK := hregs.2.2.1
  zuljk
  have hA : ztrzg := by
    have hm : ztixc := by
      simp_all
    exact lt_of_le_of_lt ztbg ((hAOK.2.2.2 r hr' _).1 hm).1
  refine ⟨hG, hWh, hDW, hCW, hMD, hxe, hx1, hxp, ?_, ?_, fun t ht => ?_, fun j hj => ?_⟩
  · have := arcList_lt hNW hr' (t := (N.region r).arcs.length - 1) by_omega
    omega
  · have := hareas.2.2.2.2.1 ztdfr by_omega
    omega
  · have := (hNAt.2.2.2.2.2.2.2.1 r hr').2.2.2.1 t ht
    omega
  · have hjA := ((hAOK.2.2.2 r hr' j).1 hj).1
    obtain ⟨-, a1, a2, a3, a4⟩ := hNAt.2.2.2.2.2.2.1 j hjA
    obtain ⟨-, -, -, -, -, -, -, hpp⟩ := hNF.2.2.2
    obtain ⟨hps, hpe⟩ := hpp j hjA
    zuexu
    have hA' := arcs_length (M := M) (Q := Qof P) (E := E) hK
    zubcn
    have hjg : j < (BuildNF.gapStarts M zta L E).length := by_grind
    -- the end of arc `j` is an event position
    have hev : (E.getD ztbarw 0) < 2 * L.length := by
      have hi : ztxgy % E.length < E.length := Nat.mod_lt _ by_omega
      have hmem : E.getD ztbarw 0 ∈ E := by
        zucpl
        simp
      simpa using hperm.mem_iff.1 hmem
    have he := arc_e (M := M) (Q := Qof P) (E := E) hK hjg
    refine ⟨hjA, ?_, ?_, ?_, ?_, hps, hpe, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · rw [he, BuildRam.wposOf_hgt]; omega
    · zvmxm; exact BuildRam.edge_lt hok hev

/-- **Some arc of region `r` matches each end of a chord found for `r`.** -/
theorem hex_of (hGM : GoodModel M) (hok : ChordTriplesOK M zta L)
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztwqj)
    (hK : 0 < L.length) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs M zta ztwni reg) {r : ℕ}
    (hr : r < (BuildNF.buildNF M zta L E).nRegions) {t : ℕ × ℕ × ℕ}
    (hf : Restore.FoundOK M zta ztwni reg r t) {s : ℕ} (hs : s < 2) :
    ∃ j ∈ ((BuildNF.buildNF M zta L E).region r).arcs,
      matchB (BuildNF.buildNF M zta L E).arcs.length j
        (tA M zta ztwni ztfre j)
        (tB M zta ztwni ztfre j) = true := by
  zubm
  zubrl
  zugyh
  have hne : ztxml := by
    zuciy

  zubcn
  obtain ⟨-, -, -, hA⟩ := endPos_props (P := P) hGM hf hs
  obtain ⟨j, hj, hjA, hcl⟩ := exists_closedArc hM hNF hregs hne hr hf.2.2.1 hf.2.2.2 hA
  refine ⟨j, hj, match_of_closedArc hK by_omega hjA hcl (by zuovb; rfl)
    (by zuovc; rfl)⟩
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
@[expose] public section
structure REnv where
  P : Polygon
  W : ℕ
  L : List zte
  E : List ℕ
  reg : ℕ → Set Point
  A₀ : ℕ
  m₀ : ℕ → ℕ
  B₀ : ℕ
  MD : ℕ
  H : ℕ
  γ : ℕ
  d0 : ℕ
  ctx : ℕ
  sF : Stmt
  κf : ℕ → ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
namespace REnv
variable (E : REnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev M : Model := interiorModel E.Q

/-- The current normal form. -/
noncomputable abbrev N : NF := BuildNF.buildNF E.M E.Q E.L E.E

/-- The number of regions. -/
def R : ℕ := E.L.length + 1

/-- The number of arcs. -/
noncomputable def A : ℕ := E.N.arcs.length

/-- The bucket base. -/
def BK : ℕ := E.B₀ + 3 * E.R

/-- The body bound of the region loop. -/
def Bf : ℕ := Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + 2 * ztrt + 60
end REnv

/-- The registers of `bDownDrv` the region loop keeps. -/
def FixR (q : ℕ) : Prop :=
  (210000 ≤ q ∧ q < 216020) ∨ (216023 ≤ q ∧ q < 216030) ∨ ztgyo

/-- **The facts at the start of the region loop.** -/
structure RGood (E : REnv) (c₀ : Config) : Prop where
  hF : Restore.FindOK E.sF E.κf E.F E.G E.Hc E.X DrvR.OkInt DrvR.ioBandsD
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, ztcqf → E.γ ≤ E.X.cap E.P m E.ctx
  hA₀ : E.A₀ ≤ E.B₀
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD E.Q E.M
  hok : ChordTriplesOK E.M E.Q E.L
  hperm : E.E.Perm ztoxe
  hsort : E.E.Pairwise (BuildNF.codeLe E.M E.Q E.L)
  hregs : Restore.NFRegs E.M E.Q E.N E.reg
  hdeg : E.M.DegLe ztjif E.d0
  hsg : E.M.Semigranular ztjif E.γ
  hNW : NFWithin c₀.nmem E.H E.B₀ E.N
  hlow : ∀ a, a < E.A₀ → c₀.nmem a = E.m₀ a
  wb : WordsBounded E.W c₀
  r001 : c₀.nreg 210001 = E.MD
  r00 : c₀.nreg 216000 = E.d0
  r01 : c₀.nreg 216001 = E.γ
  r02 : c₀.nreg 216002 = 1
  r03 : c₀.nreg 216003 = 0
  r04 : c₀.nreg 216004 = 4
  r05 : c₀.nreg 216005 = 2
  r06 : c₀.nreg 216006 = 5
  r12 : c₀.nreg 216012 = E.H
  r13 : c₀.nreg 216013 = E.R
  r14 : c₀.nreg 216014 = c₀.nmem ztdtc
  r15 : c₀.nreg 216015 = c₀.nmem ztbaq
  r16 : c₀.nreg 216016 = c₀.nmem ztdtd
  r17 : c₀.nreg 216017 = E.A
  r18 : c₀.nreg 216018 = E.B₀
  r19 : c₀.nreg 216019 = E.BK
  r20 : c₀.nreg 216020 = 0
  r21 : c₀.nreg 216021 = E.B₀
  r22 : c₀.nreg 216022 = E.BK
  r30 : c₀.nreg 216030 = 0
  r31 : c₀.nreg 216031 = c₀.nmem ztbaq + 2
  rctx : c₀.nreg 230001 = E.ctx
  alloc : E.BK + 2 * E.R ≤ c₀.nreg ALLOC
  room : c₀.nreg ALLOC + ztnd * E.R + 2 ≤ E.W

/-- **The region-loop invariant.** -/
structure RegI (E : REnv) (c₀ : Config) (newL : List ztwjg) (c : Config) :
    Prop where
  wb : WordsBounded E.W c
  r_le : c.nreg 216030 ≤ E.R
  ptr : c.nreg 216031 = c₀.nmem ztbaq + 2 + 5 * c.nreg 216030
  hfst : newL.map Prod.fst = Restore.highList E.N 4 ztmfz
  hgood : ∀ p ∈ newL, Restore.FoundOK E.M E.Q E.N E.reg p.1 p.2
  hbk : BktOK E.M E.Q E.N newL ztzfh
  cnt : c.nreg 216020 = newL.length
  dst : c.nreg 216021 = E.B₀ + 3 * newL.length
  dstB : c.nreg 216022 = E.BK + 2 * newL.length
  list : ChordListAt c.nmem E.B₀ ztvzx
  low : ∀ a, a < E.B₀ → c.nmem a = c₀.nmem a
  regs : ∀ q, FixR q → c.nreg q = c₀.nreg q
  rctx : c.nreg 230001 = E.ctx
  alloc : c₀.nreg ALLOC ≤ c.nreg ALLOC
  room : c.nreg ALLOC + ztnd * ztriz ≤ c₀.nreg ALLOC + ztnd * E.R

/-! ## Straight-line pieces -/
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
theorem argS_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      c'.nreg 81000 = c.nreg 210001 ∧ c'.nreg 81001 = c.nreg 216012 ∧
      c'.nreg 81002 = c.nreg 216030 ∧ c'.nreg 81003 = c.nreg 216001 ∧
      c'.nreg 81004 = c.nreg 230001 ∧ c'.nreg 81005 = c.nreg 216000 ∧
      c'.nreg 81006 = c.nreg 216004 ∧
      FrameB ztijy c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W argS c c' k ∧ k = 7 ∧
      (c'.nreg 81000 = c.nreg 210001 ∧ c'.nreg 81001 = c.nreg 216012 ∧
      c'.nreg 81002 = c.nreg 216030 ∧ c'.nreg 81003 = c.nreg 216001 ∧
      c'.nreg 81004 = c.nreg 230001 ∧ c'.nreg 81005 = c.nreg 216000 ∧
      c'.nreg 81006 = c.nreg 216004) := by
    unfold argS
    exec_block
    simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2, exec_frameB ex by_decide⟩

/-- The registers `appT` writes. -/
def BappT (r : ℕ) : Bool :=
  decide (r = 216020) || decide (r = 216021) || decide (r = 216033) || decide (r = 216034) ||
    decide (216040 ≤ r ∧ r ≤ 216043) || decide (r = 40000)
theorem wrM_appT : wrM BappT appT = true := by_decide
set_option maxHeartbeats 2000000 in
/-- Appending the triple and the region data of the scans. -/
theorem appT_exec (hw : WordsBounded W c) {d n p LB : ℕ}
    (h21 : c.nreg 216021 = d) (h20 : c.nreg 216020 = n) (h02 : c.nreg 216002 = 1)
    (h05 : c.nreg 216005 = 2) (h31 : c.nreg 216031 = p) (h16 : c.nreg 216016 = LB)
    (hd : d + 3 ≤ W) (hn : n + 1 ≤ W) (hp : 2 ≤ p) (hLB : LB + c.nmem ztoq ≤ W)
    (hh : c.nreg 81008 + 1 ≤ W) (hsep : p < d) :
    ∃ c' k, Exec P W appT c c' k ∧ k = 15 ∧
      c'.nmem = upd ztyfv ztvq
        ztqid ∧
      c'.nreg 216021 = d + 3 ∧ c'.nreg 216020 = n + 1 ∧
      c'.nreg 216042 = c.nmem ztftr ∧ c'.nreg 216043 = LB + c.nmem ztoq ∧
      c'.nreg 216041 = c.nreg 81008 + 1 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 216040 = c.nreg 81009 ∧ FrameM BappT c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W appT c c' k ∧ k = 15 ∧
      (c'.nmem = upd ztyfv ztvq
        ztqid ∧
      c'.nreg 216021 = d + 3 ∧ c'.nreg 216020 = n + 1 ∧
      c'.nreg 216042 = c.nmem ztftr ∧ c'.nreg 216043 = LB + c.nmem ztoq ∧
      c'.nreg 216041 = c.nreg 81008 + 1 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 216040 = c.nreg 81009) := by
    unfold appT
    exec_block
    all_goals try (config_simp; zunhl; omega)
    · config_simp
      simp only [h21, h02, h05, h31, h16, Machine.upd_apply]
      grind
    refine ztgpi
    all_goals config_simp
    all_goals try zunhl
    all_goals try zumwj
    all_goals try split_ifs
    all_goals first | omega | rfl | (congr 2; omega)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2, exec_frameM ex wrM_appT⟩
theorem wrM_stB : wrM ztzft stB = true := by_decide

/-- Storing a bucket. -/
theorem stB_exec (hw : WordsBounded W c) {d : ℕ} (h22 : c.nreg 216022 = d)
    (h02 : c.nreg 216002 = 1) (hd : d + 1 ≤ W) :
    ∃ c' k, Exec P W stB c c' k ∧ k = 2 ∧ c'.nmem = upd c.nmem d ztvhz ∧
      c'.nreg 216022 = d + 1 ∧ FrameM ztzft c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W stB c c' k ∧ k = 2 ∧
      (c'.nmem = upd c.nmem d ztvhz ∧ c'.nreg 216022 = d + 1) := by
    unfold stB
    exec_block
    · simp_all
    simp_all
  exact ⟨c', k, ex, hk, q.1, q.2, exec_frameM ex wrM_stB⟩
end exec
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
@[expose] public section
def InDrv (B : ℕ → Bool) : Prop := ∀ r, B r = true → bandOf r ∈ DrvR.drvBands ∧ r ≠ ALLOC
theorem mem_drvBands {r : ℕ} (h1 : 10000 ≤ r) (h2 : r < 230000) : bandOf r ∈ DrvR.drvBands := by
  simp only [DrvR.drvBands, phaseBands, bCore, Finset.mem_erase, Finset.mem_Icc, bandOf]
  omega
variable {B : ℕ → Bool}
theorem rf_of_frameM (hB : InDrv B) {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (h : FrameM B c c') (hm : ∀ a, a < A₀ → c'.nmem a = c.nmem a) :
    Restore.RF DrvR.drvBands A₀ c c' k := by
  have hnot : ztkoo := fun r hr => by
    cases h' : B r
    · rfl
    · exact absurd (hB r h').1 hr
  have hA : ztble := h.1 _ (by
    cases h' : B ALLOC
    · rfl
    · exact absurd rfl (hB _ h').2)
  exact ⟨fun r hr _ => h.1 r ztjya, fun r hr => h.2.1 r ztjya, hm,
    fun a _ => by zunrv, h.2.2.2, by_omega, by_omega⟩
theorem rf_of_frameB (hB : InDrv B) {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (h : FrameB B c c') : Restore.RF DrvR.drvBands A₀ c c' k :=
  rf_of_frameM hB (BuildRam.FrameB.toM h) (fun a _ => by zunrv)
theorem inDrv_scan : InDrv Bscan := by
  zuz
  simp only [Bscan, BuildRam.Bhalf, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ztbgh
theorem inDrv_appT : InDrv BappT := by
  zuz
  simp only [BappT, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ztbgh
theorem inDrv_eq {q : ℕ} (h1 : 10000 ≤ q) (h2 : q < 230000) (hq : q ≠ ALLOC) :
    InDrv (fun r => decide (r = q)) := by
  zuz
  zucy
  subst hr
  exact ⟨mem_drvBands h1 h2, hq⟩
theorem inDrv_arg : InDrv ztijy := by
  zuz
  zucy
  exact ztbgh
theorem find_bands : restoreBands ∪ DrvR.ioBandsD ⊆ DrvR.drvBands := by_decide

/-- The splitting step keeps the registers of `bDownDrv` and `coreReg 1`. -/
theorem find_keeps {c c' : Config} {k : ℕ} (h : Frame (restoreBands ∪ DrvR.ioBandsD) c c' k)
    {q : ℕ} (hq : (210000 ≤ q ∧ q < 220000) ∨ q = 230001) : c'.nreg q = c.nreg q := by
  refine h.1 q ?_ ztu
  have : bandOf q = 21 ∨ bandOf q = 23 := by unfold bandOf; omega
  rcases this with h' | h' <;> zvmxl <;> decide

/-! ## The facts of the environment -/
namespace REnv
variable (E : REnv)
theorem hQ (hG : GoodEnv E.P) : E.Q.Simple := (shearInvariance ztmjb E.P).1 hG.1
theorem hGM (hG : GoodEnv E.P) : GoodModel E.M := Or.inr ⟨E.Q, E.hQ hG, rfl⟩
theorem nRegions_N : E.N.nRegions = E.R := by
  simp [NF.nRegions, BuildNF.buildNF, REnv.R]
end REnv
theorem RGood.hNF {E : REnv} {c₀ : Config} (hE : RGood E c₀) : IsNF E.M E.Q E.N :=
  (BuildNF.isNF_goodModel (E.hGM hE.hG) hE.hok hE.hperm hE.hsort).1
theorem desc_one {m : ℕ → ℕ} {B : ℕ} {Q : Polygon} (h : ModelDescAt m B Q ztd) :
    m B = 1 := by
  rcases h with ⟨-, H, C, -, hC⟩ | ⟨h1, -, -⟩
  · zulxn
  omega

/-- **The buckets after appending a chord.** -/
theorem BktOK.snoc {M : Model} {Q : Polygon} {N : NF} {newL : List ztwjg}
    {bk bk' : ℕ → ℕ} {r : ℕ} {t : ℕ × ℕ × ℕ} (h : BktOK M Q N newL bk)
    (hold : ∀ q, q < 2 * newL.length → bk' q = bk q)
    (h0 : ScanFound M Q N r (endPos t 0) (bk' ztssl))
    (h1 : ScanFound M Q N r (endPos t 1) (bk' ztptx)) :
    BktOK M Q N (newL ++ [zteve]) bk' := by
  have hg : ∀ q, q < 2 * (newL ++ [zteve]).length →
      (q < 2 * newL.length ∧ (newL ++ [zteve]).getD ztbeu dflt = newL.getD ztbeu dflt) ∨
      ((newL ++ [zteve]).getD ztbeu dflt = zteve ∧
        (q = 2 * newL.length ∨ q = 2 * newL.length + 1)) := by
    zuco
    rw [List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q ztssl with hl | hl
    · grind
    grind
  constructor
  · zuco
    zudse
    · zunyd; exact h.key q hl
    · zucjo
      zukmb
      · rw [show 2 * newL.length % 2 = 0 by omega]; exact h0.1
      · rw [show ztptx % 2 = 1 by omega]; exact h1.1
  · zuco
    zudse
    · zunyd; exact h.arc q hl
    · zucjo
      zukmb
      · exact h0.2
      · exact h1.2
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
@[expose] public section
def Bapp (r : ℕ) : Bool := BappT r || Bscan r || decide ztkdi
theorem inDrv_app : InDrv Bapp := by
  zuz
  simp only [Bapp, Bool.or_eq_true] at hr
  zubpr
  · exact inDrv_appT r h
  · exact inDrv_scan r h
  · exact inDrv_eq by_norm_num by_norm_num by_decide r h
theorem bapp_of_appT (r : ℕ) (h : BappT r = true) : Bapp r = true := by
  zugfz
theorem bapp_of_scan (r : ℕ) (h : Bscan r = true) : Bapp r = true := by
  zugfz
theorem bapp_of_22 (r : ℕ) (h : decide ztkdi = true) : Bapp r = true := by
  zugfz
theorem bapp_of_40 (r : ℕ) (h : decide zttxq = true) : Bapp r = true := by
  zudcd
  zubst
  decide

/-- The degree word of a region of `buildNF` bounds the number of chords. -/
theorem degOf_le {M : Model} {Q : Polygon} {L : List zte} {E : List ℕ} {r : ℕ}
    (hr : r < L.length + 1) : Restore.degOf ztpwl r ≤ L.length := by
  unfold Restore.degOf
  zulqs
  exact (List.length_filter_le _ _).trans by_simp
set_option maxHeartbeats 16000000 in
/-- **One call of the splitting step.** -/
theorem call_step {E : REnv} {c₀ : Config} (hE : RGood E c₀)
    {newL : List ztwjg} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 216030 < E.R) (hhigh : 4 < Restore.degOf E.N ztmfz) :
    ∃ c' k t, Exec E.P E.W ztjss c c' k ∧ k + 10 ≤ E.Bf ∧
      Restore.RF DrvR.drvBands E.B₀ c c' k ∧ WordsBounded E.W c' ∧
      Restore.FoundOK E.M E.Q E.N E.reg ztmfz t ∧
      BktOK E.M E.Q E.N (newL ++ [ztrlw]) (fun q => c'.nmem zthak) ∧
      c'.nreg 216020 = newL.length + 1 ∧ c'.nreg 216021 = E.B₀ + 3 * zttud ∧
      c'.nreg 216022 = E.BK + 2 * zttud ∧
      ChordListAt c'.nmem E.B₀ ((newL ++ [ztrlw]).map Prod.snd) ∧
      (∀ a, a < E.B₀ → c'.nmem a = c.nmem a) ∧
      (∀ q, FixR q → c'.nreg q = c.nreg q) ∧
      c'.nreg 216030 = c.nreg 216030 ∧ c'.nreg 216031 = c.nreg 216031 ∧
      c'.nreg 230001 = c.nreg 230001 := by
  set r := c.nreg 216030 with hrd
  set i := newL.length with hid
  have hGM := E.hGM hE.hG
  zumcd
  zunx
  have hW3 : ztsbf := by have := hE.hWh; unfold hostWords at this; omega
  have hRN := E.nRegions_N
  have hrN : ztjaf := by_omega
  -- the registers of `c`
  have RR := hI.regs
  have c001 := (RR _ ztec).trans hE.r001
  have c00 := (RR _ ztec).trans hE.r00
  have c01 := (RR _ ztec).trans hE.r01
  have c02 := (RR _ ztec).trans hE.r02
  have c03 := (RR _ ztec).trans hE.r03
  have c04 := (RR _ ztec).trans hE.r04
  have c05 := (RR _ ztec).trans hE.r05
  have c12 := (RR _ ztec).trans hE.r12
  have c14 : c.nreg 216014 = c₀.nmem _ :=
    (RR _ ztec).trans hE.r14
  have c16 : c.nreg 216016 = c₀.nmem _ :=
    (RR _ ztec).trans hE.r16
  have c17 := (RR _ ztec).trans hE.r17
  -- sizes and bounds
  have hir : i ≤ r := by
    have := congrArg List.length hI.hfst
    zubus
    rw [hid, this]; exact Restore.highList_length_le _ _ _
  have hKpos : 0 < E.L.length := by
    have h' : Restore.degOf E.N r ≤ E.L.length :=
      degOf_le by_tauto
    omega
  have hBK : ztpje := rfl
  have hA0B := hE.hA₀
  have hc0A := hE.alloc
  have hcA := hI.alloc
  have hWA := hI.wb.1 ALLOC
  have hroom : c.nreg ALLOC + E.Bf + 2 ≤ E.W := by
    zumba
    have h2 := hE.room
    have : E.Bf + 2 ≤ ztnd * ztriz := Nat.le_mul_of_pos_right _ by_omega
    omega
  have hBKi : E.BK + 2 * i + 2 ≤ c.nreg ALLOC := by_omega
  have hB3i : E.B₀ + 3 * i + 3 ≤ E.BK := by_omega
  -- the memory
  have hNW₀ := hE.hNW
  have hareas := Gran.nf_areas hNW₀
  have hNAt₀ := hNW₀.nfAt
  have agree := fun a ha =>
    (hI.low a by_omega).trans ztoad
  -- 1. the arguments
  obtain ⟨c₁, k₁, e₁, hk₁, a0, a1, a2, a3, a4, a5, a6, f₁⟩ := argS_exec (P := E.P) c hI.wb
  zud
  have g₁ : ∀ q, ¬ (81000 ≤ q ∧ q ≤ 81006) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q by_grind
  zuesu
  zucfz
  have agree₁ : ztkoc := by_grind
  obtain ⟨hMD₁, hwf₁⟩ := Gran.desc_agree' hE.hwf hE.hMD agree₁
  have hNW₁ : ztylg := by
    zuoiz; exact (hNW₀.transport hI.low).mono by_omega
  have hctx : c₁.nreg 81004 = E.ctx := by rw [a4, hI.rctx]
  have hMD' : c₁.nreg 81000 = E.MD := by_omega
  have hH' : c₁.nreg 81001 = E.H := by_omega
  have hγ' : c₁.nreg 81003 = E.γ := by_omega
  have hd' : c₁.nreg 81005 = E.d0 := by_omega
  have h4' : c₁.nreg 81006 = 4 := by_omega
  have hone := desc_one hMD₁
  -- 2. the splitting step
  have hroomF : c₁.nreg ALLOC + E.κf ztqkg * E.F zterk *
      E.G zterk * ztyhk ≤ E.W := by
    rw [hd', hγ', A₁]
    have : Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ ≤ E.Bf := by unfold REnv.Bf; omega
    unfold Restore.costF at this
    omega
  have hXh : E.X.holds E.P c₁.nmem E.ctx ztbmq :=
    E.X.mono _ _ _ _ _ by_omega
      (E.X.local_ _ _ _ _ _ by_grind hE.hX)
  obtain ⟨c₂, k₂, e₂, hk₂, ⟨-, -, Ppost⟩, F₂⟩ := hE.hF E.P E.W c₁ w₁
    ⟨hE.hG, hE.hWh, by_grind, by rw [hγ', hctx]; exact hE.hcap _ agree₁,
      by zuouz; exact hwf₁.mono by_omega,
      fun h0 => by_grind,
      fun h0 => by_grind,
      E.M, E.N, by_grind, hGM, rfl, by_grind, hNF,
      by zumzk; exact hE.hdeg, by rw [hγ']; exact hE.hsg, by_omega⟩ hroomF
  zuira
  rw [hd', hγ'] at hk₂
  zue
  obtain ⟨hsnd, hcpl⟩ := Ppost E.M E.N E.reg (by zuouz; omega)
    (by rw [hH']; exact hNW₁.nfAt) hNF hE.hregs
  have hDH := (goodShear_epsOf hE.hG.2).2.1
  have hdegr : E.M.deg _ _ = Restore.degOf E.N r :=
    Gran.deg_region hNF hE.hregs.1 hE.hregs.2.2.2 hrN
  have hflag := hcpl (by rw [h4']; exact fullDegLe_interior (E.hQ hE.hG) hDH)
    (by rw [h4', a2, hdegr]; omega)
  zucya

  set t : ℕ × ℕ × ℕ := ztmic with htd
  have hfound : Restore.FoundOK E.M E.Q E.N E.reg r t := ztopn
  have K2 : ∀ q, 210000 ≤ q → q < 220000 → c₂.nreg q = c.nreg q := fun q h1 h2 =>
    (find_keeps F₂ by_omega).trans (g₁ q by_omega)
  have K2c := (find_keeps F₂ ztbt).trans (g₁ _ by_omega)
  have mem₂ : ztux := fun a ha => by
    zunye
  -- 3. the test
  have htest : c₂.nreg 216003 < c₂.nreg 81007 := by
    rw [K2 _ by_norm_num by_norm_num, c03, hflag]; norm_num
  -- 4. appending the triple
  set RB := c₀.nmem ztbaq with hRB
  have hp : c₂.nreg 216031 = RB + 2 + 5 * r := by rw [K2 _ by_norm_num by_norm_num, hI.ptr]
  have hRBr := hareas.2.2.1 r hrN
  have hnA : 0 < (E.N.region r).arcs.length := by
    have hne : (E.N.F E.M E.Q).Nonempty := by
      refine ⟨(E.N.chord 0).toSet E.M E.Q, E.N.chord 0, ?_, rfl⟩
      zudly
      have h0 : 0 < E.N.chords.length := by zuova; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some]
      simp
    exact (Restore.region_arc ztqyo hNF hE.hregs hne hrN).1
  have hlp := arcList_lt hNW₀ hrN hnA
  rw [← hRB] at hlp
  have hm2 : c₂.nmem (RB + 2 + 5 * r - 1) = c₀.nmem ztenw := by
    rw [show RB + 2 + 5 * r - 1 = RB + 5 * r + 1 by omega, mem₂ _ by_omega,
      hI.low _ by_omega]
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, d21, d20, d42, d43, d41, d400, d40, f₃⟩ := appT_exec (P := E.P)
    c₂ w₂ (d := E.B₀ + 3 * i) (n := i) (p := RB + 2 + 5 * r) (LB := c₀.nmem ztdtd)
    (by rw [K2 _ by_norm_num by_norm_num, hI.dst])
    (by rw [K2 _ by_norm_num by_norm_num, hI.cnt])
    (by rw [K2 _ by_norm_num by_norm_num, c02]) (by rw [K2 _ by_norm_num by_norm_num, c05])
    hp (by rw [K2 _ by_norm_num by_norm_num, c16]) ztnvk
    ztnvk by_omega by_omega
    by_omega by_omega
  zubj
  rw [show RB + 2 + 5 * r - 2 = RB + 5 * r by omega, mem₂ _ by_omega, hI.low _ by_omega] at d42
  rw [hm2] at d43
  rw [K2 _ by_norm_num by_norm_num, c001] at d400
  zuepy
  -- the memory of `c₃` below `B₀`
  have low₃ : ∀ a, a < E.B₀ → c₃.nmem a = c₀.nmem a := fun a ha => by
    rw [m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, mem₂ a by_omega, hI.low a ha]
  have agree₃ := low₃
  -- the scan data
  have hBW : E.B₀ ≤ E.W := by_omega
  have hscan : ∀ (m : ℕ → ℕ), (∀ a, a < E.B₀ → m a = c₀.nmem a) → (∀ a, m a ≤ E.W) →
      ∀ s, s < 2 → ScanGood E.P E.W E.M E.N r ztfre m E.MD (m ztdtc)
        (m ztdtd + m (m ztbaq + 5 * r + 1)) := by
    intro m hm hmW s hs
    obtain ⟨xe, x1, xp, -⟩ := endPos_props (P := E.P) hGM hfound hs
    have hmA := fun a ha => (hm a by_omega).trans ztoad
    obtain ⟨hMDm, hwfm⟩ := Gran.desc_agree' hE.hwf hE.hMD hmA
    exact scanGood_of hGM hE.hG hE.hWh hE.hok hE.hperm hE.hsort hKpos hE.hregs
      (hNW₀.transport hm) hBW (hwfm.mono by_omega) hMDm (by unfold REnv.R at hr; omega) xe x1 xp
  have hex : ∀ s, s < 2 → ∃ j ∈ (E.N.region r).arcs, matchB E.N.arcs.length j
      (tA E.M _ E.N _ j) (tB E.M _ E.N _ j) = true :=
    fun s hs => hex_of hGM hE.hok hE.hperm hE.hsort hKpos hE.hregs hrN hfound hs
  have hNA : (E.N.region r).arcs.length = c₀.nmem ztqch :=
    ((hNAt₀.2.2.2.2.2.2.2.1 r hrN).1).symm
  -- 5. the first scan
  have S1 := hscan c₃.nmem agree₃ w₃.2 0 by_norm_num
  have hH7 := hareas.1
  rw [agree₃ ztdtc by_omega, agree₃ ztdtd by_omega, agree₃ ztbaq by_omega,
    ← hRB, agree₃ ztenw by_omega] at S1
  have e40 : c₃.nreg 216040 = (endPos t 0).edge := by zuouo; rfl
  have e41 : c₃.nreg 216041 = (endPos t 0).hgt := by zuoup; rfl
  have r3 :=
    fun q hq h1 h2 => (g₃ q hq).trans (K2 q h1 h2)
  obtain ⟨c₄, k₄, e₄, hk₄, fd₀, f₄⟩ := scanS_exec S1 c₃ w₃ rfl e40 e41
    by_omega ztqeu
    (by rw [r3 _ by_decide by_norm_num by_norm_num, c14, ← agree₃ _ by_omega])
    (by rw [r3 _ by_decide by_norm_num by_norm_num, c17]; rfl)
    (by rw [r3 _ by_decide by_norm_num by_norm_num, c02])
    (by rw [r3 _ by_decide by_norm_num by_norm_num, c03])
    by_omega (hex 0 by_norm_num)
  zucc
  zudna
  -- 6. the first bucket
  have d22 : c₄.nreg 216022 = E.BK + 2 * i := by
    rw [g₄ _ by_decide, r3 _ by_decide by_norm_num by_norm_num, hI.dstB]
  obtain ⟨c₅, k₅, e₅, hk₅, m₅, d22', f₅⟩ := stB_exec (P := E.P) c₄ w₄ d22
    (by rw [g₄ _ by_decide, r3 _ by_decide by_norm_num by_norm_num, c02])
    by_omega
  zuef
  -- 7. the right end
  have ex₆ := Exec.copyN (P := E.P) w₅ 216040 81010
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 216040 _ } with hc₆
  have w₆ := ex₆.wb_right
  have f₆ : FrameB (fun r => decide zttxq) c₅ c₆ := exec_frameB ex₆ by_decide
  have g56 : ∀ q, q ≠ 216040 → c₆.nreg q = c₅.nreg q := fun q hq => by
    zumys; simp [hq]
  have g5 := fun q hq => f₅.1 q ztrla
  -- 8. the second scan
  have agree₆ : ∀ a, a < E.B₀ → c₆.nmem a = c₀.nmem a := fun a ha => by
    show c₅.nmem a = _
    rw [m₅, Machine.upd_other _ _ _ by_omega, f₄.2.2.1, agree₃ a ha]
  have S2 := hscan c₆.nmem agree₆ w₆.2 1 by_norm_num
  rw [agree₆ ztdtc by_omega, agree₆ ztdtd by_omega, agree₆ ztbaq by_omega,
    ← hRB, agree₆ ztenw by_omega] at S2
  have r6 : ∀ q, Bscan q = false → BappT q = false → q ≠ 216022 → q ≠ 216040 → 210000 ≤ q →
      q < 220000 → c₆.nreg q = c.nreg q := fun q h1 h2 h3 h4 h5 h6 => by
    rw [g56 q h4, g5 q h3, g₄ q h1, r3 q h2 h5 h6]
  have e40' : c₆.nreg 216040 = (endPos t 1).edge := by
    zumys; zumzo
    rw [g5 _ by_norm_num, g₄ _ by_decide, g₃ _ by_decide]
    rfl
  have e41' : c₆.nreg 216041 = (endPos t 1).hgt := by
    rw [g56 _ by_norm_num, g5 _ by_norm_num, g₄ _ by_decide, d41]
    rfl
  have hnAd : (E.N.region r).arcs.length ≤ E.d0 + 1 := by
    have h1 := Restore.arcs_le_deg hGM hNF hE.hregs hrN
    have h2 := hE.hdeg _ (hE.hregs.1.1 r hrN)
    omega
  obtain ⟨c₇, k₇, e₇, hk₇, fd₁, f₇⟩ := scanS_exec S2 c₆ w₆ rfl e40' e41'
    (by rw [g56 _ by_norm_num, g5 _ by_norm_num, g₄ _ by_decide, d42, hNA])
    (by rw [g56 _ by_norm_num, g5 _ by_norm_num, g₄ _ by_decide, d43])
    (by rw [r6 _ by_decide by_decide by_norm_num by_norm_num by_norm_num by_norm_num,
      c14, ← agree₆ _ by_omega])
    (by rw [r6 _ by_decide by_decide by_norm_num by_norm_num by_norm_num by_norm_num,
      c17]; rfl)
    (by rw [r6 _ by_decide by_decide by_norm_num by_norm_num by_norm_num by_norm_num,
      c02])
    (by rw [r6 _ by_decide by_decide by_norm_num by_norm_num by_norm_num by_norm_num,
      c03])
    (by rw [g56 _ by_norm_num, g5 _ by_norm_num, g₄ _ by_decide, d400]) (hex 1 by_norm_num)
  zubgp
  -- 9. the second bucket
  obtain ⟨c₈, k₈, e₈, hk₈, m₈, d22'', f₈⟩ := stB_exec (P := E.P) c₇ w₇
    (d := E.BK + 2 * i + 1) (by rw [f₇.1 _ by_decide, g56 _ by_norm_num, d22'])
    (by rw [f₇.1 _ by_decide, r6 _ by_decide by_decide by_norm_num by_norm_num
      by_norm_num by_norm_num, c02]) by_omega
  -- the execution
  have eApp : Exec E.P E.W appS c₂ c₈ _ :=
    .seq e₃ (.seq e₄ (.seq e₅ (.seq ex₆ ztjdu)))
  have eCall : Exec E.P E.W ztjss c c₈
      _ :=
    .seq e₁ (.seq e₂ (.ifLtN_true htest eApp))
  -- the memory of `c₈`
  have m78 : c₈.nmem = upd (upd c₃.nmem (E.BK + 2 * i) (c₄.nreg 216053)) ztnkr
      (c₇.nreg 216053) := by
    rw [m₈, f₇.2.2.1]
    show upd c₅.nmem _ _ = _
    rw [m₅, f₄.2.2.1]
  have mlow : ∀ a, a < E.B₀ → c₈.nmem a = c.nmem a := fun a ha => by
    rw [m78, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, low₃ a ha,
      hI.low a ha]
  -- the frame
  have Fapp :=
    (f₃.mono bapp_of_appT).trans (((FrameB.toM f₄).mono bapp_of_scan).trans
      ((f₅.mono bapp_of_22).trans (((FrameB.toM f₆).mono bapp_of_40).trans
        (((FrameB.toM f₇).mono bapp_of_scan).trans (f₈.mono bapp_of_22)))))
  have RF₁ : Restore.RF DrvR.drvBands E.B₀ c c₁ k₁ := rf_of_frameB inDrv_arg f₁
  have RF₂ : Restore.RF DrvR.drvBands E.B₀ c₁ c₂ k₂ :=
    (Restore.RF.of_frame F₂ (by rw [A₁]; omega)).mono find_bands le_rfl
  have RF₃ : Restore.RF DrvR.drvBands E.B₀ c₂ c₈ (k₃ + (k₄ + (k₅ + (1 + zttrl))) + 1) :=
    rf_of_frameM inDrv_app Fapp (fun a ha => by
      rw [mlow a ha, mem₂ a by_omega])
  -- registers of `c₈`
  have G := Fapp.1
  have G3 : ∀ q, Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₈.nreg q = c₃.nreg q :=
    fun q h1 h2 h3 => by
      rw [f₈.1 q (by simpa using h2), f₇.1 q h1, g56 q h3, g5 q h2, g₄ q h1]
  have fixq : ∀ q, FixR q → Bapp q = false := fun q hq => by
    zumqx
    simp only [Bapp, BappT, Bscan, BuildRam.Bhalf, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  refine ⟨c₈, _, t, eCall, ?_, RF₁.trans zthrz, e₈.wb_right, hfound, ?_, ?_, ?_, ?_, ?_,
    mlow, fun q hq => ?_, ?_, ?_, ?_⟩
  · -- cost
    have hs1 : ztkes * (E.N.region r).arcs.length ≤ ztkes * ztfnl :=
      Nat.mul_le_mul_left _ hnAd
    have hBf : E.Bf = Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ +
      2 * ztrt + 60 := rfl
    unfold Restore.costF at hBf
    omega
  · -- buckets
    refine BktOK.snoc hI.hbk zteso ?_ ?_
    · show c₈.nmem _ = c.nmem _
      rw [m78, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega, m₃,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, mem₂ _ by_omega]
    · show ScanFound E.M E.Q E.N r _ _
      rw [m78, Machine.upd_other _ _ _ by_omega, Machine.upd_same]
      omega
    · show ScanFound E.M E.Q E.N r _ (c₈.nmem ztnkr)
      rw [m78, Machine.upd_same]
      omega
  · rw [G3 _ by_decide by_norm_num by_norm_num, d20]
  · rw [G3 _ by_decide by_norm_num by_norm_num, d21]; ring
  · omega
  · -- the list
    zujgt
    have hlen : (newL.map Prod.snd).length = i := by rw [List.length_map]
    have hm8 : ∀ a, a < E.BK → c₈.nmem a = c₃.nmem a := fun a ha => by
      rw [m78, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    refine Gran.ChordListAt.snoc hI.list ztpbf ?_ ?_ ?_
    · rw [hlen] at h2
      rw [hm8 a by_omega, m₃, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        mem₂ a by_omega]
    · rw [hlen, hm8 _ by_omega, m₃, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega, Machine.upd_same]
    · rw [hlen, hm8 _ by_omega, m₃, Machine.upd_other _ _ _ by_omega, Machine.upd_same]
    · rw [hlen, hm8 _ by_omega, m₃, Machine.upd_same]
  · rw [G q (fixq q hq), K2 q zthfp zthfp]
  · zugbz
  · zugbz
  · rw [G _ by_decide, K2c]
variable {E : REnv} {c₀ : Config} {newL : List (ℕ × (ℕ × ℕ × ℕ))} {c : Config}
/-- The degree word of region `r`. -/
theorem RegI.deg_word
    (hE : RGood E c₀) (hI : RegI E c₀ newL c) (hr : c.nreg 216030 < E.R) :
    c.nmem (c.nreg 216031) = Restore.degOf E.N ztmfz := by
  have hrN : c.nreg 216030 < E.N.nRegions := by zuovd; exact hr
  have hareas := (Gran.nf_areas hE.hNW).2.2.1 _ hrN
  rw [hI.ptr, hI.low _ by_omega]
  have := ((hE.hNW.nfAt).2.2.2.2.2.2.2.1 _ hrN).2.1
  unfold Restore.degOf
  grind

/-- The invariant survives a change of the scratch register `216032`. -/
theorem RegI.load
    (hI : RegI E c₀ newL c) (v : ℕ) (hv : v ≤ E.W) :
    RegI E c₀ newL { c with nreg := upd c.nreg 216032 v } := by
  have g : ∀ q, q ≠ 216032 → (upd c.nreg 216032 v) q = c.nreg q := fun q hq => by_simp_all
  refine ⟨Machine.WordsBounded.upd_nreg hI.wb hv c.pc, ?_, ?_, ?_, hI.hgood, hI.hbk, ?_, ?_, ?_,
    hI.list, hI.low, fun q hq => ?_, ?_, ?_, ?_⟩ <;> simp only
  · zunav; exact hI.r_le
  · rw [g _ by_norm_num, g _ by_norm_num]; exact hI.ptr
  · zunav; exact hI.hfst
  · zunav; exact hI.cnt
  · zunav; exact hI.dst
  · zunav; exact hI.dstB
  · rw [g q zthfp]; exact hI.regs q hq
  · zunav; exact hI.rctx
  · zumxb; exact hI.alloc
  · rw [g _ by_decide, g _ by_norm_num]; exact hI.room
set_option maxHeartbeats 8000000 in
/-- **One step of the region loop.** -/
theorem regBody_step (hE : RGood E c₀)
    {newL : List ztwjg} {c : Config} (hI : RegI E c₀ newL c)
    (hr : c.nreg 216030 < E.R) :
    ∃ c' k newL', Exec E.P E.W ztwcm c c' k ∧ RegI E c₀ newL' c' ∧
      Restore.RF DrvR.drvBands E.B₀ c c' k ∧ k ≤ E.Bf ∧ c'.nreg 216030 = c.nreg 216030 + 1 := by
  zukbu
  obtain ⟨r, hrd⟩ : ∃ r, c.nreg 216030 = r := zths
  rw [hrd] at hr hdw
  -- load the degree
  have e₁ := Exec.loadN (P := E.P) hI.wb 216032 216031
  set c₁ : Config := { c with nreg := upd c.nreg 216032 (c.nmem (c.nreg 216031)) } with hc₁
  have hI₁ : ztscj := hI.load _ (hI.wb.2 _)
  have r1 : c₁.nreg 216030 = r := by_simp_all
  have d1 : c₁.nreg 216032 = Restore.degOf E.N r := by_simp_all
  have c04 : c₁.nreg 216004 = 4 :=
    (hI₁.regs _ ztwmk).trans hE.r04
  have RF₁ : Restore.RF DrvR.drvBands E.B₀ c c₁ 1 :=
    rf_of_frameB (inDrv_eq (q := 216032) by_norm_num by_norm_num by_decide)
      ztduj
  -- the conditional call
  obtain ⟨c₂, k₂, newL', e₂, hk₂, RF₂, hI₂', h30, h31⟩ :
      ∃ (c₂ : Config) (k₂ : ℕ) (newL' : List ztwjg),
      Exec E.P E.W (.ifLtN 216004 216032 ztjss .skip) c₁ c₂ k₂ ∧ k₂ + 8 ≤ E.Bf ∧
      Restore.RF DrvR.drvBands E.B₀ c₁ c₂ k₂ ∧
      (newL'.map Prod.fst = Restore.highList E.N 4 ztgu ∧
        (∀ p ∈ newL', Restore.FoundOK E.M E.Q E.N E.reg p.1 p.2) ∧
        BktOK E.M E.Q E.N newL' (fun q => c₂.nmem zthak) ∧
        c₂.nreg 216020 = newL'.length ∧ c₂.nreg 216021 = E.B₀ + 3 * newL'.length ∧
        c₂.nreg 216022 = E.BK + 2 * newL'.length ∧
        ChordListAt c₂.nmem E.B₀ (newL'.map Prod.snd) ∧
        (∀ a, a < E.B₀ → c₂.nmem a = c₁.nmem a) ∧ (∀ q, FixR q → c₂.nreg q = c₁.nreg q) ∧
        c₂.nreg 230001 = c₁.nreg 230001 ∧ WordsBounded E.W c₂) ∧
      c₂.nreg 216030 = r ∧ c₂.nreg 216031 = c₁.nreg 216031 := by
    by_cases hhigh : 4 < Restore.degOf E.N r
    · obtain ⟨c₂, k₂, t, e₂, hk₂, RF₂, w₂, hfound, hbk, h20, h21, h22, hlist, hlow, hreg, h30,
        h31, hctx⟩ := call_step hE hI₁ by_omega by_simp_all
      zvnal at hfound hbk hlist h30
      refine ⟨c₂, k₂ + 1, newL ++ [zteve],
        .ifLtN_true by_omega e₂, by_omega,
        RF₂.mono subset_rfl by_omega, ⟨?_, ?_, hbk, ?_, ?_, ?_, hlist, hlow, hreg, hctx, w₂⟩,
        h30, h31⟩
      · rw [List.map_append, hI.hfst, hrd, Restore.highList_succ, ite_eq_left hhigh]; rfl
      · zuda
        zutk
        · zulyn
        simp_all
      · simp_all
      · simp_all
      simp_all
    · refine ⟨c₁, 2, newL, .ifLtN_false by_omega ztekc,
        by unfold REnv.Bf; omega, Restore.RF.refl _ _,
        ⟨by rw [hI.hfst, hrd, Restore.highList_succ, ite_eq_right hhigh, List.append_nil], hI.hgood,
          hI₁.hbk, hI₁.cnt, hI₁.dst, hI₁.dstB, hI₁.list, fun _ _ => rfl, fun _ _ => rfl, rfl,
          e₁.wb_right⟩, r1, rfl⟩
  obtain ⟨hfst₂, hgood₂, hbk₂, h20, h21, h22, hlist₂, hlow₂, hreg₂, hctx₂, w₂⟩ := hI₂'
  -- the tail
  have c06 : c₂.nreg 216006 = 5 :=
    ((hreg₂ _ ztwmk).trans
      ztbarj).trans hE.r06
  have c02 : zturc :=
    ((hreg₂ _ ztwmk).trans
      ztbarj).trans hE.r02
  have hp1 : c₂.nreg 216031 = c₀.nmem ztbaq + 2 + 5 * r := by rw [h31, hI₁.ptr, r1]
  have hRW : ztsbg := by
    have := hE.room
    grind
  have hareas := (Gran.nf_areas hE.hNW).2.2.1 r (by zuovd; exact hr)
  have hB₀W : E.B₀ + 5 ≤ E.W := by
    have h1 := hE.alloc; have h2 := hE.wb.1 ALLOC
    have h3 : ztpje := rfl
    omega
  obtain ⟨c₃, k₃, e₃, hk₃, t31, t30, R₃⟩ : ∃ c₃ k₃, Exec E.P E.W
      ztiqn c₂ c₃ k₃ ∧ k₃ = 2 ∧
      c₃.nreg 216031 = c₂.nreg 216031 + 5 ∧ c₃.nreg 216030 = r + 1 ∧
      c₃ = { c₂ with nreg := upd (upd c₂.nreg 216031 (c₂.nreg 216031 + 5)) 216030 (r + 1) } := by
    exec_block
    · omega
    · config_simp; omega
    simp_all
  have g3 : ∀ q, q ≠ 216031 → q ≠ 216030 → c₃.nreg q = c₂.nreg q := fun q h1 h2 => by
    simp_all
  have m3 : ztdrk := by zunjw
  have RF₃ : Restore.RF DrvR.drvBands E.B₀ c₂ c₃ k₃ :=
    rf_of_frameB (B := fun r => decide (r = 216031) || decide (r = 216030))
      (fun q hq => by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hq
        exact ztbgh)
      ⟨fun q hq => by
        simp_all, fun q _ => by zunjw, by zunjw, by zunjw, by zunjw⟩
  zulha
  refine ⟨c₃, 1 + zttl, newL', .seq e₁ ztcr, ⟨e₃.wb_right, ?_, ?_, ?_, hgood₂,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all, fun a ha => by rw [m3, hlow₂ a ha]; exact hI.low a ha,
    fun q hq => ?_, by rw [g3 _ by_norm_num by_norm_num, hctx₂]; exact hI₁.rctx,
    le_trans hI.alloc RFall.2.2.2.2.2.1, ?_⟩, RFall, by_omega, by_omega⟩
  · omega
  · omega
  · simp_all
  · zumqx
    rw [g3 q by_omega by_omega, hreg₂ q hq, hI₁.regs q hq]
  · zudxy

    rw [t30]
    rw [hrd] at h1
    have h3 : ztxto := by
      zudkm
    omega

/-- The invariant at the start of the loop. -/
theorem RGood.regI (hE : RGood E c₀) : RegI E c₀ [] c₀ :=
  ⟨hE.wb, by rw [hE.r30]; omega, by rw [hE.r30, hE.r31], by rw [hE.r30]; rfl,
    fun p hp => by_simp_all, ⟨fun q hq => by_simp_all, fun q hq => by_simp_all⟩,
    by rw [hE.r20]; rfl, by rw [hE.r21]; simp, by rw [hE.r22]; simp,
    fun i hi => by_simp_all, fun _ _ => rfl, fun _ _ => rfl, hE.rctx, le_rfl,
    by simp⟩

/-- **The region loop.** -/
theorem reg_exec (hE : RGood E c₀) :
    ∃ c' k newL, Exec E.P E.W ztqvo c₀ c' k ∧ RegI E c₀ newL c' ∧
      c'.nreg 216030 = E.R ∧ Restore.RF DrvR.drvBands E.B₀ c₀ c' k ∧
      k ≤ ztnd * E.R + 2 := by
  obtain ⟨c', k, e, ⟨newL, I'⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := E.P) (W := E.W)
    (a := 216030) (b := 216013) (body := regBody E.sF) (B := DrvR.drvBands) (A₀ := E.B₀)
    ztjvo (fun c => E.R - c.nreg 216030) E.Bf
    ztdnu
    (fun c ⟨newL, I⟩ ht => by
      have t : c.nreg 216030 < E.R := by
        rw [I.regs 216013 ztwmk, hE.r13] at ht
        exact ht
      obtain ⟨c', k, newL', e, I', RF', hk, h30⟩ := regBody_step hE I t
      grind) ⟨[], hE.regI⟩
  have hR' : c'.nreg 216030 = E.R := by
    rw [I'.regs 216013 ztwmk, hE.r13] at hx
    have := I'.r_le; omega
  refine zthmp
  rw [hE.r30] at hk
  omega
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
structure DEnv where
  P : Polygon
  W : ℕ
  A₀ : ℕ
  m₀ : ℕ → ℕ
  r₀ : ℕ → ℕ
  MD : ℕ
  γ : ℕ
  d0 : ℕ
  ctx : ℕ
  sF : Stmt
  sB : Stmt
  κf : ℕ → ℕ
  κB : ℕ
  F : ℕ → ℕ
  G : ℕ → ℕ
  Hc : ℕ → ℕ
  X : MemCtx
  S₀ : Set ztf
  K₀ : ℕ
namespace DEnv
variable (E : DEnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev M : Model := interiorModel E.Q

/-- A bound on the number of regions during the rounds. -/
def Kc : ℕ := 2 ^ E.d0 * ztbjj

/-- The body bound of the region loop. -/
def Bf : ℕ := Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + 2 * ztrt + 60

/-- The bound of one round. -/
def Br : ℕ := 40 + ztcli * E.Kc + 8 * DrvR.κSpl E.κB * E.Kc
end DEnv

/-- The registers of `bDownDrv` the rounds keep (the post of `RoundsSpec`). -/
def KeepR (q : ℕ) : Prop :=
  q = 210000 ∨ q = 210001 ∨ (211000 ≤ q ∧ q < 216000) ∨ (217000 ≤ q ∧ q < 220000)

/-- **The facts of the rounds' data.** -/
structure DGood (E : DEnv) : Prop where
  hF : Restore.FindOK E.sF E.κf E.F E.G E.Hc E.X DrvR.OkInt DrvR.ioBandsD
  hB : DrvR.SortedMeets E.sB E.κB
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hX : E.X.holds E.P E.m₀ E.ctx E.A₀
  hcap : ∀ m : ℕ → ℕ, ztcqf → E.γ ≤ E.X.cap E.P m E.ctx
  hwf : ModelDescWF E.P E.A₀ E.m₀ E.MD
  hMD : ModelDescAt E.m₀ E.MD E.Q E.M
  hd0 : 4 ≤ E.d0

/-- **The state after `t` rounds.** -/
structure RInv (E : DEnv) (t : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  r001 : c.nreg 210001 = E.MD
  r00 : c.nreg 216000 = E.d0
  r01 : c.nreg 216001 = E.γ
  r02 : c.nreg 216002 = 1
  r03 : c.nreg 216003 = 0
  r04 : c.nreg 216004 = 4
  r05 : c.nreg 216005 = 2
  r06 : c.nreg 216006 = 5
  r10 : c.nreg 216010 = t
  rctx : c.nreg 230001 = E.ctx
  keep : ∀ q, KeepR q → c.nreg q = E.r₀ q
  state : ∃ (L : List zte) (Ev : List ℕ), DrvR.StateAt E.P c L Ev ∧
    E.S₀ ⊆ (BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q ∧
    E.M.DegLe ztdbn ztzwz ∧
    E.M.Semigranular ztdbn E.γ ∧
    L.length + 1 ≤ 2 ^ t * ztbjj
  low : ∀ a, a < E.A₀ → c.nmem a = E.m₀ a
  alloc : E.A₀ ≤ c.nreg ALLOC
  t_le : t ≤ E.d0
  room : c.nreg ALLOC + ztemm * ztbgq + 3 ≤ E.W

/-! ## Straight-line pieces -/
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 2000000 in
/-- The header of the current normal form. -/
theorem hdS_exec (hw : WordsBounded W c) {H : ℕ} (h05 : c.nreg 210005 = H)
    (h02 : c.nreg 216002 = 1) (h0205 : c.nreg 216005 = 2) (hH : H + 7 ≤ W) :
    ∃ c' k, Exec P W hdS c c' k ∧ k = 15 ∧ c'.nreg 216012 = H ∧
      c'.nreg 216017 = c.nmem ztemv ∧ c'.nreg 216013 = c.nmem ztfnq ∧
      c'.nreg 216014 = c.nmem ztdtf ∧ c'.nreg 216015 = c.nmem ztwj ∧
      c'.nreg 216016 = c.nmem ztctc ∧ c'.nreg 216018 = c.nreg ALLOC ∧
      c'.nreg 216021 = c.nreg ALLOC ∧ c'.nreg 216020 = 0 ∧ c'.nreg 216023 = 0 ∧
      FrameB (fun r => decide (216012 ≤ r ∧ r ≤ 216033)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W hdS c c' k ∧ k = 15 ∧
      (c'.nreg 216012 = H ∧
      c'.nreg 216017 = c.nmem ztemv ∧ c'.nreg 216013 = c.nmem ztfnq ∧
      c'.nreg 216014 = c.nmem ztdtf ∧ c'.nreg 216015 = c.nmem ztwj ∧
      c'.nreg 216016 = c.nmem ztctc ∧ c'.nreg 216018 = c.nreg ALLOC ∧
      c'.nreg 216021 = c.nreg ALLOC ∧ c'.nreg 216020 = 0 ∧ c'.nreg 216023 = 0) := by
    unfold hdS
    exec_block
    all_goals try (config_simp; (try zunvc); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals try zunvc
    all_goals try rfl
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.2,
    exec_frameB ex by_decide⟩

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 216023) || decide ztyc

/-- **The reservation** of `5 R` words. -/
theorem resS_exec {c : Config} (hw : WordsBounded W c) {R : ℕ} (h13 : c.nreg 216013 = R)
    (h23 : c.nreg 216023 = 0) (h02 : c.nreg 216002 = 1) (hW : c.nreg ALLOC + 5 * R + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W resS c c' k ∧ k ≤ 8 * R + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * R ∧
      c'.nreg 216023 = R ∧ FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 216023 = j ∧
    e.nreg 216013 = R ∧ e.nreg 216002 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ R
  have key : ∀ j e, j < R → Inv j e → ∃ e' k, Exec P W resBody e e' k ∧ Inv ztl e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    zuos

    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W resBody e e' k ∧ k = 6 ∧
        (e'.nreg 216023 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * ztl) := by
      unfold resBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ztkw <;> config_simp <;> simp only [h1, h3, h4']; omega
    zudyy
    have hA' : e'.nreg ALLOC = e.nreg ALLOC + 5 := by
      show e'.nreg 9999 = e.nreg 9999 + 5
      omega
    have hnot : ztdjz := fun r hr hra => by
      zucqs

    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ by_decide).trans h2,
      (hf'.1 _ by_decide).trans h3, by_omega, hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r ztlpu, fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) by_decide r rfl, fun a _ => by zuodj,
        fun a _ => by zuodk, hf'.2.2.2.2, by_omega, by_omega⟩, hk⟩
  have I0 : ztpki := ⟨hw, h23, h13, h02, by_simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := P)
    (W := W) (a := 216023) (b := 216013) (body := resBody) (B := DrvR.drvBands) (A₀ := A₀)
    ztfrn (fun e => R - e.nreg 216023) 6 ztfro
    (fun e ⟨j, hI⟩ ht => by
      zueo

      exact ztcox) ⟨0, I0⟩
  zugmn

  refine zthmn
  omega
set_option maxHeartbeats 1000000 in
/-- The bucket base and the region loop set-up. -/
theorem midS_exec (hw : WordsBounded W c) {R B RB : ℕ} (h13 : c.nreg 216013 = R)
    (h18 : c.nreg 216018 = B) (h15 : c.nreg 216015 = RB) (h05 : c.nreg 216005 = 2)
    (hW : B + 3 * R ≤ W) (hRB : RB + 2 ≤ W) :
    ∃ c' k, Exec P W midS c c' k ∧ k = 6 ∧ c'.nreg 216019 = B + 3 * R ∧
      c'.nreg 216022 = B + 3 * R ∧ c'.nreg 216030 = 0 ∧ c'.nreg 216031 = RB + 2 ∧
      FrameB (fun r => decide (r = 216019 ∨ r = 216022 ∨ r = 216030 ∨ r = 216031 ∨
        r = 216033)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W midS c c' k ∧ k = 6 ∧
      (c'.nreg 216019 = B + 3 * R ∧ c'.nreg 216022 = B + 3 * R ∧ c'.nreg 216030 = 0 ∧
        c'.nreg 216031 = RB + 2) := by
    unfold midS
    exec_block
    all_goals try (config_simp; (try simp only [h13, h18, h15, h05]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h13, h18, h15, h05]) <;> omega
  zumaa
set_option maxHeartbeats 1000000 in
/-- The arguments of the splice. -/
theorem splArgs_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W splArgs c c' k ∧ k = 5 ∧ c'.nreg 210020 = c.nreg 216018 ∧
      c'.nreg 210021 = c.nreg 216020 ∧ c'.nreg 210022 = c.nreg 216019 ∧
      c'.nreg 210023 = c.nreg 216017 ∧ c'.nreg 210024 = c.nreg 216005 ∧
      FrameB (fun r => decide ztcku) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W splArgs c c' k ∧ k = 5 ∧
      (c'.nreg 210020 = c.nreg 216018 ∧
      c'.nreg 210021 = c.nreg 216020 ∧ c'.nreg 210022 = c.nreg 216019 ∧
      c'.nreg 210023 = c.nreg 216017 ∧ c'.nreg 210024 = c.nreg 216005) := by
    unfold splArgs
    exec_block
    simp
  zulzz

/-- The round counter. -/
theorem incr_exec (hw : WordsBounded W c) {t : ℕ} (h10 : c.nreg 216010 = t)
    (h02 : c.nreg 216002 = 1) (ht : t + 1 ≤ W) :
    ∃ c' k, Exec P W ztnsb c c' k ∧ k = 1 ∧
      c'.nreg 216010 = t + 1 ∧ FrameB (fun r => decide (r = 216010)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W (block [.addN 216010 216010 216002]) c c' k ∧
      k = 1 ∧ c'.nreg 216010 = t + 1 := by
    exec_block
    · omega
    simp_all
  exact ztioa
end exec
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
theorem RF.base {B : Finset ℕ} {A A' : ℕ} {c c' : Config} {k : ℕ} (h : Restore.RF B A c c' k)
    (hA : A' ≤ A) : Restore.RF B A' c c' k :=
  ⟨h.1, h.2.1, fun a ha => h.2.2.1 a by_omega, fun a ha => h.2.2.2.1 a by_omega,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- `buildNF` has at most `2 K + 1` arcs. -/
theorem arcs_length_le {M : Model} {Q : Polygon} {L : List zte} {E : List ℕ}
    (hE : E.length = 2 * L.length) : (BuildNF.buildNF M Q L E).arcs.length ≤ 2 * L.length + 1 := by
  show (BuildNF.arcList M Q L E).length ≤ _
  unfold BuildNF.arcList
  zus
  · simp
  · zujgs
    unfold BuildNF.gapStarts
    grind
variable {m : ℕ → ℕ}
theorem chordListAt_robust {A B : ℕ} {L : List zte}
    (h : ChordListAt m A L) (hB : A + 3 * L.length ≤ B) :
    Robust B m (fun m' => ChordListAt m' A L) := by
  zulng
  zurw
  grind
theorem seg_robust {a n B : ℕ} (hB : a + n ≤ B) :
    Robust B m (fun m' => seg m' a n = seg m a n) :=
  fun m' hm' => SortL.seg_congr fun i hi => hm' _ by_omega
theorem desc_robust {P : Polygon} {A A' : ℕ} {m₀ m : ℕ → ℕ} {D : ℕ} {M : Model}
    (hwf : ModelDescWF P A m₀ D) (hM : ModelDescAt m₀ D zta M)
    (hm : ∀ a, a < A → m a = m₀ a) (hA : A ≤ A') :
    Robust A' m (fun m' => ModelDescAt m' D zta M) := fun m' hm' =>
  (Gran.desc_agree' hwf hM (fun a ha => (hm' a by_omega).trans zttny)).1
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section

/-- The region-loop data of a round. -/
def renvOf (E : DEnv) (L : List zte) (Ev : List ℕ) (reg : ℕ → Set Point) (B₀ H : ℕ) :
    REnv :=
  ⟨E.P, E.W, L, Ev, reg, E.A₀, E.m₀, B₀, E.MD, H, E.γ, E.d0, E.ctx, E.sF, E.κf, E.F, E.G, E.Hc,
    E.X⟩
set_option maxHeartbeats 16000000 in
/-- **The first part of a round**: header, reservation, set-up of the region loop. -/
theorem round_A {E : DEnv} (hE : DGood E) {t : ℕ} {c : Config} (hI : RInv E t c)
    (ht : t < E.d0) {L : List zte} {Ev : List ℕ} (hSt : DrvR.StateAt E.P c L Ev)
    (hdeg : E.M.DegLe ztdbn ztzwz)
    (hsg : E.M.Semigranular ztdbn E.γ)
    (hcnt : L.length + 1 ≤ 2 ^ t * ztbjj) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs E.M E.Q ztjhc reg) :
    ∃ c₃ k, (∀ (rest : Stmt) (c' : Config) (k' : ℕ), Exec E.P E.W rest c₃ c' k' →
        Exec E.P E.W (.seq hdS (.seq resS (.seq midS rest))) c c' zttqb) ∧
      RGood (renvOf E L Ev reg ztm ztvhx) c₃ ∧
      Restore.RF DrvR.drvBands E.A₀ c c₃ k ∧ k ≤ 8 * ztkr + 25 ∧
      c₃.nreg ALLOC = c.nreg ALLOC + 5 * ztkr ∧
      (∀ q, ztelg ∨ ztnft ∨ q = 230001 →
        c₃.nreg q = c.nreg q) ∧ c₃.nmem = c.nmem := by
  obtain ⟨hD6, hDa, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW⟩ := hSt
  zutz
  zujml
  set H := c.nreg 210005 with hH
  set N := BuildNF.buildNF E.M E.Q L Ev with hN
  zuinx
  have hGM : GoodModel E.M := Or.inr ⟨E.Q, (shearInvariance ztmjb E.P).1 hE.hG.1, rfl⟩
  zuljk
  zumcc
  have hRN : N.regions.length = R := by simp [hN, BuildNF.buildNF, hR]
  zumcq
  have hBW : B₀ ≤ E.W := hW.1 ALLOC
  have hRKc : R ≤ E.Kc := by
    zuhql

    calc R ≤ 2 ^ t * ztbjj := hcnt
      _ ≤ 2 ^ E.d0 * ztbjj := Nat.mul_le_mul_right _ this
  have hroom : ztpit := by
    have := hI.room
    zuhvk

  have hBr : 40 + ztcli * E.Kc ≤ E.Br := by unfold DEnv.Br; omega
  have hBfR : ztyzi := Nat.mul_le_mul_left _ hRKc
  have h5R : 10 * R ≤ ztcli * R := Nat.mul_le_mul_right _ by_omega
  -- 1. the header
  obtain ⟨c₁, k₁, e₁, hk₁, a12, a17, a13, a14, a15, a16, a18, a21, a20, a23, f₁⟩ :=
    hdS_exec (P := E.P) c hW (H := H) rfl hI.r02 hI.r05 by_omega
  zud
  have g₁ : ∀ q, ¬ (216012 ≤ q ∧ q ≤ 216033) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q by_grind
  zudqa
  rw [hNAt.2.2.1, hRN] at a13
  rw [hNAt.2.1] at a17
  -- 2. the reservation
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, r23, f₂, RF₂⟩ := resS_exec (P := E.P) w₁ a13 a23
    (by rw [g₁ _ by_omega, hI.r02]) (by zunct; omega) E.A₀
  zue
  have g₂ : ∀ q, q ≠ 216023 → q ≠ 9999 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    f₂.1 q ztljo
  have m₂ : ztpna := f₂.2.2.1
  have A₁ : c₁.nreg ALLOC = B₀ := g₁ _ by_decide
  zugbn
  -- 3. the set-up
  obtain ⟨c₃, k₃, e₃, hk₃, b19, b22, b30, b31, f₃⟩ := midS_exec (P := E.P) c₂ w₂ (R := R)
    (B := B₀) (RB := c.nmem ztwj) by_grind
    by_grind
    by_grind
    (by rw [g₂ _ by_norm_num by_norm_num, g₁ _ by_omega, hI.r05]) by_omega
    (by have := hareas.2.2.1 0 (by rw [show N.nRegions = N.regions.length from rfl, hRN]; omega)
        omega)
  zubj
  have g₃ : ∀ q, q ≠ 216019 → q ≠ 216022 → q ≠ 216030 → q ≠ 216031 → q ≠ 216033 →
      c₃.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 h5 => f₃.1 q by_grind
  have m₃ : ztckd := by rw [f₃.2.2.1, m₂, m₁]
  have A₃ : c₃.nreg ALLOC = B₀ + 5 * R := by
    rw [g₃ _ by_decide by_decide by_decide
      by_decide by_decide, A₂]
  -- the kept registers
  have K3 : ∀ q, ztelg ∨ ztnft ∨ q = 230001 →
      c₃.nreg q = c.nreg q := fun q hq => by
    rw [g₃ q by_omega by_omega by_omega by_omega by_omega,
      g₂ q by_omega by_omega, g₁ q by_omega]
  have K3' : ∀ q, 216012 ≤ q → q ≤ 216033 → q ≠ 216019 → q ≠ 216022 → q ≠ 216030 →
      q ≠ 216031 → q ≠ 216033 → q ≠ 216023 → c₃.nreg q = c₁.nreg q := fun q _ _ h1 h2 h3 h4 h5 h6 => by
    rw [g₃ q h1 h2 h3 h4 h5, g₂ q h6 by_omega]
  -- frames
  have RF₁ : Restore.RF DrvR.drvBands E.A₀ c c₁ k₁ :=
    rf_of_frameB (fun r hr => by
      zucy
      exact ztbgh) f₁
  have RF₃ : Restore.RF DrvR.drvBands E.A₀ c₂ c₃ k₃ :=
    rf_of_frameB (fun r hr => by
      zucy
      exact ztbgh) f₃
  have hlow : ∀ a, a < E.A₀ → c₃.nmem a = E.m₀ a := fun a ha => by zumzp; exact hI.low a ha
  have hA0B : E.A₀ ≤ B₀ := hI.alloc
  refine ⟨c₃, k₁ + zttl, fun rest c' k' h => (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ h))).cast
    by_ring, ?_, RF₁.trans zthrz, by_omega, A₃, K3, m₃⟩
  -- the region-loop facts
  have hk3 : ∀ q, q < 216012 → 210000 ≤ q → c₃.nreg q = c.nreg q := fun q h1 h2 =>
    K3 q (Or.inl ⟨h2, h1⟩)
  refine ⟨hE.hF, hE.hG, hE.hWh, hE.hX, hE.hcap, hA0B, hE.hwf, hE.hMD, hok, hperm, hsort, hregs,
    Model.DegLe.mono _ hdeg (max_le hE.hd0 ztjkm), hsg, by zumzp; exact hNW, hlow,
    w₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · show c₃.nreg 210001 = E.MD; rw [hk3 _ by_norm_num by_norm_num, hI.r001]
  · show c₃.nreg 216000 = E.d0; rw [hk3 _ by_norm_num by_norm_num, hI.r00]
  · show c₃.nreg 216001 = E.γ; rw [hk3 _ by_norm_num by_norm_num, hI.r01]
  · rw [hk3 _ by_norm_num by_norm_num, hI.r02]
  · rw [hk3 _ by_norm_num by_norm_num, hI.r03]
  · rw [hk3 _ by_norm_num by_norm_num, hI.r04]
  · rw [hk3 _ by_norm_num by_norm_num, hI.r05]
  · rw [hk3 _ by_norm_num by_norm_num, hI.r06]
  · show c₃.nreg 216012 = H
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a12]
  · show c₃.nreg 216013 = R
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a13]
  · show c₃.nreg 216014 = c₃.nmem ztdtf
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a14, m₃]
  · show c₃.nreg 216015 = c₃.nmem ztwj
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a15, m₃]
  · show c₃.nreg 216016 = c₃.nmem ztctc
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a16, m₃]
  · show c₃.nreg 216017 = N.arcs.length
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a17]
  · show c₃.nreg 216018 = B₀
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a18]
  · show c₃.nreg 216019 = B₀ + 3 * R; omega
  · show c₃.nreg 216020 = 0
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a20]
  · show c₃.nreg 216021 = B₀
    rw [K3' _ by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num
      by_norm_num by_norm_num, a21]
  · show c₃.nreg 216022 = B₀ + 3 * R; omega
  · omega
  · show c₃.nreg 216031 = c₃.nmem ztwj + 2; grind
  · show c₃.nreg 230001 = E.ctx; rw [K3 _ ztwrm, hI.rctx]
  · show B₀ + 3 * R + 2 * R ≤ c₃.nreg ALLOC; grind
  · show c₃.nreg ALLOC + ztnd * R + 2 ≤ E.W
    grind
