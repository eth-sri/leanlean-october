module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTestMath
public import Chazelle.Core.NFDecompGlue

/-!
# WP-E, Lemma 3.2 part 13: the candidate test meets its contract

* `hit_exact`: the exactness package of a hit of the test (the first exit, admissibility, the
  attachments at the candidate and at the arrival position);
* `record_ok`: the chord triple written by the test describes that chord and is attached;
* `test_post`: the postcondition of `TestOK` for the normal form of the run;
* `testOK`: **the candidate test meets `TestOK`**.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open ShotList ShotListG Machine SweepPrim

variable {P : Polygon} {M : Model} {N : NF}

/-- **The exactness package of a hit.** -/
theorem hit_exact {W : ℕ} {c₀ c' : Config} (hE : TGood P W M N c₀) (hTF : TestFacts P M N c₀ c')
    {reg : ℕ → Set Point} (hregs : NFRegs M (Qof P) N reg) (h10 : c'.nreg 83010 = 1)
    (h11 : c'.nreg 83011 = 1) :
    ∃ T > (0 : ℝ),
      (∀ t, 0 < t → t < T → rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∈
        reg (c₀.nreg 83002)) ∧
      rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∉ M.D ∧
      M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ =
        rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∧
      c'.nreg 83012 < M.W.n ∧ ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧
      chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∈ M.Adm ∧
      SideAttach M.W (chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T)
        (xOf c₀).edge (M.param (Qof P) (xOf c₀)) ∧
      SideAttach M.W (chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T)
        (c'.nreg 83012) (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀))
          (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)
          (M.key (Qof P) (xOf c₀)) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length) := by
  obtain ⟨-, hiv, -, -, -, -, h5⟩ := hTF
  have hV := hiv.1 h10
  obtain ⟨m, B, hs, A, harr, hnear, hlo, hhi, hyes, -⟩ := h5 h10
  obtain ⟨t, f₀, hfh, hp0, he0, hpos0, hpp, hpe, hposf, harrv, hint, hcnt, -⟩ := hyes h11
  obtain ⟨hout, hstr, hadm, p', t', hatt, hw'⟩ := hit_math hE.hGM hE.hNF hregs hE.hr hE.hxp hE.hxe
    hV hE.x_top harr hnear hlo hhi hfh
  have hσ := dir_pm (c₀.nreg 83008)
  have ht := hfh.1
  have hposf' : M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ =
      rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t := hposf.trans hpos0
  refine ⟨t, ht, hstr, hout, hposf', hpe, hpp, hadm, ?_, ?_, hcnt⟩
  · exact attach_start hE.hxe hE.hxp.1 hE.hxp.2.1 hσ ht hV.2.1
  · rcases hE.kind with ⟨-, C, hM⟩ | ⟨-, hM, -⟩
    · have ha := harrv C hM
      rw [hpos0] at ha
      exact attach_end ha.1 ha.2.1 ha.2.2.1 hσ ht ha.2.2.2.1 (by rw [ha.2.2.2.1]; exact ha.2.2.2.2)
    · have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hE.hG.1
      have hWs : M.W.Simple := by rw [hM]; exact (FactsInterior.interiorWalk_spec hQ).1
      exact attach_far_simple hWs hatt hw' hpe hpp.1 hpp.2.1 hposf'

/-- **The chord triple of the test** describes the chord of the hit and is attached. -/
theorem record_ok {Q : Polygon} {x f : WPos} {h σb lp rp : ℕ} {T : ℝ} (_hσb : σb ≤ 1)
    (hT : 0 < T) (hy : (M.pos Q x).2 = (Q.vtx h).2)
    (hf : M.pos Q f = rayPt (M.pos Q x) (dirOf σb) T)
    (hA : SideAttach M.W (chordOf (M.pos Q x) (dirOf σb) T) x.edge (M.param Q x))
    (hB : SideAttach M.W (chordOf (M.pos Q x) (dirOf σb) T) f.edge (M.param Q f))
    (hlr : (σb = 1 → lp = x.edge ∧ rp = f.edge) ∧ (σb ≠ 1 → lp = f.edge ∧ rp = x.edge)) :
    (recOf (h, lp, rp)).toSet M Q = chordOf (M.pos Q x) (dirOf σb) T ∧
      (recOf (h, lp, rp)).Attached M Q := by
  have hfy : (M.pos Q f).2 = (Q.vtx h).2 := by simp_all
  have px := pos_code M Q hy
  have pf := pos_code M Q hfy
  have qx := param_code M Q hy
  have qf := param_code M Q hfy
  have hfx : (M.pos Q f).1 = (M.pos Q x).1 + dirOf σb * T := by simp_all
  by_cases h1 : σb = 1
  · obtain ⟨rfl, rfl⟩ := hlr.1 h1
    have hd : dirOf σb = 1 := by rw [h1]; rfl
    have e : (recOf (h, x.edge, f.edge)).toSet M Q = chordOf (M.pos Q x) (dirOf σb) T := by
      show Visibility.hseg (Q.vtx h).2 (M.pos Q ⟨x.edge, h + 1⟩).1 (M.pos Q ⟨f.edge, h + 1⟩).1 = _
      rw [px, pf, chordOf, hfx, hd, hy, min_eq_left (by linarith), max_eq_right (by linarith)]
    refine ⟨e, ?_, ?_⟩
    · show SideAttach M.W _ x.edge (M.param Q ⟨x.edge, h + 1⟩)
      simp_all
    · show SideAttach M.W _ f.edge (M.param Q ⟨f.edge, h + 1⟩)
      simp_all
  · obtain ⟨rfl, rfl⟩ := hlr.2 h1
    have hd : dirOf σb = -1 := by core_grind
    have e : (recOf (h, f.edge, x.edge)).toSet M Q = chordOf (M.pos Q x) (dirOf σb) T := by
      show Visibility.hseg (Q.vtx h).2 (M.pos Q ⟨f.edge, h + 1⟩).1 (M.pos Q ⟨x.edge, h + 1⟩).1 = _
      rw [px, pf, chordOf, hfx, hd, hy, min_eq_right (by linarith), max_eq_left (by linarith)]
    refine ⟨e, ?_, ?_⟩
    · show SideAttach M.W _ f.edge (M.param Q ⟨f.edge, h + 1⟩)
      simp_all
    · show SideAttach M.W _ x.edge (M.param Q ⟨x.edge, h + 1⟩)
      simp_all


/-- The candidate and a point of its ray at a positive parameter differ. -/
theorem ray_ne {z : Point} {σb : ℕ} {T : ℝ} (hT : 0 < T) : z ≠ rayPt z (dirOf σb) T := by
  intro h
  have := congrArg Prod.fst h
  rw [rayPt_fst] at this
  rcases dir_pm σb with h1 | h1 <;> rw [h1] at this <;> linarith

/-- **The postcondition of `TestOK`** for the normal form of the run. -/
theorem test_post {W : ℕ} {c₀ c' : Config} (hE : TGood P W M N c₀)
    (hTF : TestFacts P M N c₀ c') {reg : ℕ → Set Point} (hregs : NFRegs M (Qof P) N reg) :
    (c'.nreg 83014 = 1 →
      (recOf (c'.nreg 83015, c'.nreg 83016, c'.nreg 83017)).Attached M (Qof P) ∧
      c'.nreg 83015 < (Qof P).n ∧
      (recOf (c'.nreg 83015, c'.nreg 83016, c'.nreg 83017)).toSet M (Qof P) ∈ M.Adm ∧
      SplitsWell M (N.F M (Qof P)) (reg (c₀.nreg 83002))
        ((recOf (c'.nreg 83015, c'.nreg 83016, c'.nreg 83017)).toSet M (Qof P))) ∧
    (c'.nreg 83010 = 1 → c'.nreg 83011 = 1 →
      ∃ T > (0 : ℝ),
        (∀ t, 0 < t → t < T → rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∈
          reg (c₀.nreg 83002)) ∧
        M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ =
          rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∧
        c'.nreg 83012 < M.W.n ∧ ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧
        chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∈ M.Adm ∧
        SideAttach M.W (chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T)
          (xOf c₀).edge (M.param (Qof P) (xOf c₀)) ∧
        SideAttach M.W (chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T)
          (c'.nreg 83012) (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) ∧
        (c'.nreg 83014 = 1 ↔ CountOK M (N.F M (Qof P)) (reg (c₀.nreg 83002))
          (M.key (Qof P) (xOf c₀)) (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩))) ∧
    (sideLeft M.W (xOf c₀).edge (M.param (Qof P) (xOf c₀))
        (rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) 1) →
      (N.region (c₀.nreg 83002)).chords ≠ [] →
      (∀ T > (0 : ℝ), (∀ t, 0 < t → t < T →
          rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∈ M.D) →
        rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∉ M.D →
        chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∈ M.Adm →
        chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∉ N.F M (Qof P) →
        chordOf (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) T ∩ M.D ⊆ reg (c₀.nreg 83002) →
        c'.nreg 83010 = 1 ∧ c'.nreg 83011 = 1)) := by
  have hGM := hE.hGM
  have hNF := hE.hNF
  have hr := hE.hr
  have hM := walkAx_of_goodModel hGM
  obtain ⟨b10, hiv, b11, b14, i11, i14, h5⟩ := hTF
  -- the counts of the test are those of `CountOK`
  have hcount : ∀ f : WPos,
      (2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀)) (M.key (Qof P) f)
          (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) f) (M.key (Qof P) (xOf c₀))
          (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length) ↔
      CountOK M (N.F M (Qof P)) (reg (c₀.nreg 83002)) (M.key (Qof P) (xOf c₀))
        (M.key (Qof P) f) := fun f => by
    unfold CountOK
    rw [sideExits_ncard hGM hNF hregs hr, sideExits_ncard hGM hNF hregs hr]
  refine ⟨fun hs => ?_, fun h10 h11 => ?_, fun hL hch T hT hdom hout hadm hnF hsub => ?_⟩
  · -- soundness
    have h11 := i14 hs
    have h10 := i11 h11
    obtain ⟨T, hT, hstr, -, hposf, hpe, hpp, hadm, hA, hB, hcnt⟩ :=
      hit_exact hE ⟨b10, hiv, b11, b14, i11, i14, h5⟩ hregs h10 h11
    obtain ⟨m, B, hs', A, -, -, -, -, hyes, -⟩ := h5 h10
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, htri⟩ := hyes h11
    obtain ⟨t15, t1, t2⟩ := htri hs
    have hy : (M.pos (Qof P) (xOf c₀)).2 = ((Qof P).vtx (c₀.nreg 83007)).2 := hE.hy.symm
    obtain ⟨he, hat⟩ := record_ok (lp := c'.nreg 83016) (rp := c'.nreg 83017) hE.hσ hT hy hposf
      hA hB ⟨t1, t2⟩
    rw [t15]
    have hQn : (Qof P).n = P.n := shear_n _ _
    refine ⟨hat, by rw [hQn]; exact hE.hh, by grind, ?_⟩
    rw [he]
    have hAB : sidePt M.W (xOf c₀).edge (M.param (Qof P) (xOf c₀)) ≠
        sidePt M.W (c'.nreg 83012) (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) := by
      show M.pos (Qof P) (xOf c₀) ≠ M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩
      rw [hposf]; exact ray_ne hT
    obtain ⟨c1, c2⟩ := (hcount _).1 (hcnt.1 hs)
    exact splitsWell_of_counts hM hNF.1.2.1 hNF.1.1 (hregs.1.1 _ hr) hadm hA hB hAB c1 c2
  · -- exactness
    obtain ⟨T, hT, hstr, -, hposf, hpe, hpp, hadm, hA, hB, hcnt⟩ :=
      hit_exact hE ⟨b10, hiv, b11, b14, i11, i14, h5⟩ hregs h10 h11
    exact ⟨T, hT, hstr, hposf, hpe, hpp, hadm, hA, hB, hcnt.trans (hcount _)⟩
  · -- completeness
    have hV : ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008) :=
      valid_compl hGM hNF hregs hr hE.hxp hE.hxe hch hL hT hdom hadm hnF hsub
    have h10 : c'.nreg 83010 = 1 := hiv.2 hV
    refine ⟨h10, ?_⟩
    by_contra h11
    obtain ⟨m, B, hs', A, harr, hnear, hlo, -, -, hno⟩ := h5 h10
    exact noHit_false hGM hNF hregs hr hE.hxp hE.hxe hV hE.x_top harr hnear hlo hT hout (hno h11)


/-! ## The cost -/

/-- The cost factor of the test for a degree cap `d`. -/
def testκ (d : ℕ) : ℕ := testK (d + 1) d 0 + 16 * (d + 2)

theorem testK_split (A D Fg : ℕ) : testK A D Fg = testK A D 0 + (A + 1) * (16 * Fg) := by
  core_grind

theorem testK_mono {A D A' D' : ℕ} (hA : A ≤ A') (hD : D ≤ D') : testK A D 0 ≤ testK A' D' 0 := by
  simp only [testK, shotAK, shotCostG, nodeG, validK, arcScanK, arcKB, vertexK, exitScanK,
    exitKB, buildK, bodyK, normK, postHitK, countK, countKB, shK]
  nlinarith

/-- **The cost of the test** is at most `testκ d · (F γ + 1)`. -/
theorem testK_le {A D d Fg : ℕ} (hA : A ≤ d + 1) (hD : D ≤ d) :
    testK A D Fg ≤ testκ d * (Fg + 1) := by
  rw [testK_split]
  have h1 := testK_mono hA hD
  have h2 : (A + 1) * (16 * Fg) ≤ 16 * (d + 2) * Fg := by nlinarith
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
  simp_all [patch] 

/-- **The candidate test meets its contract.** -/
theorem testOK {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hXl : X.CapLocal)
    (hB8 : bRestore ∉ Bo) (hBo : oracleBands ⊆ Bo) :
    TestOK (testS sh) testκ F X Ok Bo := by
  intro P W c hw pre hroom
  dsimp only at hroom ⊢
  obtain ⟨hG, hW, hX, hcap, hwf, hreg, hsimp, hσ, M, N, hMD, hGM, hOk, hNw, hNF, hdeg, hsg, hr,
    hxe, hxp, hxc, hkind, hxC, hh, hy⟩ := pre
  have hE : TGood P W M N c := tgood_of hG hW hMD hwf hreg hsimp hkind hGM hNw hNF hr hxe hxp
    hxc hxC hh hy hσ
  obtain ⟨reg₀, hregs₀⟩ := hE.regs
  have hdg : M.deg (N.F M (Qof P)) (reg₀ (c.nreg 83002)) ≤ c.nreg 83009 :=
    hdeg _ (hregs₀.1.1 _ hr)
  have hA := arcs_le_deg hGM hNF hregs₀ hr
  have hD := chords_le_deg hNF hregs₀ hr
  have hK := testK_le (Fg := F (c.nreg 83003)) (show (N.region (c.nreg 83002)).arcs.length ≤
    c.nreg 83009 + 1 by omega) (show (N.region (c.nreg 83002)).chords.length ≤ c.nreg 83009 by omega)
  obtain ⟨c', k, ex, hk, hI, hrf, hTF⟩ := testS_rsb hsh hBs hXl hB8 hBo hw hE hX hcap hOk hsg
    (by omega)
  have hsub : dBands ∪ Bo ⊆ restoreBands ∪ Bo := by
    core_grind
  refine ⟨c', k, ex, le_trans hk hK, ?_, (RF.to_frame hrf).mono hsub le_rfl⟩
  obtain ⟨b10, hiv, b11, b14, i11, i14, h5⟩ := hTF
  refine ⟨fun q hq hq' => hI.hin q (by grind [bandOf, bRestore]) (by omega), b10, b11,
    b14, fun M' N' reg hMD' hNA' hNF' hregs' => ?_⟩
  have eM : M = M' := (NFLoc.modelDesc_unique hMD' hMD).symm
  subst eM
  have hNA : NFAt c.nmem (c.nreg 83001) N := hNw.holds
  have e := nf_patch hNA hNA'
  have hregs : NFRegs M (Qof P) N reg := by
    have h : NFRegs M (Qof P) (patch N N') reg := hregs'
    rwa [e] at h
  have hF : N'.F M (Qof P) = N.F M (Qof P) := by
    have : N'.F M (Qof P) = (patch N N').F M (Qof P) := rfl
    rw [this, e]
  have hRg : ∀ r, N'.region r = N.region r := fun r => by
    have : N'.region r = (patch N N').region r := rfl
    rw [this, e]
  rw [hF, hRg]
  exact test_post hE ⟨b10, hiv, b11, b14, i11, i14, h5⟩ hregs

end

end Restore

end Chazelle.Core
