module

public import Chazelle.Core.DownPhaseDrvXRamK
public import Chazelle.Core.DownPhaseDrvXContracts
public import Chazelle.Core.DownPhaseDrvHMain

/-!
# Down phase, extraction (D6): the contract

`DrvX.extractRamSpec_of (hA : XEGlue) (hB : PostMath) : DrvR.ExtractRamSpec`: the program
`xS = setupS; padS; loopS; finS` with the cost constant `xKappa`.  Glue A gives the facts of the
run, the RAM lemmas run it, glue B and the record equality (`DrvH.nfAt_recs`,
`DrvH.regHost_congr`) give the postcondition for every readable `L', E', C', N_R'`.
-/

namespace Chazelle.Core

namespace DrvX

open Machine Machine.Stmt Programs BuildRam SignK
open DrvR (regHost keyBkt OnArcKey endPos)

@[expose] public section

theorem keyBkt_congr {Q : Polygon} {N N' : NF} (ha : N.arcs = N'.arcs) (x : WPos) :
    keyBkt Q N x = keyBkt Q N' x := by
  obtain ⟨c, a, g, s, d, o, l⟩ := N
  obtain ⟨c', a', g', s', d', o', l'⟩ := N'
  simp only at ha
  subst ha
  rfl

theorem liV_decide {x : ℕ} (hx : x ≤ 1) : liV (decide (x = 1)) = x := by
  unfold liV; by_cases h : x = 1 <;> simp [h]; omega

set_option maxHeartbeats 8000000 in
/-- **The extraction meets its contract**, given the two pieces of glue. -/
theorem extractRamSpec_of (hA : XEGlue) (hB : PostMath) : DrvR.ExtractRamSpec := by
  refine ⟨xS, xKappa, ?_⟩
  intro P W c hw hpre hroom
  obtain ⟨hG, hW, h02, hli2, L, E, C, NR, hLne, hL, hperm, hsort, hdeg, hNw, hr, hHost, hHBA, -,
    hCP, hCs, hCm, hMDwf, hMD, hCD, hNRw, hNR⟩ := hpre
  obtain ⟨XEh, SF⟩ := hA P W c L E C NR hG hW h02 hli2 hLne hL hperm hsort hdeg hNw hr hHost hHBA
    hCP hCs hCm hMDwf hMD hCD hNRw hNR hroom
  obtain ⟨sM3, sM4, sM5, sHB, sBR, sBN1, sR0, sPn, sMD, sm, sHB1, sBR3, sBN7, sR1, sRA, s7⟩ := SF
  set N := BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E
  set v := xvOf P c C N NR with hvdef
  have hK : v.K = NR.chords.length := rfl
  have hA0 := XEh.hA0
  -- set-up
  obtain ⟨d1, k1, e1, hk1, a20, a21, a22, a25, a26, a27, a28, a30, a31, a32, a33, a34, a35, a36,
      a37, a41, a42, a44, a38, a39, a40, a43, a45, a46, a47, a99, m1⟩ :=
    setupS_exec (P := P) c hw (h00 := rfl) (h01 := rfl) (h02 := rfl) (h03 := rfl) (h05 := rfl)
      (h06 := rfl) sM3 sM4 rfl sHB sBR rfl sBN1 rfl rfl rfl sR0 rfl sPn sMD sm sHB1 sBR3 sBN7 sR1
      sRA hA0 s7
  have hw1 := e1.wb_right
  have hn : (Qof P).n = P.n := shear_n _ P
  have g1 : XG P v d1 := by
    refine ⟨by rw [a20, hn], a21, a22, ?_, by rw [a26]; exact (liV_decide h02).symm, a27, a28,
      a30, a31, a32, a33, a34, a35, a36, a37, a41, a42, a44⟩
    rw [a25]
    show _ = tS C.m C.topIdx C.sideBeta
    unfold tS
    by_cases hb : C.sideBeta = true
    · rw [ite_eq_left (sM5.2 hb), ite_eq_left hb]
    · rw [ite_eq_right (fun h => hb (sM5.1 h)), ite_eq_right hb]
  -- padding
  obtain ⟨d2, k2, e2, hk2, n2⟩ := padS_exec (P := P) d1 hw1 a43 a47 a27 (Nat.zero_le _)
    (by omega)
  have o2 : ∀ r, r ≠ 217043 → d2.nreg r = d1.nreg r := fun r hr => n2.other hr
  have hw2 := e2.wb_right
  have g2 : XG P v d2 := g1.congr fun r hr => o2 r (by
    rintro rfl; revert hr; decide)
  have m2 : d2.nmem = c.nmem := by rw [n2.2.2.1, m1]
  -- the loop
  obtain ⟨d3, k3, e3, hk3, g3, c38, cm, cl, cb, f3⟩ := loopS_exec XEh d2 hw2
    (fun a _ => by rw [m2]) g2 ((o2 217039 (by decide)).trans a39)
    ((o2 217040 (by decide)).trans a40) ((o2 217038 (by decide)).trans a38)
    ((o2 217045 (by decide)).trans a45) ((o2 217046 (by decide)).trans a46)
  have hw3 := e3.wb_right
  -- the outputs
  obtain ⟨d4, k4, e4, hk4, b10, b11, b12, g4, m4⟩ : ∃ d4 k4, Exec P W finS d3 d4 k4 ∧ k4 ≤ 3 ∧
      d4.nreg 217010 = d3.nreg 217036 ∧ d4.nreg 217011 = d3.nreg 217038 ∧
      d4.nreg 217012 = d3.nreg 217037 ∧
      (∀ r, r ≠ 217010 → r ≠ 217011 → r ≠ 217012 → d4.nreg r = d3.nreg r) ∧
      d4.nmem = d3.nmem := by
    unfold finS
    exec_block
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩ <;> config_simp
    simp only [Machine.upd_other _ _ _ h1, Machine.upd_other _ _ _ h2, Machine.upd_other _ _ _ h3]
  have ex : Exec P W xS c d4 (k1 + (k2 + (k3 + k4))) := by
    simp only [xS, seqs_cons₂, seqs_one]
    exact .seq e1 (.seq e2 (.seq e3 e4))
  have fm := exec_frameM ex wrM_x
  have fr := exec_frameM2 ex wrM2_x
  -- the allocator
  have hal : d4.nreg ALLOC = c.nreg ALLOC + 5 * NR.chords.length := by
    show d4.nreg 9999 = _
    rwa [g4 9999 (by decide) (by decide) (by decide), f3.1 9999 (by decide), o2 9999 (by decide)]
  have hlen := xL_length_le P v NR v.K
  have hKc : c.nmem (c.nreg 217006) = NR.chords.length := sBR
  refine ⟨d4, k1 + (k2 + (k3 + k4)), ex, ?_, ⟨fun q hq1 hq2 => ?_, ?_⟩, ?_⟩
  · -- cost
    show _ ≤ xKappa * (c.nmem (c.nreg 217006) + 1)
    rw [hKc]; unfold xKappa
    have : v.K = NR.chords.length := rfl
    omega
  · -- registers of the band outside the reserved range
    refine fm.1 q ?_
    simp only [Bx, decide_eq_false_iff_not]
    have : q / 10000 = 21 := hq1
    omega
  · -- the outputs
    intro L' E' C' NR' reg' hLne' hL' hperm' hsort' hNat' hregs' hCP' hCs' hCm' hNRat' hNR'
    obtain ⟨rc, ra, rr⟩ := DrvH.nfAt_recs hNw.nfAt hNat'
    have hreg : regHost (decide (c.nreg 217002 = 1)) (Qof P).n N (c.nreg 217001) =
        regHost (decide (c.nreg 217002 = 1)) (Qof P).n
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L' E') (c.nreg 217001) :=
      DrvH.regHost_congr rc ra rr _ _ _
    have hP : C'.P = C.P := by rw [hCP', hCP, hreg]
    have hCC : C' = C := by
      have hs : C'.s = C.s := by rw [hCs', hCs]
      have hm : C'.m = C.m := by have h1 := hCm'; rw [hP] at h1; omega
      cases C; cases C'
      simp only [Chain.mk.injEq]
      exact ⟨hP, hs, hm⟩
    subst hCC
    obtain ⟨rcR, -, -⟩ := DrvH.nfAt_recs hNRw.nfAt hNRat'
    have hchR : ∀ t, NR'.chord t = NR.chord t := fun t => by simp only [NF.chord, rcR]
    have hxL : xL P v NR' NR'.chords.length = xL P v NR v.K := by
      show _ = xL P v NR NR.chords.length
      unfold xL kl xT
      rw [← rcR]
      simp only [hchR]
    have X' : XHyp P (decide (c.nreg 217002 = 1)) L' E' reg' (c.nreg 217001) C' NR' :=
      ⟨hG, by rwa [decide_eq_true_iff], hLne', hL', hperm', hsort', hregs',
        by have := hr; simp only [NF.nRegions] at this ⊢; rw [← rr]; exact this, hCP', hCs',
        hCm', hNR'⟩
    obtain ⟨pS, pN, pA, pO⟩ := hB P (decide (c.nreg 217002 = 1)) L' E' reg' (c.nreg 217001) C'
      NR' v X' rfl rfl rfl rfl hreg
    rw [hxL] at pS pN pA pO
    have e10 : d4.nreg 217010 = c.nreg ALLOC := b10.trans g3.r36
    have e12 : d4.nreg 217012 = c.nreg ALLOC + 3 * NR.chords.length := b12.trans g3.r37
    refine ⟨xL P v NR v.K, by omega, by omega, by omega, by omega, by rw [b11, c38],
      by rwa [m4, e10], pS, pN, pA,
      fun q hq => ⟨?_, pO q hq⟩⟩
    rw [m4, e12, ← keyBkt_congr ra]
    exact cb q hq
  · -- the frame
    refine ⟨fun r hr hra => fm.1 r ?_, fun r hr => fr r ?_, fun a ha => ?_, fun a _ => ?_,
      fm.2.2.2, ?_, ?_⟩
    · have h21 : r / 10000 ≠ 21 := fun h => hr (by
        show r / 10000 ∈ ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ)
        rw [h]; decide)
      have h99 : r ≠ 9999 := hra
      simp only [Bx, decide_eq_false_iff_not]; omega
    · have h21 : r / 10000 ≠ 21 := fun h => hr (by
        show r / 10000 ∈ ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ)
        rw [h]; decide)
      simp only [BxR, decide_eq_false_iff_not]; omega
    · rw [m4]; exact cm a ha
    · rw [fm.2.2.1]
    · rw [hal]; omega
    · rw [hal]; omega

end

end DrvX

end Chazelle.Core
