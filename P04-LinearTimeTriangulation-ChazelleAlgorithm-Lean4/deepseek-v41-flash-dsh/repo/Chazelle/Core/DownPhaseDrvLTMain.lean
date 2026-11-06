module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvLTGath

/-!
# Down-phase level tail (D12): `lvTailSpec`

**`lvTailSpec : DrvR.IntOraclesSpec O → DrvR.LvTailSpec O`**: the program `tailS sB sRd`
(`sB` the sorted build `buildNFSorted`, `sRd` the restoration rounds `DrvD.roundsSpec`) gathers
the kept lists of the region table (`gather_exec`), splices them into `(L, E)`
(`DrvR.splice_meets`; the precondition from `DrvLM.levelMathSpec`), runs the rounds at
`d₀ = regCap + 4`, `γ = 2^(⌈βμ⌉+12)`, and concludes `Inv(μ)` (`i3_step`), within
`κ (K + 1) (lemma41Nat μ + 1)` steps (`cost_le`, `DrvLC.lvCostSpec`).
-/

namespace Chazelle.Core

namespace DrvLT

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

theorem n_le_top (P : Polygon) : (Qof P).n ≤ 2 ^ topGrade P.n + 1 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have := Nat.le_pow_clog (b := 2) (⊛) (P.n - 1)
  unfold topGrade
  omega

theorem pow12 (e : ℕ) : 2 ^ (e + 12) = 4 * 2 ^ (e + 10) := by
  rw [show e + 12 = (e + 10) + 2 by omega, pow_add]; ring


/-- **D12: the tail of a level.** -/
theorem lvTailSpec {O : OracleIface} (hio : DrvR.IntOraclesSpec O) : DrvR.LvTailSpec O := by
  classical
  obtain ⟨sB, κB, hB⟩ := DrvR.sortedMeets_of buildNFSorted
  obtain ⟨κo, sRd, κRd, hRd⟩ := DrvD.roundsSpec hio
  obtain ⟨κc, hκc⟩ := DrvLC.lvCostSpec.2 κo
  refine ⟨tailS sB sRd, 300 + 48 * κc + 5 * DrvR.κSpl κB * κc + κRd 134 * κc, ?_⟩
  intro Kb P W c₁ c L E reg lam X hI3 hInv hroom
  obtain ⟨hw, -, h11, hfix, hlow, -, hnreg, -, -, hA1, -, C, NR, γR, Lx, h12, hMx, hMor, hreg⟩ :=
    hInv
  -- the registers of the context
  have hfx := hfix
  have c00 : c.nreg 210000 = lam := Ρ hfx _ (by unfold DrvR.LvFixed; omega), X.r00
  have c01 : c.nreg 210001 = c₁.nreg 210001 := hfx _ (by unfold DrvR.LvFixed; omega)
  have c02 : c.nreg 210002 = c₁.nreg 210002 := hfx _ (by unfold DrvR.LvFixed; omega)
  have c03 : c.nreg 210003 = L.length := Ρ hfx _ (by unfold DrvR.LvFixed; omega), X.r03
  have c04 : c.nreg 210004 = c₁.nreg 210004 := hfx _ (by unfold DrvR.LvFixed; omega)
  have c07 : c.nreg 211007 = 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 12) := by
    Ξ hfx _ (by unfold DrvR.LvFixed; omega), X.r07
  have c09 : c.nreg 211009 = c₁.nreg 211009 := hfx _ (by unfold DrvR.LvFixed; omega)
  have hT := X.r09
  have hK : 0 < L.length := List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ X.hL)
  have hnR : (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions = L.length + 1 :=
    nRegions_build _ _ _ _
  have hμ15 : 15 ≤ DrvR.nextLvl lam := by
    unfold DrvR.nextLvl; rw [Setup.ceilBeta_eq]; have := X.h16; omega
  have hp10 : 128 ≤ 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 10) :=
    le_trans (⊛) (Nat.pow_le_pow_right (⊛) (show 7 ≤ _ by omega))
  have hγ₀ : c₁.nreg 211006 + 128 ≤ 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 12) := by
    rw [X.r06, pow12]; omega
  -- the math of the level
  obtain ⟨-, hlm⟩ := DrvLM.levelMathSpec P L E reg lam X.good X.hL X.ok X.perm X.sort X.deg X.wt
    X.regs
  obtain ⟨hsize, hok', hbk, hcode, hbcnt, hfam⟩ := hlm (c₁.nreg 211006) (c.nreg 211013) C NR γR
    Lx hγ₀ (fun r hr => by
      Ξ' hnR at hr
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, -⟩ := hreg r hr
      exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, hMx r hr⟩)
  Ξ' hnR at hsize hok' hbk hcode hbcnt hfam
  -- the sizes
  have hlen : ∀ r, r < L.length + 1 → (Lx r).length ≤ DrvR.lvNch (DrvR.nextLvl lam) :=
    fun r hr => by
      have := hsize r hr
      Ξ' X.r06 at this
      exact le_lvNch this
  have hMν : c.nreg 211013 ≤ DrvR.lvNch (DrvR.nextLvl lam) := by
    rcases hMor with h | ⟨r, hr, h⟩
    · rw [h]; exact Nat.zero_le _
    · rw [h]; exact hlen r hr
  have hK₂ : ((List.range (L.length + 1)).flatMap Lx).length ≤ (L.length + 1) * c.nreg 211013 :=
    flat_length_le Lx _ _ hMx
  obtain ⟨hc1, hc2, hc3⟩ := hκc (DrvR.nextLvl lam) hμ15
  have hc3' : (DrvR.lvNch (DrvR.nextLvl lam) + 1) *
      (DrvR.shCost κo (DrvR.lvGr (DrvR.nextLvl lam)) * DrvR.cuCost κo (DrvR.lvGr (DrvR.nextLvl lam)) *
        (cutGran (DrvR.lvGr (DrvR.nextLvl lam)) + Nat.clog 2 (DrvR.lvGr (DrvR.nextLvl lam)) + 1)) ≤
      κc * (lemma41Nat (DrvR.nextLvl lam) + 1) := by
    refine le_trans (le_of_eq ?_) hc3; ring
  have hcost := cost_le (R := L.length + 1) (K := L.length)
    (K₂ := ((List.range (L.length + 1)).flatMap Lx).length) (M := c.nreg 211013)
    (ν := DrvR.lvNch (DrvR.nextLvl lam)) (Λ := lemma41Nat (DrvR.nextLvl lam) + 1) (κc := κc)
    (κS := DrvR.κSpl κB) (κr := κRd 134) rfl hK₂ hMν (⋄) hc1 hc2 hc3'
  obtain ⟨hW134, hWK, hWM⟩ := room_small (R := L.length + 1) (K := L.length)
    (M := c.nreg 211013) (κc := κc) (κS := DrvR.κSpl κB) (κr := κRd 134) rfl hMν (⋄) hc1
  set κ := 300 + 48 * κc + 5 * DrvR.κSpl κB * κc + κRd 134 * κc with hκ
  set B := κ * (L.length + 1) * (lemma41Nat (DrvR.nextLvl lam) + 1) with hBd
  set K₂ := ((List.range (L.length + 1)).flatMap Lx).length with hK₂d
  set L₂ := (List.range (L.length + 1)).flatMap Lx with hL₂d
  -- 1. the gather
  let G : GEnv := ⟨P, W, c.nreg ALLOC, c.nmem, c.nreg, c₁.nreg 211009, c₁.nreg ALLOC,
    L.length + 1, c.nreg 211013, Qof P, BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E, Lx⟩
  have hGK : G.K₂ = K₂ := rfl
  have hGG : GGood G := ⟨by show c₁.nreg 211009 + 3 * (L.length + 1) ≤ c₁.nreg ALLOC; omega,
    hA1, fun r hr => (hreg r hr).2, hMx, by show c.nreg ALLOC + 5 * G.K₂ + 1 ≤ W; omega⟩
  obtain ⟨cg, kg, xg, hkg0, wg, v20₀, v21₀, v22₀, v23, v24₀, Ag₀, keepg, lowg₀, CLg₀, bkg₀, RFg₀⟩ :=
    gather_exec (G := G) hGG hw rfl rfl rfl h12 h11 (Ρ c09) rfl c03
      (by show 4 * L.length + 3 ≤ W; omega) (by show 4 * c.nreg 211013 ≤ W; omega)
  have hkg : kg ≤ 8 * K₂ + (35 * c.nreg 211013 + 32) * (L.length + 1) + 26 := hkg0
  have v20 : cg.nreg 210020 = c.nreg ALLOC := v20₀
  have v21 : cg.nreg 210021 = K₂ := v21₀
  have v22 : cg.nreg 210022 = c.nreg ALLOC + 3 * K₂ := v22₀
  have v24 : cg.nreg 210024 = 4 * c.nreg 211013 := v24₀
  have Ag : cg.nreg ALLOC = c.nreg ALLOC + 5 * K₂ := Ag₀
  have lowg : ∀ a, a < c.nreg ALLOC → cg.nmem a = c.nmem a := lowg₀
  have CLg : ChordListAt cg.nmem (c.nreg ALLOC) L₂ := CLg₀
  have bkg : ∀ q, q < 2 * K₂ → cg.nmem (c.nreg ALLOC + 3 * K₂ + q) =
      DrvR.keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
        (DrvR.endPos L₂ q) := bkg₀
  have RFg : Restore.RF DrvR.drvBands (c.nreg ALLOC) c cg kg := RFg₀
  have gk : ∀ r, BL r = false → r ≠ ALLOC → cg.nreg r = c.nreg r := keepg
  have g01 : cg.nreg 210001 = c₁.nreg 210001 := Ρ gk _ (⌖) (⌖), c01
  have g02 : cg.nreg 210002 = c₁.nreg 210002 := Ρ gk _ (⌖) (⌖), c02
  have g03 : cg.nreg 210003 = L.length := Ρ gk _ (⌖) (⌖), c03
  have g04 : cg.nreg 210004 = c₁.nreg 210004 := Ρ gk _ (⌖) (⌖), c04
  have g00 : cg.nreg 210000 = lam := Ρ gk _ (⌖) (⌖), c00
  have g07 : cg.nreg 211007 = 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 12) := by
    Ξ gk _ (⌖) (⌖), c07
  -- the memory below the table
  have hTA : c₁.nreg 211009 ≤ c.nreg ALLOC := ⋄
  have memg : ∀ a, a < c₁.nreg 211009 → cg.nmem a = c₁.nmem a := fun a ha => by
    rw [lowg a (⋄)]; exact hlow a ha
  have hMD : ModelDescAt cg.nmem (c₁.nreg 210001) (Qof P) (interiorModel (Qof P)) :=
    X.md cg.nmem memg
  have hone : cg.nmem (c₁.nreg 210001) = 1 := DrvD.desc_one hMD
  have hmdA := X.mdA
  have hlA := X.lA
  have heA := X.eA
  have hGM : GoodModel (interiorModel (Qof P)) :=
    Or.inr ⟨Qof P, (shearInvariance (epsOf P) P).1 X.good.1, rfl⟩
  -- the buckets
  have hbkOf : ∀ q, q < 2 * K₂ → DrvR.bkOf cg q =
      DrvR.keyBkt (Qof P) (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E)
        (DrvR.endPos L₂ q) := fun q hq => by
    show cg.nmem (cg.nreg 210022 + q) = _
    rw [v22]; exact bkg q hq
  have harcs : (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).arcs.length ≤
      2 * L.length + 1 := DrvD.arcs_length_le (Ρ X.perm.length_eq, List.length_range)
  -- 2. the splice
  have hsplCost : DrvR.splCost κB cg = DrvR.κSpl κB * (L.length + K₂ + (4 * L.length + 3) + 1) *
      (Nat.clog 2 (4 * c.nreg 211013) + 1) := by
    unfold DrvR.splCost
    ϴ rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd
    Ξ g03, v21, v23, v24
  obtain ⟨cs, ks, xs, hks, ⟨keepS, postS⟩, Fs⟩ := DrvR.splice_meets hB P W cg wg
    ⟨X.good, X.wh, by
      show ModelDescWF P (cg.nreg ALLOC) cg.nmem (cg.nreg 210001)
      Ξ g01
      exact ⟨by rw [Ag]; omega, fun h0 => absurd (hone.symm.trans h0) (⊛)⟩,
      interiorModel (Qof P), L, L₂, E, by
      show ModelDescAt cg.nmem (cg.nreg 210001) (Qof P) (interiorModel (Qof P))
      rw [g01]; exact hMD, hGM, by show cg.nreg 210003 = _; exact g03, by
      show cg.nreg 210002 + 3 * L.length ≤ cg.nreg ALLOC
      rw [g02, Ag]; omega, by
      show ChordListAt cg.nmem (cg.nreg 210002) L
      rw [g02]; exact X.lmem cg.nmem memg, by
      show cg.nreg 210021 = _; rw [v21], by
      show cg.nreg 210020 + 3 * L₂.length ≤ cg.nreg ALLOC
      rw [v20, Ag]; omega, by
      show ChordListAt cg.nmem (cg.nreg 210020) L₂
      rw [v20]; exact CLg, hok', by
      show cg.nreg 210004 + 2 * L.length ≤ cg.nreg ALLOC
      rw [g04, Ag]; omega, by
      show seg cg.nmem (cg.nreg 210004) (2 * L.length) = E
      rw [g04]; exact X.emem cg.nmem memg, X.perm, X.sort, by
      show cg.nreg 210022 + 2 * L₂.length ≤ cg.nreg ALLOC
      rw [v22, Ag]; omega,
      fun q hq => by
        show DrvR.bkOf cg q ≤ cg.nreg 210023
        Ξ hbkOf q hq, v23
        have := hbk q hq
        omega,
      fun q q' hq hq' hb => by
        Ξ' hbkOf q hq, hbkOf q' hq' at hb
        exact hcode q q' hq hq' hb,
      fun b => by
        show DrvR.bcnt (DrvR.bkOf cg) (2 * L₂.length) b ≤ cg.nreg 210024
        rw [v24, DrvLM.bcnt_congr (bk' := fun q => DrvR.keyBkt (Qof P)
          (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) (DrvR.endPos L₂ q))
          (fun q hq => hbkOf q hq)]
        exact hbcnt b⟩
    (by show cg.nreg ALLOC + DrvR.splCost κB cg ≤ W; rw [hsplCost, Ag]; omega)
  have ws := xs.wb_right
  have hks' : ks ≤ DrvR.κSpl κB * (L.length + K₂ + (4 * L.length + 3) + 1) *
      (Nat.clog 2 (4 * c.nreg 211013) + 1) := by
    have h : ks ≤ DrvR.splCost κB cg := hks
    Ξ' hsplCost at h; exact h
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS (interiorModel (Qof P)) L L₂
    (by show ModelDescAt cg.nmem (cg.nreg 210001) (Qof P) (interiorModel (Qof P)); rw [g01]; exact hMD)
    (by show cg.nreg 210003 = _; exact g03)
    (by show ChordListAt cg.nmem (cg.nreg 210002) L; rw [g02]; exact X.lmem cg.nmem memg)
    (by show cg.nreg 210021 = _; rw [v21])
    (by show ChordListAt cg.nmem (cg.nreg 210020) L₂; rw [v20]; exact CLg)
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at p3 p2l p2b p2 p4l p4b
  ϴ' rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd at pperm psort p5l pNW
  have hLL : (L ++ L₂).length = L.length + L₂.length := List.length_append
  have As : cg.nreg ALLOC ≤ cs.nreg ALLOC := Fs.2.2.2.2.2.1
  have As' : cs.nreg ALLOC ≤ cg.nreg ALLOC + ks := Fs.2.2.2.2.2.2
  set E' := seg cs.nmem (cs.nreg 210004) (2 * (L.length + L₂.length)) with hE'
  have hperm' : E'.Perm (List.range (2 * (L ++ L₂).length)) := by rw [hLL]; exact pperm
  have hsort' : E'.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) (L ++ L₂)) := psort
  obtain ⟨fsub, fdeg, fsg, fcnt⟩ := hfam E' hperm' hsort'
  -- 3. the arguments of the rounds
  obtain ⟨cr, kr0, xr0, hkr0, u00, u01, mr, fr⟩ := ltRd_exec (P := P) cs ws (⋄)
  have gr : ∀ q, q ≠ 216000 → q ≠ 216001 → cr.nreg q = cs.nreg q := fun q h1 h2 =>
    fr.1 q (⊚ h1, h2)
  have wr := xr0.wb_right
  have Ar : cr.nreg ALLOC = cs.nreg ALLOC := gr _ (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have r1 : cr.nreg 210001 = c₁.nreg 210001 := by
    Ξ gr _ (⊛) (⊛), keepS _ (Or.inl ⟨⊛, ⊛⟩), g01
  have rγ : cr.nreg 216001 = 2 ^ (Cost.ceilBeta (DrvR.nextLvl lam) + 12) := by
    Ξ u01, keepS _ (Or.inr (Or.inr ⟨⊛, ⊛⟩)), g07
  -- the frames so far
  have RFs : Restore.RF DrvR.drvBands (c.nreg ALLOC) cg cs ks :=
    (Restore.RF.of_frame Fs (by rw [Ag]; omega)).mono DrvD.splBands_sub le_rfl
  have RFr : Restore.RF DrvR.drvBands (c.nreg ALLOC) cs cr kr0 :=
    DrvD.rf_of_frameB (fun r hr => by
      ϴ' decide_eq_true_eq at hr
      exact ⟨DrvD.mem_drvBands (⋄) (⋄), by unfold ALLOC; omega⟩) fr
  have RF3 := RFg.trans (RFs.trans RFr)
  have memr : ∀ a, a < c₁.nreg 211009 → cr.nmem a = c₁.nmem a := fun a ha => by
    rw [RF3.2.2.1 a (⋄)]; exact hlow a ha
  have hcore : ∀ i, i < 10000 → cr.nreg (coreReg i) = c₁.nreg (coreReg i) := fun i hi => by
    have hb : bandOf (coreReg i) ∉ DrvR.drvBands := by
      rw [DrvR.coreReg_band i hi]; exact DrvR.bCore_notin_drvBands
    Ξ RF3.1 _ hb (DrvR.coreReg_ne_alloc i hi), hnreg _ hb (DrvR.coreReg_ne_alloc i hi)
  have Acr : c.nreg ALLOC ≤ cr.nreg ALLOC := RF3.2.2.2.2.2.1
  -- the state after the splice
  have hst : DrvR.StateAt P cr (L ++ L₂) E' := by
    have r2 : cr.nreg 210002 = cs.nreg 210002 := gr _ (⊛) (⊛)
    have r3 : cr.nreg 210003 = cs.nreg 210003 := gr _ (⊛) (⊛)
    have r4 : cr.nreg 210004 = cs.nreg 210004 := gr _ (⊛) (⊛)
    have r5 : cr.nreg 210005 = cs.nreg 210005 := gr _ (⊛) (⊛)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hok', hperm', hsort', ?_⟩ <;>
      ϴ rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd
    · rw [r1]; omega
    · rw [r1]; exact (X.md.transport memr).mono (⋄)
    · Ξ r3, p3, hLL
    · rw [r2, Ar, hLL]; exact p2b
    · rw [r2, Ar, mr]; exact DrvD.chordListAt_robust p2 (by rw [hLL]; exact p2b)
    · rw [r4, Ar, hLL]; exact p4b
    · rw [r4, Ar, mr, hLL]; exact DrvD.seg_robust (⋄)
    · rw [r5, Ar, mr]; exact pNW
  -- 4. the rounds
  have hcostR : κRd (cr.nreg 216000) * (rd cr bDownDrv 3 + 1) *
      DrvR.shCost κo (cr.nreg 216001) * DrvR.cuCost κo (cr.nreg 216001) *
      (cutGran (cr.nreg 216001) + Nat.clog 2 (cr.nreg 216001) + 1) =
      κRd 134 * (L.length + K₂ + 1) *
        (DrvR.shCost κo (DrvR.lvGr (DrvR.nextLvl lam)) *
          DrvR.cuCost κo (DrvR.lvGr (DrvR.nextLvl lam)) *
          (cutGran (DrvR.lvGr (DrvR.nextLvl lam)) +
            Nat.clog 2 (DrvR.lvGr (DrvR.nextLvl lam)) + 1)) := by
    have e3 : rd cr bDownDrv 3 = L.length + K₂ := by
      show cr.nreg 210003 = _
      Ξ gr _ (⊛) (⊛), p3
    Ξ e3, u00, rγ
    unfold DrvR.lvGr
    ring
  obtain ⟨c', k₄, x₄, hk₄, ⟨keepR, postR⟩, F₄⟩ := hRd P W cr wr
    ⟨X.envD (hcore 0 (⊛)) (hcore 1 (⊛)) memr (⋄), by rw [u00]; norm_num,
      by rw [rγ]; exact Nat.one_le_two_pow, by rw [rγ]; exact X.big2, L ++ L₂, E', hst,
      by rw [u00]; exact fdeg, by rw [rγ]; exact fsg⟩
    (by
      show cr.nreg ALLOC + κRd (cr.nreg 216000) * (rd cr bDownDrv 3 + 1) *
        DrvR.shCost κo (cr.nreg 216001) * DrvR.cuCost κo (cr.nreg 216001) *
        (cutGran (cr.nreg 216001) + Nat.clog 2 (cr.nreg 216001) + 1) ≤ W
      rw [hcostR, Ar]; omega)
  obtain ⟨L', E'', st', sub', deg', sg', cnt'⟩ := postR (L ++ L₂) E' hst
  have hk₄' : k₄ ≤ κRd (cr.nreg 216000) * (rd cr bDownDrv 3 + 1) *
      DrvR.shCost κo (cr.nreg 216001) * DrvR.cuCost κo (cr.nreg 216001) *
      (cutGran (cr.nreg 216001) + Nat.clog 2 (cr.nreg 216001) + 1) := hk₄
  Ξ' hcostR at hk₄'
  have RF4 : Restore.RF DrvR.drvBands (c.nreg ALLOC) cr c' k₄ :=
    Restore.RF.of_frame F₄ Acr
  have RFall := RF3.trans RF4
  refine ⟨c', kg + (ks + (kr0 + k₄)), Exec.seq xg (Exec.seq xs (Exec.seq xr0 x₄)), ?_,
    (RFall.mono subset_rfl (⋄)).to_frame, ?_, ?_⟩
  · -- the cost
    omega
  · -- the level register
    rw [keepR _ (Or.inl rfl), gr _ (⊛) (⊛),
      keepS _ (Or.inl ⟨⊛, ⊛⟩), g00]
  · -- `Inv(μ)`
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := st'
    refine ⟨s1, s2, L', E'', s3, s4, s5, s6, s7, s8, s9, s10, s11, deg', by rw [← rγ]; exact sg',
      ?_⟩
    have h2 : L'.length + 1 ≤ 2 ^ (DrvR.regCap + 4) * ((L ++ L₂).length + 1) := by
      Ξ' u00 at cnt'; exact cnt'
    exact i3_step X.h16 X.hlp hI3 (n_le_top P) X.r06 fcnt h2

end

end DrvLT

end Chazelle.Core
