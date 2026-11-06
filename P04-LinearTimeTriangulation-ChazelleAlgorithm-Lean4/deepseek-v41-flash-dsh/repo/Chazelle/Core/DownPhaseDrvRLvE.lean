module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRLvCall

/-!
# Down-phase driver (RAM side): one level, the region loop

**`lvBody_exec`**: one iteration of the region loop (`lvBody sH sR sX`: host RAM, region
procedure, extraction of region `j`, its table entry) keeps the invariant `LvInv` (from `j` to
`j + 1` regions) in at most `Kb` steps, allocating at most its steps.
**`lvLoop_exec`**: the region loop, from `LvInv … 0` to `LvInv … (K + 1)`.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

open Classical in

/-- **One iteration of the region loop.** -/
theorem lvBody_exec {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hH : HostMeets sH κH) (hR : RegMeets O sR κR) (hX : ExtMeets sX κX)
    (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    {c₁ : Config} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ}
    (ctx : LvCtx O P W c₁ L E reg lam) {Kb : ℕ}
    (hKb : 30 + κH + κR * (lemma41Nat (nextLvl lam) + 1) + κX * (lvNch (nextLvl lam) + 1) +
      lvNch (nextLvl lam) ≤ Kb)
    (hroom : c₁.nreg ALLOC + (L.length + 1) * Kb ≤ W)
    {j : ℕ} {c : Config} (hj : j < L.length + 1) (hinv : LvInv O P W c₁ L E reg Kb j c) :
    ∃ c' k, Exec P W (lvBody sH sR sX) c c' k ∧ LvInv O P W c₁ L E reg Kb (j + 1) c' ∧
      k ≤ Kb ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, h10, h11, hfix, hmem, hrmem, hoth, hroth, hout, hA1, hA2, C, NR, γR, Lx, htot, hMx,
    hM0, hdat⟩ := hinv
  set Q := Qof P with hQ
  set N := BuildNF.buildNF (interiorModel Q) Q L E with hN
  set T := c₁.nreg 211009 with hT
  set A₁ := c₁.nreg ALLOC with hA₁
  set μ := nextLvl lam with hμ
  set γ₀ := 3 * 2 ^ (Cost.ceilBeta μ + 10) with hγ₀
  have hT9 := ctx.r09
  have fx := hfix
  have f05 := fx 210005 (by unfold LvFixed; omega)
  have f02 := fx 211002 (by unfold LvFixed; omega)
  have f04 := fx 211004 (by unfold LvFixed; omega)
  have f06 := fx 211006 (by unfold LvFixed; omega)
  have f08 := fx 211008 (by unfold LvFixed; omega)
  have f09 := fx 211009 (by unfold LvFixed; omega)
  have f14 := fx 211014 (by unfold LvFixed; omega)
  have f31 := fx 230001 (by unfold LvFixed; omega)
  have f30 := fx 230000 (by unfold LvFixed; omega)
  have hjr : j < N.nRegions := by rw [nRegions_bnf]; exact hj
  have hjK : (j + 1) * Kb ≤ (L.length + 1) * Kb := Nat.mul_le_mul_right _ (⋄)
  have hjK' : (j + 1) * Kb = j * Kb + Kb := ⋆
  -- the math of region `j`
  obtain ⟨hHwf, hHreg, hHsimp, -, -, -, -⟩ :=
    hR1 P L E reg j ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs hjr
  have hsz := (hLM P L E reg lam ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.wt
    ctx.regs).1
  obtain ⟨hH20, hrun, hpt3, hpt10⟩ := hsz j hjr
  set H := regHost (decide (Mountain.LeftInside Q)) Q.n N j with hHdef
  -- A: the arguments of the host RAM
  obtain ⟨cA, kA, eA, hkA, a00, a01, a02⟩ := lvRegA_exec (P := P) c hw
  have gA : FrameB BregA c cA := exec_frameB eA wr_lvRegA
  have hwA := eA.wb_right
  have AA : cA.nreg ALLOC = c.nreg ALLOC := gA.1 _ (⌖)
  have hnfA : NFWithin cA.nmem (cA.nreg 215000) (cA.nreg ALLOC) N := by
    Ξ a00, f05, gA.2.2.1, AA
    exact (ctx.nf.transport hmem).mono (⋄)
  -- H: the host
  obtain ⟨cH, kH, eH, hkH, frH, keepH, b10, b10', hHA, b12⟩ := callH hH cA hwA ctx.good ctx.wh
    ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg hnfA (by rw [a02, f08]; exact ctx.r08)
    (by rw [a02, f08]; exact ctx.r08') (Ρ a01, h10) hj (by rw [AA]; omega)
  have hwH := eH.wb_right
  have AH := frH.2.2.2.2.2.2
  have AH' := frH.2.2.2.2.2.1
  set HB := cH.nreg 215010 with hHB
  -- B: the arguments of the region procedure
  obtain ⟨cB, kB, eB, hkB, d00, d01, d02, d03, d04, d05⟩ := lvRegB_exec (P := P) cH hwH
  have gB : FrameB BregB cH cB := exec_frameB eB wr_lvRegB
  have hwB := eB.wb_right
  have AB : cB.nreg ALLOC = cH.nreg ALLOC := gB.1 _ (⌖)
  have kHq : ∀ q, bandOf q = bDownDrv → (q < 215000 ∨ 216000 ≤ q) → cH.nreg q = c.nreg q :=
    fun q hq hr => (keepH q hq hr).trans (gA.1 q (by
      simp only [BregA, decide_eq_false_iff_not]; omega))
  have core : ∀ q, bandOf q ∉ ({bDownDrv} : Finset ℕ) → q ≠ ALLOC → cH.nreg q = c.nreg q :=
    fun q hq hA => (frH.1 q hq hA).trans (gA.1 q (by
      simp only [Finset.mem_singleton, bandOf, bDownDrv] at hq
      simp only [BregA, decide_eq_false_iff_not]; omega))
  have mB : ∀ a, a < c.nreg ALLOC → cB.nmem a = c.nmem a := fun a ha => by
    rw [gB.2.2.1, frH.2.2.1 a (⋄), gA.2.2.1]
  have envB := ctx.envD
    (by rw [show coreReg 0 = 230000 from rfl, gB.1 _ (⌖), core _ (by decide) (by decide)]
        exact f30)
    (by rw [show coreReg 1 = 230001 from rfl, gB.1 _ (⌖), core _ (by decide) (by decide)]
        exact f31)
    (fun a ha => (mB a (⋄)).trans (hmem a ha)) (by omega)
  have g31 : cB.nreg 219205 = c₁.nreg (coreReg 1) := by
    rw [d05, core _ (⌖) (by decide)]; exact f31
  have hXB : (gradeCtx O).holds P cB.nmem (c₁.nreg (coreReg 1)) (cB.nreg ALLOC) := by
    have := envB.2.2.2.2.1
    rwa [gB.1 _ (⌖), core _ (by decide) (by decide), show coreReg 1 = 230001 from rfl,
      f31] at this
  have hcapB : P.n - 1 ≤ (gradeCtx O).cap P cB.nmem (c₁.nreg (coreReg 1)) := by
    have := envB.2.2.2.2.2
    rwa [gB.1 _ (⌖), core _ (by decide) (by decide), show coreReg 1 = 230001 from rfl,
      f31] at this
  have hHrob : Robust (cB.nreg ALLOC) cB.nmem (fun m => HostAt m HB H) := by
    rw [AB, gB.2.2.1]; exact hostAt_robust hHA b10'
  have hjKb : c.nreg ALLOC + Kb ≤ W := by
    have := hA2; omega
  have hroomR : cB.nreg ALLOC + κR * (lemma41Nat μ + 1) ≤ W := by
    have e1 : cB.nreg ALLOC ≤ c.nreg ALLOC + κH := ⋄
    have e2 : 30 + κH + κR * (lemma41Nat μ + 1) ≤ Kb := ⋄
    omega
  -- R: the region procedure
  obtain ⟨cR, kR, eR, hkR, frR, keepR, e10, e11, e12, e12', hmwf, hmd, NRj, hNRj, hcj⟩ :=
    callR hR cB hwB ctx.good ctx.wh (HB := HB) (H := H) d00 (Ρ d01, b12)
      (by rw [d02, kHq _ (⌖) (by decide), f02]; exact ctx.r02)
      (by rw [d03, kHq _ (⌖) (by decide), f04]; exact ctx.r04)
      (by rw [d04, kHq _ (⌖) (by decide), f06]; exact ctx.r06) g31 hXB
      (by have := nextLvl_lt ctx.h16; unfold nextLvl at this ⊢; omega)
      (mu_le_grades hcapB ctx.h16 ctx.hlp) (g0_facts μ).1 (g0_facts μ).2.1 (g0_facts μ).2.2
      (le_trans ctx.big hcapB) hHrob (by rw [AB]; exact b10') hH20 hHwf hHreg hHsimp hpt3
      hrun hroomR
  have hwR := eR.wb_right
  have hkR' : kR ≤ κR * (lemma41Nat μ + 1) := hkR
  have AR : cR.nreg ALLOC ≤ cB.nreg ALLOC + kR := frR.2.2.2.2.2.2
  have AR' : cB.nreg ALLOC ≤ cR.nreg ALLOC := frR.2.2.2.2.2.1
  have kRq : ∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → ¬(219200 ≤ q ∧ q ≤ 219205) →
      cR.nreg q = cH.nreg q := fun q hq hr hb => (keepR q hq hr).trans (gB.1 q (by
        simp only [BregB, decide_eq_false_iff_not]; omega))
  -- C: the arguments of the extraction
  obtain ⟨cC, kC, eC, hkC, x00, x01, x02, x03, x04, x05, x06⟩ := lvRegC_exec (P := P) cR hwR
  have gC : FrameB BregC cR cC := exec_frameB eC wr_lvRegC
  have hwC := eC.wb_right
  have AC : cC.nreg ALLOC = cR.nreg ALLOC := gC.1 _ (⌖)
  have mC : ∀ a, a < c.nreg ALLOC → cC.nmem a = c.nmem a := fun a ha => by
    rw [gC.2.2.1, frR.2.2.1 a (⋄), mB a ha]
  have hnfC : NFWithin cC.nmem (cC.nreg 217000) (cC.nreg ALLOC) N := by
    rw [x00, kRq _ (⌖) (by decide) (by decide), kHq _ (by decide) (by decide), f05]
    exact ((ctx.nf.transport fun a ha => (mC a (⋄)).trans (hmem a ha)).mono (by omega))
  have hHrobC : Robust (cC.nreg ALLOC) cC.nmem (fun m => HostAt m HB H) := by
    rw [AC, gC.2.2.1]; exact hHrob.frame frR
  have hpt : (hostChainOf Q H hpt3).m + 1 ≤ 10 * 2 ^ μ + 8 := by
    rw [hostChainOf_m]; show (H.poly Q).n ≤ _; rw [DownMath.host_poly_n]; exact hpt10
  have hnch : NRj.chords.length ≤ lvNch μ := nch_le hHsimp hcj e12 hpt rfl
  have hroomX : cC.nreg ALLOC + κX * (NRj.chords.length + 1) ≤ W := by
    have e1 : cC.nreg ALLOC ≤ c.nreg ALLOC + κH + κR * (lemma41Nat μ + 1) := by
      have := hkR'; omega
    have e2 : κX * (NRj.chords.length + 1) ≤ κX * (lvNch μ + 1) :=
      Nat.mul_le_mul_left _ (⋄)
    have e3 : 30 + κH + κR * (lemma41Nat μ + 1) + κX * (lvNch μ + 1) ≤ Kb := ⋄
    omega
  -- X: the extraction
  obtain ⟨cX, kX, eX, hkX, frX, keepX, Lj, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10⟩ :=
    callX hX cC hwC ctx.good ctx.wh ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs hnfC
      (by rw [x02, kRq _ (⌖) (by decide) (by decide), kHq _ (by decide) (by decide), f08]
          exact ctx.r08)
      (by rw [x02, kRq _ (⌖) (by decide) (by decide), kHq _ (by decide) (by decide), f08]
          exact ctx.r08')
      (by rw [x01, kRq _ (⌖) (by decide) (by decide), kHq _ (by decide) (by decide), h10])
      hj (by rw [x03, kRq _ (⌖) (by decide) (by decide)]) x05 hHrobC
      (by rw [AC]; omega) (by rw [x04, kRq _ (⌖) (by decide) (by decide)]; exact b12)
      (hostChainOf_P _ _ hpt3) (hostChainOf_s _ _ hpt3) (hostChainOf_m _ _ hpt3)
      (by rw [AC, gC.2.2.1]; exact hmwf) (by rw [AC, gC.2.2.1]; exact hmd)
      (by rw [x06, AC, gC.2.2.1]; exact hNRj) hcj.1 hroomX
  have hwX := eX.wb_right
  have AX : cX.nreg ALLOC ≤ cC.nreg ALLOC + kX := frX.2.2.2.2.2.2
  have AX' : cC.nreg ALLOC ≤ cX.nreg ALLOC := frX.2.2.2.2.2.1
  have kXq : ∀ q, bandOf q = bDownDrv → q < 215000 → cX.nreg q = c.nreg q := fun q hq hr => by
    rw [keepX q hq (⋄), gC.1 q (by simp only [BregC, decide_eq_false_iff_not]; omega),
      kRq q hq (⋄) (by omega), kHq q hq (by omega)]
  -- the length of the new kept list
  have hLj : Lj.length ≤ lvNch μ := by
    have h2 := len_le_of_kept y7 y8 (fun x hx => hx.1) hcj.1.1.1
    rw [Gran.ncard_F hcj.1] at h2
    exact h2.trans hnch
  have hlen_r : ∀ r, r < j → (Lx r).length ≤ lvNch μ := by
    intro r hr
    have hrr : r < N.nRegions := by rw [nRegions_bnf]; omega
    obtain ⟨hok_r, -⟩ := hdat r hr
    have hok_r' := hok_r
    obtain ⟨hCP, -, hCm, -⟩ := hok_r'
    have simp_r := (hR1 P L E reg r ctx.good ctx.hL ctx.ok ctx.perm ctx.sort ctx.deg ctx.regs
      hrr).2.2.1
    have sz := (hsz r hrr).2.2.2
    rw [ctx.r06] at hok_r
    refine regOK_len (μ := μ) hok_r (by rw [hCP]; exact simp_r) ?_
    rw [hCm, hCP, DownMath.host_poly_n]; exact sz
  have htot_le : ((List.range j).flatMap Lx).length ≤ j * lvNch μ := by
    Ξ List.length_flatMap
    have := List.sum_le_length_nsmul ((List.range j).map fun r => (Lx r).length) (lvNch μ)
      (fun x hx => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        exact hlen_r r (List.mem_range.1 hr))
    simpa using this
  -- E: the largest length
  obtain ⟨cE, kE, eE, hkE, z13⟩ := lvRegE_exec (P := P) cX hwX
  have gE : FrameB BregE cX cE := exec_frameB eE wr_lvRegE
  have hwE := eE.wb_right
  have kEq : ∀ q, q ≠ 211013 → cE.nreg q = cX.nreg q := fun q hq => gE.1 q (by
    simp only [BregE, decide_eq_false_iff_not]; exact hq)
  -- D: the table entry
  have hNK1 : (j + 1) * lvNch μ ≤ (j + 1) * Kb := Nat.mul_le_mul_left _ (⋄)
  have hjm : (j + 1) * lvNch μ = j * lvNch μ + lvNch μ := ⋆
  obtain ⟨cD, kD, eD, hkD, w12, w10, wp, wl, wb, wm, wrr, wrm, wout⟩ :=
    lvRegD_exec (P := P) cE hwE (T := T) (j := j) (ℓ := Lj.length)
      (tot := ((List.range j).flatMap Lx).length)
      (by rw [kEq _ (⌖), kXq _ (by decide) (by decide)]; exact f09)
      (by rw [kEq _ (⌖), kXq _ (by decide) (by decide)]; exact h10)
      (by rw [kEq _ (⌖), kXq _ (by decide) (by decide), f14]; exact ctx.r14)
      (kEq _ (⌖)) (by rw [kEq _ (by decide)]; exact y5) (kEq _ (by decide))
      (by rw [kEq _ (⌖), kXq _ (by decide) (by decide)]; exact htot)
      (⋄) (by omega) (by omega)
  have gD : FrameM BregD cE cD := exec_frameM eD wrM_lvRegD
  have hwD := eD.wb_right
  have kDq : ∀ q, q ≠ 211020 → q ≠ 211012 → q ≠ 211010 → cD.nreg q = cE.nreg q := fun q h1 h2 h3 =>
    gD.1 q (by simp only [BregD, decide_eq_false_iff_not]; omega)
  have AD : cD.nreg ALLOC = cX.nreg ALLOC := by
    rw [kDq _ (⌖) (by decide) (by decide), kEq _ (by decide)]
  -- the memory
  have hmD : ∀ a, a < c.nreg ALLOC → (a < T + 3 * j ∨ T + 3 * j + 3 ≤ a) →
      cD.nmem a = c.nmem a := fun a ha hb => by
    rw [wm a hb, gE.2.2.1, frX.2.2.1 a (⋄), mC a ha]
  -- the registers outside the driver's bands
  have hob : ∀ q, bandOf q ∉ drvBands → q ≠ ALLOC → cD.nreg q = c.nreg q := by
    intro q hq hA
    have h21 : bandOf q ≠ bDownDrv := fun h => hq (h ▸ bDownDrv_mem_drvBands)
    have hr : q < 210000 ∨ 220000 ≤ q := by
      simp only [bandOf, bDownDrv] at h21; omega
    rw [kDq q (⋄) (by omega) (by omega), kEq q (by omega),
      frX.1 q (fun h => hq (by
        have : ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ) ⊆ drvBands := ⌖
        exact this h)) hA,
      gC.1 q (by simp only [BregC, decide_eq_false_iff_not]; omega),
      frR.1 q hq hA, gB.1 q (by simp only [BregB, decide_eq_false_iff_not]; omega),
      core q (by simp only [Finset.mem_singleton]; exact h21) hA]
  have hrob : ∀ q, bandOf q ∉ drvBands → cD.rreg q = c.rreg q := by
    intro q hq
    have h21 : bandOf q ≠ bDownDrv := fun h => hq (h ▸ bDownDrv_mem_drvBands)
    have hr : q < 210000 ∨ 220000 ≤ q := by
      simp only [bandOf, bDownDrv] at h21; omega
    rw [wrr, gE.2.1 q (by simp only [BregE, decide_eq_false_iff_not]; omega),
      frX.2.1 q (fun h => hq (by
        have : ({bDownDrv, bSign, bLocate, bBuild, bSort} : Finset ℕ) ⊆ drvBands := ⌖
        exact this h)),
      gC.2.1 q (by simp only [BregC, decide_eq_false_iff_not]; omega),
      frR.2.1 q hq, gB.2.1 q (by simp only [BregB, decide_eq_false_iff_not]; omega),
      frH.2.1 q (by simp only [Finset.mem_singleton]; exact h21),
      gA.2.1 q (by simp only [BregA, decide_eq_false_iff_not]; omega)]
  have hrm : ∀ a, a < c.nreg ALLOC → cD.rmem a = c.rmem a := fun a ha => by
    rw [wrm, gE.2.2.2.1, frX.2.2.2.1 a (⋄), gC.2.2.2.1, frR.2.2.2.1 a (by omega),
      gB.2.2.2.1, frH.2.2.2.1 a (⋄), gA.2.2.2.1]
  have hoD : cD.output = c.output := by
    rw [wout, gE.2.2.2.2, frX.2.2.2.2.1, gC.2.2.2.2, frR.2.2.2.2.1, gB.2.2.2.2, frH.2.2.2.2.1,
      gA.2.2.2.2]
  have kFix : ∀ q, bandOf q = bDownDrv → q < 215000 → q ≠ 211020 → q ≠ 211012 → q ≠ 211010 →
      q ≠ 211013 → cD.nreg q = c.nreg q := fun q hq hr h1 h2 h3 h4 => by
    Ξ kDq q h1 h2 h3, kEq q h4, kXq q hq hr
  -- the cost
  have ex : Exec P W (lvBody sH sR sX) c cD (kA + (kH + (kB + (kR + (kC + (kX + (kE + kD))))))) :=
    .seq eA (.seq eH (.seq eB (.seq eR (.seq eC (.seq eX (.seq eE eD))))))
  have hkX' : kX ≤ κX * (lvNch μ + 1) :=
    hkX.trans (Nat.mul_le_mul_left _ (⋄))
  refine ⟨cD, _, ex, ?_, ⋄, by omega⟩
  have hb21 : ∀ q, (210000 ≤ q ∧ q < 215000) → bandOf q = bDownDrv := fun q hq => by
    simp only [bandOf, bDownDrv]; omega
  refine ⟨hwD, w10, ?_, ?_, fun a ha => by rw [hmD a (⋄) (by omega)]; exact hmem a ha,
    fun a ha => by rw [hrm a (⋄)]; exact hrmem a ha,
    fun q hq hA => by rw [hob q hq hA]; exact hoth q hq hA,
    fun q hq => by rw [hrob q hq]; exact hroth q hq, by rw [hoD]; exact hout, ⋄,
    by rw [hjK'] at hjK; omega, ?_⟩
  · rw [kFix _ (⌖) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h11
  · intro q hq
    have hq' := hq
    unfold LvFixed at hq'
    rcases hq' with h | h | h | h | h
    · rw [kFix q (hb21 q (⋄)) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact fx q hq
    · rw [kFix q (hb21 q (⋄)) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact fx q hq
    · rw [kFix q (hb21 q (⋄)) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact fx q hq
    · subst h; rw [hob _ (⌖) (by decide)]; exact fx _ hq
    · subst h; rw [hob _ (⌖) (by decide)]; exact fx _ hq
  · have m13 : cD.nreg 211013 = max (c.nreg 211013) Lj.length := by
      rw [kDq _ (⌖) (by decide) (by decide), z13, y5, kXq _ (by decide) (by decide)]
    have hTj : T + 3 * j + 3 ≤ A₁ := ⋄
    refine ⟨fun r => if r = j then hostChainOf Q H hpt3 else C r,
      fun r => if r = j then NRj else NR r, fun r => if r = j then cR.nreg 219212 else γR r,
      fun r => if r = j then Lj else Lx r, ?_, ?_, ?_, ?_⟩
    · have e1 : (List.range j).flatMap (fun r => if r = j then Lj else Lx r) =
          (List.range j).flatMap Lx :=
        List.flatMap_congr (fun r hr => by
          simp only [show r ≠ j by have := List.mem_range.1 hr; omega, ↓reduceIte])
      rw [w12, List.range_succ, List.flatMap_append, List.length_append, e1,
        List.flatMap_singleton]
      ϴ ↓reduceIte
    · intro r hr
      Ξ m13
      by_cases h : r = j
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte]; have := hMx r (⋄); omega
    · Ξ m13
      rcases hM0 with h0 | ⟨r, hr, hr'⟩
      · by_cases hl : Lj.length = 0
        · left; omega
        · right; exact ⟨j, ⋄, by simp only [↓reduceIte]; omega⟩
      · right
        by_cases hl : Lj.length ≤ c.nreg 211013
        · exact ⟨r, ⋄, by simp only [show r ≠ j by omega, ↓reduceIte]; omega⟩
        · exact ⟨j, ⋄, by simp only [↓reduceIte]; omega⟩
    · intro r hr
      by_cases h : r = j
      · subst h
        ϴ ↓reduceIte
        refine ⟨⟨hostChainOf_P _ _ hpt3, hostChainOf_s _ _ hpt3, hostChainOf_m _ _ hpt3, hcj,
          by rw [ctx.r06]; exact e12, by rw [ctx.r06]; exact e12', y7, y8, y9,
          fun q hq => (y10 q hq).2⟩, ?_⟩
        have pA : c.nreg ALLOC ≤ cX.nreg 217010 := ⋄
        have bA : c.nreg ALLOC ≤ cX.nreg 217012 := ⋄
        refine ⟨wl, by rw [wp]; omega, by rw [wp, AD]; exact y2, ?_, by rw [wb]; omega,
          by rw [wb, AD]; exact y4, fun q hq => ?_⟩
        · Ξ wp
          exact clAt_congr y6 fun x hx1 hx2 => Ρ wm x (by right; omega), gE.2.2.1
        · Ξ wb, wm _ (by right; omega), gE.2.2.1
          exact (y10 q hq).1
      · ϴ h, ↓reduceIte
        obtain ⟨h1, h2⟩ := hdat r (⋄)
        refine ⟨h1, h2.transport (⋄) (fun a ha => ?_) (by omega)⟩
        obtain ⟨ha1, ha2⟩ := ha
        refine hmD a ha1 ?_
        by_cases hA : a < A₁
        · have := ha2 hA; left; omega
        · right; omega

/-- **The region loop.** -/
theorem lvLoop_exec {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hH : HostMeets sH κH) (hR : RegMeets O sR κR) (hX : ExtMeets sX κX)
    (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    {c₁ : Config} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {lam : ℕ}
    (ctx : LvCtx O P W c₁ L E reg lam) {Kb : ℕ}
    (hKb : 30 + κH + κR * (lemma41Nat (nextLvl lam) + 1) + κX * (lvNch (nextLvl lam) + 1) +
      lvNch (nextLvl lam) ≤ Kb)
    (hroom : c₁.nreg ALLOC + (L.length + 1) * Kb ≤ W)
    {c : Config} (hinv0 : LvInv O P W c₁ L E reg Kb 0 c) :
    ∃ c' k, Exec P W (lvLoop sH sR sX) c c' k ∧ LvInv O P W c₁ L E reg Kb (L.length + 1) c' ∧
      k ≤ (Kb + 2) * (L.length + 1) + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, ex, hI, hk, hA⟩ := forLoopA (P := P) (W := W) (ir := 211010) (nr := 211011)
    (fun j c => LvInv O P W c₁ L E reg Kb j c) Kb (L.length + 1)
    (fun j c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c hj h => lvBody_exec hH hR hX hR1 hLM ctx hKb hroom hj h) hinv0 (Nat.zero_le _)
  exact ⟨c', k, ex, hI, by simpa using hk, hA⟩

end exec

end

end DrvR

end Chazelle.Core
