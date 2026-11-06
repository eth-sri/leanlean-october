module

public import Chazelle.Core.DownPhaseDrvDRound2

/-!
# Down-phase restoration rounds (D8), part 13: one round

**`round_step`**: from the state after `t < d₀` rounds (`RInv E t`), one execution of
`roundBody sF sB` (header, reservation, region loop, splice) reaches the state after `t + 1`
rounds, within the relative frame `Restore.RF drvBands A₀` and at most `Br` steps.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

theorem clog_two_two : Nat.clog 2 2 = 1 := by
  simpa using Nat.clog_pow 2 1 (by norm_num)

theorem splBands_sub : ({bDownDrv, bBuild, bSort, bSign} : Finset ℕ) ⊆ DrvR.drvBands := by decide

set_option maxHeartbeats 32000000 in
/-- **One round.** -/
theorem round_step {E : DEnv} (hE : DGood E) {t : ℕ} {c : Config} (hI : RInv E t c)
    (ht : t < E.d0) :
    ∃ c' k, Exec E.P E.W (roundBody E.sF E.sB) c c' k ∧ RInv E (t + 1) c' ∧
      Restore.RF DrvR.drvBands E.A₀ c c' k ∧ k ≤ E.Br := by
  obtain ⟨L, Ev, hSt, hsub, hdeg, hsg, hcnt⟩ := hI.state
  have hSt' := hSt
  obtain ⟨hD6, hDa, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW⟩ := hSt'
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at hD6 hDa hK hLb hLa hEb hEa hNW
  have hGM : GoodModel E.M := Or.inr ⟨E.Q, (shearInvariance (epsOf E.P) E.P).1 hE.hG.1, rfl⟩
  obtain ⟨hNF, -, -⟩ := BuildNF.isNF_goodModel hGM hok hperm hsort
  obtain ⟨reg, hRC, hCS, hAO, hRO, -⟩ := hNF.2.2.2
  have hregs : Restore.NFRegs E.M E.Q (BuildNF.buildNF E.M E.Q L Ev) reg := ⟨hRC, hCS, hAO, hRO⟩
  set B₀ := c.nreg ALLOC
  set R := L.length + 1 with hR
  have hElen : Ev.length = 2 * L.length := by rw [hperm.length_eq, List.length_range]
  have hRKc : R ≤ E.Kc := by
    unfold DEnv.Kc
    have : 2 ^ t ≤ 2 ^ E.d0 := Nat.pow_le_pow_right (by norm_num) ht.le
    calc R ≤ 2 ^ t * (E.K₀ + 1) := hcnt
      _ ≤ 2 ^ E.d0 * (E.K₀ + 1) := Nat.mul_le_mul_right _ this
  have hroom : B₀ + E.Br + 2 ≤ E.W := by
    have := hI.room
    have : E.Br + 2 ≤ (E.d0 - t) * (E.Br + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- 1. header, reservation, set-up
  obtain ⟨c₃, k₃, e₃, hgood, RF₃, hk₃, A₃, K3, m₃⟩ := round_A hE hI ht hSt hdeg hsg hcnt hregs
  set E' := renvOf E L Ev reg B₀ (c.nreg 210005)
  have hBK : E'.BK = B₀ + 3 * R := rfl
  have hR' : E'.R = R := rfl
  -- 2. the region loop
  obtain ⟨c₄, k₄, newL, e₄, I₄, h30, RF₄, hk₄⟩ := reg_exec hgood
  have hnew : Restore.NewOK E.M E.Q (BuildNF.buildNF E.M E.Q L Ev) reg 4 newL := by
    refine ⟨?_, I₄.hgood⟩
    have := I₄.hfst
    rwa [h30, ← E'.nRegions_N] at this
  have hnewR : newL.length ≤ R := by
    have := congrArg List.length hnew.fst
    rw [List.length_map] at this
    rw [this]
    refine (Restore.highList_length_le _ _ _).trans ?_
    simp [NF.nRegions, BuildNF.buildNF, hR]
  obtain ⟨hok', hbkA, hmono, hbcnt⟩ := round_ok hGM hok hperm hsort hregs hnew I₄.hbk
  rw [List.length_map] at hbkA hmono hbcnt
  have w₄ := I₄.wb
  have F4 : ∀ q, (210000 ≤ q ∧ q < 216012) ∨ (216060 ≤ q ∧ q < 220000) → c₄.nreg q = c.nreg q :=
    fun q hq => (I₄.regs q (by unfold FixR; omega)).trans (K3 q (by omega))
  -- 3. the arguments of the splice
  obtain ⟨c₅, k₅, e₅, hk₅, s20, s21, s22, s23, s24, f₅⟩ := splArgs_exec (P := E.P) c₄ w₄
  have w₅ := e₅.wb_right
  have g₅ : ∀ q, ¬ (210020 ≤ q ∧ q ≤ 210024) → c₅.nreg q = c₄.nreg q := fun q hq =>
    f₅.1 q (by simpa using hq)
  have m₅ : c₅.nmem = c₄.nmem := f₅.2.2.1
  have A₄ : B₀ + 5 * R ≤ c₄.nreg ALLOC := by rw [← A₃]; exact RF₄.2.2.2.2.2.1
  have A₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := g₅ _ (by unfold ALLOC; omega)
  have F5 : ∀ q, (210000 ≤ q ∧ q < 216012) ∨ (216060 ≤ q ∧ q < 220000) →
      ¬ (210020 ≤ q ∧ q ≤ 210024) → c₅.nreg q = c.nreg q := fun q hq hq' =>
    (g₅ q hq').trans (F4 q hq)
  have r1 : c₅.nreg 210001 = E.MD := by
    rw [F5 _ (Or.inl ⟨by norm_num, by norm_num⟩) (by norm_num), hI.r001]
  have r2 : c₅.nreg 210002 = c.nreg 210002 := F5 _ (Or.inl ⟨by norm_num, by norm_num⟩) (by norm_num)
  have r3 : c₅.nreg 210003 = L.length := by
    rw [F5 _ (Or.inl ⟨by norm_num, by norm_num⟩) (by norm_num), hK]
  have r4 : c₅.nreg 210004 = c.nreg 210004 := F5 _ (Or.inl ⟨by norm_num, by norm_num⟩) (by norm_num)
  have r20 : c₅.nreg 210020 = B₀ := by
    rw [s20, I₄.regs _ (Or.inl ⟨by norm_num, by norm_num⟩)]; exact hgood.r18
  have r21 : c₅.nreg 210021 = newL.length := by rw [s21, I₄.cnt]
  have r22 : c₅.nreg 210022 = B₀ + 3 * R := by
    rw [s22, I₄.regs _ (Or.inl ⟨by norm_num, by norm_num⟩)]; exact hgood.r19
  have r23 : c₅.nreg 210023 = (BuildNF.buildNF E.M E.Q L Ev).arcs.length := by
    rw [s23, I₄.regs _ (Or.inl ⟨by norm_num, by norm_num⟩)]; exact hgood.r17
  have r24 : c₅.nreg 210024 = 2 := by
    rw [s24, F4 _ (Or.inl ⟨by norm_num, by norm_num⟩), hI.r05]
  -- the memory below `B₀`
  have low5 : ∀ a, a < B₀ → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅, I₄.low a ha, m₃]
  have hA0B : E.A₀ ≤ B₀ := hI.alloc
  have agree5 : ∀ a, a < E.A₀ → c₅.nmem a = E.m₀ a := fun a ha =>
    (low5 a (by omega)).trans (hI.low a ha)
  obtain ⟨hMD₅, hwf₅⟩ := Gran.desc_agree' hE.hwf hE.hMD agree5
  -- 4. the splice
  have hAle : (BuildNF.buildNF E.M E.Q L Ev).arcs.length ≤ 2 * L.length + 1 :=
    arcs_length_le hElen
  have hspl : DrvR.splCost E.κB c₅ ≤ 8 * DrvR.κSpl E.κB * R := by
    unfold DrvR.splCost
    simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd]
    rw [r3, r21, r23, r24, clog_two_two]
    have : L.length + newL.length + (BuildNF.buildNF E.M E.Q L Ev).arcs.length + 1 ≤ 4 * R := by
      omega
    calc DrvR.κSpl E.κB * (L.length + newL.length +
          (BuildNF.buildNF E.M E.Q L Ev).arcs.length + 1) * (1 + 1)
        ≤ DrvR.κSpl E.κB * (4 * R) * 2 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = 8 * DrvR.κSpl E.κB * R := by ring
  have hk4' : k₄ ≤ (E.Bf + 2) * R + 2 := hk₄
  have hA4 : c₄.nreg ALLOC ≤ c₃.nreg ALLOC + k₄ := RF₄.2.2.2.2.2.2
  have hBr : E.Br = 40 + (E.Bf + 10) * E.Kc + 8 * DrvR.κSpl E.κB * E.Kc := rfl
  have hKc1 : (E.Bf + 10) * R ≤ (E.Bf + 10) * E.Kc := Nat.mul_le_mul_left _ hRKc
  have hKc2 : 8 * DrvR.κSpl E.κB * R ≤ 8 * DrvR.κSpl E.κB * E.Kc := Nat.mul_le_mul_left _ hRKc
  have hBfR : (E.Bf + 10) * R = (E.Bf + 2) * R + 8 * R := by ring
  have hroomS : c₅.nreg ALLOC + DrvR.splCost E.κB c₅ ≤ E.W := by
    rw [A₅]
    omega
  obtain ⟨c₆, k₆, e₆, hk₆, ⟨keepS, postS⟩, F₆⟩ := DrvR.splice_meets hE.hB E.P E.W c₅ w₅
    ⟨hE.hG, hE.hWh, by
      show ModelDescWF E.P (c₅.nreg ALLOC) c₅.nmem (c₅.nreg 210001)
      rw [r1]; exact hwf₅.mono (by omega),
      E.M, L, newL.map Prod.snd, Ev, by
      show ModelDescAt c₅.nmem (c₅.nreg 210001) E.Q E.M
      rwa [r1], hGM, by show c₅.nreg 210003 = _; exact r3, by
      show c₅.nreg 210002 + 3 * L.length ≤ c₅.nreg ALLOC
      rw [r2]; omega, by
      show ChordListAt c₅.nmem (c₅.nreg 210002) L
      rw [r2]; exact hLa c₅.nmem low5, by
      show c₅.nreg 210021 = _; rw [r21, List.length_map], by
      show c₅.nreg 210020 + 3 * (newL.map Prod.snd).length ≤ c₅.nreg ALLOC
      rw [r20, List.length_map]; omega, by
      show ChordListAt c₅.nmem (c₅.nreg 210020) (newL.map Prod.snd)
      rw [r20, m₅]; exact I₄.list, hok', by
      show c₅.nreg 210004 + 2 * L.length ≤ c₅.nreg ALLOC
      rw [r4]; omega, by
      show seg c₅.nmem (c₅.nreg 210004) (2 * L.length) = Ev
      rw [r4]; exact hEa c₅.nmem low5, hperm, hsort, by
      show c₅.nreg 210022 + 2 * (newL.map Prod.snd).length ≤ c₅.nreg ALLOC
      rw [r22, List.length_map]; omega, fun q hq => by
      show c₅.nmem (c₅.nreg 210022 + q) ≤ c₅.nreg 210023
      rw [r22, r23, m₅, ← hBK]; rw [List.length_map] at hq; exact hbkA q hq, fun q q' hq hq' hb => by
      rw [List.length_map] at hq hq'
      refine hmono q q' hq hq' ?_
      have e1 : DrvR.bkOf c₅ q = c₄.nmem (E'.BK + q) := by
        show c₅.nmem (c₅.nreg 210022 + q) = _; rw [r22, m₅, hBK]
      have e2 : DrvR.bkOf c₅ q' = c₄.nmem (E'.BK + q') := by
        show c₅.nmem (c₅.nreg 210022 + q') = _; rw [r22, m₅, hBK]
      rwa [e1, e2] at hb, fun b => by
      show DrvR.bcnt (DrvR.bkOf c₅) (2 * (newL.map Prod.snd).length) b ≤ c₅.nreg 210024
      rw [r24, List.length_map]
      have e : DrvR.bkOf c₅ = fun q => c₄.nmem (E'.BK + q) := by
        funext q; show c₅.nmem (c₅.nreg 210022 + q) = _; rw [r22, m₅, hBK]
      rw [e]; exact hbcnt b⟩ hroomS
  have w₆ := e₆.wb_right
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS E.M L (newL.map Prod.snd)
    (by show ModelDescAt c₅.nmem (c₅.nreg 210001) E.Q E.M; rwa [r1])
    (by show c₅.nreg 210003 = _; exact r3)
    (by show ChordListAt c₅.nmem (c₅.nreg 210002) L; rw [r2]; exact hLa c₅.nmem low5)
    (by show c₅.nreg 210021 = _; rw [r21, List.length_map])
    (by show ChordListAt c₅.nmem (c₅.nreg 210020) (newL.map Prod.snd); rw [r20, m₅]; exact I₄.list)
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at p3 p2l p2b p2 p4l p4b
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at pperm psort p5l pNW
  have hL'len : (L ++ newL.map Prod.snd).length = L.length + (newL.map Prod.snd).length :=
    List.length_append
  have A₆ : c₅.nreg ALLOC ≤ c₆.nreg ALLOC := F₆.2.2.2.2.2.1
  have mem₆ : ∀ a, a < c₅.nreg ALLOC → c₆.nmem a = c₅.nmem a := F₆.2.2.1
  have K6 : ∀ q, 216000 ≤ q → q < 216012 → c₆.nreg q = c.nreg q := fun q h1 h2 => by
    rw [keepS q (Or.inr (Or.inr ⟨by omega, by omega⟩)), F5 q (Or.inl ⟨by omega, h2⟩) (by omega)]
  -- 5. the counter
  have t10 : c₆.nreg 216010 = t := by rw [K6 _ (by norm_num) (by norm_num), hI.r10]
  have t02 : c₆.nreg 216002 = 1 := by rw [K6 _ (by norm_num) (by norm_num), hI.r02]
  have hk6 : k₆ ≤ 8 * DrvR.κSpl E.κB * R := le_trans hk₆ hspl
  obtain ⟨c₇, k₇, e₇, hk₇, v10, f₇⟩ := incr_exec (P := E.P) c₆ w₆ t10 t02
    (by have h1 := w₆.1 216000; rw [K6 _ (by norm_num) (by norm_num), hI.r00] at h1; omega)
  have g₇ : ∀ q, q ≠ 216010 → c₇.nreg q = c₆.nreg q := fun q hq => f₇.1 q (by simpa using hq)
  have m₇ : c₇.nmem = c₆.nmem := f₇.2.2.1
  have A₇ : c₇.nreg ALLOC = c₆.nreg ALLOC := g₇ _ (by unfold ALLOC; omega)
  -- frames
  have RF₄' : Restore.RF DrvR.drvBands E.A₀ c₃ c₄ k₄ := RF.base RF₄ hA0B
  have RF₅ : Restore.RF DrvR.drvBands E.A₀ c₄ c₅ k₅ :=
    rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₅
  have RF₆ : Restore.RF DrvR.drvBands E.A₀ c₅ c₆ k₆ :=
    (Restore.RF.of_frame F₆ (by rw [A₅]; omega)).mono splBands_sub le_rfl
  have RF₇ : Restore.RF DrvR.drvBands E.A₀ c₆ c₇ k₇ :=
    rf_of_frameB (inDrv_eq (q := 216010) (by norm_num) (by norm_num) (by unfold ALLOC; norm_num)) f₇
  have RFall := RF₃.trans (RF₄'.trans (RF₅.trans (RF₆.trans RF₇)))
  have hktot : k₃ + (k₄ + (k₅ + (k₆ + k₇))) ≤ E.Br := by omega
  -- the memory below `A₀`
  have agree7 : ∀ a, a < E.A₀ → c₇.nmem a = E.m₀ a := fun a ha => by
    rw [m₇, mem₆ a (by omega), agree5 a ha]
  -- the new state
  have hperm' : (seg c₆.nmem (c₆.nreg 210004) (2 * (L.length + (newL.map Prod.snd).length))).Perm
      (List.range (2 * (L ++ newL.map Prod.snd).length)) := by rwa [hL'len]
  have hsort' : (seg c₆.nmem (c₆.nreg 210004) (2 * (L.length + (newL.map Prod.snd).length))).Pairwise
      (BuildNF.codeLe E.M E.Q (L ++ newL.map Prod.snd)) := psort
  obtain ⟨hsub', hdeg', hsg', hcnt'⟩ := round_family hGM hok hperm hsort hregs hnew hdeg hsg
    (seg c₆.nmem (c₆.nreg 210004) (2 * (L.length + (newL.map Prod.snd).length))) hperm' hsort'
  refine ⟨c₇, k₃ + (k₄ + (k₅ + (k₆ + k₇))),
    e₃ _ c₇ _ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆ e₇))), ?_, RFall, hktot⟩
  refine ⟨e₇.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, v10, ?_, fun q hq => ?_, ?_, agree7, ?_,
    by omega, ?_⟩
  · rw [g₇ _ (by norm_num), keepS _ (Or.inl ⟨by norm_num, by norm_num⟩), r1]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r00]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r01]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r02]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r03]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r04]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r05]
  · rw [g₇ _ (by norm_num), K6 _ (by norm_num) (by norm_num), hI.r06]
  · -- the context register
    rw [g₇ _ (by norm_num), F₆.1 _ (by decide) (by unfold ALLOC; norm_num), g₅ _ (by norm_num),
      RF₄.1 _ (by decide) (by unfold ALLOC; norm_num), K3 _ (Or.inr (Or.inr rfl)), hI.rctx]
  · -- the kept registers
    unfold KeepR at hq
    rw [g₇ q (by omega), keepS q (by omega), g₅ q (by omega), F4 q (by omega), hI.keep q hq]
  · -- the state
    refine ⟨L ++ newL.map Prod.snd,
      seg c₆.nmem (c₆.nreg 210004) (2 * (L.length + (newL.map Prod.snd).length)), ?_,
      hsub.trans hsub', ?_, hsg', ?_⟩
    · have r71 : c₇.nreg 210001 = E.MD := by
        rw [g₇ _ (by norm_num), keepS _ (Or.inl ⟨by norm_num, by norm_num⟩), r1]
      have r72 : c₇.nreg 210002 = c₆.nreg 210002 := g₇ _ (by norm_num)
      have r73 : c₇.nreg 210003 = c₆.nreg 210003 := g₇ _ (by norm_num)
      have r74 : c₇.nreg 210004 = c₆.nreg 210004 := g₇ _ (by norm_num)
      have r75 : c₇.nreg 210005 = c₆.nreg 210005 := g₇ _ (by norm_num)
      have hA07 : E.A₀ ≤ c₇.nreg ALLOC := by omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hok', hperm', hsort', ?_⟩ <;>
        simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd]
      · rw [r71]; have := hE.hwf.1; omega
      · rw [r71]; exact desc_robust hE.hwf hE.hMD agree7 hA07
      · rw [r73, p3, hL'len]
      · rwa [r72, A₇, hL'len]
      · rw [r72, A₇, m₇]; exact chordListAt_robust p2 (by rwa [hL'len])
      · rwa [r74, A₇, hL'len]
      · rw [r74, A₇, m₇, hL'len]; exact seg_robust (by omega)
      · rwa [r75, A₇, m₇]
    · exact Model.DegLe.mono _ hdeg' (by omega)
    · rw [pow_succ]
      have := hcnt'
      have h2 : 2 * (L.length + 1) ≤ 2 * (2 ^ t * (E.K₀ + 1)) := Nat.mul_le_mul_left _ hcnt
      have h3 : 2 * (2 ^ t * (E.K₀ + 1)) = 2 ^ t * 2 * (E.K₀ + 1) := by ring
      omega
  · have := hI.alloc; omega
  · -- the room
    have h1 := hI.room
    have h2 := RFall.2.2.2.2.2.2
    have h3 : (E.d0 - t) * (E.Br + 2) = (E.d0 - (t + 1)) * (E.Br + 2) + (E.Br + 2) := by
      rw [show E.d0 - t = (E.d0 - (t + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

end

end DrvD

end Chazelle.Core
