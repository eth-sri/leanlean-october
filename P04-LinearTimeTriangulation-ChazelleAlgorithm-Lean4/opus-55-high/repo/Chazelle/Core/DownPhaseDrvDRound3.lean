module

public import Chazelle.MacT
public import Chazelle.Core.RestoreTestOK
public import Chazelle.Core.ShootCutShK1M
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.ShootCutGrade

namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)
@[expose] public section
theorem clog_two_two : Nat.clog 2 2 = 1 := by
  rfl
theorem splBands_sub : ({bDownDrv, bBuild, bSort, bSign} : Finset ℕ) ⊆ DrvR.drvBands := by_decide
set_option maxHeartbeats 32000000 in
/-- **One round.** -/
theorem round_step {E : DEnv} (hE : DGood E) {t : ℕ} {c : Config} (hI : RInv E t c)
    (ht : t < E.d0) :
    ∃ c' k, Exec E.P E.W ztkec c c' k ∧ RInv E ztbx c' ∧
      Restore.RF DrvR.drvBands E.A₀ c c' k ∧ k ≤ E.Br := by
  obtain ⟨L, Ev, hSt, hsub, hdeg, hsg, hcnt⟩ := hI.state
  have hSt' := hSt
  obtain ⟨hD6, hDa, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW⟩ := hSt'
  zutz
  have hGM : GoodModel E.M := Or.inr ⟨E.Q, (shearInvariance _ E.P).1 hE.hG.1, rfl⟩
  zubrl
  obtain ⟨reg, hRC, hCS, hAO, hRO, -⟩ := hNF.2.2.2
  have hregs : Restore.NFRegs E.M E.Q ztjhc reg := zteyk
  zujml
  zuinx
  have hElen : Ev.length = 2 * L.length := by zunoj
  have hRKc : R ≤ E.Kc := by
    zuhql

    calc R ≤ 2 ^ t * ztbjj := hcnt
      _ ≤ 2 ^ E.d0 * ztbjj := Nat.mul_le_mul_right _ this
  have hroom : ztpit := by
    have := hI.room
    zuhvk

  -- 1. header, reservation, set-up
  obtain ⟨c₃, k₃, e₃, hgood, RF₃, hk₃, A₃, K3, m₃⟩ := round_A hE hI ht hSt hdeg hsg hcnt hregs
  set E' := renvOf E L Ev reg B₀ _ with hE'
  have hBK : E'.BK = B₀ + 3 * R := rfl
  have hR' : E'.R = R := rfl
  -- 2. the region loop
  obtain ⟨c₄, k₄, newL, e₄, I₄, h30, RF₄, hk₄⟩ := reg_exec hgood
  have hnew : Restore.NewOK E.M E.Q ztjhc reg 4 newL := by
    refine ⟨?_, I₄.hgood⟩
    have := I₄.hfst
    rw [h30, ← E'.nRegions_N] at this
    tauto
  have hnewR : newL.length ≤ R := by
    have := congrArg List.length hnew.fst
    zubus
    zubk
    zuhit
    simp [NF.nRegions, BuildNF.buildNF, hR]
  obtain ⟨hok', hbkA, hmono, hbcnt⟩ := round_ok hGM hok hperm hsort hregs hnew I₄.hbk
  rw [List.length_map] at hbkA hmono hbcnt
  have w₄ := I₄.wb
  have F4 : ∀ q, ztelg ∨ ztgyo → c₄.nreg q = c.nreg q :=
    fun q hq => (I₄.regs q (by unfold FixR; omega)).trans by_grind
  -- 3. the arguments of the splice
  obtain ⟨c₅, k₅, e₅, hk₅, s20, s21, s22, s23, s24, f₅⟩ := splArgs_exec (P := E.P) c₄ w₄
  zuef
  have g₅ : ∀ q, ¬ ztnfm → c₅.nreg q = c₄.nreg q := fun q hq =>
    f₅.1 q by_grind
  have m₅ := f₅.2.2.1
  have A₄ : B₀ + 5 * R ≤ c₄.nreg ALLOC := by rw [← A₃]; exact RF₄.2.2.2.2.2.1
  have A₅ : ztcrj := by_grind
  have F5 : ∀ q, ztelg ∨ ztgyo →
      ¬ ztnfm → c₅.nreg q = c.nreg q := by_grind
  have r1 : c₅.nreg 210001 = E.MD := by
    rw [F5 _ by_omega by_norm_num, hI.r001]
  have r2 : c₅.nreg 210002 = c.nreg 210002 := by_grind
  have r3 : c₅.nreg 210003 = L.length := by
    grind
  have r4 : c₅.nreg 210004 = c.nreg 210004 := by_grind
  have r20 : c₅.nreg 210020 = B₀ := by
    rw [s20, I₄.regs _ ztec]; exact hgood.r18
  have r21 : c₅.nreg 210021 = newL.length := by rw [s21, I₄.cnt]
  have r22 : c₅.nreg 210022 = B₀ + 3 * R := by
    rw [s22, I₄.regs _ ztec]; exact hgood.r19
  have r23 : c₅.nreg 210023 = (BuildNF.buildNF E.M E.Q L Ev).arcs.length := by
    rw [s23, I₄.regs _ ztec]; exact hgood.r17
  have r24 : c₅.nreg 210024 = 2 := by
    rw [s24, F4 _ by_omega, hI.r05]
  -- the memory below `B₀`
  have low5 : ∀ a, a < B₀ → c₅.nmem a = c.nmem a := fun a ha => by
    rw [m₅, I₄.low a ha, m₃]
  have hA0B := hI.alloc
  have agree5 := fun a ha =>
    (low5 a by_omega).trans (hI.low a ha)
  obtain ⟨hMD₅, hwf₅⟩ := Gran.desc_agree' hE.hwf hE.hMD agree5
  -- 4. the splice
  have hAle : (BuildNF.buildNF E.M E.Q L Ev).arcs.length ≤ 2 * L.length + 1 :=
    arcs_length_le hElen
  have hspl : DrvR.splCost E.κB c₅ ≤ 8 * DrvR.κSpl E.κB * R := by
    unfold DrvR.splCost
    zuju
    rw [r3, r21, r23, r24, clog_two_two]
    have : L.length + newL.length + (BuildNF.buildNF E.M E.Q L Ev).arcs.length + 1 ≤ 4 * R := by
      omega
    calc DrvR.κSpl E.κB * (L.length + newL.length +
          (BuildNF.buildNF E.M E.Q L Ev).arcs.length + 1) * (1 + 1)
        ≤ DrvR.κSpl E.κB * (4 * R) * 2 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
      _ = 8 * DrvR.κSpl E.κB * R := by_ring
  have hk4' : k₄ ≤ ztnd * R + 2 := hk₄
  have hA4 := RF₄.2.2.2.2.2.2
  have hBr : E.Br = 40 + ztcli * E.Kc + 8 * DrvR.κSpl E.κB * E.Kc := rfl
  have hKc1 : ztyzi := Nat.mul_le_mul_left _ hRKc
  have hKc2 : 8 * DrvR.κSpl E.κB * R ≤ 8 * DrvR.κSpl E.κB * E.Kc := Nat.mul_le_mul_left _ hRKc
  have hBfR : ztcli * R = ztnd * R + 8 * R := by_ring
  have hroomS : c₅.nreg ALLOC + DrvR.splCost E.κB c₅ ≤ E.W := by
    omega
  obtain ⟨c₆, k₆, e₆, hk₆, ⟨keepS, postS⟩, F₆⟩ := DrvR.splice_meets hE.hB E.P E.W c₅ w₅
    ⟨hE.hG, hE.hWh, by
      show ModelDescWF E.P _ c₅.nmem ztqkr
      zvnal; exact hwf₅.mono by_omega,
      E.M, L, newL.map Prod.snd, Ev, by
      show ModelDescAt c₅.nmem ztqkr E.Q E.M
      grind, hGM, by show c₅.nreg 210003 = _; exact r3, by
      show c₅.nreg 210002 + 3 * L.length ≤ c₅.nreg ALLOC
      omega, by
      show ChordListAt c₅.nmem ztvnw L
      rw [r2]; exact hLa c₅.nmem low5, by
      show c₅.nreg 210021 = _; zuoja, by
      show c₅.nreg 210020 + 3 * (newL.map Prod.snd).length ≤ c₅.nreg ALLOC
      rw [r20, List.length_map]; omega, by
      show ChordListAt c₅.nmem ztvnx _
      zuojb; exact I₄.list, hok', by
      show c₅.nreg 210004 + 2 * L.length ≤ c₅.nreg ALLOC
      omega, by
      show seg c₅.nmem (c₅.nreg 210004) _ = Ev
      rw [r4]; exact hEa c₅.nmem low5, hperm, hsort, by
      show c₅.nreg 210022 + 2 * (newL.map Prod.snd).length ≤ c₅.nreg ALLOC
      rw [r22, List.length_map]; omega, fun q hq => by
      show c₅.nmem ztlmr ≤ c₅.nreg 210023
      rw [r22, r23, m₅, ← hBK]; rw [List.length_map] at hq; exact hbkA q hq, fun q q' hq hq' hb => by
      rw [List.length_map] at hq hq'
      refine hmono q q' hq hq' ?_
      have e1 : DrvR.bkOf c₅ q = c₄.nmem ztswv := by
        show c₅.nmem ztlmr = _; grind
      have e2 : DrvR.bkOf c₅ q' = c₄.nmem (E'.BK + q') := by
        show c₅.nmem (c₅.nreg 210022 + q') = _; grind
      omega, fun b => by
      show DrvR.bcnt _ _ b ≤ c₅.nreg 210024
      rw [r24, List.length_map]
      have e : DrvR.bkOf c₅ = fun q => c₄.nmem ztswv := by
        funext q; show c₅.nmem ztlmr = _; grind
      zvmwe; exact hbcnt b⟩ hroomS
  zujb
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS E.M L ztvzx
    (by show ModelDescAt c₅.nmem ztqkr E.Q E.M; zvnal; omega)
    (by show c₅.nreg 210003 = _; exact r3)
    (by show ChordListAt c₅.nmem ztvnw L; rw [r2]; exact hLa c₅.nmem low5)
    (by show c₅.nreg 210021 = _; zuoja)
    (by show ChordListAt c₅.nmem ztvnx _; zuojb; exact I₄.list)
  zufl

  have hL'len : (L ++ newL.map Prod.snd).length = L.length + (newL.map Prod.snd).length :=
    List.length_append
  have A₆ := F₆.2.2.2.2.2.1
  have mem₆ := F₆.2.2.1
  have K6 : ∀ q, 216000 ≤ q → q < 216012 → c₆.nreg q = c.nreg q := fun q h1 h2 => by
    rw [keepS q by_omega, F5 q by_omega by_omega]
  -- 5. the counter
  have t10 : c₆.nreg 216010 = t := by rw [K6 _ by_norm_num by_norm_num, hI.r10]
  have t02 : c₆.nreg 216002 = 1 := by rw [K6 _ by_norm_num by_norm_num, hI.r02]
  have hk6 := le_trans hk₆ hspl
  have hA6 := F₆.2.2.2.2.2.2
  have hk5 := hk₅
  have hA3 := A₃
  obtain ⟨c₇, k₇, e₇, hk₇, v10, f₇⟩ := incr_exec (P := E.P) c₆ w₆ t10 t02
    (by have h1 := w₆.1 216000; rw [K6 _ by_norm_num by_norm_num, hI.r00] at h1; omega)
  have g₇ := fun q hq => f₇.1 q ztrla
  have m₇ := f₇.2.2.1
  have A₇ : ztfky := g₇ _ by_decide
  -- frames
  have RF₄' := RF.base RF₄ hA0B
  have RF₅ : Restore.RF DrvR.drvBands E.A₀ c₄ c₅ k₅ :=
    rf_of_frameB (fun r hr => by
      zucy
      exact ztbgh) f₅
  have RF₆ : Restore.RF DrvR.drvBands E.A₀ c₅ c₆ k₆ :=
    (Restore.RF.of_frame F₆ by_omega).mono splBands_sub le_rfl
  have RF₇ : Restore.RF DrvR.drvBands E.A₀ c₆ c₇ k₇ :=
    rf_of_frameB (inDrv_eq by_norm_num by_norm_num by_decide) f₇
  have RFall := RF₃.trans (RF₄'.trans ztqci)
  have hktot : k₃ + ztber ≤ E.Br := by_omega
  -- the memory below `A₀`
  have agree7 : ztkod := fun a ha => by
    rw [m₇, mem₆ a by_omega, agree5 a ha]
  -- the new state
  have hperm' : (seg c₆.nmem ztqkt ztjer).Perm
      ztihj := by rw [hL'len]; omega
  have hsort' : (seg c₆.nmem _ _).Pairwise
      (BuildNF.codeLe E.M E.Q _) := psort
  obtain ⟨hsub', hdeg', hsg', hcnt'⟩ := round_family hGM hok hperm hsort hregs hnew hdeg hsg
    (seg c₆.nmem ztqkt ztjer) hperm' hsort'
  refine ⟨c₇, k₃ + ztber,
    e₃ _ c₇ _ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆ e₇))), ?_, RFall, hktot⟩
  refine ⟨e₇.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, v10, ?_, fun q hq => ?_, ?_, agree7, ?_,
    by omega, ?_⟩
  · zufmz
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r00]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r01]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r02]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r03]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r04]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r05]
  · rw [g₇ _ by_norm_num, K6 _ by_norm_num by_norm_num, hI.r06]
  · -- the context register
    rw [g₇ _ by_norm_num, F₆.1 _ by_decide by_decide, g₅ _ by_norm_num,
      RF₄.1 _ by_decide by_decide, K3 _ by_omega, hI.rctx]
  · -- the kept registers
    unfold KeepR at hq
    rw [g₇ q by_omega, keepS q by_omega, g₅ q by_omega, F4 q by_omega, hI.keep q hq]
  · -- the state
    refine ⟨L ++ newL.map Prod.snd,
      seg c₆.nmem _ _, ?_,
      hsub.trans hsub', ?_, hsg', ?_⟩
    · have r71 : c₇.nreg 210001 = E.MD := by
        zufmz
      have r72 : c₇.nreg 210002 = c₆.nreg 210002 := g₇ _ by_norm_num
      have r73 : c₇.nreg 210003 = c₆.nreg 210003 := g₇ _ by_norm_num
      have r74 : c₇.nreg 210004 = c₆.nreg 210004 := g₇ _ by_norm_num
      have r75 : c₇.nreg 210005 = c₆.nreg 210005 := g₇ _ by_norm_num
      have hA07 : ztukm := by_omega
      refine ztfcy <;>
        zuju
      · zuove; have := hE.hwf.1; omega
      · zuove; exact desc_robust hE.hwf hE.hMD agree7 hA07
      · omega
      · omega
      · rw [r72, A₇, m₇]; exact chordListAt_robust p2 by_omega
      · omega
      · rw [r74, A₇, m₇, hL'len]; exact seg_robust by_omega
      · rw [r75, A₇, m₇]; omega
    · exact Model.DegLe.mono _ hdeg' by_omega
    · zugwx
      have := hcnt'
      have h2 := by_omega
      have h3 : 2 * (2 ^ t * ztbjj) = 2 ^ t * 2 * ztbjj := by_ring
      omega
  · have := hI.alloc; omega
  · -- the room
    zudxy

    have h3 : ztemm * ztbgq = ztztj * ztbgq + ztbgq := by
      rw [show E.d0 - t = ztztj + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega
end
end DrvD
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (ivB qE)
@[expose] public section
def ivS : Stmt :=
  .ifLtN 212001 212011 (.instr (.copyN 212046 212070))
    (block [.subN 212046 212010 212000, .subN 212046 212046 212070])

/-- The record `vtrip li n i d w` into `81008 … 81010`. -/
def recS : Stmt :=
  .seq (.instr (.copyN 81008 212070)) (.seq ivS
    (.ifLtN 212001 212086 (block [.copyN 81009 212097, .copyN 81010 212046])
      (block [.copyN 81009 212046, .copyN 81010 212097])))

/-- The buckets of both ends: arc scans (`K > 0`) or `0` (`K = 0`). -/
def bktS : Stmt :=
  .ifLtN 212001 212012
    (.seq DrvD.scanS (.seq DrvD.stB (.seq ztovg
      (.seq DrvD.scanS DrvD.stB))))
    (.seq ztotx (.seq DrvD.stB DrvD.stB))

/-- **Append the record and its buckets.** -/
def emitS : Stmt := .seq recS (.seq DrvD.appT bktS)

/-- The registers `recS` writes. -/
def Brec (r : ℕ) : Bool := decide (81008 ≤ r ∧ r ≤ 81010) || decide (r = 212046)
theorem wr_recS : wr Brec recS = true := by_decide

/-- The registers `emitS` writes. -/
def Bemit (r : ℕ) : Bool := Brec r || DrvD.Bapp r
theorem bemit_rec (r : ℕ) (h : Brec r = true) : Bemit r = true := by zuoip
theorem bemit_app (r : ℕ) (h : DrvD.Bapp r = true) : Bemit r = true := by zuoip
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **The record.** -/
theorem recS_exec (c : Config) (hw : WordsBounded W c) {li : Bool} {n i d w : ℕ}
    (hn : c.nreg 212010 = n) (hi : c.nreg 212070 = i) (_hin : i < n) (hd : c.nreg 212086 = d)
    (hd1 : d ≤ 1) (hw97 : c.nreg 212097 = w) (hli : c.nreg 212011 = if li then 1 else 0)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k, Exec P W recS c c' k ∧ k ≤ 9 ∧ c'.nreg 81008 = (vtrip li n i d w).1 ∧
      c'.nreg 81009 = (vtrip li n i d w).2.1 ∧ c'.nreg 81010 = (vtrip li n i d w).2.2 ∧
      FrameB Brec c c' := by
  have e₁ := Exec.copyN (P := P) hw 81008 212070
  set c₁ : Config := { c with nreg := upd c.nreg 81008 _ } with hc₁
  zud
  have g₁ : ∀ r, r ≠ 81008 → c₁.nreg r = c.nreg r := by_simp_all
  -- `ivB`
  obtain ⟨c₂, k₂, e₂, hk₂, v46, g₂⟩ : ∃ c₂ k₂, Exec P W ivS c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 212046 = ivB li n i ∧ ∀ r, r ≠ 212046 → c₂.nreg r = c₁.nreg r := by
    cases li with
    | true =>
      have a := Exec.copyN (P := P) w₁ 212046 212070
      refine ⟨_, _, .ifLtN_true by_simp_all a,
        by omega, ?_, by_simp_all⟩
      zumzo; rw [g₁ _ by_norm_num, hi]; rfl
    | false =>
      obtain ⟨c₂, k₂, e₂, hk₂, v⟩ : ∃ c₂ k₂, Exec P W (block [.subN 212046 212010 212000,
          .subN 212046 212046 212070]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ (c₂.nreg 212046 = n - 1 - i ∧
          ∀ r, r ≠ 212046 → c₂.nreg r = c₁.nreg r) := by
        exec_block
        simp_all
      exact ⟨c₂, _, .ifLtN_false by_simp_all
        e₂, by_omega, by_tauto, v.2⟩
  zue
  -- the ends
  have hd' : c₂.nreg 212086 = d := by_simp_all
  have c1' : zturb := by_simp_all
  have hw' : c₂.nreg 212097 = w := by_simp_all
  have h81 : c₂.nreg 81008 = i := by
    simp_all
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
  · obtain ⟨c₃, k₃, e₃, hk₃, v⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 81009 212046,
        .copyN 81010 212097]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 81009 = ivB li n i ∧
        c₃.nreg 81010 = w ∧ c₃.nreg 81008 = i) := by
      exec_block
      simp_all
    have ex : ztpjv := .seq e₁ ztejy
    exact ztgos
  · obtain ⟨c₃, k₃, e₃, hk₃, v⟩ : ∃ c₃ k₃, Exec P W (block [.copyN 81009 212097,
        .copyN 81010 212046]) c₂ c₃ k₃ ∧ k₃ = 2 ∧ (c₃.nreg 81009 = w ∧
        c₃.nreg 81010 = ivB li n i ∧ c₃.nreg 81008 = i) := by
      exec_block
      simp_all
    have ex : ztpjv := .seq e₁ ztgxc
    exact ztgos
theorem vtrip_fst (li : Bool) (n i d w : ℕ) : (vtrip li n i d w).1 = i := by
  unfold vtrip; grind
set_option maxHeartbeats 8000000 in
/-- **Appending an emitted chord**: the record `x = vtrip li n i d w` is appended at
`B₂ + 3 |T|`, the buckets of its ends at `BK + 2 |T|`, `BK + 2 |T| + 1` (`BK = B₂ + 3 Kmax`). -/
theorem emitS_exec (_hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {li : Bool} {i d w r K MD H A₀ B₂ Kmax : ℕ} {m₀ : ℕ → ℕ}
    {N : NF} {T : List ztwjg}
    (hi : c.nreg 212070 = i) (hin : i < P.n) (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (hw97 : c.nreg 212097 = w) (hli : c.nreg 212011 = if li then 1 else 0)
    (hn : c.nreg 212010 = P.n) (hK : c.nreg 212012 = K)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0)
    (d02 : c.nreg 216002 = 1) (d03 : c.nreg 216003 = 0) (d05 : c.nreg 216005 = 2)
    (d14 : c.nreg 216014 = m₀ ztdtf) (d16 : c.nreg 216016 = m₀ ztctc)
    (d17 : c.nreg 216017 = N.arcs.length) (d31 : c.nreg 216031 = m₀ ztwj + 2 + 5 * r)
    (d001 : c.nreg 210001 = MD)
    (d20 : c.nreg 216020 = T.length) (d21 : c.nreg 216021 = B₂ + 3 * T.length)
    (d22 : c.nreg 216022 = B₂ + 3 * Kmax + 2 * T.length)
    (hlow : ∀ a, a < A₀ → c.nmem a = m₀ a) (hA₀ : A₀ ≤ B₂) (hTK : T.length < Kmax)
    (hroom : B₂ + 5 * Kmax ≤ W) (hp : m₀ ztwj + 2 + 5 * r < A₀)
    (hLB : m₀ ztctc + m₀ ztyjt ≤ W)
    (hlist : ChordListAt c.nmem B₂ ztqcx)
    (hbk : 0 < K → DrvD.BktOK ztwiq zta N T
      (fun q => c.nmem ztelz))
    (hbk0 : K = 0 → ∀ q, q < 2 * T.length → c.nmem ztelz = 0)
    (hnA : (N.region r).arcs.length = m₀ (m₀ ztwj + 5 * r))
    (hscan : 0 < K → ∀ m : ℕ → ℕ, (∀ a, a < A₀ → m a = m₀ a) → (∀ a, m a ≤ W) → ∀ s, s < 2 →
      DrvD.ScanGood P W ztwiq N r ztfbb m MD
        (m₀ ztdtf) (m₀ ztctc + m₀ ztyjt))
    (hex : 0 < K → ∀ s, s < 2 → ∃ j ∈ (N.region r).arcs, DrvD.matchB N.arcs.length j
      (DrvD.tA ztwiq zta N ztfbb j)
      (DrvD.tB ztwiq zta N ztfbb j) = true) :
    ∃ c' k, Exec P W emitS c c' k ∧ k ≤ 2 * ztjic * (N.region r).arcs.length + 40 ∧
      FrameM Bemit c c' ∧ WordsBounded W c' ∧
      (∀ a, (a < B₂ ∨ B₂ + 5 * Kmax ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 216020 = T.length + 1 ∧ c'.nreg 216021 = B₂ + 3 * ztnpv ∧
      c'.nreg 216022 = B₂ + 3 * Kmax + 2 * ztnpv ∧
      ChordListAt c'.nmem B₂ ((T ++ [ztmnf]).map Prod.snd) ∧
      (0 < K → DrvD.BktOK ztwiq zta N (T ++ [ztmnf])
        (fun q => c'.nmem ztelz)) ∧
      (K = 0 → ∀ q, q < 2 * ztnpv → c'.nmem ztelz = 0) := by
  set x := vtrip li P.n i d w with hx
  set t := T.length with ht
  set BK := B₂ + 3 * Kmax with hBK
  set p := m₀ ztwj + 2 + 5 * r with hpd
  have hW3 : ztmd := by have := hWh; unfold hostWords at this; omega
  -- 1. the record
  obtain ⟨c₁, k₁, e₁, hk₁, r1, r2, r3, f₁⟩ := recS_exec (P := P) c hw hn hi hin hd hd1 hw97 hli c0 c1
  zud
  zuepx
  -- 2. the triple
  obtain ⟨c₂, k₂, e₂, hk₂, m₂, d21', d20', d42, d43, d41, d400, d40, f₂⟩ := DrvD.appT_exec (P := P)
    c₁ w₁ (d := B₂ + 3 * t) (n := t) (p := p) (LB := m₀ ztctc)
    (by rw [g₁ _ by_decide, d21]) (by rw [g₁ _ by_decide, d20])
    (by rw [g₁ _ by_decide, d02]) (by rw [g₁ _ by_decide, d05])
    (by rw [g₁ _ by_decide, d31]) (by rw [g₁ _ by_decide, d16]) by_omega by_omega
    by_omega (by rw [f₁.2.2.1, show p - 1 = m₀ ztwj + 5 * r + 1 by omega,
      hlow _ by_omega]; omega)
    (by rw [r1, vtrip_fst]; omega) by_omega
  zue
  rw [f₁.2.2.1, show p - 2 = m₀ ztwj + 5 * r by omega, hlow _ by_omega, ← hnA] at d42
  rw [f₁.2.2.1, show p - 1 = m₀ ztwj + 5 * r + 1 by omega, hlow _ by_omega] at d43
  rw [r1, vtrip_fst] at d41
  rw [r2] at d40
  rw [g₁ _ by_decide, d001] at d400
  zucgb
  have m₂' : ∀ a, (a < B₂ + 3 * t ∨ B₂ + 3 * t + 3 ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
      Machine.upd_other _ _ _ by_omega, f₁.2.2.1]
  -- the list
  have hL₂ : ChordListAt c₂.nmem B₂ ((T ++ [ztcof]).map Prod.snd) := by
    zujgt
    have hlen : (T.map Prod.snd).length = t := by_grind
    refine Gran.ChordListAt.snoc hlist ztpbf ?_ ?_ ?_
    · grind
    · rw [hlen, m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_same, r1]
    · rw [hlen, m₂, Machine.upd_other _ _ _ by_omega, Machine.upd_same, r2]
    · rw [hlen, m₂, Machine.upd_same, r3]
  have hlow₂ : ∀ a, a < A₀ → c₂.nmem a = m₀ a := by_grind
  -- registers kept so far
  have K2 : ∀ q, Brec q = false → DrvD.BappT q = false → c₂.nreg q = c.nreg q :=
    by grind
  have c1₂ : zturb := by rw [K2 _ by_decide by_decide, c1]
  have hK₂ : c₂.nreg 212012 = K := by rw [K2 _ by_decide by_decide, hK]
  have d22₂ : c₂.nreg 216022 = BK + 2 * t := by rw [K2 _ by_decide by_decide, d22]
  have d02₂ : zturc := by rw [K2 _ by_decide by_decide, d02]
  have hlen₂ : ((T ++ [ztcof]).map Prod.snd).length = t + 1 := by simp [ht]
  have FM₁ := (FrameB.toM f₁).mono bemit_rec
  have FM₂ := f₂.mono fun q h => bemit_app q (DrvD.bapp_of_appT q h)
  rcases Nat.eq_zero_or_pos K with hK0 | hKp
  · -- `K = 0`: the buckets `0`
    have e₃ := Exec.constN (P := P) w₂ 216053 0 ztbg
    set c₃ : Config := { c₂ with nreg := upd c₂.nreg 216053 0 } with hc₃
    have g₃ : ∀ q, q ≠ 216053 → c₃.nreg q = c₂.nreg q := fun q h => by zumwr; zumxk
    obtain ⟨c₄, k₄, e₄, hk₄, m₄, d22₄, f₄⟩ := DrvD.stB_exec (P := P) c₃ e₃.wb_right
      (d := BK + 2 * t) by_grind by_grind
      by_omega
    obtain ⟨c₅, k₅, e₅, hk₅, m₅, d22₅, f₅⟩ := DrvD.stB_exec (P := P) c₄ e₄.wb_right
      (d := BK + 2 * t + 1) d22₄ (by rw [f₄.1 _ by_decide, g₃ _ by_norm_num, d02₂])
      by_omega
    have v53 : c₄.nreg 216053 = 0 := by rw [f₄.1 _ by_decide, hc₃]; simp
    have ex : Exec P W emitS c c₅ _ :=
      .seq e₁ (.seq e₂ (.ifLtN_false by_omega ztbpd))
    have m₅' : c₅.nmem = upd (upd c₂.nmem ztjgu 0) ztnjp 0 := by
      rw [m₅, m₄, v53]; rfl
    have FM₃ : FrameM Bemit c₂ c₅ := (((FrameB.toM (exec_frameB e₃ (by decide :
      wr (fun q => decide (q = 216053)) _ = true))).mono fun q h => by
        zvmwo at h; subst h; decide).trans
      ((f₄.mono fun q h => by zvmwo at h; subst h; decide).trans
        (f₅.mono fun q h => by zvmwo at h; subst h; decide)))
    have G5 : ∀ q, q ≠ 216053 → q ≠ 216022 → c₅.nreg q = c₂.nreg q := fun q h1 h2 => by
      rw [f₅.1 q by_grind, f₄.1 q by_grind, g₃ q h1]
    refine ⟨c₅, _, ex, ?_, FM₁.trans ztuyf, e₅.wb_right, fun a ha => ?_, ?_, ?_, ?_,
      ?_, fun h => absurd hK0 by_omega, fun _ q hq => ?_⟩
    · omega
    · rw [m₅', Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        m₂' a by_omega]
    · rw [G5 _ by_norm_num by_norm_num, d20']
    · rw [G5 _ by_norm_num by_norm_num, d21']; ring
    · omega
    · zueby

      rw [m₅', Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    · rw [m₅']
      rcases Nat.lt_or_ge q ztssn with hq' | hq'
      · rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
          m₂' _ by_omega]
        exact hbk0 hK0 q hq'
      · rcases (by omega : q = 2 * t ∨ q = 2 * t + 1) with rfl | rfl
        · simp
        · rw [show BK + ztbxv = BK + 2 * t + 1 by ring, Machine.upd_same]
  · -- `K > 0`: the arc scans
    have S1 := hscan hKp c₂.nmem hlow₂ w₂.2 0 by_norm_num
    obtain ⟨c₃, k₃, e₃, hk₃, fd₀, f₃⟩ := DrvD.scanS_exec S1 c₂ w₂ rfl
      (by zuouo; rfl) (by zuoup; zunxy) (by rw [d42])
      ztqeu (by rw [K2 _ by_decide by_decide, d14])
      (by rw [K2 _ by_decide by_decide, d17]) d02₂
      (by rw [K2 _ by_decide by_decide, d03]) by_omega (hex hKp 0 by_norm_num)
    zubj
    zuepy
    obtain ⟨c₄, k₄, e₄, hk₄, m₄, d22₄, f₄⟩ := DrvD.stB_exec (P := P) c₃ w₃
      (d := BK + 2 * t) (by rw [g₃ _ by_decide, d22₂]) (by rw [g₃ _ by_decide, d02₂])
      by_omega
    zucc
    have g₄ : ∀ q, q ≠ 216022 → c₄.nreg q = c₃.nreg q := fun q h => f₄.1 q by_grind
    have e₅ := Exec.copyN (P := P) w₄ 216040 81010
    set c₅ : Config := { c₄ with nreg := upd c₄.nreg 216040 _ } with hc₅
    zuef
    have g₅ : ∀ q, q ≠ 216040 → c₅.nreg q = c₄.nreg q := fun q h => by zunbe; zumxk
    -- the memory before the second scan
    have m₄' : c₄.nmem = upd c₂.nmem ztjgu ztvnh := by rw [m₄, f₃.2.2.1]
    have hlow₅ : ztknz := fun a ha => by
      show c₄.nmem a = _
      rw [m₄', Machine.upd_other _ _ _ by_omega, hlow₂ a ha]
    have S2 := hscan hKp c₅.nmem hlow₅ w₅.2 1 by_norm_num
    have K3 : ∀ q, DrvD.Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₅.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 => by rw [g₅ q h3, g₄ q h2, g₃ q h1]
    obtain ⟨c₆, k₆, e₆, hk₆, fd₁, f₆⟩ := DrvD.scanS_exec S2 c₅ w₅ rfl
      (by zunbe; zumzo
          rw [g₄ _ by_norm_num, g₃ _ by_decide, g₂ _ by_decide, r3]; rfl)
      (by rw [K3 _ by_decide by_norm_num by_norm_num, d41]
          zunxy)
      (by rw [K3 _ by_decide by_norm_num by_norm_num, d42])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, d43])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, K2 _ by_decide by_decide, d14])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, K2 _ by_decide by_decide, d17])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, d02₂])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, K2 _ by_decide by_decide, d03])
      (by rw [K3 _ by_decide by_norm_num by_norm_num, d400]) (hex hKp 1 by_norm_num)
    zujb
    obtain ⟨c₇, k₇, e₇, hk₇, m₇, d22₇, f₇⟩ := DrvD.stB_exec (P := P) c₆ w₆
      (d := BK + 2 * t + 1) (by rw [f₆.1 _ by_decide, g₅ _ by_norm_num, d22₄])
      (by rw [f₆.1 _ by_decide, K3 _ by_decide by_norm_num by_norm_num, d02₂])
      by_omega
    have ex : Exec P W emitS c c₇ _ :=
      .seq e₁ (.seq e₂ (.ifLtN_true by_omega
        ztyoi))
    have m₇' : c₇.nmem = upd (upd c₂.nmem ztjgu ztvnh) ztnjp
        (c₆.nreg 216053) := by
      rw [m₇, f₆.2.2.1]; grind
    have FM₃ :=
      (((FrameB.toM f₃).mono fun q h => bemit_app q ztsws).trans
      ((f₄.mono fun q h => bemit_app q ztswr).trans
      (((FrameB.toM (exec_frameB e₅ (by decide :
        wr (fun q => decide _) _ = true))).mono
          fun q h => bemit_app q (DrvD.bapp_of_40 q h)).trans
      (((FrameB.toM f₆).mono fun q h => bemit_app q ztsws).trans
      (f₇.mono fun q h => bemit_app q ztswr)))))
    have G7 : ∀ q, DrvD.Bscan q = false → q ≠ 216022 → q ≠ 216040 → c₇.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 => by rw [f₇.1 q by_grind, f₆.1 q h1, K3 q h1 h2 h3]
    have hnA' : (N.region r).arcs.length = (N.region r).arcs.length := rfl
    refine ⟨c₇, _, ex, ?_, FM₁.trans ztuyf, e₇.wb_right, fun a ha => ?_, ?_, ?_, ?_,
      ?_, fun _ => ?_, fun h => absurd h by_omega⟩
    · grind
    · rw [m₇', Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        m₂' a by_omega]
    · rw [G7 _ by_decide by_norm_num by_norm_num, d20']
    · rw [G7 _ by_decide by_norm_num by_norm_num, d21']; ring
    · omega
    · zueby

      rw [m₇', Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega]
    · refine DrvD.BktOK.snoc (hbk hKp) zteso ?_ ?_
      · show c₇.nmem _ = c.nmem _
        rw [m₇', Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
          m₂' _ by_omega]
      · show DrvD.ScanFound _ _ N r _ _
        rw [m₇', Machine.upd_other _ _ _ by_omega, Machine.upd_same]
        omega
      · show DrvD.ScanFound _ _ N r _ _
        rw [m₇', show BK + ztbxv = BK + 2 * t + 1 by ring, Machine.upd_same]
        omega
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt sideInArc)
open Chazelle.Visibility (DirInterior chordEnd chordSet chords OpenEdgePt)
open DrvR (ivB qE walkItems regHost)
open BuildNF (codeLe wposOf gapStarts)
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-! ## The ends of a new chord -/

/-- **Both ends of an emitted record lie on closed arcs of its region.** -/
theorem ends_on_arcs (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ regList li Q ztbapn) {y : WPos}
    (hy : y = (recOf x).lpos ∨ y = (recOf x).rpos) :
    ∃ j ∈ ((BuildNF.buildNF ztd Q L E).region r).arcs,
      j < (BuildNF.buildNF ztd Q L E).arcs.length ∧
      Restore.ClosedArc ztxes
        ztxer
        ((interiorModel Q).key Q y) := by
  zugyj
  zubpb
  obtain ⟨hcQ, hcS, hcR, hatt, -⟩ := regList_sound B.hQ B.hdh B.hli B.fam hR hl hx
  zumbp
  zulip
  have hnc := DownMath.nChords_build B.hQ B.hL B.hperm B.hsort
  have hNF : IsNF _ Q N := DownMath.isNF_build B.hQ B.hL B.hperm B.hsort
  have hne : (N.F _ Q).Nonempty :=
    ⟨_, (DownMath.chordPos_attach hNF (show 0 < N.nChords by rw [hnc]; exact B.hK)
      ztp).1⟩
  have hA : SideAttach (interiorModel Q).W ((recOf x).toSet ztd Q) y.edge
      ((interiorModel Q).param Q y) := by
    zukmr
    · exact hatt.1
    · exact hatt.2
  obtain ⟨a, b, harc, hcl⟩ := Restore.attach_closedArc hM hFam.2.1 hFam.1 hne
    (B.hregs.1.1 r hr) (chords_family B.hQ hcQ) hcS hcR hA
  obtain ⟨j, hj, hjr, hs, he⟩ := B.hregs.2.2.1.2.2.1 r hr a b harc
  refine ⟨j, (B.hregs.2.2.1.2.2.2 r hr j).2 by_omega, hj, ?_⟩
  zuoiq; tauto

/-- **The arc scan of an end of an emitted record finds a match.** -/
theorem scan_hex (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ regList li Q ztbapn) {y : WPos}
    (hy : y = (recOf x).lpos ∨ y = (recOf x).rpos) :
    ∃ j ∈ ((BuildNF.buildNF ztd Q L E).region r).arcs,
      DrvD.matchB (BuildNF.buildNF ztd Q L E).arcs.length j
        (DrvD.tA ztd Q ztwjp y j)
        (DrvD.tB ztd Q ztwjp y j) = true := by
  obtain ⟨j, hjm, hj, hcl⟩ := ends_on_arcs B hr hx hy
  zudz
  exact ⟨j, hjm, DrvD.match_of_closedArc B.hK hE hj hcl (by simp [DrvD.tA]) (by simp [DrvD.tB])⟩

/-! ## The walk edges of an arc -/

/-- The number of walk edges `s.edge, s.edge + 1, …, e.edge` (cyclically) of an arc. -/
def arcCnt (n : ℕ) (a : ARec) : ℕ := (a.e.edge + n - a.s.edge) % n + 1

/-- The event positions of a valid list are on walk edges, with parameters in `[0, 1)`. -/
theorem evPos_ok (B : BaseCtx Q L E reg li) {m : ℕ} (hm : m < E.length) :
    (wposOf L ztbgr).edge < Q.n ∧ 0 ≤ (interiorModel Q).param Q ztwwn ∧
      (interiorModel Q).param Q ztwwn < 1 := by
  have hmem : E.getD m 0 ∈ E := by
    simp_all
  have hc : ztpjh := by simpa using B.hperm.mem_iff.1 hmem
  obtain ⟨hp, h0, h1, -⟩ := BuildNF.attach_wposOf B.hL hc
  rw [show (interiorModel Q).W.n = Q.n from DownMath.walk_n Q] at hp
  simp_all

/-- The key of a position on a walk edge determines its edge. -/
theorem edge_of_key {M : Model} {Q : Polygon} {x : WPos} (h0 : 0 ≤ M.param Q x)
    (h1 : M.param Q x < 1) {w : ℕ} (hk : (w : ℝ) ≤ M.key Q x) (hk' : M.key Q x < w + 1) :
    x.edge = w := by
  unfold Model.key at hk hk'
  have a : (x.edge : ℝ) < w + 1 := by_linarith
  have b : (w : ℝ) < x.edge + 1 := by_linarith
  have a' : x.edge < w + 1 := by exact_mod_cast a
  have b' : w < x.edge + 1 := by exact_mod_cast b
  omega

/-- **The last arc of `buildNF` starts and ends on distinct walk edges** (otherwise every event,
in particular both ends of the first chord, would lie on one walk edge). -/
theorem last_arc_edges (B : BaseCtx Q L E reg li) :
    ((BuildNF.buildNF ztd Q L E).arc
        ztxbc).s.edge ≠
      ((BuildNF.buildNF ztd Q L E).arc
        ztxbc).e.edge := by
  zuhm
  zudz
  zucrs
  zucbl
  zugum
  set j := (gapStarts I Q L E).length - 1 with hj
  have hs := DrvD.arc_s (M := I) (Q := Q) (E := E) B.hK (j := j) by_omega
  have he := DrvD.arc_e (M := I) (Q := Q) (E := E) B.hK (j := j) by_omega
  rw [hlast, Nat.sub_add_cancel hE, Nat.mod_self] at he
  rw [hlast] at hs
  zuoiq
  intro hedge
  set w := (wposOf L _).edge with hw
  obtain ⟨-, p00, p01⟩ := evPos_ok B hE
  obtain ⟨-, pl0, pl1⟩ := evPos_ok B (show E.length - 1 < E.length by omega)
  -- every event is on walk edge `w`
  have hall : ∀ m, m < E.length → (wposOf L ztbgr).edge = w := by
    zucng
    obtain ⟨-, q0, q1⟩ := evPos_ok B hm
    have k1 := DrvD.kE_mono B.hsort (Nat.zero_le m) hm
    have k2 := DrvD.kE_mono B.hsort (show m ≤ E.length - 1 by omega) by_omega
    unfold DrvD.kE at k1 k2
    refine edge_of_key q0 q1 ?_ ?_
    · have : (w : ℝ) ≤ I.key Q ztojv := by
        zuhac
      linarith
    · have : I.key Q (wposOf L (E.getD ztswz 0)) < w + 1 := by
        zuhac
      linarith
  -- the two ends of chord `0`
  have h0 : (0 : ℕ) ∈ E := B.hperm.mem_iff.2 (List.mem_range.2 (by have := B.hK; omega))
  have h1 : (1 : ℕ) ∈ E := B.hperm.mem_iff.2 (List.mem_range.2 (by have := B.hK; omega))
  obtain ⟨m0, hm0, e0⟩ := List.mem_iff_getElem.1 h0
  obtain ⟨m1, hm1, e1⟩ := List.mem_iff_getElem.1 h1
  have g0 : E.getD m0 0 = 0 := by
    simp_all
  have g1 : E.getD m1 0 = 1 := by
    simp_all
  have w0 := hall m0 hm0
  have w1 := hall m1 hm1
  rw [g0] at w0
  rw [g1] at w1
  rw [BuildNF.wposOf_even by_norm_num] at w0
  rw [BuildNF.wposOf_odd by_norm_num] at w1
  have hlt := BuildNF.pos_lt' (walkAx_interiorModel B.hQ) B.hL B.hK
  have hpos : I.pos Q (BuildRegions.crec L (0 / 2)).lpos = I.pos Q (BuildRegions.crec L ztcn).rpos := by
    show I.pos Q ztufv = I.pos Q ztufv
    unfold CRec.lpos at w0
    unfold CRec.rpos at w1
    simp_all
  grind

/-- **A position on a closed arc lies on one of the walk edges of the arc.** -/
theorem closedArc_range (B : BaseCtx Q L E reg li) {j : ℕ}
    (hj : j < (BuildNF.buildNF ztd Q L E).arcs.length) {p : ℕ} {t : ℝ} (hp : p < Q.n)
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hc : Restore.ClosedArc ztxes
      ztxer ztk) :
    ∃ u, u < arcCnt Q.n ztyde ∧
      (((BuildNF.buildNF ztd Q L E).arc j).s.edge + u) % Q.n = p := by
  zuhm
  set N := BuildNF.buildNF I Q L E with hN
  zudz
  zucrs
  rw [hN, hA] at hj
  zucbl
  zufhc

  obtain ⟨sn, s0, s1⟩ := evPos_ok B ztpxf
  obtain ⟨en, e0, e1⟩ := evPos_ok B (Nat.mod_lt (DrvD.gs I Q L E j + 1) hE)
  rw [← hs] at sn s0 s1
  zvndl at en e0 e1
  set s := (N.arc j).s with hsd
  set e := (N.arc j).e with hed
  have ks : I.key Q s = s.edge + I.param Q s := rfl
  have ke : I.key Q e = e.edge + I.param Q e := rfl
  zuhqp
  rw [← hsd, ← hed]
  have hpt1 : (p : ℝ) + t < p + 1 := by_linarith
  by_cases hlt : j + 1 < (gapStarts I Q L E).length
  · -- an arc that does not wrap
    zuiyd
    rw [← hN, ← hsd, ← hed] at hk
    have hin : I.key Q s ≤ p + t ∧ p + t ≤ I.key Q e := by
      zuik
      · zucrg
      · grind
      grind
    have h1 : s.edge ≤ p := by
      zuepk

    have h2 : p ≤ e.edge := by
      zuepj

    refine ⟨p - s.edge, ?_, ?_⟩
    · rw [show e.edge + Q.n - s.edge = ztnxt + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega]
      omega
    · zuemq
  · -- the last arc wraps
    have hjl : j = (gapStarts I Q L E).length - 1 := by_omega
    have hks := DrvD.key_s_last (M := I) (Q := Q) B.hK hE
    have hke := DrvD.key_e_last (M := I) (Q := Q) B.hK hE
    rw [← hN, ← hjl, ← hsd] at hks
    rw [← hN, ← hjl, ← hed] at hke
    have hge : I.key Q e ≤ I.key Q s := by
      zufnn
    zulku
    rw [← hN, hA, ← hjl, ← hsd, ← hed] at hne
    have hse : e.edge < s.edge := by
      zuepi

    have hor : I.key Q s ≤ p + t ∨ p + t ≤ I.key Q e := by
      zuik
      · zuhaz
        grind
      · grind
      grind
    have hcnt : (e.edge + Q.n - s.edge) % Q.n = e.edge + Q.n - s.edge :=
      Nat.mod_eq_of_lt by_omega
    zumna
    rcases hor with h | h
    · have h1 : s.edge ≤ p := by
        zuepk

      refine ⟨p - s.edge, by_omega, ?_⟩
      zuemq
    · have h2 : p ≤ e.edge := by
        zuepj

      refine ⟨p + Q.n - s.edge, by_omega, ?_⟩
      rw [show s.edge + (p + Q.n - s.edge) = p + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hp]
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (sideInArc)
open BuildNF (codeLe wposOf gapStarts)
open DrvR (regHost walkItems)

/-! ## Inner vertices and weights -/

/-- **An interval has at most its weight of inner walk vertices** (interior model: every edge is
counted). -/
theorem vertsIn_le_arcWt (Q : Polygon) (a b : ℝ) :
    (WalkAx.vertsIn ztd a b).ncard ≤ (interiorModel Q).arcWt a b := by
  have hfin : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}.Finite :=
    (Set.finite_lt_nat _).subset fun p hp => hp.1
  refine Set.ncard_le_ncard ?_ hfin
  rintro p ⟨hp, hin⟩
  refine ⟨hp, trivial, ?_⟩
  obtain ⟨t, h1, h2⟩ := ((cyc_open hin).and
    ztxve).exists
  grind

/-- **An arc weighs at most the weight of its region.** -/
theorem arcWt_le_weight {Q : Polygon} (hQ : Q.Simple) {S : Set ztf}
    (hFam : (interiorModel Q).ChordFamily Q S) {R : Set Point}
    (hR : R ∈ (interiorModel Q).regions S) {a b : ℝ} (harc : (interiorModel Q).IsArc S R a b) :
    (interiorModel Q).arcWt a b ≤ (interiorModel Q).weight S R := by
  have hfin := (arcsPerRegion _ Q S ztbmd hFam R hR).1
  unfold Model.weight
  apply le_csSup ((hfin.image _).bddAbove)
  exact ztziu

/-! ## The arcs of a region of `buildNF` -/
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}
theorem region_arcs_nodup (r : ℕ) :
    ((BuildNF.buildNF ztd Q L E).region r).arcs.Nodup := by
  unfold NF.region
  by_cases hr : r < L.length + 1
  · zuhjz
    simp only [BuildNF.buildNF, List.getElem?_map, List.getElem?_range hr, Option.map_some,
      Option.getD_some]
    exact List.nodup_range.filter _
  · zuhjz
    simp only [BuildNF.buildNF, List.getElem?_map]
    simp_all

/-- **A region has at most `deg + 1` arcs.** -/
theorem arcs_length_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) :
    ((BuildNF.buildNF ztd Q L E).region r).arcs.length ≤
      (interiorModel Q).deg ztwjn
        ztcz + 1 := by
  zugyi
  set S := N.F _ Q with hS
  zudnv
  obtain ⟨hfin, hcard⟩ := arcsPerRegion _ Q S ztgek B.fam _ hR
  set f : ℕ → ℝ × ℝ := fun j => ((interiorModel Q).key Q (N.arc j).s,
    (interiorModel Q).key Q (N.arc j).e) with hf
  have hmem : ∀ j ∈ (N.region r).arcs, f j ∈ {ab : ℝ × ℝ | (interiorModel Q).IsArc S ztcz ab.1 ab.2} := by
    zun
    zubky
    have := (B.hregs.2.2.1.1 j hjA).2
    simp_all
  have hinj : Set.InjOn f {j | j ∈ (N.region r).arcs} := by
    zukjm
    zubky
    obtain ⟨hjA', hjr'⟩ := (B.hregs.2.2.1.2.2.2 r hr j').1 hj'
    exact B.hregs.2.2.1.2.1 j j' hjA hjA' (hjr.trans hjr'.symm) by_simp_all
  have h1 : ((N.region r).arcs.toFinset.image f).card = (N.region r).arcs.length := by
    rw [Finset.card_image_of_injOn by_simp_all, List.toFinset_card_of_nodup (region_arcs_nodup r)]
  have h2 : (((N.region r).arcs.toFinset.image f : Finset _) : Set _) ⊆
      {ab : ℝ × ℝ | (interiorModel Q).IsArc S ztcz ab.1 ab.2} := by
    simp_all
  have h3 := Set.ncard_le_ncard h2 hfin
  zuigu
  omega

/-- A union of a finite family of sets of bounded size. -/
theorem ncard_biUnion_le_mul {α β : Type*} {T : Set α} (hT : T.Finite) (f : α → Set β) {m : ℕ}
    (hf : ∀ x ∈ T, (f x).ncard ≤ m) (hfin : ∀ x ∈ T, (f x).Finite) :
    (⋃ x ∈ T, f x).ncard ≤ m * T.ncard := by
  induction T, hT using Set.Finite.induction_on with
  | empty => simp
  | @insert c T hcT hT ih =>
    rw [Set.biUnion_insert, Set.ncard_insert_of_notMem hcT hT]
    zuieu
    have h1 := hf c by_simp_all
    have h2 := ih by_simp_all
      by_simp_all
    zuewu

/-- **A region has at most `(deg + 1) γ + 2 deg` host points.** -/
theorem regPts_length_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ztwjn γ) :
    (regPts li Q.n ztwjp r).length ≤
      ((interiorModel Q).deg ztwjn
          ztcz + 1) * γ +
        2 * (interiorModel Q).deg ztwjn
          ztcz := by
  zudnv
  zudqn
  have hlenP : (regPts li Q.n ztwjp r).length =
      DownHost.nk ztd
        ztwjn ztcz := by
    unfold regPts
    rw [wlist_length, DownMath.regHost_pts]
    grind
  rw [hlenP]
  zulip
  have hnk := DownDrv.nk_le hM B.fam.2.1 B.fam.1 ztcz
  obtain ⟨hfin, hcard⟩ := arcsPerRegion _ Q _ ztgek B.fam _ hR
  have hsub : DownDrv.vtxIdx ztd
      ztwjn ztcz ⊆
      ⋃ ab ∈ {ab : ℝ × ℝ | (interiorModel Q).IsArc
          ztwjn ztcz ab.1 ab.2},
        WalkAx.vertsIn ztd ab.1 ab.2 := by
    rintro k ⟨hk, a, b, harc, hin⟩
    exact Set.mem_iUnion₂.2 ⟨ztvk, harc, hk, hin⟩
  have hv := (Set.ncard_le_ncard hsub (Set.Finite.biUnion hfin fun _ _ =>
      (Set.finite_lt_nat _).subset fun p hp => hp.1)).trans
    (ncard_biUnion_le_mul hfin _
      (fun ab hab => (vertsIn_le_arcWt Q _ _).trans ((arcWt_le_weight B.hQ B.fam hR hab).trans
        ztobi))
      (fun _ _ => (Set.finite_lt_nat _).subset fun p hp => hp.1))
  have hmul := Nat.mul_le_mul_left γ hcard
  grind

/-- **An arc of a region has at most its weight plus two walk edges.** -/
theorem arcCnt_le (B : BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ztwjn γ) {j : ℕ}
    (hj : j ∈ ((BuildNF.buildNF ztd Q L E).region r).arcs) :
    arcCnt Q.n ztyde ≤ γ + 2 := by
  zudnv
  zubky
  have harc := (B.hregs.2.2.1.1 j hjA).2
  zugdy
  have hbound := (vertsIn_le_arcWt Q _ _).trans ((arcWt_le_weight B.hQ B.fam hR harc).trans
    ztobi)
  zudz
  zuur
  zukct
  obtain ⟨sn, s0, s1⟩ := evPos_ok B ztuxq
  obtain ⟨en, e0, e1⟩ := evPos_ok B ztwxs
  zuckd

  generalize hsg : ((BuildNF.buildNF _ Q L E).arc j).s = s at *
  generalize heg : ((BuildNF.buildNF _ Q L E).arc j).e = e at *
  zukib
  zukic
  zuiyl
  zuhqp
  rw [hsg, heg]
  by_cases hlt : j + 1 < (gapStarts ztd Q L E).length
  · zuiyd
    rw [hsg, heg] at hk
    have hse : s.edge ≤ e.edge := by
      have : (s.edge : ℝ) < e.edge + 1 := by_linarith
      have : s.edge < e.edge + 1 := by exact_mod_cast this
      omega
    rw [show e.edge + Q.n - s.edge = ztnxt + Q.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt by_omega]
    have hsub : ((Finset.Ioo s.edge e.edge : Finset ℕ) : Set ℕ) ⊆
        WalkAx.vertsIn ztd ztmzc
          ztmzb := by
      zuml
      simp only [Finset.coe_Ioo, Set.mem_Ioo] at hv
      zubsc
      unfold sideInArc; rw [ite_eq_left hk]
      zuhvy
      zuhwb
      grind
    have := Set.ncard_le_ncard hsub ztkph
    rw [Set.ncard_coe_finset, Nat.card_Ioo] at this
    omega
  · have hjl : j = (gapStarts ztd Q L E).length - 1 := by_omega
    have hks := DrvD.key_s_last (M := interiorModel Q) (Q := Q) B.hK hE
    have hke := DrvD.key_e_last (M := interiorModel Q) (Q := Q) B.hK hE
    rw [← hjl, hsg] at hks
    rw [← hjl, heg] at hke
    have hge : (interiorModel Q).key Q e ≤ (interiorModel Q).key Q s := by
      zufnn
    zulku
    rw [hA, ← hjl, hsg, heg] at hne
    have hse : e.edge < s.edge := by
      zuepi

    zuey
    have hsub : ((Finset.Ioo s.edge Q.n ∪ Finset.Ico 0 e.edge : Finset ℕ) : Set ℕ) ⊆
        WalkAx.vertsIn ztd ztmzc
          ztmzb := by
      zuml
      simp only [Finset.coe_union, Finset.coe_Ioo, Finset.coe_Ico, Set.mem_union, Set.mem_Ioo,
        Set.mem_Ico] at hv
      zubsc
      unfold sideInArc; rw [ite_eq_right (not_lt.2 hge)]
      zukmn
      · left
        zuhvy
        linarith
      · right
        zuhwb
        linarith
    have := Set.ncard_le_ncard hsub ztkph
    rw [Set.ncard_coe_finset] at this
    have hd : Disjoint (Finset.Ioo s.edge Q.n) (Finset.Ico 0 e.edge) := by
      zuzt
      grind
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ioo, Nat.card_Ico] at this
    omega

/-! ## The empty family -/

/-- The whole walk weighs `n`. -/
theorem arcWt_zero (Q : Polygon) : (interiorModel Q).arcWt 0 0 = Q.n := by
  zuiyl
  zuiqa
  have : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc 0 0 ztk} = {p | p < Q.n} := by
    zufj
    simp only [mem_ofPred_eq, hn]
    constructor
    · omega
    · zuq
      refine ⟨h, trivial, 1 / 2, by_norm_num, by_norm_num, ?_⟩
      zujv
  rw [this, show {p : ℕ | p < Q.n} = ((Finset.range Q.n : Finset ℕ) : Set ℕ) by ext; simp,
    Set.ncard_coe_finset, Finset.card_range]

/-- **With no chords, the walk is one arc**: `n` is at most the weight bound. -/
theorem n_le_of_empty {Q : Polygon} (hQ : Q.Simple) {E : List ℕ} (hE : E = []) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ((BuildNF.buildNF ztd Q [] E).F ztd Q) γ) : Q.n ≤ γ := by
  subst hE
  zuhm
  set N := BuildNF.buildNF I Q [] [] with hN
  have hL : ChordTriplesOK I Q [] := ⟨⟨by_simp, by_simp, by_simp⟩, by_simp, by_simp, by_simp⟩
  have hNF : ztuld := DownMath.isNF_build hQ hL by_simp by_simp
  obtain ⟨-, -, -, reg, hRC, -, hAO, -⟩ := id hNF
  have hA : N.arcs = [ztgp] := by
    rfl
  have h0 : ztrzg := by_simp_all
  obtain ⟨hreg, harc⟩ := hAO.1 0 h0
  have ha : N.arc 0 = ztgp := by_rfl
  rw [ha] at hreg harc
  have hk : I.key Q ztbqw = 0 := by
    simp
  rw [hk] at harc
  have hR := hRC.1 _ hreg
  have := (arcWt_le_weight hQ hNF.1 hR harc).trans ztobi
  rwa [arcWt_zero] at this
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt
open BuildNF (codeLe)
@[expose] public section
noncomputable def ptsB (li : Bool) (Q : Polygon) (L : List zte) (E : List ℕ) (r : ℕ) :
    List SymPt :=
  if L.length = 0 then wlist li ztwqf
  else regPts li Q.n ztwjp r

/-- **The new chords, tagged by their region.** -/
noncomputable def tagLB (li : Bool) (Q : Polygon) (L : List zte) (E : List ℕ) :
    List ztwjg :=
  (List.range ztkr).flatMap fun r => (regList li Q ztpcz).map fun x => ztcof

/-- **The new chords of the base case** (`newL` for `K > 0`, `newL0` for `K = 0`). -/
noncomputable def newLB (li : Bool) (Q : Polygon) (L : List zte) (E : List ℕ) :
    List zte :=
  (tagLB li Q L E).map Prod.snd
variable (li : Bool) (Q : Polygon) {L : List (ℕ × ℕ × ℕ)}
theorem newLB_eq_flatMap (L : List zte) (E : List ℕ) :
    newLB li Q L E = (List.range ztkr).flatMap fun r => regList li Q ztpcz := by
  unfold newLB tagLB
  zumlk
  simp

/-- **`newLB` is `newL`** for `K > 0`. -/
theorem newLB_pos (E : List ℕ)
    (hK : 0 < L.length) :
    newLB li Q L E = newL li Q ztwjp := by
  rw [newLB_eq_flatMap]
  unfold newL
  have hR : (BuildNF.buildNF ztd Q L E).nRegions = L.length + 1 := by
    zudvx
  zumms
  zucr
  funext r
  unfold ptsB
  grind

/-- **`newLB` is `newL0`** for `K = 0`. -/
theorem newLB_zero (E : List ℕ)
    (hK : L.length = 0) : newLB li Q L E = newL0 li Q := by
  rw [newLB_eq_flatMap, hK]
  unfold ptsB newL0
  simp_all

/-- **The precondition of the region loop**, with bounds `S₀` (points of a region) and `Cm`
(walk edges of an arc of a region, or `n` when `K = 0`). -/
structure RegPre (P : Polygon) (W : ℕ) (c : Config) (L : List zte) (E : List ℕ)
    (S₀ Cm : ℕ) : Prop where
  hG : GoodEnv P
  hWh : hostWords P.n ≤ W
  hK : c.nreg 210003 = L.length
  hok : ChordTriplesOK ztwiq zta L
  hperm : E.Perm ztct
  hsort : E.Pairwise ztbajl
  hdeg : (interiorModel zta).DegLe
    ztbajd 4
  hNF : NFWithin c.nmem ztvhx ztmfx
    ztbaja
  hMD : ModelDescAt c.nmem ztvhw zta ztwiq
  hMDW : c.nreg 210001 + 6 ≤ c.nreg 212019
  hroom : c.nreg 212019 + 10 * P.n ≤ c.nreg ALLOC
  hS₀ : ∀ r, r < L.length + 1 →
    (ptsB ztbkr zta L E r).length ≤ S₀
  hCm0 : L.length = 0 → P.n ≤ Cm
  hCm : ∀ r, r < L.length + 1 → ∀ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
    arcCnt P.n ztbamq ≤ Cm

/-- **The postcondition of the region loop**: the new chords `newLB` at `B₂ = r212019` (their
number in `216020`), the buckets `bk q = mem[B₂ + 6 n + q]` of their ends bounded by the number
of arcs, ordered by the event comparator, with at most `4 MX` codes per bucket
(`MX = r212018 ≤ S₀`). -/
structure RegPost (P : Polygon) (c c' : Config) (L : List zte) (E : List ℕ) (S₀ : ℕ) :
    Prop where
  keep : ∀ q, 210000 ≤ q → q < 210030 → c'.nreg q = c.nreg q
  keepB : c'.nreg 212019 = c.nreg 212019
  cnt : c'.nreg 216020 = (newLB ztbkr zta L E).length
  len : (newLB ztbkr zta L E).length ≤ 2 * P.n
  list : ChordListAt c'.nmem ztmfx (newLB ztbkr zta L E)
  bkle : ∀ q, q < 2 * (newLB ztbkr zta L E).length →
    c'.nmem ztghc ≤
      (BuildNF.buildNF ztwiq zta L E).arcs.length
  bkmono : ∀ q q', q < 2 * (newLB ztbkr zta L E).length →
    q' < 2 * (newLB ztbkr zta L E).length →
    c'.nmem ztghc < c'.nmem (c.nreg 212019 + 6 * P.n + q') →
    codeLe ztwiq zta (L ++ newLB ztbkr zta L E)
      ztbhj ztekx
  bcnt : ∀ b, DrvR.bcnt (fun q => c'.nmem ztghc)
    (2 * (newLB ztbkr zta L E).length) b ≤ 4 * c'.nreg 212018
  mx : c'.nreg 212018 ≤ S₀

/-- **The contract of the region loop of the base case.** -/
def RegLoopSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (c : Config) (L : List zte) (E : List ℕ)
    (S₀ Cm : ℕ), WordsBounded W c → RegPre P W c L E S₀ Cm →
    c.nreg ALLOC + κ * ztkr * ztdto * ztdsy ≤ W →
    ∃ c' k, Exec P W s c c' k ∧ k ≤ κ * ztkr * ztdto * ztdsy ∧
      RegPost P c c' L E S₀ ∧ Restore.RF DrvR.drvBands ztmfx c c' k
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt
open BuildNF (codeLe)
open Chazelle.Visibility (DirInterior chordEnd OpenEdgePt)
open DrvR (qE ivB)
@[expose] public section
structure BEnv where
  P : Polygon
  W : ℕ
  L : List zte
  E : List ℕ
  reg : ℕ → Set Point
  m₀ : ℕ → ℕ
  MD : ℕ
  H : ℕ
  B₂ : ℕ
  S₀ : ℕ
  Cm : ℕ
namespace BEnv
variable (E : BEnv)

/-- The geometry polygon. -/
noncomputable abbrev Q : Polygon := Qof E.P

/-- The interior model. -/
noncomputable abbrev I : Model := interiorModel E.Q

/-- The current normal form. -/
noncomputable abbrev N : NF := BuildNF.buildNF E.I E.Q E.L E.E

/-- The number of chords. -/
abbrev K : ℕ := E.L.length

/-- The `LeftInside` bit. -/
def li : Bool := liBit E.m₀ E.MD

/-- The bucket base. -/
def BK : ℕ := E.B₂ + 6 * E.P.n

/-- The pointer `RB + 5 r + 2` to the record of region `r`. -/
def RP (r : ℕ) : ℕ := E.m₀ ztbaq + 2 + 5 * r

/-- The arc list of region `r`. -/
def LP (r : ℕ) : ℕ := E.m₀ ztdtd + E.m₀ ztyhm

/-- The number of walk-edge ranges of region `r`. -/
noncomputable def nRg (r : ℕ) : ℕ := if E.K = 0 then 1 else (E.N.region r).arcs.length

/-- Arc `t` of region `r`. -/
noncomputable def arcR (r t : ℕ) : ARec := E.N.arc ((E.N.region r).arcs.getD t 0)

/-- The first walk edge of range `t` of region `r`. -/
noncomputable def stF (r t : ℕ) : ℕ := if E.K = 0 then 0 else (E.arcR r t).s.edge

/-- The number of walk edges of range `t` of region `r`. -/
noncomputable def cntF (r t : ℕ) : ℕ := if E.K = 0 then E.P.n else arcCnt E.P.n (E.arcR r t)

/-- The walk-order points of region `r`. -/
noncomputable def pts (r : ℕ) : List SymPt := ptsB E.li E.Q E.L E.E r

/-- The records of region `r`. -/
noncomputable def recs (r : ℕ) : List zte := regList E.li E.Q ztdbu

/-- The tagged records of the regions `< r`. -/
noncomputable def TL (r : ℕ) : List ztwjg :=
  (List.range r).flatMap fun r' => (E.recs r').map fun x => zttya
theorem TL_succ (r : ℕ) : E.TL ztgu = E.TL r ++ (E.recs r).map fun x => ztcof := by
  unfold TL; zunxz
theorem TL_all : E.TL zthal = tagLB E.li E.Q E.L E.E := rfl
end BEnv

/-- **The facts about the data of the region loop.** -/
structure BGood (E : BEnv) : Prop where
  hG : GoodEnv E.P
  hWh : hostWords E.P.n ≤ E.W
  hok : ChordTriplesOK E.I E.Q E.L
  hperm : E.E.Perm ztoxe
  hsort : E.E.Pairwise (codeLe E.I E.Q E.L)
  hdeg : E.I.DegLe (E.N.F E.I E.Q) 4
  hregs : Restore.NFRegs E.I E.Q E.N E.reg
  hNF : NFWithin E.m₀ E.H E.B₂ E.N
  hMD : ModelDescAt E.m₀ E.MD E.Q E.I
  hMDW : E.MD + 6 ≤ E.B₂
  hBW : E.B₂ + 10 * E.P.n ≤ E.W
  hS₀ : ∀ r, r < E.K + 1 → (E.pts r).length ≤ E.S₀
  hCm : ∀ r, r < E.K + 1 → ∀ t, t < E.nRg r → E.cntF r t ≤ E.Cm
namespace BGood
variable {E : BEnv}
variable {r : ℕ}
theorem pts_pos (hK : 0 < E.K) : E.pts r = regPts E.li E.Q.n E.N r := by
  have : E.L.length ≠ 0 := Nat.pos_iff_ne_zero.1 hK
  zufpl
theorem pts_zero (hK : E.K = 0) :
    E.pts r = wlist E.li (Host.pts E.Q.n [HostItem.run 0 (E.Q.n - 1)]) := by
  have : E.L.length = 0 := hK
  zufpl
variable (hE : BGood E)
include hE
theorem hQ : E.Q.Simple := (shearInvariance ztmjb E.P).1 hE.hG.1
theorem hDH : DistinctHeights E.Q := (goodShear_epsOf hE.hG.2).2.1
omit hE in
theorem hQn (_hE : BGood E) : E.Q.n = E.P.n := shear_n _ _
theorem hn3 : 3 ≤ E.P.n := hE.hG.1.1
theorem hli : E.li = true ↔ Mountain.LeftInside E.Q := by
  unfold BEnv.li liBit
  rcases hE.hMD with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exfalso
    have := DrvD.desc_one hE.hMD
    omega
  simp_all
omit hE in
theorem nRegions (_hE : BGood E) : E.N.nRegions = E.K + 1 := by
  zudvx

/-- The context of the base case (`K > 0`). -/
theorem ctx (hK : 0 < E.K) : BaseCtx E.Q E.L E.E E.reg E.li :=
  ⟨hE.hQ, hE.hDH, hE.hok, hE.hperm, hE.hsort, hK, hE.hregs, hE.hli⟩

/-- **The points of a region are symbolic points of `Q`.** -/
theorem pts_lt (hr : r < E.K + 1) : ∀ s ∈ E.pts r, s.Lt E.Q.n := by
  zuhk
  · zuorg; exact run_pts_lt hE.hQ
  · zulqq
    exact (region_facts ztyuy hE.hli).2

/-- **The shooting polygon of a region.** -/
theorem regOK (hr : r < E.K + 1) :
    ∃ (S : Set ztf) (R : Set Point), E.I.ChordFamily E.Q S ∧
      RegOK E.Q S R (polyOf E.Q ztdbu) := by
  zuhk
  · refine ⟨∅, E.I.D, ⟨Set.finite_empty, Set.empty_subset _, fun c hc => absurd hc
      (Set.notMem_empty c)⟩, ?_⟩
    zuorg; exact regOK0 hE.hQ hE.hli
  · refine ⟨_, E.reg r, (hE.ctx hK).fam, ?_⟩
    zulqq
    exact (region_facts ztyuy hE.hli).1
end BGood

/-! ## The registers and the output during the region loop -/

/-- The registers fixed during the region loop. -/
def FixB (q : ℕ) : Prop :=
  ztnfl ∨ (212000 ≤ q ∧ q < 212013) ∨ q = 212019 ∨ (216000 ≤ q ∧ q < 216020)

/-- **The registers fixed during the region loop.** -/
structure BRegs (E : BEnv) (c : Config) : Prop where
  c0 : c.nreg 212000 = 1
  c1 : c.nreg 212001 = 0
  c2 : c.nreg 212002 = 2
  n : c.nreg 212010 = E.P.n
  li : c.nreg 212011 = if E.li then 1 else 0
  K : c.nreg 212012 = E.K
  d02 : c.nreg 216002 = 1
  d03 : c.nreg 216003 = 0
  d05 : c.nreg 216005 = 2
  d14 : c.nreg 216014 = E.m₀ ztdtc
  d16 : c.nreg 216016 = E.m₀ ztdtd
  d17 : c.nreg 216017 = E.N.arcs.length
  md : c.nreg 210001 = E.MD
  h5 : c.nreg 210005 = E.H
theorem BRegs.congr {E : BEnv} {c c' : Config} (h : BRegs E c)
    (hc : ∀ q, FixB q → c'.nreg q = c.nreg q) : BRegs E c' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  refine ztzv <;>
    (rw [hc _ (by unfold FixB; omega)]; assumption)

/-- **The output so far**: the records of `T` at `B₂`, their buckets at `BK`, the memory below
`B₂` the initial one. -/
structure OutSt (E : BEnv) (c : Config) (T : List ztwjg) : Prop where
  cnt : c.nreg 216020 = T.length
  dst : c.nreg 216021 = E.B₂ + 3 * T.length
  dstB : c.nreg 216022 = E.BK + 2 * T.length
  list : ChordListAt c.nmem E.B₂ ztqcx
  bk : 0 < E.K → DrvD.BktOK E.I E.Q E.N T ztzfh
  bk0 : E.K = 0 → ∀ q, q < 2 * T.length → c.nmem zthak = 0
  low : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt
open BuildNF (codeLe)
open BuildRam (FrameM)
@[expose] public section
def PtAtB (m : ℕ → ℕ) (a : ℕ) : SymPt → Prop
  | .vtx i => m a = 0 ∧ m ztdf = i
  | .onEdge e h => m a = 1 ∧ m ztdf = e ∧ m ztvj = h

/-- **The point array** at `PA`: point `k` of `l` at `PA + 3 k`. -/
def PtArrB (m : ℕ → ℕ) (PA : ℕ) (l : List SymPt) : Prop :=
  ∀ k, k < l.length → PtAtB m ztqbl ztxad

/-- **The expansion of a host block** (RAM): the host `H` at `HB = r212022` (`HostAt`, well
formed, `r212021 = H.length` items, `r212016 = (H.pts n).length` points) is expanded into the
point array of `wlist li (H.pts n)` at `PA = r212015` (`li` the bit in `r212011`; `r212010 = n`,
constants `r212000 = 1`, `r212001 = 0`, `r212002 = 2`).  The host block lies below `PA`, the
array fits below `W`.  Only the memory `[PA, PA + 3 NP)` and the registers
`212023 … 212031` are written; cost `κ (NP + |H| + 1)`. -/
def ExpSpec : Prop :=
  ∃ (s : Stmt) (κ : ℕ), ∀ (P : Polygon) (W : ℕ) (c : Config) (H : Host) (li : Bool),
    WordsBounded W c → HostAt c.nmem ztmfy H → HostWF P.n H →
    c.nreg 212021 = H.length → c.nreg 212016 = (H.pts P.n).length →
    c.nreg 212011 = ztfhy → c.nreg 212010 = P.n →
    c.nreg 212000 = 1 → c.nreg 212001 = 0 → c.nreg 212002 = 2 →
    c.nreg 212022 + 3 * H.length + 1 ≤ c.nreg 212015 →
    c.nreg 212015 + 3 * (H.pts P.n).length ≤ W →
    ∃ c' k, Exec P W s c c' k ∧ k ≤ κ * ztlcj ∧
      PtArrB c'.nmem zthun ztzyj ∧
      (∀ a, ztgfa →
        c'.nmem a = c.nmem a) ∧
      FrameM ztzfp c c'

/-- **The splice preconditions of the region-loop output** (mathematics): for the data of the
region loop (`BEnv`, `BGood`), buckets `bk` of the tagged records `TL (K + 1)` (`DrvD.BktOK` for
`K > 0`, `0` for `K = 0`) and a bound `MX` on the points of every region: the new chords
`newLB` number at most `2 n`, the buckets are at most the number of arcs, ordered by the event
comparator, and hold at most `4 MX` codes each. -/
def BktMathSpec : Prop :=
  ∀ (E : BEnv), BGood E → ∀ (bk : ℕ → ℕ) (MX : ℕ),
    (0 < E.K → DrvD.BktOK E.I E.Q E.N (E.TL zthal) bk) →
    (E.K = 0 → ∀ q, q < 2 * (E.TL zthal).length → bk q = 0) →
    (∀ r, r < E.K + 1 → (E.pts r).length ≤ MX) →
    (newLB E.li E.Q E.L E.E).length ≤ 2 * E.P.n ∧
    (∀ q, q < 2 * (newLB E.li E.Q E.L E.E).length → bk q ≤ E.N.arcs.length) ∧
    (∀ q q', q < 2 * (newLB E.li E.Q E.L E.E).length →
      q' < 2 * (newLB E.li E.Q E.L E.E).length → bk q < bk q' →
      codeLe E.I E.Q ztgdm ztptp (2 * E.L.length + q')) ∧
    (∀ b, DrvR.bcnt bk (2 * (newLB E.li E.Q E.L E.E).length) b ≤ 4 * MX)
open BuildNF (wposOf)
theorem countP_half (P : ℕ → Bool) (m : ℕ) :
    (List.range ztdk).countP (fun q => P ztbeu) = 2 * (List.range m).countP P := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * ztbl = 2 * m + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.countP_append, List.countP_append, ih, List.range_succ, List.countP_append]
    have h1 : 2 * m / 2 = m := by_omega
    have h2 : ztcsk / 2 = m := by_omega
    cases hP : P m <;> simp [h1, h2, hP]; omega

/-- Counting the indices of a list by a predicate on its entries. -/
theorem countP_range_getD {α : Type*} (l : List α) (d : α) (p : α → Bool) :
    (List.range l.length).countP (fun i => p zttro) = l.countP p := by
  have e : (List.range l.length).map (fun i => l.getD i d) = l := by
    zulda
    simp_all
  conv_rhs => rw [← e]
  rw [List.countP_map]
  rfl

/-- The tagged records of region `r` among the regions `< s`. -/
theorem TL_countP (E : BEnv) (r s : ℕ) :
    (E.TL s).countP (fun x => decide ztuef) = if r < s then (E.recs r).length else 0 := by
  induction s with
  | zero => simp [BEnv.TL]
  | succ s ih =>
    rw [E.TL_succ, List.countP_append, ih, List.countP_map]
    by_cases hrs : r = s
    · simp_all
    · have : (List.countP ((fun x : ℕ × (ℕ × ℕ × ℕ) => decide ztuef) ∘ fun x => (s, x))
          (E.recs s)) = 0 := by
        grind
      grind

/-- The tags of `TL s` are below `s`. -/
theorem TL_mem_lt (E : BEnv) {s : ℕ} {x : ℕ × zte} (hx : x ∈ E.TL s) : x.1 < s := by
  unfold BEnv.TL at hx
  grind

/-- The bucket count as a count over the range. -/
theorem bcnt_eq (bk : ℕ → ℕ) (n b : ℕ) :
    DrvR.bcnt bk n b = (List.range n).countP ztfbz := by
  unfold DrvR.bcnt DrvR.bfilt
  grind

/-! ## The bucket mathematics -/

/-- **The splice preconditions of the region-loop output.** -/
theorem bktMath : BktMathSpec := by
  intro E hE bk MX hbk hbk0 hMX
  set TLk := E.TL zthal with hTLk
  have hnew : newLB E.li E.Q E.L E.E = TLk.map Prod.snd := rfl
  have hlen : (newLB E.li E.Q E.L E.E).length = TLk.length := by_simp_all
  zujjh
  zudfi
  · -- at most `2 n` new chords
    rw [← hlen, ← hE.hQn]
    apply length_le_of_chords
    · zuhk
      · zudki
      · zuilt
        have := (newL_ok ztqpf).2.1
        grind
    · zuh
      zukxy
      zucoe
      have hr' : r < E.K + 1 := List.mem_range.1 hr
      zubxi

  · -- the buckets are at most the number of arcs
    zuco
    zuhk
    · simp_all
    · exact ((hbk hK).key q hq).le
  · -- the buckets are ordered by the event comparator
    intro q q' hq hq' hbb
    zuhk
    · simp_all
    · zulhn
      have hok' : ChordTriplesOK E.I E.Q ztgdm := by
        rw [newLB_pos _ _ _ hK]; exact newL_ok ztqpf
      have hM : WalkAx E.I := walkAx_interiorModel hE.hQ
      have hkey : ∀ q, q < 2 * TLk.length →
          E.I.key E.Q (wposOf ztgdm ztptp) =
            E.I.key E.Q (DrvD.endPos (TLk.getD ztbeu DrvD.dflt).2 ztkcq) := by
        zuco
        rw [DrvD.wposOf_new by_omega, hnew, DrvD.getD_map_snd]
      have hlen' : (E.L ++ newLB E.li E.Q E.L E.E).length = E.L.length + TLk.length := by
        simp_all
      refine DrvD.codeLe_of_bkt hM hok' hK hE.hperm hE.hsort by_omega by_omega
        by_omega by_omega ?_ ?_ hbb
      · zuoir; exact hB.key q hq
      · zuois; exact hB.key q' hq'
  · -- at most `4 MX` codes per bucket
    intro b
    zuhk
    · -- one region: all codes
      have h1 : DrvR.bcnt bk ztjfd b ≤ 2 * TLk.length := by
        zumlz
        exact List.countP_le_length.trans by_simp
      have h2 : TLk.length ≤ 2 * MX := by
        have e : TLk = (E.recs 0).map fun x => (0, x) := by
          rw [hTLk, hK, E.TL_succ]; rfl
        rw [e, List.length_map]
        exact (regList_length_le _ _).trans by_simp_all
      omega
    · zulhn
      zumlz
      by_cases hex : ∃ q, q < 2 * TLk.length ∧ bk q = b
      · obtain ⟨q₀, hq₀, hb₀⟩ := hex
        set r₀ := (TLk.getD (q₀ / 2) DrvD.dflt).1 with hr₀
        have hmem : ∀ i, i < TLk.length → (TLk.getD i DrvD.dflt).1 < E.K + 1 := fun i hi =>
          TL_mem_lt E (s := E.K + 1) (DrvD.getD_mem' hi)
        have hreg : ∀ q, q < 2 * TLk.length → (TLk.getD ztbeu DrvD.dflt).1 < E.N.nRegions := by
          zuco
          zuoda
          grind
        -- the region of a code of bucket `b`
        have hone : ∀ q, q < 2 * TLk.length → bk q = b → (TLk.getD ztbeu DrvD.dflt).1 = r₀ := by
          intro q hq hbq
          have ha := hB.arc q hq
          have ha₀ := hB.arc q₀ hq₀
          rw [hbq] at ha
          rw [hb₀] at ha₀
          have e1 := ((hE.hregs.2.2.1.2.2.2 _ (hreg q hq) _).1 ha).2
          have e2 := ((hE.hregs.2.2.1.2.2.2 _ (hreg q₀ hq₀) _).1 ha₀).2
          omega
        have hr₀K : r₀ < E.K + 1 := hmem _ by_omega
        calc (List.range ztjfd).countP ztfbz
            ≤ (List.range ztjfd).countP
                (fun q => decide ((TLk.getD ztbeu DrvD.dflt).1 = r₀)) := by
              refine List.countP_mono_left fun q hq hbq => ?_
              grind
          _ = 2 * TLk.countP ztloz := by
              rw [countP_half (fun i => decide ((TLk.getD i DrvD.dflt).1 = r₀)),
                countP_range_getD TLk DrvD.dflt ztloz]
          _ = 2 * (E.recs r₀).length := by rw [hTLk, TL_countP, ite_eq_left hr₀K]
          _ ≤ 4 * MX := by
              have := regList_length_le (Q := E.Q) E.li (E.pts r₀)
              have := hMX r₀ hr₀K
              unfold BEnv.recs
              omega
      · zumim
        have : (List.range ztjfd).countP ztfbz = 0 := by
          simp_all
        omega
open Programs
open BuildRam (FrameM.mono FrameM.trans exec_frameM wrM)
def Bexp : ℕ → Bool := fun r => decide ztgyl

/-- The slot of point `k` (of `NP`) in the walk-order array. -/
def slotE (li : Bool) (NP k : ℕ) : ℕ := if li then k else NP - 1 - k

/-- The output pointer after `K` points. -/
def ptrE (li : Bool) (PA NP K : ℕ) : ℕ := if li then PA + 3 * K else PA + 3 * (NP - K)

/-- Write the vertex `r212030` at the output pointer (forwards or backwards). -/
def wrV : Stmt := .ifLtN 212001 212011
  (block [.storeN 212025 212001, .addN 212025 212025 212000, .storeN 212025 212030,
    .addN 212025 212025 212000, .addN 212025 212025 212000])
  (block [.subN 212025 212025 212000, .subN 212025 212025 212000, .storeN 212025 212030,
    .subN 212025 212025 212000, .storeN 212025 212001])

/-- Write the edge point `(r212027, r212028)` at the output pointer. -/
def wrE : Stmt := .ifLtN 212001 212011
  (block [.storeN 212025 212000, .addN 212025 212025 212000, .storeN 212025 212027,
    .addN 212025 212025 212000, .storeN 212025 212028, .addN 212025 212025 212000])
  (block [.subN 212025 212025 212000, .storeN 212025 212028, .subN 212025 212025 212000,
    .storeN 212025 212027, .subN 212025 212025 212000, .storeN 212025 212000])

/-- **The state of the expansion** after the first `K` points of `L`. -/
structure ESt (W n PA : ℕ) (li : Bool) (L : List SymPt) (c₀ c : Config) (K : ℕ) : Prop where
  wb : WordsBounded W c
  le : K ≤ L.length
  hW : PA + 3 * L.length ≤ W
  fr : FrameM Bexp c₀ c
  r0 : c.nreg 212000 = 1
  r1 : c.nreg 212001 = 0
  rli : c.nreg 212011 = if li then 1 else 0
  rn : c.nreg 212010 = n
  mem : ∀ a, (a < PA ∨ PA + 3 * L.length ≤ a) → c.nmem a = c₀.nmem a
  pts : ∀ k, k < K → PtAtB c.nmem (PA + 3 * slotE li L.length k) (L.getD k ztga)
  ptr : c.nreg 212025 = ptrE li PA L.length K
theorem PtAtB.congr {m m' : ℕ → ℕ} {a : ℕ} {x : SymPt} (h : PtAtB m a x)
    (hm : ∀ b, a ≤ b → b < a + 3 → m' b = m b) : PtAtB m' a x := by
  cases x with
  | vtx i =>
    exact ⟨(hm a le_rfl by_omega).trans h.1, (hm ztdf by_omega by_omega).trans h.2⟩
  | onEdge e h' =>
    exact ⟨(hm a le_rfl by_omega).trans h.1, (hm ztdf by_omega by_omega).trans h.2.1,
      (hm ztvj by_omega by_omega).trans h.2.2⟩
variable {li : Bool}
theorem slotE_lt {NP k : ℕ} (hk : k < NP) : slotE li NP k < NP := by
  zumuy
theorem slotE_ne {NP k k' : ℕ} (hk : k < NP) (hk' : k' < NP) (h : k ≠ k') :
    slotE li NP k ≠ slotE li NP k' := by
  zumuy

/-- **One more point**: the new slot written, nothing else changed. -/
theorem ESt.step {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c c' : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length) (hw : WordsBounded W c')
    (hf : FrameM ztcni c c')
    (hm : ∀ a, ztbze →
      c'.nmem a = c.nmem a)
    (hp : PtAtB c'.nmem ztgeo ztyov)
    (hptr : c'.nreg 212025 = ptrE li PA L.length ztbr) :
    ESt W n PA li L c₀ c' ztbr := by
  have hsl := slotE_lt (li := li) hK
  have hreg : ∀ r, r ≠ 212025 → c'.nreg r = c.nreg r := fun r hr =>
    hf.1 r by_simp_all
  refine ⟨hw, by_omega, hS.hW, hS.fr.trans (hf.mono fun r hr => ?_), ?_, ?_, ?_, ?_, ?_, ?_, hptr⟩
  · zvmwo at hr; subst hr; decide
  · zunfu; exact hS.r0
  · zunfu; exact hS.r1
  · zunfu; exact hS.rli
  · zunfu; exact hS.rn
  · zuge
    rw [hm a by_omega]; exact hS.mem a ha
  · zugf
    rcases Nat.lt_or_ge k K with hk' | hk'
    · have hne := slotE_ne (li := li) by_omega hK (Nat.ne_of_lt hk')
      refine (hS.pts k hk').congr fun b hb1 hb2 => hm b ?_
      omega
    grind

/-- **Register writes** (other than the output pointer) keep the state. -/
theorem ESt.frame {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c c' : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hw : WordsBounded W c') (hf : FrameM Bexp c c')
    (h25 : c'.nreg 212025 = c.nreg 212025) (hm : c'.nmem = c.nmem) :
    ESt W n PA li L c₀ c' K := by
  refine ⟨hw, hS.le, hS.hW, hS.fr.trans hf, ?_, ?_, ?_, ?_, ?_, ?_, h25.trans hS.ptr⟩
  · zunfv; exact hS.r0
  · zunfv; exact hS.r1
  · zunfv; exact hS.rli
  · zunfv; exact hS.rn
  · intro a ha; zvmwi; exact hS.mem a ha
  · intro k hk; zvmwi; exact hS.pts k hk
theorem wr_wrV : wrM ztcni wrV = true := by_decide
theorem wr_wrE : wrM ztcni wrE = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
variable {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c : Config} {K : ℕ}
/-- **Writing a vertex.** -/
theorem wrV_exec
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length)
    (hx : L.getD K ztga = .vtx (c.nreg 212030)) :
    ∃ c' k, Exec P W wrV c c' k ∧ k ≤ 7 ∧ ESt W n PA li L c₀ c' ztbr ∧
      FrameM ztcni c c' := by
  zuiau

  obtain ⟨c', k, ex, hk, hm, hp, hptr⟩ : ∃ c' k, Exec P W wrV c c' k ∧ k ≤ 7 ∧
      (∀ a, ztbze →
        c'.nmem a = c.nmem a) ∧
      PtAtB c'.nmem ztgeo ztyov ∧
      c'.nreg 212025 = ptrE li PA L.length ztbr := by
    zudnc

    zucjv
    cases li
    · zudx
      exec_block
      simp only [ptrE, slotE, Bool.false_eq_true, ite_false] at hp ⊢
      zunjq
      zumkk
      · zubd
      · zubd
    · zuek
      simp only [ptrE, slotE, ↓reduceIte] at hp ⊢
      exec_block
      all_goals config_simp
      all_goals zunjq
      · omega
      · omega
      · omega
      zumkk
      · zubd
      simp
  exact ⟨c', k, ex, hk, hS.step hK ex.wb_right (exec_frameM ex wr_wrV) hm hp hptr,
    exec_frameM ex wr_wrV⟩

/-- **Writing an edge point.** -/
theorem wrE_exec
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length)
    (hx : L.getD K ztga = .onEdge (c.nreg 212027) (c.nreg 212028)) :
    ∃ c' k, Exec P W wrE c c' k ∧ k ≤ 8 ∧ ESt W n PA li L c₀ c' ztbr ∧
      FrameM (fun r => decide (r = 212025)) c c' := by
  zuiau

  obtain ⟨c', k, ex, hk, hm, hp, hptr⟩ : ∃ c' k, Exec P W wrE c c' k ∧ k ≤ 8 ∧
      (∀ a, ztbze →
        c'.nmem a = c.nmem a) ∧
      PtAtB c'.nmem ztgeo ztyov ∧
      c'.nreg 212025 = ptrE li PA L.length (K + 1) := by
    zudnc

    zucjv
    cases li
    · zudx
      exec_block
      simp only [ptrE, slotE, Bool.false_eq_true, ite_false] at hp ⊢
      zunoc
      zumkk
      · zubd
      · refine ⟨?_, ?_, ?_⟩ <;> simp only [upd] <;> (try split_ifs) <;> omega
    · zuek
      simp only [ptrE, slotE, ↓reduceIte] at hp ⊢
      exec_block
      all_goals config_simp
      all_goals zunoc
      · omega
      · omega
      · omega
      zumkk
      · zubd
      · refine ⟨?_, ?_, ?_⟩ <;> simp only [upd] <;> (try split_ifs) <;> omega
  exact ⟨c', k, ex, hk, hS.step hK ex.wb_right (exec_frameM ex wr_wrE) hm hp hptr,
    exec_frameM ex wr_wrE⟩
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)
@[expose] public section
def runBody : Stmt := .seq wrV (.seq
  ztebv
  ztebr)

/-- **A run** `(a = r212027, ℓ = r212028)`. -/
def runS : Stmt := .seq
  ztdgp
  (.whileLtN 212029 212028 runBody)
theorem wr_runBody :
    wrM ztgjk runBody = true := by_decide
theorem wr_runTail : wrM Bexp (.seq
    ztebv
    ztebr) = true := by_decide
theorem wr_runS :
    wrM ztbht runS = true := by
  decide
theorem wr_runInit : wrM Bexp
    ztdgp = true := by
  decide
theorem succ_mod_ite (x n : ℕ) (hn : 0 < n) :
    zthf % n = if x % n + 1 < n then x % n + 1 else 0 := by
  have h := Nat.mod_lt x hn
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · zudjt
    split_ifs with h2
    · exact Nat.mod_eq_of_lt h2
    · have : x % n + 1 = n := by_omega
      simp_all
  grind
section loops
variable {P : Polygon} {W : ℕ}

/-- **A counted loop with a potential** `Φ`: the iteration at `j` costs at most
`Φ (j + 1) - Φ j`. -/
theorem forLoopPot {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (Φ : ℕ → ℕ) (N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv ztl c' ∧ k + Φ j ≤ Φ ztl)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W ztfmn c c' k ∧ Inv N c' ∧
      k + Φ j ≤ Φ N + 2 * zthbl + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    zubaq

    zucq
    exact ztkje
  | succ t ih =>
    zucq
    zuem

    exact ⟨c', k₁ + 2 + k₂, .whileLtN_true by_omega e₁ e₂, hI', by_omega⟩
end loops
section exec
variable {P : Polygon} {W : ℕ}
variable {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ e : Config}
/-- **One step of a run.** -/
theorem runBody_exec {K₀ t a : ℕ}
    (hS : ESt W n PA li L c₀ e ztjjj) (hK : K₀ + t < L.length) (hn : 0 < n)
    (h29 : e.nreg 212029 = t) (h30 : e.nreg 212030 = ztne % n)
    (hx : L.getD ztjjj ztga = .vtx ztxyz) :
    ∃ e' k, Exec P W runBody e e' k ∧ k ≤ 12 ∧ ESt W n PA li L c₀ e' (K₀ + t + 1) ∧
      e'.nreg 212029 = t + 1 ∧ e'.nreg 212030 = ztzuz % n ∧
      FrameM ztgjk e e' := by
  obtain ⟨e₁, k₁, x₁, hk₁, hS₁, f₁⟩ := wrV_exec (P := P) hS hK by_simp_all
  have r29 : e₁.nreg 212029 = t := (f₁.1 _ by_decide).trans h29
  have r30 : e₁.nreg 212030 = ztne % n := (f₁.1 _ by_decide).trans h30
  have hw₁ := hS₁.wb
  have h0 := hS₁.r0
  have h1 := hS₁.r1
  have hrn := hS₁.rn
  have hnW : ztskn := hrn ▸ hw₁.1 212010
  have hmod := Nat.mod_lt ztne hn
  have hLW := hS₁.hW
  have hsucc := succ_mod_ite ztne n hn
  obtain ⟨e₂, k₂, x₂, hk₂, h29', h30', h25', hm'⟩ : ∃ e₂ k₂, Exec P W (.seq
      ztebv
      ztebr) e₁ e₂ k₂ ∧ k₂ ≤ 5 ∧
      e₂.nreg 212029 = t + 1 ∧ e₂.nreg 212030 = ztzuz % n ∧
      e₂.nreg 212025 = e₁.nreg 212025 ∧ e₂.nmem = e₁.nmem := by
    refine spec_seq ?_
    exec_block
    · omega
    · config_simp; omega
    · rw [← Nat.add_assoc, hsucc]
      by_cases hlt : ztne % n + 1 < n
      · zuek
        zurc
        simp_all
      · zudx
        zujfk
        simp_all
  have hS₂ := hS₁.frame x₂.wb_right (exec_frameM x₂ wr_runTail) h25' hm'
  zujwi
  exact ⟨e₂, _, X, by_omega, hS₂, h29', h30', exec_frameM X wr_runBody⟩

/-- **A run**: the points `(a + t) mod n`, `t ≤ ℓ`, are written. -/
theorem runS_exec {K₀ a ℓ : ℕ}
    (hS : ESt W n PA li L c₀ e K₀) (h27 : e.nreg 212027 = a) (h28 : e.nreg 212028 = ℓ)
    (ha : a < n) (hℓ : ℓ < n) (hK : K₀ + ztmv ≤ L.length)
    (hx : ∀ t, t ≤ ℓ → L.getD ztjjj ztga = .vtx ztxyz) :
    ∃ e' k, Exec P W runS e e' k ∧ k ≤ 14 * ztmv + 5 ∧
      ESt W n PA li L c₀ e' (K₀ + ztmv) ∧
      FrameM ztbht e e' := by
  zuiat

  have h1 := hS.r1
  have hnW : ztskn := hS.rn ▸ hw.1 212010
  zuqi
  obtain ⟨e₁, k₁, x₁, hk₁, h28', h29', h30', h25', hm'⟩ : ∃ e₁ k₁, Exec P W
      ztdgp e e₁ k₁ ∧
      k₁ ≤ 3 ∧ e₁.nreg 212028 = ℓ + 1 ∧ e₁.nreg 212029 = 0 ∧ e₁.nreg 212030 = a ∧
      e₁.nreg 212025 = e.nreg 212025 ∧ e₁.nmem = e.nmem := by
    exec_block
    · omega
    simp_all
  have hS₁ := hS.frame x₁.wb_right (exec_frameM x₁ wr_runInit) h25' hm'
  let Inv : ℕ → Config → Prop := fun t d => ESt W n PA li L c₀ d ztjjj ∧
    d.nreg 212029 = t ∧ d.nreg 212028 = ℓ + 1 ∧ d.nreg 212030 = ztne % n
  have I0 : Inv 0 e₁ := ⟨by_omega, h29', h28', by rw [h30', Nat.add_zero,
    Nat.mod_eq_of_lt ha]⟩
  obtain ⟨e', k₂, x₂, ⟨hS', -⟩, hk₂⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212029)
    (nr := 212028) (body := runBody) Inv 12 ztmv
    (fun j d ⟨hS, h1, h2, _⟩ => ⟨hS.wb, h1, h2⟩)
    (fun j d hj ⟨hS, h1, h2, h3⟩ => by
      obtain ⟨d', k', x, hk', hS', h29, h30, f⟩ :=
        runBody_exec (P := P) hS by_omega hn h1 h3 (hx j by_omega)
      exact ⟨d', k', x, ⟨by_omega, h29,
        (f.1 _ by_decide).trans h2, h30⟩, hk'⟩)
    I0 ztbg
  zujwi
  exact ⟨e', _, X, by_omega, hS', exec_frameM X wr_runS⟩
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)
@[expose] public section
theorem host_mem_getD {H : Host} {q : ℕ} (hq : q < H.length) :
    H.getD q ztmn ∈ H := by
  simp_all
variable (n : ℕ)
theorem pts_take_succ {H : Host} {q : ℕ} (hq : q < H.length) :
    Host.pts n ztyhp = Host.pts n ztemw ++ (H.getD q ztmn).pts n := by
  zultt
  rw [List.take_add_one, List.getElem?_eq_getElem hq, List.getD_eq_getElem _ _ hq,
    List.flatMap_append]
  simp
theorem pts_take_length_le (H : Host) (q : ℕ) :
    (Host.pts n ztemw).length ≤ (H.pts n).length := by
  zultt
  conv_rhs => rw [← List.take_append_drop q H]
  grind
theorem pts_getD_mid {H : Host} {q j : ℕ} (hq : q < H.length)
    (hj : j < ((H.getD q ztmn).pts n).length) (d : SymPt) :
    (H.pts n).getD ((Host.pts n ztemw).length + j) d =
      ((H.getD q ztmn).pts n).getD j d := by
  have e : H.pts n = (Host.pts n ztemw ++ (H.getD q ztmn).pts n) ++
      Host.pts n (H.drop ztfo) := by
    rw [← pts_take_succ n hq]
    zultt
    rw [← List.flatMap_append, List.take_append_drop]
  grind
theorem run_pts_getD (n a ℓ t : ℕ) (ht : t ≤ ℓ) (d : SymPt) :
    ((HostItem.run a ℓ).pts n).getD t d = .vtx ztxyz := by
  simp [HostItem.pts, List.getD_eq_getElem?_getD, List.getElem?_range (show t < ℓ + 1 by omega)]

/-! ## One item -/

/-- Load the three words of the current item. -/
def loadB : List Instr :=
  [.loadN 212026 212023, .addN 212031 212023 212000, .loadN 212027 212031,
    .addN 212031 212031 212000, .loadN 212028 212031]

/-- Dispatch on the kind of the item. -/
def dispS : Stmt := .ifLtN 212026 212000 runS
  (.ifLtN 212026 212002 (.seq (.instr (.copyN 212030 212027)) wrV) wrE)

/-- Advance the item pointer and the item counter. -/
def incB : List Instr :=
  [.addN 212023 212023 212000, .addN 212023 212023 212000, .addN 212023 212023 212000,
    .addN 212024 212024 212000]

/-- **One host item.** -/
def itemS : Stmt := .seq ztqeh (.seq dispS ztqee)
theorem wr_loadB : wrM Bexp ztqeh = true := by_decide
theorem wr_incB : wrM Bexp ztqee = true := by_decide
theorem wr_dispS :
    wrM ztbht dispS = true := by
  decide

/-- **The invariant of the item loop** after `q` items. -/
def IInv (W n PA HB : ℕ) (li : Bool) (H : Host) (c₀ : Config) (q : ℕ) (e : Config) : Prop :=
  ESt W n PA li ztmbe c₀ e (Host.pts n ztemw).length ∧ e.nreg 212023 = HB + 1 + 3 * q ∧
    e.nreg 212024 = q
section exec
variable {P : Polygon} {W : ℕ}
variable {PA HB : ℕ} {li : Bool} {H : Host} {c₀ e : Config} {q : ℕ}
set_option maxHeartbeats 1000000 in
/-- **The dispatch** on the item `q`, after its words are loaded. -/
theorem dispS_exec
    (hH : HostAt c₀.nmem HB H) (hWF : HostWF P.n H) (h2 : c₀.nreg 212002 = 2)
    (hq : q < H.length)
    (hS : ESt W P.n PA li ztbkj c₀ e (Host.pts P.n ztemw).length)
    (h26 : e.nreg 212026 = c₀.nmem ztnlk)
    (h27 : e.nreg 212027 = c₀.nmem ztnll)
    (h28 : e.nreg 212028 = c₀.nmem ztnlm) :
    ∃ e' k, Exec P W dispS e e' k ∧ k ≤ 14 * ((H.getD q ztmn).pts P.n).length + 10 ∧
      ESt W P.n PA li ztbkj c₀ e' (Host.pts P.n ztyhp).length ∧
      FrameM ztbht e e' := by
  suffices h : ∃ e' k, Exec P W dispS e e' k ∧
      k ≤ 14 * ((H.getD q ztmn).pts P.n).length + 10 ∧
      ESt W P.n PA li ztbkj c₀ e' (Host.pts P.n ztyhp).length by
    obtain ⟨e', k, x, hk, hS'⟩ := h
    exact ⟨e', k, x, hk, hS', exec_frameM x wr_dispS⟩
  have hlen := pts_take_length_le P.n H ztfo
  rw [pts_take_succ P.n hq] at hlen ⊢
  rw [List.length_append] at hlen ⊢
  have hmid := fun j hj => pts_getD_mid P.n hq (j := j) hj ztga
  have h0 := hS.r0
  have r2 : e.nreg 212002 = 2 := (hS.fr.1 _ by_decide).trans h2
  have hmem := host_mem_getD hq
  have hh := hH.2 q hq
  revert hmid hmem hh hlen
  generalize H.getD q ztmn = it
  intro hlen hmid hmem hh
  cases it with
  | run a ℓ =>
    obtain ⟨k0, ka, kl⟩ := hh
    obtain ⟨ha, hl⟩ : a < P.n ∧ ℓ < P.n := hWF _ hmem
    have hlr : ((HostItem.run a ℓ).pts P.n).length = ℓ + 1 := by zunjr
    rw [hlr] at hlen ⊢
    obtain ⟨e', k, x, hk, hS', -⟩ := runS_exec (P := P) hS (h27.trans ka) (h28.trans kl) ha hl
      hlen (fun t ht => by
        rw [hmid t by_omega, run_pts_getD _ _ _ _ ht])
    exact ⟨e', k + 1, .ifLtN_true by_omega x, by_omega, hS'⟩
  | pt x =>
    cases x with
    | vtx j =>
      obtain ⟨k0, kj⟩ := hh
      have hl1 : ((HostItem.pt ztmae).pts P.n).length = 1 := rfl
      zujjf
      have hw := hS.wb
      obtain ⟨e₁, x₁⟩ : ∃ e₁, Exec P W (.instr (.copyN 212030 212027)) e e₁ 1 ∧
          ESt W P.n PA li ztbkj c₀ e₁ (Host.pts P.n ztemw).length ∧
          e₁.nreg 212030 = j :=
        ⟨_, Machine.Exec.copyN hw _ _, hS.frame (Machine.Exec.copyN (P := P) hw 212030 212027).wb_right
          ⟨fun r hr => by
            simp only [Bexp, decide_eq_false_iff_not] at hr
            dsimp only; rw [Machine.upd_other]; omega,
            fun _ _ => rfl, rfl, rfl⟩ by_simp rfl, by_simp_all⟩
      obtain ⟨x₁, hS₁, h30⟩ := x₁
      obtain ⟨e', k, x, hk, hS', -⟩ := wrV_exec (P := P) hS₁ by_omega
        (by have := hmid 0 by_omega; rw [Nat.add_zero] at this
            rw [h30, this]; rfl)
      refine ⟨e', 1 + k + 2 + 1, .ifLtN_false by_omega
        (.ifLtN_true by_omega (.seq x₁ x)), by_omega, hS'⟩
    | onEdge ee hh' =>
      obtain ⟨k0, ke, kh⟩ := hh
      have hl1 : ((HostItem.pt (.onEdge ee hh')).pts P.n).length = 1 := rfl
      zujjf
      obtain ⟨e', k, x, hk, hS', -⟩ := wrE_exec (P := P) hS by_omega
        (by have := hmid 0 by_omega; rw [Nat.add_zero] at this
            rw [h27, h28, ke, kh, this]; rfl)
      refine ⟨e', k + 2 + 2, .ifLtN_false by_omega
        (.ifLtN_false by_omega x), by_omega, hS'⟩

/-- **One host item**: its points are written, the item pointer and counter advance. -/
theorem itemS_exec
    (hH : HostAt c₀.nmem HB H) (hWF : HostWF P.n H) (h2 : c₀.nreg 212002 = 2)
    (hHB : HB + 3 * H.length + 1 ≤ PA) (hq : q < H.length)
    (hI : IInv W P.n PA HB li H c₀ q e) :
    ∃ e' k, Exec P W itemS e e' k ∧ IInv W P.n PA HB li H c₀ ztfo e' ∧
      k + 30 * ztygz ≤
        30 * ((Host.pts P.n ztyhp).length + ztfo) := by
  obtain ⟨hS, h23, h24⟩ := hI
  zuiat

  have hPA : PA ≤ W := by have := hS.hW; omega
  obtain ⟨e₁, k₁, x₁, hk₁, h26, h27, h28, h23', h24', h25', hm'⟩ : ∃ e₁ k₁,
      Exec P W ztqeh e e₁ k₁ ∧ k₁ ≤ 5 ∧
      e₁.nreg 212026 = c₀.nmem ztnlk ∧ e₁.nreg 212027 = c₀.nmem ztnll ∧
      e₁.nreg 212028 = c₀.nmem ztnlm ∧ e₁.nreg 212023 = HB + 1 + 3 * q ∧
      e₁.nreg 212024 = q ∧ e₁.nreg 212025 = e.nreg 212025 ∧ e₁.nmem = e.nmem := by
    unfold loadB
    exec_block
    · config_simp; omega
    · config_simp; omega
    · refine ztdiy <;> config_simp
      · zuodb; exact hS.mem _ ztec
      · rw [h23, h0, show HB + 1 + 3 * q + 1 = HB + 2 + 3 * q by omega]
        zulyr
      · rw [h23, h0, show HB + 1 + 3 * q + 1 + 1 = HB + 3 + 3 * q by omega]
        zulyr
      · omega
      omega
  have hS₁ := hS.frame x₁.wb_right (exec_frameM x₁ wr_loadB) h25' hm'
  obtain ⟨e₂, k₂, x₂, hk₂, hS₂, f₂⟩ := dispS_exec (P := P) hH hWF h2 hq hS₁ h26 h27 h28
  have r23 : e₂.nreg 212023 = HB + 1 + 3 * q := (f₂.1 _ by_decide).trans h23'
  have r24 : e₂.nreg 212024 = q := (f₂.1 _ by_decide).trans h24'
  have hw₂ := hS₂.wb
  have h0' := hS₂.r0
  obtain ⟨e₃, k₃, x₃, hk₃, h23'', h24'', h25'', hm''⟩ : ∃ e₃ k₃,
      Exec P W ztqee e₂ e₃ k₃ ∧ k₃ ≤ 4 ∧
      e₃.nreg 212023 = HB + 1 + 3 * ztfo ∧ e₃.nreg 212024 = q + 1 ∧
      e₃.nreg 212025 = e₂.nreg 212025 ∧ e₃.nmem = e₂.nmem := by
    unfold incB
    exec_block
    · omega
    · config_simp; omega
    · config_simp; omega
    · config_simp; omega
    · refine ztcot <;> config_simp
      · omega
      omega
  have hS₃ := hS₂.frame x₃.wb_right (exec_frameM x₃ wr_incB) h25'' hm''
  refine ⟨e₃, k₁ + zttl, .seq x₁ ztjdw, ⟨hS₃, h23'', h24''⟩, ?_⟩
  rw [pts_take_succ P.n hq, List.length_append]
  nlinarith
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)
@[expose] public section
def initS : Stmt := .seq (block [.addN 212023 212022 212000, .copyN 212024 212001])
  (.ifLtN 212001 212011 (.instr (.copyN 212025 212015))
    (block [.addN 212025 212015 212016, .addN 212025 212025 212016,
      .addN 212025 212025 212016]))

/-- **The expansion of a host block** into the point array. -/
def expS : Stmt := .seq initS (.whileLtN 212024 212021 itemS)
theorem wr_initS : wrM Bexp initS = true := by_decide

/-- The final state is the point array in walk order. -/
theorem ESt.arr {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c : Config}
    (hS : ESt W n PA li L c₀ c L.length) : PtArrB c.nmem PA (wlist li L) := by
  zugf
  cases li
  · simp only [wlist, Bool.false_eq_true, ↓reduceIte, List.length_reverse] at hk ⊢
    have h := hS.pts (L.length - 1 - k) by_omega
    simp only [slotE, Bool.false_eq_true, ↓reduceIte] at h
    grind
  · simp only [wlist, ↓reduceIte] at hk ⊢
    simpa [slotE] using hS.pts k hk
section exec
variable {P : Polygon} {W : ℕ}
theorem initS_exec (c : Config) (hw : WordsBounded W c) (li : Bool) (NP : ℕ)
    (h0 : c.nreg 212000 = 1) (h1 : c.nreg 212001 = 0)
    (h11 : c.nreg 212011 = if li then 1 else 0) (h16 : c.nreg 212016 = NP)
    (hHB : c.nreg 212022 + 1 ≤ c.nreg 212015) (hPW : c.nreg 212015 + 3 * NP ≤ W) :
    ∃ c₁ k₁, Exec P W initS c c₁ k₁ ∧ k₁ ≤ 7 ∧ c₁.nreg 212023 = c.nreg 212022 + 1 ∧
      c₁.nreg 212024 = 0 ∧ c₁.nreg 212025 = ptrE li zthun NP 0 ∧
      c₁.nmem = c.nmem := by
  zujqm
  refine spec_seq ?_
  exec_block
  · omega
  · cases li
    · zudx
      exec_block
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · refine ztcot <;> config_simp
        · zudty
        · zuwv
        · rw [h16]; simp only [ptrE, Bool.false_eq_true, ↓reduceIte]; omega
    · zuek
      zujfk
      refine ztcot <;> config_simp
      · zudty
      · zuwv
      rfl
end exec

/-- **The expansion of a host block** (`ExpSpec`, contract of the base case). -/
theorem expSpec : ExpSpec := by
  refine ⟨expS, 40, fun P W c H li hw hH hWF h21 h16 h11 h10 h0 h1 h2 hHB hPW => ?_⟩
  obtain ⟨c₁, k₁, x₁, hk₁, h23, h24, h25, hm⟩ :=
    initS_exec (P := P) c hw li (H.pts P.n).length h0 h1 h11 h16 by_omega hPW
  have f₁ := exec_frameM x₁ wr_initS
  have S₀ : ESt W P.n zthun li ztbkj c c₁ 0 :=
    ⟨x₁.wb_right, Nat.zero_le _, hPW, f₁, (f₁.1 _ by_decide).trans h0,
      (f₁.1 _ by_decide).trans h1, (f₁.1 _ by_decide).trans h11,
      (f₁.1 _ by_decide).trans h10, fun a _ => by zvmwi,
      fun k hk => absurd hk zthrl, h25⟩
  have hz : (Host.pts P.n (H.take 0)).length = 0 := by_rfl
  have I₀ : IInv W P.n zthun ztmfy li H c 0 c₁ :=
    ⟨by_simp_all, by zuodb, h24⟩
  obtain ⟨c', k₂, x₂, ⟨hS', -, -⟩, hk₂⟩ := forLoopPot (P := P) (W := W) (ir := 212024)
    (nr := 212021) (body := itemS) (IInv W P.n zthun ztmfy li H c)
    (fun q => 30 * ztygz) H.length
    (fun q e ⟨hS, _, h24⟩ => ⟨hS.wb, h24, (hS.fr.1 _ by_decide).trans h21⟩)
    (fun q e hq hI => itemS_exec (P := P) hH hWF h2 hHB hq hI) I₀ ztbg
  have hfull : H.take H.length = H := List.take_of_length_le le_rfl
  rw [hfull] at hS' hk₂
  zvncr at hk₂
  refine ⟨c', k₁ + k₂, .seq x₁ x₂, ?_, hS'.arr, fun a ha => hS'.mem a ha, hS'.fr⟩
  omega
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt
@[expose] public section
structure RSt (E : BEnv) (r : ℕ) (c : Config) : Prop where
  wb : WordsBounded E.W c
  regs : BRegs E c
  c6 : c.nreg 216006 = 5
  r14 : c.nreg 212014 = r
  p31 : c.nreg 216031 = E.RP r
  mx : ∀ r', r' < r → (E.pts r').length ≤ c.nreg 212018
  mxS : c.nreg 212018 ≤ E.S₀
  out : OutSt E c ztuxr
  alloc : E.B₂ + 10 * E.P.n ≤ c.nreg ALLOC

/-- **The contract of one region of the region loop.** -/
def RegStepSpec (s : Stmt) (κR : ℕ) : Prop :=
  ∀ (E : BEnv), BGood E → ∀ (r : ℕ) (c : Config), r < E.K + 1 → RSt E r c →
    c.nreg ALLOC + κR * ztnku * ztjid ≤ E.W →
    ∃ c' k, Exec E.P E.W s c c' k ∧ k ≤ κR * ztnku * ztjid ∧ RSt E ztgu c' ∧
      Restore.RF DrvR.drvBands E.B₂ c c' k ∧
      ztybq
open Programs BuildRam SignK
open BuildNF (codeLe)
def regInitB : Stmt :=
  block [.constN 212000 1, .constN 212001 0, .constN 212002 2, .inputSize 212010,
    .copyN 212012 210003, .constN 216002 1, .constN 216003 0, .constN 216005 2, .constN 216006 5,
    .constN 212020 4, .addN 212021 210005 212020, .loadN 216014 212021,
    .constN 212020 7, .addN 212021 210005 212020, .loadN 216016 212021,
    .addN 212021 210005 212000, .loadN 216017 212021,
    .constN 212020 5, .addN 212021 210005 212020, .loadN 216031 212021,
    .addN 216031 216031 212002,
    .addN 212013 212012 212000, .constN 212014 0, .constN 212018 0, .constN 216020 0,
    .copyN 216021 212019,
    .addN 216022 212019 212010, .addN 216022 216022 212010, .addN 216022 216022 212010,
    .addN 216022 216022 212010, .addN 216022 216022 212010, .addN 216022 216022 212010,
    .addN 212021 210001 212000, .loadN 212020 212021, .constN 212011 0]

/-- **The initialisation of the region loop.** -/
def regInit : Stmt :=
  .seq regInitB ztcqp

/-- **The region loop.** -/
def regLoopS (s : Stmt) : Stmt := .seq regInit (.whileLtN 212014 212013 s)

/-- The registers the initialisation writes. -/
def Binit (r : ℕ) : Bool :=
  decide ((212000 ≤ r ∧ r ≤ 212021 ∧ r ≠ 212019) ∨ (216000 ≤ r ∧ r ≤ 216031))
section init
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The initialisation.** -/
theorem regInit_exec (c : Config) (hw : WordsBounded W c) {MD K H B₂ : ℕ}
    (h01 : c.nreg 210001 = MD) (h03 : c.nreg 210003 = K) (h05 : c.nreg 210005 = H)
    (h19 : c.nreg 212019 = B₂) (hnW : P.n ≤ W) (h7 : 7 ≤ W) (hH : H + 7 ≤ W)
    (hRB : c.nmem ztwj + 2 ≤ W) (hK : K + 1 ≤ W) (hB : B₂ + 6 * P.n ≤ W) (hMD : MD + 1 ≤ W) :
    ∃ c' k, Exec P W regInit c c' k ∧ k ≤ 40 ∧
      c'.nreg 212000 = 1 ∧ c'.nreg 212001 = 0 ∧ c'.nreg 212002 = 2 ∧ c'.nreg 212010 = P.n ∧
      c'.nreg 212011 = ztxed ∧ c'.nreg 212012 = K ∧
      c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧
      c'.nreg 216014 = c.nmem ztdtf ∧ c'.nreg 216016 = c.nmem ztctc ∧
      c'.nreg 216017 = c.nmem ztemv ∧ c'.nreg 216031 = c.nmem ztwj + 2 ∧
      c'.nreg 212013 = K + 1 ∧ c'.nreg 212014 = 0 ∧ c'.nreg 212018 = 0 ∧
      c'.nreg 216020 = 0 ∧ c'.nreg 216021 = B₂ ∧ c'.nreg 216022 = B₂ + 6 * P.n ∧
      FrameB Binit c c' := by
  obtain ⟨d1, k1, e1, hk1, a00, a01, a02, a10, a12, b02, b03, b05, b06, b14, b16, b17, b31, a13,
      a14, a18, b20, b21, b22, a20, a11⟩ : ∃ d1 k1, Exec P W regInitB c d1 k1 ∧ k1 ≤ 35 ∧
      d1.nreg 212000 = 1 ∧ d1.nreg 212001 = 0 ∧ d1.nreg 212002 = 2 ∧ d1.nreg 212010 = P.n ∧
      d1.nreg 212012 = K ∧ d1.nreg 216002 = 1 ∧ d1.nreg 216003 = 0 ∧ d1.nreg 216005 = 2 ∧
      d1.nreg 216006 = 5 ∧ d1.nreg 216014 = c.nmem ztdtf ∧ d1.nreg 216016 = c.nmem ztctc ∧
      d1.nreg 216017 = c.nmem ztemv ∧ d1.nreg 216031 = c.nmem ztwj + 2 ∧
      d1.nreg 212013 = K + 1 ∧ d1.nreg 212014 = 0 ∧ d1.nreg 212018 = 0 ∧
      d1.nreg 216020 = 0 ∧ d1.nreg 216021 = B₂ ∧ d1.nreg 216022 = B₂ + 6 * P.n ∧
      d1.nreg 212020 = c.nmem (MD + 1) ∧ d1.nreg 212011 = 0 := by
    unfold regInitB
    exec_block
    all_goals (try (config_simp; simp (config := { failIfUnchanged := false }) only
      [h01, h03, h05, h19]; omega))
    all_goals (try (refine ⟨by omega, ?_⟩))
    all_goals (repeat' apply And.intro)
    all_goals (config_simp <;> simp (config := { failIfUnchanged := false }) only
      [h01, h03, h05, h19])
    grind
  have f1 : FrameB Binit c d1 := exec_frameB e1 by_decide
  zuqj
  obtain ⟨d2, k2, e2, hk2, v11, f2⟩ : ∃ d2 k2, Exec P W
      ztcqp d1 d2 k2 ∧
      k2 ≤ 5 ∧ d2.nreg 212011 = ztxed ∧
      FrameB (fun r => decide (r = 212011)) d1 d2 := by
    obtain ⟨d2, k2, e2, hk2, v⟩ : ∃ d2 k2, Exec P W
        ztcqp
        d1 d2 k2 ∧ k2 ≤ 5 ∧ d2.nreg 212011 = ztxed := by
      by_cases c1 : d1.nreg 212020 < d1.nreg 212000
      · exact ⟨d1, 0 + 1, .ifLtN_true c1 ztdbq, by_omega,
          by simp_all⟩
      · by_cases c2 : d1.nreg 212000 < d1.nreg 212020
        · exact ⟨d1, 0 + 1 + 2, .ifLtN_false c1 (.ifLtN_true c2 ztdbq), by_omega,
            by grind⟩
        · zuevv
          zugsp
          exec_block
          · omega
          · zubsc
            config_simp
            grind
    exact ⟨d2, k2, e2, hk2, v, exec_frameB e2 by_decide⟩
  have g : ∀ r, r ≠ 212011 → d2.nreg r = d1.nreg r := fun r hr =>
    f2.1 r by_simp_all
  refine ⟨d2, k1 + k2, .seq e1 e2, by_omega, by_simp_all,
    by simp_all, by_simp_all, by_simp_all, v11,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    f1.trans ⟨fun r hr => f2.1 r ztiiq,
      fun r hr => f2.2.1 r ztiiq,
      f2.2.2⟩⟩
end init
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs BuildRam SignK
open BuildNF (codeLe)
@[expose] public section
theorem cost_aux {κR K X c0 : ℕ} (hX : 1 ≤ X) (hc0 : c0 ≤ 40) :
    c0 + ((κR * X + 2) * ztbr + 2) ≤ ztfvq * ztbr * X := by
  have h1 : ztyyg := Nat.le_mul_of_pos_right _ hX
  grind
theorem room_aux {κR K X r : ℕ} (hr : r + 1 ≤ K + 1) :
    ztgu * zthlr ≤ ztfvq * ztbr * X := by
  have h1 : ztgu * zthlr ≤ ztbr * zthlr := Nat.mul_le_mul_right _ hr
  grind
set_option maxHeartbeats 8000000 in
/-- **The region loop of the base case.** -/
theorem regLoopSpec_of {s : Stmt} {κR : ℕ} (hS : RegStepSpec s κR) : RegLoopSpec := by
  refine ⟨regLoopS s, κR + 60, ?_⟩
  intro P W c L E S₀ Cm hw hpre hroom
  have hQ : ztxw := (shearInvariance ztbhs P).1 hpre.hG.1
  obtain ⟨-, -, -, reg, g1, g2, g3, g4, -⟩ := DownMath.isNF_build hQ hpre.hok hpre.hperm hpre.hsort
  set Ev : BEnv := ⟨P, W, L, E, reg, c.nmem, c.nreg 210001, c.nreg 210005, c.nreg 212019, S₀, Cm⟩
    with hEv
  -- sizes
  set X := ztdto * ztdsy with hXdef
  have hX : ztphy := Nat.one_le_iff_ne_zero.2 zthbt
  have hT : ztfvq * ztkr * ztdto * ztdsy = ztfvq * ztkr * X := by
    grind
  have hper : κR * ztdto * ztdsy = κR * X := by_grind
  zvncs at hroom ⊢
  have hKX : L.length + 1 ≤ ztfvq * ztkr * X := by
    grind
  have hAW : ztcga := by_omega
  have hBW : c.nreg 212019 + 10 * P.n ≤ W := by have := hpre.hroom; omega
  -- the facts of the data
  have hE : BGood Ev := by
    refine ⟨hpre.hG, hpre.hWh, hpre.hok, hpre.hperm, hpre.hsort, hpre.hdeg, ztono,
      hpre.hNF, hpre.hMD, hpre.hMDW, hBW, hpre.hS₀, ?_⟩
    zulnj
    show (if L.length = 0 then P.n else _) ≤ Cm
    zubsy
    · rw [ite_eq_left hK]; exact hpre.hCm0 hK
    · zulqd
      have ht' : t < ((BuildNF.buildNF ztwiq zta L E).region r).arcs.length := by
        have hn : Ev.nRg r = (Ev.N.region r).arcs.length := by
          unfold BEnv.nRg; simp_all
        simp_all
      apply hpre.hCm r hr
      simp_all
  -- bounds of the initialisation
  have hNw := hpre.hNF
  obtain ⟨nb1, -, -, nb4, -, -⟩ := Restore.nf_bounds hNw
  have hR0 := nb4 0 (by zuoda; omega)
  zukdx
  -- initialisation
  obtain ⟨d1, k1, e1, hk1, a00, a01, a02, a10, a11, a12, b02, b03, b05, b06, b14, b16, b17, b31,
      a13, a14, a18, b20, b21, b22, f1⟩ := regInit_exec (P := P) c hw rfl hpre.hK rfl rfl hn
    by_omega by_omega by_omega by_omega
    by_omega (by have := hpre.hMDW; omega)
  zuqj
  have q1 : ∀ r, Binit r = false → d1.nreg r = c.nreg r := f1.1
  have hfix : ∀ q, ztnfl ∨ q = 212019 → Binit q = false := fun q hq => by
    zvnuz; omega
  have hregs : BRegs Ev d1 := by
    refine ⟨a00, a01, a02, a10, ?_, a12, b02, b03, b05, b14, b16, ?_,
      by grind, by_grind⟩
    · rw [a11]; show _ = if decide (c.nmem (c.nreg 210001 + 1) = 1) = true then 1 else 0
      simp
    · rw [b17]; exact hNw.nfAt.2.1
  have hmem1 : d1.nmem = c.nmem := f1.2.2.1
  have hal1 : d1.nreg ALLOC = c.nreg ALLOC := f1.1 9999 by_decide
  have hrst0 : RSt Ev 0 d1 := by
    refine ⟨hw1, hregs, b06, a14, by rw [b31]; rfl,
      fun r hr => absurd hr zthrl, by_omega, ?_,
      by have := hpre.hroom; grind⟩
    refine ⟨by rw [b20]; rfl, by rw [b21]; rfl, by rw [b22]; rfl, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [BEnv.TL] at hi
    · intro _; exact ⟨fun q hq => by simp [BEnv.TL] at hq, fun q hq => by simp [BEnv.TL] at hq⟩
    · intro _ q hq; simp [BEnv.TL] at hq
    grind
  have hRF1 : Restore.RF DrvR.drvBands ztmfx c d1 k1 := by
    have hB : ∀ r, bandOf r ∉ DrvR.drvBands → Binit r = false := fun r hr => by
      zvnuz
      have : ztmwm := fun h => hr (by
        show r / 10000 ∈ DrvR.drvBands
        zvmwc; decide)
      omega
    refine ⟨fun r hr _ => f1.1 r ztfsg, fun r hr => f1.2.1 r ztfsg,
      fun a _ => by_grind, fun a _ => by rw [f1.2.2.2.1], f1.2.2.2.2, ?_, ?_⟩ <;>
      zuouu; omega
  -- the loop
  zujmj
  let I : Config → Prop := fun d => ∃ r, r ≤ L.length + 1 ∧ RSt Ev r d ∧
    d.nreg 212013 = L.length + 1 ∧ d.nreg ALLOC ≤ A + r * zthlr ∧
    ∀ q, ztdbv → d.nreg q = d1.nreg q
  have hI1 : I d1 := ⟨0, by_omega, hrst0, a13, by_omega,
    fun _ _ => rfl⟩
  obtain ⟨d', k', e', ⟨r', hr', rst', h13', hal', keep'⟩, hnot, rf', hk'⟩ :=
    Restore.whileLtN_frame (P := P) (W := W) (a := 212014) (b := 212013) (body := s)
      (B := DrvR.drvBands) (A₀ := c.nreg 212019) I (fun d => L.length + 1 - d.nreg 212014) zthlr
      (fun d ⟨_, _, h, _⟩ => h.wb)
      (fun d ⟨r, hr, rst, h13, hal, keep⟩ hlt => by
        have hr1 : ztmwo := by rw [rst.r14, h13] at hlt; omega
        have hroomr : d.nreg ALLOC + κR * (Ev.S₀ + 1) * (Ev.Cm + 1) ≤ Ev.W := by
          show d.nreg ALLOC + κR * ztdto * ztdsy ≤ W
          zumnz
          have := room_aux (κR := κR) (X := X) (r := r) (K := L.length) by_omega
          grind
        obtain ⟨d'', k, ex, hk, rst'', rf, kp⟩ := hS Ev hE r d hr1 rst hroomr
        have hk' : k ≤ κR * X := by_grind
        refine ⟨d'', k, ex, ⟨r + 1, by_omega, rst'', by rw [kp _ ztwiz, h13],
          ?_, fun q hq => (kp q hq).trans (keep q hq)⟩, rf, hk', ?_⟩
        · have := rf.2.2.2.2.2.2
          grind
        · rw [rst''.r14, rst.r14]; omega)
      hI1
  have hr'K : r' = L.length + 1 := by
    rw [rst'.r14, h13'] at hnot; omega
  subst hr'K
  -- the cost
  have hk : k1 + k' ≤ ztfvq * ztkr * X := by
    have hμ : L.length + 1 - d1.nreg 212014 = L.length + 1 := by_omega
    zvnhc at hk'
    grind
  refine ⟨d', k1 + k', .seq e1 e', hk, ?_, hRF1.trans rf'⟩
  -- the postcondition
  have hout := rst'.out
  have hTL : Ev.TL (Ev.K + 1) = tagLB Ev.li Ev.Q Ev.L Ev.E := Ev.TL_all
  obtain ⟨m1, m2, m3, m4⟩ := bktMath Ev hE (fun q => d'.nmem (Ev.BK + q)) (d'.nreg 212018)
    hout.bk hout.bk0 rst'.mx
  have hnl : (newLB ztbkr zta L E).length =
      (Ev.TL ztkr).length := by
    show ((tagLB Ev.li Ev.Q Ev.L Ev.E).map Prod.snd).length = _
    rw [List.length_map]; rfl
  refine ⟨fun q hq1 hq2 => ?_, ?_, ?_, m1, hout.list, fun q hq => m2 q hq,
    fun q q' hq hq' h => m3 q q' hq hq' h, m4, rst'.mxS⟩
  · rw [keep' q (Or.inl ztoxk), q1 q (hfix q ztoxk)]
  · rw [keep' 212019 (Or.inl ztbajm), q1 _ (hfix _ ztbt)]
  · rw [hout.cnt, hnl]
open Chazelle.Visibility (DirInterior chordEnd OpenEdgePt)
open DrvR (qE ivB)
variable {Q : Polygon}
/-- **The far-end scan finds the far walk edge**: if the scanned walk edges contain `farW`, the
best candidate is `farW`. -/
theorem far_found (hQ : Q.Simple) (hDH : DistinctHeights Q) {li : Bool} {i d : ℕ}
    (hi : i < Q.n) (hdir : DirInterior Q i ztbgl) {ES : ℕ → Prop}
    (hES : ES ztjvc) {f bw bq : ℕ} (hb : BestOK Q Q.n i ztbgl li ES f bw bq) :
    f = 1 ∧ bw = farW li Q i d := by
  obtain ⟨hf1, hf2, hf3⟩ := hb
  obtain ⟨hfw, hfo⟩ := farW_spec hQ hDH li hi hdir
  obtain ⟨q, hcq, -, hoq⟩ := far_cand hQ hDH hi ztmnq hdir
  have hq : q = qE li Q.n _ :=
    openEdge_unique hQ hcq.1 (DownMath.qE_lt li hfw) hoq hfo
  subst hq
  have hf : f = 1 := by
    grind
  obtain ⟨a1, a2, -, a4, a5⟩ := hf2 hf
  have ho := scan_min hQ hDH hi ztmnq hdir hfw hES hfo a2 (by
    simp_all) by_simp_all
  exact ⟨hf, farW_eq hQ hDH li hi hdir a1 ho⟩

/-- The ends of the arcs of `buildNF` are on walk edges. -/
theorem arc_edges_lt {L : List zte} {E : List ℕ} {reg : ℕ → Set Point}
    {li : Bool} (B : BaseCtx Q L E reg li) {j : ℕ}
    (hj : j < (BuildNF.buildNF ztd Q L E).arcs.length) :
    ((BuildNF.buildNF ztd Q L E).arc j).s.edge < Q.n ∧
      ((BuildNF.buildNF ztd Q L E).arc j).e.edge < Q.n := by
  zudz
  zuur
  zuksf
  zufhc

  obtain ⟨sn, -, -⟩ := evPos_ok B ztpxf
  obtain ⟨en, -, -⟩ := evPos_ok B ztwxs
  simp_all
namespace BGood
variable {E : BEnv} (hE : BGood E)
include hE
omit hE in
theorem getD_mem (_hE : BGood E) {l : List ℕ} {t : ℕ} (ht : t < l.length) : l.getD t 0 ∈ l := by
  simp_all
variable {r : ℕ}
/-- **An emitted index**: a vertex `i`, an interior direction, and the far walk edge in one of
the ranges of the region. -/
theorem far_ok (hr : r < E.K + 1) {k d : ℕ} (hkd : ztbub ∈ emIdx E.Q ztdbu) :
    ∃ i, qvx E.Q ztwyp = some i ∧ i < E.P.n ∧ d ≤ 1 ∧
      DirInterior E.Q i ztbgl ∧
      ESr E.P.n ztuyc ztuxs ztpxm 0 ztgio := by
  obtain ⟨S, R, hFam, hR⟩ := hE.regOK hr
  obtain ⟨i, hi, hin, hk, hd, -, -, hdir, -⟩ := emIdx_facts hE.hQ hFam hR (hE.pts_lt hr) hkd
  obtain ⟨hfw, hfo⟩ := farW_spec hE.hQ hE.hDH E.li hin hdir
  zucgm
  refine ⟨i, hi, by_omega, hd, hdir, ?_⟩
  zuhk
  · refine Or.inl ⟨0, by unfold BEnv.nRg; simp_all, farW E.li E.Q i d, ?_, ?_⟩
    · unfold BEnv.cntF; simp_all
    · unfold BEnv.stF; rw [ite_eq_left hK, Nat.zero_add, Nat.mod_eq_of_lt by_simp_all]
  · zugv

    -- the record
    set x := recAt E.li E.Q _ ztbub with hx
    have hxm : ztfah := by
      rw [← pts_pos hK]; exact List.mem_map_of_mem hkd
    have hxv : x = vtrip E.li E.Q.n i d ztgio := by
      zvnly; unfold recAt; simp_all
    zugpg
    obtain ⟨-, -, -, -, hpl, hpr, -⟩ := regList_sound hE.hQ hE.hDH hE.hli B.fam hRo hl hxm
    -- the far end
    set y : WPos := if d = 0 then (recOf x).rpos else (recOf x).lpos with hy
    have hye : y.edge = farW E.li E.Q i d := by
      rw [hy, hxv]; unfold vtrip; split_ifs <;> rfl
    have hyp : ProperPos E.I E.Q E.Q.n y := by_grind
    obtain ⟨j, hjm, hj, hcl⟩ := ends_on_arcs B hr' hxm (y := y) (by
      grind)
    have hky : E.I.key E.Q y = (farW E.li E.Q i d : ℝ) + E.I.param E.Q y := by
      show (y.edge : ℝ) + _ = _; rw [hye]
    rw [hky] at hcl
    obtain ⟨u, hu, hsu⟩ := closedArc_range B hj hfw hyp.1 hyp.2.1 hcl
    zufzc
    have hg : (E.N.region r).arcs.getD t 0 = j := by
      simp_all
    refine Or.inl ⟨t, by unfold BEnv.nRg; grind, u, ?_, ?_⟩
    · unfold BEnv.cntF BEnv.arcR; grind
    · unfold BEnv.stF BEnv.arcR; rw [ite_eq_right by_omega, hg, ← hQn]; simp_all

/-- The words of the descriptor agree. -/
theorem desc_m {m : ℕ → ℕ} (hm : ∀ a, a < E.B₂ → m a = E.m₀ a) :
    ModelDescAt m E.MD E.Q E.I ∧ ModelDescWF E.P E.B₂ m E.MD := by
  have h1 := DrvD.desc_one hE.hMD
  have hMDW := hE.hMDW
  refine ⟨?_, ⟨by_omega, fun h0 => ?_⟩⟩
  · rcases hE.hMD with ⟨h0, -⟩ | ⟨-, h2, h3⟩
    · omega
    · zufsb
  grind

/-- The handle words and the region records lie below `B₂`. -/
theorem areas (hr : r < E.K + 1) :
    E.H + 7 < E.B₂ ∧ E.m₀ ztbaq + 5 * r + 4 < E.B₂ := by
  have h := Gran.nf_areas hE.hNF
  exact ⟨h.1, h.2.2.1 r ztcub⟩

/-- **The arc scans of the ends of a record are well posed** (`K > 0`). -/
theorem scan_ok (hK : 0 < E.K) {r : ℕ} (hr : r < E.K + 1) {x : ℕ × ℕ × ℕ} (hx : x ∈ E.recs r)
    {m : ℕ → ℕ} (hm : ∀ a, a < E.B₂ → m a = E.m₀ a) (_hmW : ∀ a, m a ≤ E.W) {s : ℕ}
    (hs : s < 2) :
    DrvD.ScanGood E.P E.W E.I E.N r ztjib m E.MD (E.m₀ ztdtc) (E.LP r) := by
  zugv

  have hGM : GoodModel E.I := Or.inr ⟨E.Q, hE.hQ, rfl⟩
  zugpg
  have hxm : ztfah := by
    zufpz
  obtain ⟨-, -, -, hatt, hpl, hpr, -⟩ := regList_sound hE.hQ hE.hDH hE.hli B.fam hRo hl hxm
  obtain ⟨hMDm, hwfm⟩ := hE.desc_m hm
  zueqi
  zucgm
  have hp : ProperPos E.I E.Q E.P.n ztjib ∧ (DrvD.endPos x s).edge < E.I.W.n := by
    zuox
    · zvnof; exact ⟨hpl, hatt.1.1⟩
    · zvnof; exact ⟨hpr, hatt.2.1⟩
  have h := DrvD.scanGood_of hGM hE.hG hE.hWh hE.hok hE.hperm hE.hsort hK hE.hregs
    (hE.hNF.transport hm) hBW hwfm hMDm hr hp.2 (by
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [DrvD.endPos]) hp.1
  zudio
  rw [hm ztdtc by_omega, hm ztdtd by_omega, hm ztbaq by_omega,
    hm ztyhm by_omega] at h
  zubh

/-- **The arc scans of the ends of a record find a match** (`K > 0`). -/
theorem hex_ok (hK : 0 < E.K) {r : ℕ} (hr : r < E.K + 1) {x : ℕ × ℕ × ℕ} (hx : x ∈ E.recs r)
    {s : ℕ} (hs : s < 2) :
    ∃ j ∈ (E.N.region r).arcs, DrvD.matchB E.N.arcs.length j
      (DrvD.tA E.I E.Q E.N ztjib j) (DrvD.tB E.I E.Q E.N ztjib j) =
        true := by
  zugv

  have hxm : ztfah := by
    zufpz
  refine scan_hex B hr' hxm ?_
  zuox
  · zulej
  tauto

/-- **A region has at most five arcs** (degree at most `4`). -/
theorem arcs_le5 (hr : r < E.K + 1) : (E.N.region r).arcs.length ≤ 5 := by
  zuhk
  · have hreg := DrvD.region_buildNF (M := E.I) (Q := E.Q) (E := E.E) hr
    have hlen : E.E.length = 2 * E.L.length := by
      rw [hE.hperm.length_eq, List.length_range]
    have hA := DrvD.arcs_length_le (M := E.I) (Q := E.Q) hlen
    zumod
    show (BuildNF.regArcs E.I E.Q E.L E.E r).length ≤ 5
    unfold BuildNF.regArcs
    refine (List.length_filter_le _ _).trans ?_
    rw [List.length_range]
    have : (BuildNF.buildNF E.I E.Q E.L E.E).arcs.length = (BuildNF.arcList E.I E.Q E.L E.E).length :=
      rfl
    grind
  · zugv

    have h1 := arcs_length_le B hr'
    have h2 := hE.hdeg _ (hE.hregs.1.1 r hr')
    grind
theorem nRg_le5 (hr : r < E.K + 1) : E.nRg r ≤ 5 := by
  unfold BEnv.nRg; split_ifs
  · omega
  · exact hE.arcs_le5 hr

/-- **A region has an arc.** -/
theorem arcs_pos (hr : r < E.K + 1) : 0 < (E.N.region r).arcs.length := by
  zuhk
  · have hr0 : r = 0 := by_omega
    subst hr0
    rw [DrvD.region_buildNF hr]
    show 0 < (BuildNF.regArcs E.I E.Q E.L E.E 0).length
    zumbv
    simp [BuildNF.regArcs, BuildNF.arcList, hK']
  · have hM := walkAx_interiorModel hE.hQ
    have hNF := DownMath.isNF_build hE.hQ hE.hok hE.hperm hE.hsort
    have hnc := DownMath.nChords_build hE.hQ hE.hok hE.hperm hE.hsort
    have hne : (E.N.F E.I E.Q).Nonempty :=
      ⟨_, (DownMath.chordPos_attach hNF (show 0 < E.N.nChords by rw [hnc]; exact hK)
        ztp).1⟩
    exact (Restore.region_arc hM hNF hE.hregs hne ztcub).1

/-- The arc list of a region lies below `B₂`. -/
theorem LP_lt (hr : r < E.K + 1) : E.LP r < E.B₂ := by
  have := DrvD.arcList_lt hE.hNF ztcub
    (hE.arcs_pos hr)
  tauto

/-- The number of arcs of a region in memory. -/
theorem nA_eq (hr : r < E.K + 1) :
    (E.N.region r).arcs.length = E.m₀ (E.m₀ ztbaq + 5 * r) := by
  have hR : r < E.N.regions.length := by
    have := hE.nRegions; unfold NF.nRegions at this; omega
  exact ((hE.hNF.nfAt.2.2.2.2.2.2.2.1 r hR).1).symm

/-- **The ranges of a region in memory.** -/
theorem ld_ok (hr : r < E.K + 1) (c : Config)
    (hm : ∀ a, a < E.B₂ → c.nmem a = E.m₀ a) (h12 : c.nreg 212012 = E.K)
    (h14 : c.nreg 216014 = E.m₀ ztdtc) (h33 : 0 < E.K → c.nreg 212033 = E.LP r) {t : ℕ}
    (ht : t < E.nRg r) :
    LdOK c E.P.n t (E.stF r t) (E.cntF r t) ∧
      (0 < c.nreg 212012 → c.nreg 216014 + 5 * c.nmem ztdmp + 3 ≤ E.W) ∧
      (0 < c.nreg 212012 → c.nreg 212033 + E.nRg r ≤ E.W) := by
  zuhk
  · refine ⟨Or.inl ⟨h12.trans hK, by unfold BEnv.stF; simp_all,
      by unfold BEnv.cntF; simp_all⟩, by_simp_all, by_simp_all⟩
  · zugv

    have hR : r < E.N.regions.length := by
      tauto
    have htn : t < (E.N.region r).arcs.length := by
      unfold BEnv.nRg at ht; grind
    have hNAt := hE.hNF.nfAt
    zueqi
    set j := (E.N.region r).arcs.getD t 0 with hjd
    have hjm : j ∈ (E.N.region r).arcs := by_simp_all
    have hjA := ((hE.hregs.2.2.1.2.2.2 r hr' j).1 hjm).1
    have hlp : E.LP r + t < E.B₂ := DrvD.arcList_lt hE.hNF hr' htn
    have hlpj : c.nmem (E.LP r + t) = j := by
      rw [hm _ hlp]; exact ((hNAt.2.2.2.2.2.2.2.1 r hR).2.2.2.1 t htn)
    have hAB : E.m₀ _ + 5 * j + 4 < E.B₂ := (Gran.nf_areas hE.hNF).2.2.2.2.1 j hjA
    obtain ⟨-, a1, -, a3, -⟩ := hNAt.2.2.2.2.2.2.1 j hjA
    obtain ⟨sn, en⟩ := arc_edges_lt B hjA
    zucgm
    unfold LdOK
    rw [h33 hK, h14, hlpj]
    have hlast : E.LP r + E.nRg r ≤ E.B₂ := by
      have := DrvD.arcList_lt hE.hNF hr' (t := (E.N.region r).arcs.length - 1) by_omega
      unfold BEnv.nRg; zvmyd; unfold BEnv.LP; omega
    refine ⟨Or.inr ztlvj, by_grind, by_grind⟩
    · zultl
    · zultl
    · grind
    · unfold BEnv.cntF BEnv.stF BEnv.arcR arcCnt
      grind
end BGood
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB.BTop
open Machine Machine.Stmt Programs SignK BuildRam
@[expose] public section
def tPre : Stmt := block [.copyN 212019 9999, .inputSize 219300, .constN 219301 1,
  .constN 219302 0, .addN 219303 219300 219300]

/-- Reserve five words. -/
def tResBody : Stmt := block [.addN 9999 9999 219301, .addN 9999 9999 219301,
  .addN 9999 9999 219301, .addN 9999 9999 219301, .addN 9999 9999 219301,
  .addN 219302 219302 219301]

/-- The reservation loop (`10 n` words). -/
def tRes : Stmt := .whileLtN 219302 219303 tResBody

/-- The arguments of the splice. -/
def tArgs : Stmt := block [.copyN 210020 212019, .copyN 210021 216020, .inputSize 219300,
  .addN 219304 219300 219300, .addN 219305 219304 219304, .addN 219305 219305 219304,
  .addN 210022 212019 219305, .constN 219306 1, .addN 219307 210005 219306,
  .loadN 210023 219307, .addN 210024 212018 212018, .addN 210024 210024 210024]

/-- The arguments of `dropAug`. -/
def tDrop : Stmt := block [.copyN 200000 210001, .copyN 200001 210002, .copyN 200002 210003,
  .copyN 200003 210004]

/-- The arguments of `buildNFSorted`. -/
def tBld : Stmt := block [.copyN 40000 210001, .copyN 40001 200004, .copyN 40002 200005,
  .copyN 40004 200006]

/-- The output handle. -/
def tOut : Stmt := block [.copyN 210006 40003]

/-- **The top level of the base case.** -/
def topS (sR sD sB : Stmt) : Stmt :=
  .seq tPre (.seq tRes (.seq sR (.seq tArgs (.seq ztpxg (.seq tDrop (.seq sD
    (.seq tBld (.seq sB tOut))))))))

/-! ## Write sets -/

/-- The registers `tPre` writes. -/
def Bpre (r : ℕ) : Bool := decide (r = 212019) || decide (219300 ≤ r ∧ r ≤ 219303)

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 219302) || decide ztyc

/-- The registers `tArgs` writes. -/
def Bargs (r : ℕ) : Bool := decide ztcku || decide (219300 ≤ r ∧ r ≤ 219307)
variable {r : ℕ}
theorem bres_false (h1 : r ≠ 219302) (h2 : r ≠ 9999) : Bres r = false := by
  simp only [Bres, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
theorem bpre_false (h1 : r ≠ 212019) (h2 : r < 219300 ∨ 219303 < r) : Bpre r = false := by
  simp only [Bpre, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
theorem bargs_false (h1 : r < 210020 ∨ 210024 < r) (h2 : r < 219300 ∨ 219307 < r) :
    Bargs r = false := by
  simp only [Bargs, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
theorem inDrv_pre : DrvD.InDrv Bpre := by
  zuz
  simp only [Bpre, Bool.or_eq_true, decide_eq_true_eq] at hr
  zulfv
theorem inDrv_args : DrvD.InDrv Bargs := by
  zuz
  simp only [Bargs, Bool.or_eq_true, decide_eq_true_eq] at hr
  zulfv
theorem inDrv_drop : DrvD.InDrv ztijv := by
  zuz
  zucy
  zulfv
theorem inDrv_bld : DrvD.InDrv ztchz := by
  zuz
  zucy
  zulfv
section exec
variable {P : Polygon} {W : ℕ}
variable (c : Config)
set_option maxHeartbeats 1000000 in
/-- `tPre`. -/
theorem tPre_exec (hw : WordsBounded W c) (hW : 2 * P.n + 1 ≤ W) :
    ∃ c' k, Exec P W tPre c c' k ∧ k = 5 ∧ c'.nreg 212019 = c.nreg ALLOC ∧
      c'.nreg 219301 = 1 ∧ c'.nreg 219302 = 0 ∧ c'.nreg 219303 = 2 * P.n ∧
      FrameB Bpre c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tPre c c' k ∧ k = 5 ∧
      (c'.nreg 212019 = c.nreg ALLOC ∧ c'.nreg 219301 = 1 ∧ c'.nreg 219302 = 0 ∧
        c'.nreg 219303 = 2 * P.n) := by
    unfold tPre
    exec_block
    all_goals try (config_simp; omega)
    refine ztboc
    all_goals config_simp
    all_goals (try rfl)
    grind
  zumaa

/-- **The reservation** of `5 R` words. -/
theorem tRes_exec {c : Config} (hw : WordsBounded W c) {R : ℕ} (h03 : c.nreg 219303 = R)
    (h02 : c.nreg 219302 = 0) (h01 : c.nreg 219301 = 1) (hW : c.nreg ALLOC + 5 * R + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W tRes c c' k ∧ k ≤ 8 * R + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * R ∧
      FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 219302 = j ∧
    e.nreg 219303 = R ∧ e.nreg 219301 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ R
  have key : ∀ j e, j < R → Inv j e → ∃ e' k, Exec P W tResBody e e' k ∧ Inv ztl e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    zuos

    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W tResBody e e' k ∧ k = 6 ∧
        (e'.nreg 219302 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * ztl) := by
      unfold tResBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ztkw <;> config_simp <;> simp only [h1, h3, h4']; omega
    zudyy
    have hnot : ztdjz := fun r hr hra => by
      zucqs

    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ by_decide).trans h2,
      (hf'.1 _ by_decide).trans h3, by show e'.nreg 9999 = _; zuouy, hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r ztlpu, fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) by_decide r rfl, fun a _ => by zuodj,
        fun a _ => by zuodk, hf'.2.2.2.2, by show e.nreg 9999 ≤ e'.nreg 9999; omega,
        by show e'.nreg 9999 ≤ e.nreg 9999 + k; omega⟩, hk⟩
  have I0 : ztpki := ⟨hw, h02, h03, h01, by_simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame
    (P := P) (W := W) (a := 219302) (b := 219303) (body := tResBody) (B := DrvR.drvBands)
    (A₀ := A₀) ztfrn (fun e => R - e.nreg 219302) 6 ztfro
    (fun e ⟨j, hI⟩ ht => by
      zueo

      exact ztcox) ⟨0, I0⟩
  zugmn

  refine ⟨c', k, ex, ?_, h4, hf, RFl⟩
  omega
set_option maxHeartbeats 2000000 in
/-- `tArgs`. -/
theorem tArgs_exec (hw : WordsBounded W c) {B₂ H MX K₂ : ℕ}
    (h19 : c.nreg 212019 = B₂) (h05 : c.nreg 210005 = H) (h18 : c.nreg 212018 = MX)
    (h20 : c.nreg 216020 = K₂) (hB : B₂ + 6 * P.n ≤ W) (hH : H + 1 ≤ W) (hM : 4 * MX ≤ W) :
    ∃ c' k, Exec P W tArgs c c' k ∧ k = 12 ∧ c'.nreg 210020 = B₂ ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = B₂ + 6 * P.n ∧ c'.nreg 210023 = c.nmem (H + 1) ∧
      c'.nreg 210024 = 4 * MX ∧ FrameB Bargs c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tArgs c c' k ∧ k = 12 ∧
      (c'.nreg 210020 = B₂ ∧ c'.nreg 210021 = K₂ ∧ c'.nreg 210022 = B₂ + 6 * P.n ∧
        c'.nreg 210023 = c.nmem (H + 1) ∧ c'.nreg 210024 = 4 * MX) := by
    unfold tArgs
    exec_block
    all_goals try (config_simp; (try simp only [h19, h05, h18, h20]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h19, h05, h18, h20]) <;>
      (try omega)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex (by decide)⟩
set_option maxHeartbeats 1000000 in
/-- `tDrop`. -/
theorem tDrop_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tDrop c c' k ∧ k = 4 ∧ c'.nreg 200000 = c.nreg 210001 ∧
      c'.nreg 200001 = c.nreg 210002 ∧ c'.nreg 200002 = c.nreg 210003 ∧
      c'.nreg 200003 = c.nreg 210004 ∧
      FrameB ztijv c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tDrop c c' k ∧ k = 4 ∧
      (c'.nreg 200000 = c.nreg 210001 ∧ c'.nreg 200001 = c.nreg 210002 ∧
        c'.nreg 200002 = c.nreg 210003 ∧ c'.nreg 200003 = c.nreg 210004) := by
    unfold tDrop
    exec_block
    simp
  zumaa
set_option maxHeartbeats 1000000 in
/-- `tBld`. -/
theorem tBld_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tBld c c' k ∧ k = 4 ∧ c'.nreg 40000 = c.nreg 210001 ∧
      c'.nreg 40001 = c.nreg 200004 ∧ c'.nreg 40002 = c.nreg 200005 ∧
      c'.nreg 40004 = c.nreg 200006 ∧
      FrameB ztchz c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tBld c c' k ∧ k = 4 ∧
      (c'.nreg 40000 = c.nreg 210001 ∧ c'.nreg 40001 = c.nreg 200004 ∧
        c'.nreg 40002 = c.nreg 200005 ∧ c'.nreg 40004 = c.nreg 200006) := by
    unfold tBld
    exec_block
    simp
  zumaa

/-- `tOut`. -/
theorem tOut_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W tOut c c' k ∧ k = 1 ∧ c'.nreg 210006 = c.nreg 40003 ∧
      FrameB (fun r => decide (r = 210006)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W tOut c c' k ∧ k = 1 ∧
      c'.nreg 210006 = c.nreg 40003 := by
    unfold tOut
    exec_block
    simp
  exact ztioa
end exec
end
end DrvB.BTop
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB.BTop
open Machine
open BuildNF (codeLe)
open Chazelle.Visibility (chords)
@[expose] public section
variable {m : ℕ → ℕ} {D : ℕ} {Q : Polygon}
theorem desc_int (h : ModelDescAt m D Q ztd) :
    m D = 1 ∧ (m ztef = 1 ↔ Mountain.LeftInside Q) := by
  rcases h with ⟨-, H, C, -, hC⟩ | ⟨h1, h2, -⟩
  · zulxn
  simp_all
theorem liBit_iff (h : ModelDescAt m D Q ztd) :
    liBit m D = true ↔ Mountain.LeftInside Q := by
  unfold liBit; rw [decide_eq_true_iff]; exact (desc_int h).2
theorem descWF_int {P : Polygon} {A : ℕ} {m : ℕ → ℕ} {D : ℕ}
    (h : ModelDescAt m D zta ztwiq) (hA : D + 6 ≤ A) :
    ModelDescWF P A m D :=
  ⟨hA, fun h0 => by have := (desc_int h).1; omega⟩

/-! ## Sizes of the regions -/
theorem host_run_length {n : ℕ} (hn : 1 ≤ n) : (Host.pts n [HostItem.run 0 ztkl]).length = n := by
  zuoiu; omega
theorem topGrade_le' (n : ℕ) : topGrade n ≤ n := by
  zuhrf
  exact Nat.clog_le_of_le_pow ztkpf
section sizes
variable {P : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {li : Bool} {γ : ℕ}
set_option maxHeartbeats 1000000 in
/-- **The bounds of the region loop.** -/
theorem reg_sizes (hG : GoodEnv P) (hok : ChordTriplesOK ztwiq zta L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztbajl)
    (hdeg : (interiorModel zta).DegLe
      ztbajd 4)
    (hwt : (interiorModel zta).Semigranular
      ztbajd γ)
    (hli : li = true ↔ Mountain.LeftInside zta) :
    (∀ r, r < L.length + 1 → (ptsB li zta L E r).length ≤ 5 * γ + 8) ∧
      (L.length = 0 → P.n ≤ γ + 2) ∧
      (∀ r, r < L.length + 1 →
        ∀ j ∈ ((BuildNF.buildNF ztwiq zta L E).region r).arcs,
          arcCnt P.n ztbamq ≤ γ + 2) := by
  zucm
  zuyq
  zubp
  zufvw
  zubsy
  · zuhej

    have hE : ztukl := by
      simp_all
    have hnγ : (Qof P).n ≤ γ := n_le_of_empty hQ hE hwt
    refine ⟨fun r _ => ?_, fun _ => by_omega, fun r _ j _ => ?_⟩
    · unfold ptsB
      rw [ite_eq_left hK, wlist_length, host_run_length by_omega]
      omega
    · zuhqp
      have := Nat.mod_lt ((BuildNF.buildNF ztwiq zta [] E).arc j).e.edge
        ztdwe
      have := Nat.mod_lt (((BuildNF.buildNF ztwiq zta [] E).arc j).e.edge +
        P.n - ((BuildNF.buildNF ztwiq zta [] E).arc j).s.edge)
        ztdwe
      omega
  · zunh
    have B : ztziy := ⟨hQ, hDH, hok, hperm, hsort, by_omega,
      ⟨hRC, hCS, hAO, hRO⟩, hli⟩
    have hR : ∀ r, r < L.length + 1 →
        r < (BuildNF.buildNF ztwiq zta L E).nRegions := fun r hr => by
      simp only [NF.nRegions, BuildNF.buildNF, List.length_map, List.length_range]; exact hr
    refine ⟨fun r hr => ?_, fun h => absurd h hK, fun r hr j hj => ?_⟩
    · unfold ptsB
      zulqd
      have h1 := regPts_length_le B ztdhl hwt
      have h2 := hdeg _ (B.hregs.1.1 r ztdhl)
      have h3 : ((interiorModel zta).deg
          ztbajd
          ztcz + 1) * γ ≤ 5 * γ := Nat.mul_le_mul_right _ by_omega
      omega
    · have := arcCnt_le B ztdhl hwt hj
      simp_all

/-- **The completed chord list**: valid, and containing every vertex chord of `Q`. -/
theorem newLB_facts (hG : GoodEnv P) (hok : ChordTriplesOK ztwiq zta L)
    (hperm : E.Perm ztct)
    (hsort : E.Pairwise ztbajl)
    (hli : li = true ↔ Mountain.LeftInside zta) :
    ChordTriplesOK ztwiq zta ztyhq ∧
      chords zta ⊆ famL ztwiq zta ztyhq := by
  zucm
  zuyq
  zubsy
  · rw [newLB_zero li zta E hK]
    zuhej

    rw [List.nil_append]
    exact ⟨newL0_ok hQ hDH hli, newL0_full hQ hDH hli⟩
  · rw [newLB_pos li zta E by_omega]
    zunh
    have B : ztziy := ⟨hQ, hDH, hok, hperm, hsort, by_omega,
      ⟨hRC, hCS, hAO, hRO⟩, hli⟩
    exact ⟨newL_ok B, newL_full B⟩
end sizes

/-! ## Counts and costs -/

/-- (I3) as a bound: `K ≤ cnt (2^p + 1)`. -/
theorem count_le {K c p b : ℕ} (h : K * 2 ^ b ≤ c * ztele) : K ≤ c * zteld := by
  have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have h2 : c * ztele ≤ c * zteld * 2 ^ b := by
    have : 2 ^ p + 2 ^ b ≤ zteld * 2 ^ b := by
      have : 2 ^ p ≤ 2 ^ p * 2 ^ b := Nat.le_mul_of_pos_right _ by_omega
      grind
    calc c * ztele ≤ c * (zteld * 2 ^ b) := Nat.mul_le_mul_left _ this
      _ = c * zteld * 2 ^ b := by_ring
  exact Nat.le_of_mul_le_mul_right (h.trans h2) by_omega

/-- A count below the threshold is at most the sum of the counts below it. -/
theorem cnt_le_sum (cnt : ℕ → ℕ) {Λ lam : ℕ} (h : lam < Λ) :
    cnt lam ≤ ∑ i ∈ Finset.range Λ, cnt i :=
  Finset.single_le_sum (f := cnt) (fun _i _ => Nat.zero_le _) (Finset.mem_range.2 h)
theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-- **The cost constant of the top level.** -/
def topK (κR κS κD κB Cc Γ : ℕ) : ℕ :=
  κR * ztgcl * ztjfx * ztoks + κS * ztdkp * ztgck +
    (κD + κB) * ztcsm + 40
theorem topK_ge {κR κS κD κB Cc Γ : ℕ} (h : 1 ≤ κS) : 20 * Γ + 73 ≤ topK κR κS κD κB Cc Γ := by
  unfold topK
  have h1 : 1 ≤ κS * ztdkp := Nat.mul_le_mul h (by omega : 1 ≤ 9 * Cc + 2)
  have h2 : 20 * Γ + 33 ≤ κS * ztdkp * ztgck := Nat.le_mul_of_pos_left _ by_omega
  omega

/-- **The total cost is linear.** -/
theorem top_cost {n K K₂ A K' S₀ Cm Mb Cc Γ κR κS κD κB : ℕ} (hK : K ≤ Cc * (2 * n + 3))
    (hK₂ : K₂ ≤ 2 * n) (hA : A ≤ 2 * K + 1) (hK' : K' ≤ K + K₂) (hS₀ : S₀ ≤ 5 * Γ + 8)
    (hCm : Cm ≤ Γ + 2) (hMb : Mb ≤ 20 * Γ + 32) :
    16 * n + 30 + κR * ztbr * ztdto * ztdsy +
        κS * ztbdy * ztvg + κD * ztcte + κB * ztnlz ≤
      topK κR κS κD κB Cc Γ * ztkk := by
  have e : topK κR κS κD κB Cc Γ * ztkk =
      κR * ztzzy * ztjfx * ztoks +
        κS * ztzzh * ztgck + κD * ztxyv +
        κB * ztxyv + 40 * ztkk := by
    unfold topK; ring
  have hX1 : K + 1 ≤ ztgcl * ztkk := by
    grind
  have hX2 : K + K₂ + A + 1 ≤ ztdkp * ztkk := by
    grind
  have hX3 : K + K₂ + 1 ≤ ztcsm * ztkk := by
    grind
  have hX4 : K' + 1 ≤ ztcsm * ztkk := by_omega
  have t1 : κR * ztbr * ztdto * ztdsy ≤
      κR * ztzzy * ztjfx * ztoks :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hX1) by_omega) by_omega
  have hcl : Nat.clog 2 Mb + 1 ≤ 20 * Γ + 33 := by have := clog_le_self Mb; omega
  have t2 : κS * ztbdy * ztvg ≤
      κS * ztzzh * ztgck :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hX2) hcl
  have t3 : κD * ztcte ≤ κD * ztxyv := Nat.mul_le_mul_left _ hX3
  have t4 : κB * ztnlz ≤ κB * ztxyv := Nat.mul_le_mul_left _ hX4
  omega
