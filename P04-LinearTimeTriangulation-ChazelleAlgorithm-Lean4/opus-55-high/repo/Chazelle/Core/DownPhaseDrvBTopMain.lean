module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.DownPhaseDrvRPlB
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.DownPhaseRegionBox
public import Chazelle.Core.DownPhaseMathHR1
public import Chazelle.Core.DownPhaseTransWt
public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.UpPhase15
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.SweepIoHoles
public import Chazelle.Core.RestoreTestOK
public import Chazelle.Core.GranInitL3

namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK BuildRam
open BuildNF (codeLe)
open SortL (seg)
open Chazelle.Visibility (chords)
open BTop
@[expose] public section
variable {X : MemCtx} {cnt : ℕ → ℕ} {n₀ : ℕ}
set_option maxHeartbeats 64000000 in
/-- **The top level of the base case meets `DrvR.BaseSpec`.** -/
theorem baseSpec_of (hRL : RegLoopSpec)
    (hDA : DropAugSpec) (hBS : BuildNFSortedSpec) : DrvR.BaseSpec X cnt n₀ := by
  obtain ⟨sR, κR, hsR⟩ := hRL
  obtain ⟨sD, κD, hsD⟩ := hDA
  obtain ⟨sB, κB, hsB⟩ := hBS
  obtain ⟨Λ, hΛ⟩ : ∃ x, x = max 16 (n₀ + 1) := by_grind
  obtain ⟨Γ, hΓ⟩ : ∃ x, x = 2 ^ (Λ + 12) := by_grind
  obtain ⟨Cc, hCc⟩ : ∃ x, x = ∑ i ∈ Finset.range Λ, cnt i := by_grind
  obtain ⟨κT, hκT⟩ : ∃ x, x = topK κR (DrvR.κSpl κB) κD κB Cc Γ := by_grind
  refine ⟨topS sR sD sB, κT, ?_⟩
  zubgq
  zuewb
  obtain ⟨hE, lam, hlamp, hlam, hInv⟩ := hpre
  obtain ⟨hG, -, hWh, -, -, -⟩ := hE
  obtain ⟨hD6, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW, hdeg, hwt, hcnt⟩ := hInv
  zutz
  -- the polygon
  zurr
  zubp
  zufvx
  zukas
  have hGM : ztebh := Or.inr ztini
  -- the level and the constants
  have h16 : 16 ≤ Λ := by_omega
  have hn0 : n₀ + 1 ≤ Λ := by_omega
  have hlΛ : lam < Λ := by have := topGrade_le' P.n; omega
  have hγΓ : 2 ^ ztcle ≤ Γ := by
    rw [hΓ]; exact Nat.pow_le_pow_right by_norm_num (by have := Cost.ceilBeta_le lam; omega)
  have hKc : L.length ≤ Cc * (2 * P.n + 3) := by
    have h1 := count_le hcnt
    have h2 : cnt lam ≤ Cc := by rw [hCc]; exact cnt_le_sum cnt hlΛ
    have h3 : 2 ^ topGrade P.n ≤ 2 * P.n := Setup.pow_topGrade_le by_omega
    exact h1.trans (Nat.mul_le_mul h2 by_omega)
  have hκTge : 20 * Γ + 73 ≤ κT := by rw [hκT]; exact topK_ge (by unfold DrvR.κSpl; omega)
  have hκTn : κT ≤ κT * ztju := by_grind
  -- the facts of the level
  have hMD0 := hDa.holds
  have hli : liBit c.nmem _ = true ↔ Mountain.LeftInside _ := liBit_iff hMD0
  obtain ⟨hS, hC0, hCm⟩ := reg_sizes (γ := 2 ^ ztcle) hG hok hperm hsort hdeg
    hwt hli
  obtain ⟨hok', hfull⟩ := newLB_facts hG hok hperm hsort hli
  zubcn
  have hAle := DrvD.arcs_length_le (M := interiorModel zta) (Q := Qof P) hElen
  have hH7 := (Gran.nf_areas hNW).1
  generalize hγ : 2 ^ ztcle = γ at hS hC0 hCm hγΓ
  -- 1. `B₂ := ALLOC`
  obtain ⟨c₁, k₁, e₁, hk₁, a19, a01, a02, a03, f₁⟩ := tPre_exec (P := P) c hw by_omega
  zuepx
  zucfz
  zuesu
  -- 2. the reservation
  have T₁ := top_cost (K₂ := 0) (A := 0) (K' := 0) (S₀ := 5 * γ + 8)
    (Cm := γ + 2) (Mb := 0) (Γ := Γ) (κR := κR) (κS := DrvR.κSpl κB) (κD := κD)
    (κB := κB) hKc by_omega by_omega by_omega by_omega by_omega by_omega
  rw [← hκT] at T₁
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, f₂, RF₂⟩ := tRes_exec (P := P) e₁.wb_right a03 a02 a01
    by_omega ztm
  zugbn
  zucgb
  have m₂ : ztckc := by zunoe
  have K2 : ∀ r, 210000 ≤ r → r < 210030 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g₂ r (bres_false by_omega by_omega), g₁ r (bpre_false by_omega by_omega)]
  have B19 : c₂.nreg 212019 = c.nreg ALLOC := by
    rw [g₂ _ (bres_false by_norm_num by_norm_num), a19]
  -- 3. the region loop
  have hMD₂ : ModelDescAt c₂.nmem ztvmw zta ztwiq := by
    zunvb; omega
  have hli₂ : liBit c₂.nmem ztvmw = liBit c.nmem ztvhw := by
    zunvb
  have hpre₂ : RegPre P W c₂ L E ztpul ztufc := by
    refine ⟨hG, hWh, by rw [K2 210003 by_norm_num by_norm_num]; exact hK, hok, hperm, hsort, hdeg,
      ?_, hMD₂, ?_, ?_, ?_, hC0, hCm⟩
    · rw [m₂, K2 210005 by_norm_num by_norm_num, B19]; omega
    · rw [K2 210001 by_norm_num by_norm_num, B19]; omega
    · omega
    · intro r hr; rw [hli₂]; exact hS r hr
  obtain ⟨c₃, k₃, e₃, hk₃, post₃, RF₃⟩ := hsR P W c₂ L E ztpul ztufc e₂.wb_right hpre₂
    by_omega
  obtain ⟨pk, pkB, pcnt, plen, plist, pbkle, pmono, pbcnt, pmx⟩ := post₃
  rw [hli₂] at pcnt plen plist pbkle pmono pbcnt
  rw [B19] at plist pbkle pmono pbcnt RF₃
  generalize hL₂ : newLB _ _ L E = L₂
    at pcnt plen plist pbkle pmono pbcnt hok' hfull
  have hlow3 : ztblg := fun a ha => by
    rw [RF₃.2.2.1 a ha, m₂]
  have A₃ := RF₃.2.2.2.2.2.1
  have A₃' := RF₃.2.2.2.2.2.2
  have K3 : ∀ r, 210000 ≤ r → r < 210030 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [pk r h1 h2, K2 r h1 h2]
  have hW3 := e₃.wb_right.1 ALLOC
  -- 4. the arguments of the splice
  obtain ⟨c₄, k₄, e₄, hk₄, s20, s21, s22, s23, s24, f₄⟩ := tArgs_exec (P := P) c₃ e₃.wb_right
    (B₂ := c.nreg ALLOC) (H := c.nreg 210005) (MX := c₃.nreg 212018) (K₂ := L₂.length)
    by_omega (K3 _ by_norm_num by_norm_num) rfl pcnt by_omega
    by_omega by_omega
  zudna
  have m₄ := f₄.2.2.1
  have A₄ : ztmvk := g₄ _ by_decide
  have K4 : ∀ r, 210000 ≤ r → r < 210020 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g₄ r (bargs_false by_omega by_omega), K3 r h1 by_omega]
  have hlow4 : ztjbc := fun a ha => by
    rw [m₄, hlow3 a ha]
  have s23' : c₄.nreg 210023 =
      (BuildNF.buildNF ztwiq zta L E).arcs.length := by
    rw [s23, hlow3 _ by_omega]; exact hNW.holds.2.1
  have hMD₄ : ModelDescAt c₄.nmem _ _ _ :=
    hDa c₄.nmem hlow4
  -- 5. the splice
  have T₂ := top_cost (K' := 0)
    (S₀ := 5 * γ + 8) (Cm := γ + 2) (Mb := 4 * c₃.nreg 212018) (Γ := Γ) (κR := κR)
    (κS := DrvR.κSpl κB) (κD := κD) (κB := κB) hKc plen hAle by_omega by_omega by_omega
    by_omega
  rw [← hκT] at T₂
  have hspl : DrvR.splCost κB c₄ = DrvR.κSpl κB * (L.length + L₂.length +
      (BuildNF.buildNF ztwiq zta L E).arcs.length + 1) *
      ztkqf := by
    unfold DrvR.splCost
    zuju
    rw [K4 210003 by_norm_num by_norm_num, hK, s21, s23', s24]
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨keepS, postS⟩, F₅⟩ := DrvR.splice_meets hsB P W c₄ e₄.wb_right
    ⟨hG, hWh, by
      show ModelDescWF P _ c₄.nmem ztqkp
      zunju; exact descWF_int hMD₄ by_omega,
      interiorModel zta, L, L₂, E, by
      show ModelDescAt c₄.nmem ztqkp _ _
      zunju; omega, hGM, by
      show c₄.nreg 210003 = _; zuodh; exact hK, by
      show c₄.nreg 210002 + 3 * L.length ≤ c₄.nreg ALLOC
      zunjv; omega, by
      show ChordListAt c₄.nmem ztvnq L
      zunjv; exact hLa c₄.nmem hlow4, by
      show c₄.nreg 210021 = _; omega, by
      show c₄.nreg 210020 + 3 * L₂.length ≤ c₄.nreg ALLOC
      omega, by
      show ChordListAt c₄.nmem ztvnr L₂
      zuoiw; omega, hok', by
      show c₄.nreg 210004 + 2 * L.length ≤ c₄.nreg ALLOC
      zuodi; omega, by
      show seg c₄.nmem (c₄.nreg 210004) _ = E
      zuodi; exact hEa c₄.nmem hlow4, hperm, hsort, by
      show c₄.nreg 210022 + 2 * L₂.length ≤ c₄.nreg ALLOC
      omega, fun q hq => by
      show c₄.nmem ztlmp ≤ c₄.nreg 210023
      rw [s22, s23', m₄]; exact pbkle q hq, fun q q' hq hq' hb => by
      refine pmono q q' hq hq' ?_
      have e1 : DrvR.bkOf c₄ q = c₃.nmem ztmgr := by
        show c₄.nmem ztlmp = _; zunog
      have e2 : DrvR.bkOf c₄ q' = c₃.nmem (c.nreg ALLOC + 6 * P.n + q') := by
        show c₄.nmem (c₄.nreg 210022 + q') = _; zunog
      omega, fun b => by
      show DrvR.bcnt _ _ b ≤ c₄.nreg 210024
      rw [s24]
      have e : DrvR.bkOf c₄ = fun q => c₃.nmem ztmgr := by
        funext q; show c₄.nmem ztlmp = _; zunog
      zvmwe; exact pbcnt b⟩
    (by show c₄.nreg ALLOC + DrvR.splCost κB c₄ ≤ W; omega)
  obtain ⟨p3, p2l, p2b, p2, p4l, p4b, pperm, psort, p5l, pNW⟩ := postS ztwiq L L₂
    (by show ModelDescAt c₄.nmem ztqkp _ _
        zunju; omega)
    (by show c₄.nreg 210003 = _; zuodh; exact hK)
    (by show ChordListAt c₄.nmem ztvnq L
        zunjv; exact hLa c₄.nmem hlow4)
    (by show c₄.nreg 210021 = _; omega)
    (by show ChordListAt c₄.nmem ztvnr L₂; zuoiw; omega)
  zufl

  have hk₅' : k₅ ≤ DrvR.κSpl κB * (L.length + L₂.length +
      (BuildNF.buildNF ztwiq zta L E).arcs.length + 1) *
      ztkqf := by rw [← hspl]; omega
  have A₅ := F₅.2.2.2.2.2.1
  have A₅' := F₅.2.2.2.2.2.2
  have hlow5 : ztjbd := fun a ha => by
    rw [F₅.2.2.1 a by_omega, hlow4 a ha]
  have r51 : c₅.nreg 210001 = c.nreg 210001 := by
    rw [keepS 210001 by_omega, K4 210001 by_norm_num by_norm_num]
  zujzl
  -- 6. the arguments of `dropAug`
  obtain ⟨c₆, k₆, e₆, hk₆, d00, d01, d02, d03, f₆⟩ := tDrop_exec (P := P) c₅ e₅.wb_right
  have g₆ : ∀ r, decide _ = false → c₆.nreg r = c₅.nreg r := f₆.1
  have m₆ := f₆.2.2.1
  zuhvl
  -- 7. `dropAug`
  obtain ⟨c₇, k₇, e₇, hk₇, postD, F₇⟩ := hsD P W c₆ e₆.wb_right
    ⟨hG, hWh, by
      show c₆.nreg 200000 + 2 ≤ c₆.nreg ALLOC
      rw [d00, r51, A₆]; omega, by
      show c₆.nmem (c₆.nreg 200000 + 1) = 1 ↔ Mountain.LeftInside _
      rw [d00, r51, m₆, hlow5 _ by_omega]; exact (desc_int hMD0).2,
      L ++ L₂, by
      show c₆.nreg 200002 = _; omega, by
      show c₆.nreg 200001 + 3 * (L ++ L₂).length ≤ c₆.nreg ALLOC
      omega, by
      show ChordListAt c₆.nmem ztvoa _
      zuoix; exact p2, hok', by
      show c₆.nreg 200003 + 2 * (L ++ L₂).length ≤ c₆.nreg ALLOC
      omega, by
      show (seg c₆.nmem ztvob _).Perm
        _
      zunyc; omega, by
      show (seg c₆.nmem ztvob _).Pairwise
        _
      zunyc; omega⟩
    (by show c₆.nreg ALLOC + κD * (c₆.nreg 200002 + 1) ≤ W
        rw [d02, p3, A₆]; omega)
  obtain ⟨d4l, d4b, dCL, d5, d6l, d6b, dseg, dfam, dok, dperm, dsort⟩ := postD ztfi
    (by show c₆.nreg 200002 = _; omega)
    (by show ChordListAt c₆.nmem ztvoa _; zuoix; exact p2)
  zvnhj at d4l d4b dCL d5 d6l d6b dseg
  zvnhj at dfam dok dperm dsort
  have hKLlen : (DownBase.keepL (liBit c₆.nmem (c₆.nreg 200000)) (Qof P).n ztfi).length ≤
      L.length + L₂.length := by
    rw [← hLL]; unfold DownBase.keepL; exact List.length_filter_le _ _
  have hk₇' : k₇ ≤ κD * ztpzj := by
    have h := hk₇
    zvnhj at h
    rw [d02, p3] at h; exact h
  generalize hKL : DownBase.keepL _ (Qof P).n _ = KL
    at d4b dCL d5 d6b dseg dfam dok dperm dsort hKLlen
  generalize hDE : DownBase.dropE _ (Qof P).n _
    _ = DE
    at dseg dperm dsort
  have A₇ := F₇.2.2.2.2.2.1
  have A₇' := F₇.2.2.2.2.2.2
  have hlow7 : ∀ a, a < c.nreg ALLOC → c₇.nmem a = c.nmem a := fun a ha => by
    rw [F₇.2.2.1 a by_omega, m₆, hlow5 a ha]
  have r71 : c₇.nreg 210001 = c.nreg 210001 := by
    rw [F₇.1 _ by_decide by_decide, g₆ _ by_decide, r51]
  -- 8. the arguments of `buildNFSorted`
  obtain ⟨c₈, k₈, e₈, hk₈, b00, b01, b02, b04, f₈⟩ := tBld_exec (P := P) c₇ e₇.wb_right
  have g₈ : ∀ r, decide _ = false → c₈.nreg r = c₇.nreg r := f₈.1
  have m₈ := f₈.2.2.1
  have A₈ : ztshs := g₈ _ by_decide
  have hlow8 : ∀ a, a < c.nreg ALLOC → c₈.nmem a = c.nmem a := fun a ha => by
    rw [m₈, hlow7 a ha]
  have hMD₈ : ModelDescAt c₈.nmem _ _ _ :=
    hDa c₈.nmem hlow8
  -- 9. `buildNFSorted`
  have T₃ := top_cost
    (S₀ := 5 * γ + 8) (Cm := γ + 2) (Mb := 4 * c₃.nreg 212018) (Γ := Γ) (κR := κR)
    (κS := DrvR.κSpl κB) (κD := κD) (κB := κB) hKc plen hAle hKLlen by_omega by_omega
    by_omega
  rw [← hκT] at T₃
  obtain ⟨c₉, k₉, e₉, hk₉, postB, F₉⟩ := hsB P W c₈ e₈.wb_right
    ⟨hG, hWh, by
      show ModelDescWF P _ c₈.nmem ztqkv
      zunoh; exact descWF_int hMD₈ by_omega,
      interiorModel zta, KL, DE, by
      show ModelDescAt c₈.nmem ztqkv _ _
      zunoh; omega, hGM, by
      show c₈.nreg 40002 = _; omega, by
      show c₈.nreg 40001 + 3 * KL.length ≤ c₈.nreg ALLOC
      omega, by
      show ChordListAt c₈.nmem ztvof KL
      zuoiy; omega, dok, by
      show c₈.nreg 40004 + 2 * KL.length ≤ c₈.nreg ALLOC
      omega, by
      show seg c₈.nmem (c₈.nreg 40004) _ = DE
      rw [b04, m₈]; omega, dperm, dsort⟩
    (by show c₈.nreg ALLOC + κB * (c₈.nreg 40002 + 1) ≤ W
        rw [b02, d5, A₈]; omega)
  obtain ⟨b3l, bNW, bNF, -, -⟩ := postB ztwiq KL
    (by show ModelDescAt c₈.nmem ztqkv _ _
        zunoh; omega)
    (by show c₈.nreg 40002 = _; omega)
    (by show ChordListAt c₈.nmem ztvof KL; zuoiy; omega)
  have hk₉' : k₉ ≤ κB * (KL.length + 1) := by
    have h := hk₉
    zubmp
    rw [b02, d5] at h; exact h
  -- 10. the output
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, o06, f₁₀⟩ := tOut_exec (P := P) c₉ e₉.wb_right
  have m₁₀ := f₁₀.2.2.1
  have A₁₀ : c₁₀.nreg ALLOC = c₉.nreg ALLOC := f₁₀.1 _ by_decide
  -- frames
  have RF₁ : ztzjd := DrvD.rf_of_frameB inDrv_pre f₁
  have RF₄ : Restore.RF DrvR.drvBands ztm c₃ c₄ k₄ := DrvD.rf_of_frameB inDrv_args f₄
  have RF₅ : Restore.RF DrvR.drvBands ztm c₄ c₅ k₅ :=
    (Restore.RF.of_frame F₅ by_omega).mono DrvD.splBands_sub le_rfl
  have RF₆ : Restore.RF DrvR.drvBands ztm c₅ c₆ k₆ := DrvD.rf_of_frameB inDrv_drop f₆
  have RF₇ : Restore.RF DrvR.drvBands ztm c₆ c₇ k₇ :=
    (Restore.RF.of_frame F₇ by_omega).mono by_decide le_rfl
  have RF₈ : Restore.RF DrvR.drvBands ztm c₇ c₈ k₈ := DrvD.rf_of_frameB inDrv_bld f₈
  have RF₉ : Restore.RF DrvR.drvBands ztm c₈ c₉ k₉ :=
    (Restore.RF.of_frame F₉ by_omega).mono by_decide le_rfl
  have RF₁₀ : Restore.RF DrvR.drvBands ztm c₉ c₁₀ k₁₀ :=
    DrvD.rf_of_frameB (DrvD.inDrv_eq by_norm_num by_norm_num
      by_decide) f₁₀
  have RFall := RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans (RF₅.trans (RF₆.trans (RF₇.trans
    ztqcj))))))
  refine ⟨c₁₀, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + ztjzt))))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆ (Exec.seq e₇
      (Exec.seq e₈ (Exec.seq e₉ e₁₀)))))))), ?_, ?_, RFall⟩
  · show _ ≤ κT * ztju
    omega
  · refine ⟨_, ?_, bNF, ?_⟩
    · show Robust _ c₁₀.nmem (fun m => NFAt m (c₁₀.nreg 210006) _)
      rw [A₁₀, m₁₀, o06]; exact bNW
    · rw [F_build]
      exact dfam.trans (Set.inter_eq_right.2 hfull)

/-- **The base case from the region loop** (with `dropAug` and `buildNFSorted`). -/
theorem baseSpec_of_regLoop (hRL : RegLoopSpec) :
    DrvR.BaseSpec X cnt n₀ :=
  baseSpec_of hRL DownBase.dropAug buildNFSorted
end
end DrvB
namespace DrvLM
@[expose] public section
open DrvR (regHost walkItems arcItems runItems runCnt atVtx ptI)
open BuildNF (codeLe wposOf gapStarts)

/-! ## Item counts -/
theorem runItems_length (li : Bool) (n : ℕ) (s e : WPos) : (runItems li n s e).length ≤ 1 := by
  zulcc
theorem arcItems_length (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) :
    (arcItems li n N r jp j).length ≤ 4 := by
  zumrp
  have := runItems_length li n (N.arc j).s (N.arc j).e
  grind
theorem walkItems_length (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (walkItems li n N r).length ≤ 4 * (N.region r).arcs.length := by
  unfold walkItems
  zugtt
  have : ∀ x ∈ (List.range (N.region r).arcs.length).map (fun t => (arcItems li n N r
      ztml ((N.region r).arcs.getD (ztbx %
        (N.region r).arcs.length) 0)).length), x ≤ 4 := by
    zuh
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
    exact arcItems_length _ _ _ _ _ _
  have h := List.sum_le_length_nsmul _ 4 this
  simp only [List.length_map, List.length_range, smul_eq_mul] at h
  omega
theorem regHost_length (li : Bool) (n : ℕ) (N : NF) (r : ℕ) :
    (regHost li n N r).length ≤ 4 * (N.region r).arcs.length := by
  unfold regHost
  split_ifs
  · exact walkItems_length _ _ _ _
  · rw [List.length_reverse]; exact walkItems_length _ _ _ _

/-! ## Runs -/
theorem run_mem_runItems {li : Bool} {n : ℕ} {s e : WPos} {a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ runItems li n s e) : runCnt li n s e ≠ 0 ∧ ℓ = runCnt li n s e - 1 := by
  unfold runItems at h
  grind
theorem run_mem_arcItems {li : Bool} {n : ℕ} {N : NF} {r jp j a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ arcItems li n N r jp j) :
    runCnt li n (N.arc j).s (N.arc j).e ≠ 0 ∧ ℓ = runCnt li n (N.arc j).s (N.arc j).e - 1 := by
  unfold arcItems at h
  simp only [List.mem_append, List.mem_singleton] at h
  rcases h with ((h | h) | h) | h
  · split_ifs at h with h'
    · simp_all
    tauto
  · tauto
  · exact run_mem_runItems h
  tauto

/-- A run of the host comes from an arc of the region. -/
theorem run_mem_regHost {li : Bool} {n : ℕ} {N : NF} {r a ℓ : ℕ}
    (h : HostItem.run a ℓ ∈ regHost li n N r) :
    ∃ j ∈ (N.region r).arcs,
      runCnt li n (N.arc j).s (N.arc j).e ≠ 0 ∧ ℓ = runCnt li n (N.arc j).s (N.arc j).e - 1 := by
  have hw : HostItem.run a ℓ ∈ walkItems li n N r := by
    unfold regHost at h
    grind
  unfold walkItems at hw
  obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.1 hw
  zudtp
  refine ⟨_, ?_, run_mem_arcItems hmem⟩
  have hk : ztbx % (N.region r).arcs.length < (N.region r).arcs.length :=
    Nat.mod_lt _ by_omega
  simp_all
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point} {li : Bool}

/-- **The run of an arc has at most `γ + 1` walk vertices.** -/
theorem runCnt_le (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ztwjn γ) {j : ℕ}
    (hj : j ∈ ((BuildNF.buildNF ztd Q L E).region r).arcs)
    (hne : runCnt li Q.n ((BuildNF.buildNF ztd Q L E).arc j).s
      ((BuildNF.buildNF ztd Q L E).arc j).e ≠ 0) :
    runCnt li Q.n ((BuildNF.buildNF ztd Q L E).arc j).s
      ((BuildNF.buildNF ztd Q L E).arc j).e ≤ γ + 1 := by
  zugyj
  have hac := DrvB.arcCnt_le B hr hwt hj
  obtain ⟨hjA, -⟩ := (B.hregs.2.2.1.2.2.2 r hr j).1 hj
  zudz
  zuur
  zukct
  obtain ⟨sn, s0, s1⟩ := DrvB.evPos_ok B ztuxq
  obtain ⟨en, e0, e1⟩ := DrvB.evPos_ok B ztwxs
  zuckd

  obtain ⟨-, hpe⟩ := DownMath.arc_pos B.hQ B.hL B.hperm B.hsort B.hK hjA
  have hNF := (BuildNF.isNF_goodModel ztgek B.hL B.hperm B.hsort).1
  have hvtx := DownMath.atVtx_iff hNF B.hdh B.hli hpe
  unfold DrvB.arcCnt at hac
  unfold runCnt at hne ⊢
  generalize hsg : (N.arc j).s = s at *
  generalize heg : (N.arc j).e = e at *
  zukic
  zukib
  by_cases hv : atVtx li Q.n e = true
  · rw [ite_eq_left hv] at hne ⊢
    by_cases hxy : s.edge < e.edge
    · rw [show e.edge + 0 + Q.n - 1 - s.edge = (e.edge - s.edge - 1) + Q.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
      rw [show e.edge + Q.n - s.edge = ztnxt + Q.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt by_omega] at hac
      omega
    by_cases hyx : e.edge < s.edge
    · zuey
      zvmyc at hac
      omega
    · -- the degenerate case: both ends on one walk edge, the end at its start vertex
      exfalso
      have hxe : s.edge = e.edge := by_omega
      have hk : (interiorModel Q).key Q e = (e.edge : ℝ) := by
        have h1 := hvtx.1 hv
        rw [kb, DownHost.floor_add e0 e1] at h1
        simp_all
      by_cases hlast : j + 1 < (gapStarts ztd Q L E).length
      · have hlt := DrvD.key_s_lt_e (M := interiorModel Q) (Q := Q) B.hK hE hlast
        grind
      · have hne' := DrvB.last_arc_edges B
        grind
  grind

/-- The host has as many points as the region has host keys. -/
theorem pts_length (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions) :
    ((regHost li Q.n ztwjp r).pts Q.n).length =
      DownHost.nk ztd
        ztwjn ztcz := by
  zudqn
  zumld
  grind

/-- **The sizes of a region host** (degree `≤ 4`, weight `≤ γ`). -/
theorem host_facts (B : DrvB.BaseCtx Q L E reg li) {r : ℕ}
    (hr : r < (BuildNF.buildNF ztd Q L E).nRegions)
    (hdeg : (interiorModel Q).DegLe
      ztwjn 4) {γ : ℕ}
    (hwt : (interiorModel Q).Semigranular
      ztwjn γ) :
    (regHost li Q.n ztwjp r).length ≤ 20 ∧
      (∀ a ℓ, HostItem.run a ℓ ∈ regHost li Q.n ztwjp r →
        ℓ ≤ γ) ∧
      3 ≤ ((regHost li Q.n ztwjp r).pts Q.n).length ∧
      ((regHost li Q.n ztwjp r).pts Q.n).length ≤
        5 * γ + 8 := by
  zudnv
  have hd : (interiorModel Q).deg ztwjn
      ztcz ≤ 4 := hdeg _ hR
  have hnA := DrvB.arcs_length_le B hr
  refine ⟨?_, fun a ℓ h => ?_, ?_, ?_⟩
  · have := regHost_length li Q.n ztwjp r
    omega
  · obtain ⟨j, hj, hne, rfl⟩ := run_mem_regHost h
    have := runCnt_le B hr hwt hj hne
    omega
  · rw [pts_length B hr]
    have hne : ((BuildNF.buildNF ztd Q L E).F ztd Q).Nonempty := by
      refine ⟨((BuildNF.buildNF ztd Q L E).chord 0).toSet ztd Q,
        (BuildNF.buildNF ztd Q L E).chord 0, ?_, rfl⟩
      zudly
      have h0 : 0 < (BuildNF.buildNF ztd Q L E).chords.length := by
        zuova; exact B.hK
      simp_all
    exact DownHost.three_le_nk B.hQ B.fam hne hR
  · have h1 := DrvB.regPts_length_le B hr hwt
    rw [DrvB.regPts, DrvB.wlist_length] at h1
    have h2 : ((interiorModel Q).deg ((BuildNF.buildNF ztd Q L E).F
        ztd Q) (reg r) + 1) * γ ≤ 5 * γ :=
      Nat.mul_le_mul_right _ by_omega
    omega
end
end DrvLM
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLM
@[expose] public section
open DrvR (keyBkt OnArcKey)
open BuildNF (codeLe wposOf gapStarts)
open Chazelle.Chain (sideInArc)

/-! ## Buckets and keys -/
theorem keyBkt_le (Q : Polygon) (N : NF) (x : WPos) : keyBkt Q N x ≤ 2 * N.arcs.length + 1 := by
  unfold keyBkt
  have := List.length_filter_le (fun j => decide ((interiorModel Q).key Q (N.arc j).s <
    (interiorModel Q).key Q x)) (List.range N.arcs.length)
  rw [List.length_range] at this
  zuwd

/-- Filtering a range by a stronger predicate, with a witness, is shorter. -/
theorem filter_range_lt {p p' : ℕ → Bool} (hpp : ∀ i, p i = true → p' i = true) {A j : ℕ}
    (hj : j < A) (hj1 : p' j = true) (hj0 : p j = false) :
    ((List.range A).filter p).length < ((List.range A).filter p').length := by
  induction A with
  | zero => omega
  | succ A ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append,
      List.length_append]
    have hle : ((List.range A).filter p).length ≤ ((List.range A).filter p').length :=
      (List.monotone_filter_right _ by_omega).length_le
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · grind
    · simp_all
theorem keyBkt_mono (Q : Polygon) (N : NF) {x y : WPos}
    (h : (interiorModel Q).key Q y ≤ (interiorModel Q).key Q x) :
    keyBkt Q N y ≤ keyBkt Q N x := by
  classical
  rcases lt_or_eq_of_le h with h | h
  · unfold keyBkt
    have hle : ((List.range N.arcs.length).filter fun j =>
          decide ztflx).length ≤
        ((List.range N.arcs.length).filter fun j =>
          decide ztblk).length :=
      (List.monotone_filter_right _ (fun {i} hi => by
        grind)).length_le
    by_cases hex : ∃ j, j < N.arcs.length ∧
        (interiorModel Q).key Q (N.arc j).s = (interiorModel Q).key Q y
    · obtain ⟨j, hj, hjy⟩ := hex
      have hlt := filter_range_lt
        (p := fun j => decide ztflx)
        (p' := fun j => decide ztblk)
        ztbmx hj
        by_simp_all by_simp_all
      rw [ite_eq_left by_grind]
      omega
    grind
  · unfold keyBkt; zvmwc

/-- **A smaller bucket means a smaller key.** -/
theorem key_lt_of_keyBkt_lt (Q : Polygon) (N : NF) {x y : WPos}
    (h : keyBkt Q N x < keyBkt Q N y) :
    (interiorModel Q).key Q x < (interiorModel Q).key Q y := by
  zux

  have := keyBkt_mono Q N hc
  omega

/-! ## Counting the ends of a bucket -/
section count
open DrvR (bcnt bfilt)
theorem bcnt_congr {bk bk' : ℕ → ℕ} {n b : ℕ} (h : ∀ q, q < n → bk q = bk' q) :
    bcnt bk n b = bcnt bk' n b := by
  zuluf
  zucr
  refine List.filter_congr fun q hq => ?_
  simp_all
theorem bcnt_le (bk : ℕ → ℕ) (n b : ℕ) : bcnt bk n b ≤ n := by
  zuluf
  grind
theorem bcnt_add (bk : ℕ → ℕ) (a c b : ℕ) :
    bcnt bk (a + c) b = bcnt bk a b + bcnt (fun q => bk zttei) c b := by
  induction c with
  | zero => simp [bcnt, bfilt]
  | succ c ih =>
    rw [← Nat.add_assoc, DrvR.bcnt_succ, ih, DrvR.bcnt_succ]
    zuwd

/-- The number of ends of `l` in bucket `b`. -/
noncomputable def cntB (Q : Polygon) (N : NF) (l : List zte) (b : ℕ) : ℕ :=
  bcnt (fun q => keyBkt Q N (DrvR.endPos l q)) (2 * l.length) b
theorem endPos_append_left {l₁ l₂ : List zte} {q : ℕ} (hq : q < 2 * l₁.length) :
    DrvR.endPos zthyu q = DrvR.endPos l₁ q := by
  unfold DrvR.endPos
  grind
theorem endPos_append_right (l₁ l₂ : List zte) (q : ℕ) :
    DrvR.endPos zthyu ztjfi = DrvR.endPos l₂ q := by
  have e2 : ztjfi / 2 = l₁.length + q / 2 := by_omega
  have e3 : ztjfi % 2 = q % 2 := by_omega
  unfold DrvR.endPos
  rw [e2, e3, List.getD_append_right _ _ _ _ by_omega, Nat.add_sub_cancel_left]
variable {Q : Polygon} {N : NF}
theorem cntB_nil (b : ℕ) : cntB Q N [] b = 0 := by_rfl
theorem cntB_append (l₁ l₂ : List zte) (b : ℕ) :
    cntB Q N zthyu b = cntB Q N l₁ b + cntB Q N l₂ b := by
  unfold cntB
  rw [List.length_append, Nat.mul_add, bcnt_add]
  zucr
  · exact bcnt_congr fun q hq => by simp only [endPos_append_left hq]
  · exact bcnt_congr fun q _ => by simp only [endPos_append_right]
theorem cntB_flatMap (Lx : ℕ → List zte) (R b : ℕ) :
    cntB Q N ztosc b = ∑ r ∈ Finset.range R, cntB Q N ztdyq b := by
  induction R with
  | zero => simp [cntB_nil]
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, cntB_append, ih, Finset.sum_range_succ]
    simp
theorem length_flatMap_range (Lx : ℕ → List zte) (R : ℕ) :
    ((List.range R).flatMap Lx).length = ∑ r ∈ Finset.range R, (Lx r).length := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]
    simp

/-- **A bucket fed by two regions** holds at most `4 M` ends. -/
theorem cntB_flat_le {Lx : ℕ → List zte} {R M b : ℕ} (rA rB : ℕ)
    (hM : ∀ r, r < R → (Lx r).length ≤ M)
    (hreg : ∀ r, r < R → ∀ q, q < 2 * (Lx r).length →
      keyBkt Q N ztztf = b → r = rA ∨ r = rB) :
    cntB Q N ztosc b ≤ 4 * M := by
  classical
  rw [cntB_flatMap]
  have hper : ∀ r ∈ Finset.range R, cntB Q N ztdyq b ≤
      (if r = rA then 2 * M else 0) + (if r = rB then 2 * M else 0) := by
    zuz
    zudtk
    by_cases hab : r = rA ∨ r = rB
    · have h1 : cntB Q N ztdyq b ≤ 2 * M := (bcnt_le _ _ _).trans by_simp_all
      grind
    · have h0 : cntB Q N ztdyq b = 0 := by
        unfold cntB bcnt bfilt
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        grind
      omega
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  zuwd
end count

/-! ## The order of the new codes -/

/-- The positions of the new event codes. -/
theorem wposOf_new' {L L₂ : List zte} {q : ℕ} (_hq : q < 2 * L₂.length) :
    wposOf ztfi ztbhj = DrvR.endPos L₂ q := by
  zuffd

  have hg : ztxsw := by
    grind
  unfold wposOf DrvR.endPos
  zuexi

/-- **Bucket order gives code order.** -/
theorem codeLe_of_keyBkt (Q : Polygon) (N : NF) {L L₂ : List zte} {q q' : ℕ}
    (hq : q < 2 * L₂.length) (hq' : q' < 2 * L₂.length)
    (h : keyBkt Q N ztnkn < keyBkt Q N (DrvR.endPos L₂ q')) :
    codeLe ztd Q ztfi ztbhj ztekx := by
  left
  rw [wposOf_new' hq, wposOf_new' hq']
  exact key_lt_of_keyBkt_lt Q N h

/-! ## The arcs of `buildNF` -/
section arcs
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- The key of the start of arc `i`. -/
noncomputable def st (Q : Polygon) (L : List zte) (E : List ℕ) (i : ℕ) : ℝ :=
  (interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc i).s

/-- Equal keys between gap starts. -/
theorem kE_const (hsort : E.Pairwise ztxnq) {a b : ℕ} (hab : a ≤ b)
    (hb : b < E.length)
    (hgap : ∀ m, a ≤ m → m < b → m ∉ gapStarts ztd Q L E) :
    DrvD.kE ztd Q L E a = DrvD.kE ztd Q L E b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have h1 := ih by_omega by_grind
    have hm := hgap b hab by_omega
    rw [DrvD.mem_gapStarts] at hm
    push Not at hm
    have h2 := (hm by_omega).2
    rw [DrvD.kap_evs by_omega, DrvD.kap_evs by_omega] at h2
    have h3 := DrvD.kE_mono hsort (show b ≤ b + 1 by omega) hb
    linarith

/-- A gap start index is some `gs k`. -/
theorem gs_of_mem {m : ℕ} (hm : m ∈ gapStarts ztd Q L E) :
    ∃ k, k < (gapStarts ztd Q L E).length ∧ DrvD.gs ztd Q L E k = m := by
  obtain ⟨k, hk, hkm⟩ := List.mem_iff_getElem.1 hm
  exact ⟨k, hk, by rw [DrvD.gs_eq hk]; omega⟩
theorem gs_strict {k k' : ℕ} (hk : k < (gapStarts ztd Q L E).length)
    (_hk' : k' < (gapStarts ztd Q L E).length)
    (h : DrvD.gs ztd Q L E k < DrvD.gs ztd Q L E k') : k < k' := by
  zux

  rcases lt_or_eq_of_le hc with hc | hc
  · have := DrvD.gs_lt_gs hc
      by_omega
    omega
  simp_all

/-! ## The bucket of a key -/
theorem len_filter_lt (c A : ℕ) :
    ((List.range A).filter fun i => decide zttpb).length = min A c := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : A < c
    · grind
    · grind

/-- The bucket of a key, from the number `c` of arc starts below it. -/
theorem keyBkt_eq {x : WPos} {A c : ℕ}
    (hA : (BuildNF.buildNF ztd Q L E).arcs.length = A) (hc : c ≤ A)
    (h : ∀ i, i < A → (st Q L E i < (interiorModel Q).key Q x ↔ i < c)) :
    ((∃ i, i < A ∧ st Q L E i = (interiorModel Q).key Q x) →
      keyBkt Q ztwjp x = 2 * c + 1) ∧
    ((¬ ∃ i, i < A ∧ st Q L E i = (interiorModel Q).key Q x) →
      keyBkt Q ztwjp x = 2 * c) := by
  classical
  subst hA
  have hf : ((List.range (BuildNF.buildNF ztd Q L E).arcs.length).filter fun j =>
      decide ((interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc j).s <
        (interiorModel Q).key Q x)) =
      (List.range (BuildNF.buildNF ztd Q L E).arcs.length).filter
        fun i => decide zttpb := by
    refine List.filter_congr fun i hi => ?_
    zucpm
    exact decide_eq_decide.2 (h i hi)
  have hm : min (BuildNF.buildNF _ Q L E).arcs.length c = c := Nat.min_eq_right hc
  constructor
  · zuibr

    rw [hf, len_filter_lt, hm, ite_eq_left hex]
  · zuibr

    rw [hf, len_filter_lt, hm, ite_eq_right hex, Nat.add_zero]

/-- The first arc of bucket `b` (`A` arcs). -/
def arcA (A b : ℕ) : ℕ := if b = 0 then A - 1 else zteow / 2

/-- The second arc of bucket `b`. -/
def arcB (A b : ℕ) : ℕ := if b ≤ 1 then A - 1 else zteow / 2 - 1
variable (hK : 0 < L.length) (hperm : E.Perm (List.range (2 * L.length)))
  (hsort : E.Pairwise ztxnq)
include hK hperm hsort
omit hK hperm hsort in
theorem hElen (hK : 0 < L.length) (hperm : E.Perm ztct)
    (_hsort : E.Pairwise ztxnq) : 0 < E.length := by zunoj; omega
variable {i i' : ℕ} {j : ℕ}
/-- **The arc starts increase strictly.** -/
theorem st_lt (hii : i < i') (hi' : i' < (BuildNF.buildNF ztd Q L E).arcs.length) :
    st Q L E i < st Q L E i' := by
  zulj

  zvmze at hi'
  unfold st
  rw [DrvD.key_s hK by_omega, DrvD.key_s hK hi']
  have h1 := DrvD.gs_succ (M := interiorModel Q) (Q := Q) (L := L) hE (j := i) by_omega
  have h2 := DrvD.gs_lt_gs hii hi'
  have h3 := DrvD.kE_mono hsort (show DrvD.gs ztd Q L E i + 1 ≤
    DrvD.gs _ Q L E i' by omega) (DrvD.gs_lt_len hi')
  grind
theorem st_le (hii : i ≤ i')
    (hi' : i' < (BuildNF.buildNF ztd Q L E).arcs.length) :
    st Q L E i ≤ st Q L E i' := by
  rcases lt_or_eq_of_le hii with h | h
  · exact (st_lt hK hperm hsort h hi').le
  · zuzx

/-- **An arc other than the last ends at the next start.** -/
theorem key_e_eq (hj : j + 1 < (BuildNF.buildNF ztd Q L E).arcs.length) :
    (interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc j).e = st Q L E ztl := by
  zulj

  zuksf
  unfold st
  rw [DrvD.key_e hK hE hj, DrvD.key_s hK hj]
  have h1 := DrvD.gs_succ hE hj
  have h2 := DrvD.gs_lt_gs
    ztmnz hj
  refine kE_const hsort by_omega ztpxf fun m hm1 hm2 hm => ?_
  zufys
  have := gs_strict by_omega hk (k := j) by_omega
  have := gs_strict hk hj hm2
  omega

/-- **The last arc ends at the first start.** -/
theorem key_e_last_eq :
    (interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc
      ztxbc).e = st Q L E 0 := by
  zulj

  obtain ⟨hA0, -⟩ := DrvD.gs_last (M := interiorModel Q) (Q := Q) (L := L) hE
  rw [hA, DrvD.key_e_last hK hE]
  unfold st
  rw [DrvD.key_s hK hA0]
  refine kE_const hsort ztbg (DrvD.gs_lt_len hA0) fun m _ hm2 hm => ?_
  zufys
  have := gs_strict hk hA0 hm2
  omega

/-- **Every bucket meets at most two arcs**: a position on the closure of arc `j` has a bucket
`b` with `j = arcA A b ∨ j = arcB A b`. -/
theorem arc_of_bkt {x : WPos}
    (hj : j < (BuildNF.buildNF ztd Q L E).arcs.length)
    (hx : OnArcKey Q ztwjp j x) :
    j = arcA (BuildNF.buildNF ztd Q L E).arcs.length
        ztbaqg ∨
      j = arcB (BuildNF.buildNF ztd Q L E).arcs.length
        ztbaqg := by
  have hlt : ∀ i i', i < i' → i' < (BuildNF.buildNF _ Q L E).arcs.length →
      st Q L E i < st Q L E i' := fun i i' h1 h2 => st_lt hK hperm hsort h1 h2
  have hle : ∀ i i', i ≤ i' → i' < (BuildNF.buildNF _ Q L E).arcs.length →
      st Q L E i ≤ st Q L E i' := fun i i' h1 h2 => st_le hK hperm hsort h1 h2
  have hks : (interiorModel Q).key Q ((BuildNF.buildNF _ Q L E).arc j).s =
      st Q L E j := rfl
  -- the end of arc `j`
  have hke : (j + 1 < (BuildNF.buildNF ztd Q L E).arcs.length →
      (interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc j).e =
        st Q L E ztl) ∧
      (j + 1 = (BuildNF.buildNF ztd Q L E).arcs.length →
      (interiorModel Q).key Q ((BuildNF.buildNF ztd Q L E).arc j).e =
        st Q L E 0) := by
    refine ⟨(key_e_eq hK hperm hsort), fun h => ?_⟩
    have : j = (BuildNF.buildNF ztd Q L E).arcs.length - 1 := by_omega
    zvmwk; exact key_e_last_eq hK hperm hsort
  unfold OnArcKey at hx
  rw [hks] at hx
  generalize hA : (BuildNF.buildNF _ Q L E).arcs.length = A at hlt hle hke hj ⊢
  have hkb := fun c (hc : c ≤ A) h => keyBkt_eq (x := x) hA hc h
  zuebu
  · -- the start of arc `j`
    have := (hkb j hj.le by_grind).1 by_grind
    left; zvmwk; unfold arcA; simp
  · zuidj
    · zujjd
      have := (hkb _ hj1.le by_grind).1 by_grind
      right; zvmwk; unfold arcB; simp
    · zujje
      have := (hkb 0 ztbg (fun i hi => ⟨fun h => by
          have := hle 0 i by_omega hi; linarith, by_grind⟩)).1 by_grind
      right; zvmwk; unfold arcB; grind
  · zuidj
    · zujjd
      zuhba
      rw [ite_eq_left by_grind] at hx
      have := (hkb _ hj1.le (fun i hi => ⟨fun h => by
          grind,
        fun h => by_grind⟩)).2 (by
          grind)
      zucnk
    · zujje
      zuhba
      rw [ite_eq_right (by have := hle 0 j by_omega hj; linarith)] at hx
      zuky
      · have := (hkb A le_rfl (fun i hi => ⟨by_omega,
          fun _ => by have := hle i j by_omega hj; linarith⟩)).2 (by
            zuecn
            have := hle i j by_omega hj; linarith)
        zucnk
      · have := (hkb 0 ztbg (fun i hi => ⟨fun h => by
            have := hle 0 i by_omega hi; linarith, by_grind⟩)).2 (by
            zuecn
            have := hle 0 i by_omega hi; linarith)
        zucnk

/-- **At most `4 M` ends per bucket.** -/
theorem bcnt_le_four {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs ztd Q ztwjp reg)
    {Lx : ℕ → List zte} {M : ℕ}
    (hM : ∀ r, r < (BuildNF.buildNF ztd Q L E).nRegions → (Lx r).length ≤ M)
    (hon : ∀ r, r < (BuildNF.buildNF ztd Q L E).nRegions →
      ∀ q, q < 2 * (Lx r).length →
        ∃ j ∈ ((BuildNF.buildNF ztd Q L E).region r).arcs,
          OnArcKey Q ztwjp j ztztf)
    (b : ℕ) :
    DrvR.bcnt (fun q => keyBkt Q ztwjp
        (DrvR.endPos ((List.range (BuildNF.buildNF ztd Q L E).nRegions).flatMap
          Lx) q))
      (2 * ((List.range (BuildNF.buildNF ztd Q L E).nRegions).flatMap Lx).length)
      b ≤ 4 * M := by
  refine cntB_flat_le
    ((BuildNF.buildNF ztd Q L E).arc
      (arcA (BuildNF.buildNF ztd Q L E).arcs.length b)).reg
    ((BuildNF.buildNF ztd Q L E).arc
      (arcB (BuildNF.buildNF ztd Q L E).arcs.length b)).reg hM ?_
  intro r hr q hq hqb
  obtain ⟨j, hj, hjx⟩ := hon r hr q hq
  obtain ⟨hjA, hjr⟩ := (hregs.2.2.1.2.2.2 r hr j).1 hj
  rcases arc_of_bkt hK hperm hsort hjA hjx with h | h
  · simp_all
  simp_all
end arcs
end
end DrvLM
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLM
@[expose] public section
open Set
open DownStep (stepFam)
open Chazelle.Chain (regionsIn freeIn)

/-! ## Lists of chords as sets -/
variable {α β : Type*}
theorem ncard_lset {l : List α} {f : α → β} (hnd : (l.map f).Nodup) :
    {x | ∃ y ∈ l, x = f y}.ncard = l.length := by
  classical
  have : {x | ∃ y ∈ l, x = f y} = ↑(l.map f).toFinset := by
    zumx
    simp only [mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
    grind
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map]
theorem mem_flat {α : Type*} {Lx : ℕ → List α} {R : ℕ} {y : α} :
    y ∈ (List.range R).flatMap Lx ↔ ∃ r, r < R ∧ y ∈ Lx r := by
  simp
theorem nodup_flat (f : α → β) (Lx : ℕ → List α) (R : ℕ)
    (hnd : ∀ r, r < R → ((Lx r).map f).Nodup)
    (hdis : ∀ r r', r < R → r' < R → ∀ y ∈ Lx r, ∀ y' ∈ Lx r', f y = f y' → r = r') :
    (((List.range R).flatMap Lx).map f).Nodup := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.nodup_append]
    refine ⟨ih (fun r hr => hnd r by_omega)
      (fun r r' hr hr' => hdis r r' by_omega by_omega), by_grind, ?_⟩
    zubtp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hb
    zufyy
    have hy'' : y' ∈ Lx R := by_grind
    have := hdis r R by_omega by_omega y hyr y' hy'' hab
    omega

/-! ## The region index of a region -/

/-- The index of a region (`0` if none). -/
noncomputable def rOf (R : ℕ) (reg : ℕ → Set Point) (U : Set Point) : ℕ := by
  classical
  exact if h : ∃ r, r < R ∧ reg r = U then h.choose else 0
theorem rOf_spec {R : ℕ} {reg : ℕ → Set Point} {U : Set Point} (h : ∃ r, r < R ∧ reg r = U) :
    rOf R reg U < R ∧ reg ztbir = U := by
  classical
  unfold rOf
  simp only [dite_eq_left h]
  exact h.choose_spec
theorem rOf_reg {R : ℕ} {reg : ℕ → Set Point}
    (hinj : ∀ r r', r < R → r' < R → reg r = reg r' → r = r') {r : ℕ} (hr : r < R) :
    rOf R reg ztcz = r :=
  hinj _ _ (rOf_spec ztkmp).1 hr (rOf_spec ztkmp).2

/-! ## Lemma 2.3 for one kept list -/
theorem lx_size {Q : Polygon} {C : Chain} (hP : C.P.Simple) {F₁ : Set ztf}
    {γ₀ γR D : ℕ} {R₀ : Set Point} {l : List zte}
    (hcan : (chainModel C).ChordFamily Q F₁ ∧ (chainModel C).DegLe F₁ D ∧
      (chainModel C).Granular F₁ γR)
    (hγ : γ₀ ≤ γR) (hkept : Gran.lset ztd Q l = Extract.kept R₀ F₁)
    (hnd : (l.map fun y => (recOf y).toSet ztd Q).Nodup) :
    l.length * ztbfd ≤ 140 * ztmo * ztyw := by
  have h1 : l.length = (Extract.kept R₀ F₁).ncard := by
    rw [← hkept]; exact (ncard_lset hnd).symm
  have h2 : (Extract.kept R₀ F₁).ncard ≤ F₁.ncard :=
    Set.ncard_le_ncard ztjvp hcan.1.1
  have h3 := DownMath.lemma23_chain hP hcan.1 hcan.2.1 hcan.2.2
  calc l.length * ztbfd ≤ F₁.ncard * (γR + 1) :=
        Nat.mul_le_mul by_omega by_omega
    _ ≤ _ := h3

/-! ## The abstract level -/

/-- **The data of one level.** -/
structure LvlCtx (Q : Polygon) (L : List zte) (R : ℕ) (reg : ℕ → Set Point)
    (C : ℕ → Chain) (F : ℕ → Set ztf) (Lx : ℕ → List zte) (D γ : ℕ) :
    Prop where
  hQ : Q.Simple
  hL : ChordTriplesOK ztd Q L
  hdeg : (interiorModel Q).DegLe ztwlg 4
  hmem : ∀ r, r < R → reg r ∈ (interiorModel Q).regions ztwlg
  hinj : ∀ r r', r < R → r' < R → reg r = reg r' → r = r'
  hsurj : ∀ U ∈ (interiorModel Q).regions ztwlg,
    ∃ r, r < R ∧ reg r = U
  hEx : ∀ r, r < R → DownDrv.ExtractOK Q ztwlg ztcz ztdyi
  hF : ∀ r, r < R → (chainModel ztdyi).ChordFamily Q zthqy ∧ (chainModel ztdyi).DegLe zthqy D ∧
    (chainModel ztdyi).Semigranular zthqy γ
  hkept : ∀ r, r < R → Gran.lset ztd Q ztdyq = Extract.kept ztcz zthqy
  hnd : ∀ r, r < R → ((Lx r).map fun y => (recOf y).toSet ztd Q).Nodup
  hatt : ∀ r, r < R → ∀ y ∈ Lx r, (recOf y).Attached ztd Q ∧ y.1 < Q.n
namespace LvlCtx
variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {R : ℕ} {reg : ℕ → Set Point} {C : ℕ → Chain}
  {F : ℕ → Set ztf} {Lx : ℕ → List zte} {D γ : ℕ}
theorem fam (X : LvlCtx Q L R reg C F Lx D γ) :
    (interiorModel Q).ChordFamily Q ztwlg := X.hL.1
theorem mem_kept (X : LvlCtx Q L R reg C F Lx D γ) {r : ℕ} (hr : r < R) {y : ℕ × ℕ × ℕ}
    (hy : y ∈ Lx r) : (recOf y).toSet ztd Q ∈ Extract.kept ztcz zthqy := by
  rw [← X.hkept r hr]; tauto

/-- A kept chord is admissible and meets the domain only in its region. -/
theorem loc (X : LvlCtx Q L R reg C F Lx D γ) {r : ℕ} (hr : r < R) {c : Set Point}
    (hc : c ∈ Extract.kept ztcz zthqy) :
    c ∈ (interiorModel Q).Adm ∧ c ∩ (interiorModel Q).D ⊆ reg r :=
  (X.hEx r hr).loc (X.hF r hr).1.2.1 c hc
theorem step (X : LvlCtx Q L R reg C F Lx D γ) :
    Gran.lset ztd Q ztlfc =
      stepFam Q ztwlg ztwzu := by
  zubcj
  constructor
  · zuod
    zuoy
    · exact Or.inl ztcyj
    · zucof
      refine Or.inr (mem_iUnion₂.2 ⟨reg r, X.hmem r hr, ?_⟩)
      beta_reduce
      rw [rOf_reg X.hinj hr]
      exact X.mem_kept hr hxr
  · rintro (hc | hc)
    · zucyc
      exact ⟨x, List.mem_append_left _ hx, rfl⟩
    · obtain ⟨U, hU, hcU⟩ := mem_iUnion₂.1 hc
      beta_reduce at hcU
      zuhhu
      generalize rOf R reg U = r at hr hrU hcU
      subst hrU
      rw [← X.hkept r hr] at hcU
      obtain ⟨x, hx, rfl⟩ := hcU
      exact ⟨x, List.mem_append_right _ (mem_flat.2 ⟨r, hr, hx⟩), rfl⟩

/-- **The down step of the level.** -/
theorem down (X : LvlCtx Q L R reg C F Lx D γ) :
    (interiorModel Q).ChordFamily Q
        ztbanc ∧
      (interiorModel Q).DegLe
        ztbanc ztcel ∧
      (interiorModel Q).Semigranular
        ztbanc γ := by
  have hEx : ∀ U ∈ (interiorModel Q).regions ztwlg,
      DownDrv.ExtractOK Q ztwlg U ztyhh := by
    zucne
    zuhhu
    have := X.hEx _ hr
    simp_all
  have hF : ∀ U ∈ (interiorModel Q).regions ztwlg,
      (chainModel ztyhh).ChordFamily Q ztzbv ∧
        (chainModel ztyhh).DegLe ztzbv D ∧
        (chainModel ztyhh).Semigranular ztzbv γ := by
    zucne
    obtain ⟨hr, -⟩ := rOf_spec ztnql
    exact X.hF _ hr
  have h := DownDrv.downStepG (D := D) (γ := γ) X.hQ X.fam X.hdeg (fun U => C ztbir)
    ztwzu hEx hF
  simp_all

/-- **The spliced list is valid.** -/
theorem ok (X : LvlCtx Q L R reg C F Lx D γ) :
    ChordTriplesOK ztd Q ztlfc := by
  have hM : ztygo := walkAx_interiorModel X.hQ
  zudfi
  · show (interiorModel Q).ChordFamily Q (Gran.lset ztd Q _)
    rw [X.step]; exact X.down.1
  · zukpp
    refine ⟨X.hL.2.1, nodup_flat _ _ _ X.hnd ?_, ?_⟩
    · intro r r' hr hr' y hy y' hy' hyy
      have h1 := X.loc hr (X.mem_kept hr hy)
      have h2 := X.loc hr' (X.mem_kept hr' hy')
      rw [hyy] at h1
      obtain ⟨p, hp⟩ := Restore.inter_nonempty_of_adm hM h2.1
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint zttef (X.hmem r' hr') with h | h
      · exact X.hinj r r' hr hr' h
      grind
    · zubtp
      zufzf
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      zufyy
      have h1 := X.loc hr (X.mem_kept hr hyr)
      obtain ⟨p, hp⟩ := Restore.inter_nonempty_of_adm hM h1.1
      have hpR := Chazelle.Chain.regionsIn_subset zttef (h1.2 hp)
      refine hpR.2 ⟨(recOf x).toSet ztd Q, ztcyj, ?_⟩
      simp_all
  · zuh
    zuoy
    · exact X.hL.2.2.1 x hx
    · zucof
      exact (X.hatt r hr x hxr).1
  · zuh
    zuoy
    · exact X.hL.2.2.2 x hx
    · zucof
      exact (X.hatt r hr x hxr).2

/-- **The size of the spliced list.** -/
theorem count (X : LvlCtx Q L R reg C F Lx D γ) {γ₀ : ℕ}
    (hper : ∀ r, r < R → (Lx r).length * ztbfd ≤
      280 * ztmo * DownHost.nk ztd ztwlg ztcz) :
    (L ++ (List.range R).flatMap Lx).length * ztbfd ≤
      L.length * ztbfd + 1120 * ztmo * ztjli := by
  classical
  have hsum : ∑ r ∈ Finset.range R,
      DownHost.nk ztd ztwlg ztcz ≤
        Q.n + 4 * L.length := by
    rw [← Finset.sum_image (f := DownHost.nk ztd ztwlg)
      (fun r hr r' hr' h => X.hinj r r' ztjix (Finset.mem_range.1 hr') h)]
    have := DownMath.sum_nk_le' X.hQ X.fam ((Finset.range R).image reg) (fun U hU => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hU
      exact X.hmem r ztjix)
    rwa [show (Gran.lset ztd Q L).ncard = L.length from ncard_lset X.hL.2.1]
      at this
  have hle : ∑ r ∈ Finset.range R, (Lx r).length * ztbfd ≤
      ∑ r ∈ Finset.range R, 280 * ztmo *
        DownHost.nk ztd ztwlg ztcz :=
    Finset.sum_le_sum fun r hr => hper r ztjix
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hle
  rw [List.length_append, length_flatMap_range, Nat.add_mul]
  have h2 := Nat.mul_le_mul_left (280 * ztmo) hsum
  have h3 : 280 * ztmo * ztjli ≤ 1120 * ztmo * ztjli :=
    Nat.mul_le_mul_right _ by_omega
  omega
end LvlCtx
end
end DrvLM
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLM
@[expose] public section
open DrvR (regHost keyBkt)
open DownStep (stepFam)

/-- `2^(⌈βλ⌉+12) = 2 · 2^μ`. -/
theorem pow_lvl (lam : ℕ) : 2 ^ ztcle = 2 * 2 ^ DrvR.nextLvl lam := by
  unfold DrvR.nextLvl
  grind

/-- **The math of one level (D7).** -/
theorem levelMathSpec : DrvR.LevelMathSpec := by
  classical
  intro P L E reg lam hG hLne hL hperm hsort hdeg hwt hregs
  zucm
  zugmd
  zueqj
  have B : DrvB.BaseCtx zta L E reg ztwkl :=
    ⟨hQ, hdh, hL, hperm, hsort, hK, hregs, decide_eq_true_iff⟩
  have hS : (BuildNF.buildNF ztwiq zta L E).F ztwiq
      zta = Gran.lset ztwiq zta L :=
    Gran.F_of_map (BuildNF.isNF_goodModel ztbafb hL hperm hsort).2.1
  have hγ := pow_lvl lam
  refine zthna
  · -- 1. the hosts
    obtain ⟨h1, h2, h3, h4⟩ := host_facts B hr hdeg hwt
    grind
  intro γ₀ M C NR γR Lx hγ₀ hreg
  -- the host facts of the regions
  have hH : ∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
      (C r).P.Simple ∧ DownDrv.ExtractOK zta ztbapw
        ztcz ztdyi := by
    zuz
    obtain ⟨hP, hs, hm, -⟩ := hreg r hr
    have h := DownMath.hostR1Spec P L E reg r hG hLne hL hperm hsort hdeg hregs hr
    obtain ⟨-, -, hsimp, -, -, -, hex⟩ := h
    refine ⟨by rw [hP]; omega, ?_⟩
    have := hex ztdyi hP hs hm
    zvojf at this
    omega
  -- the abstract level
  have X : LvlCtx zta L (BuildNF.buildNF ztwiq zta L E).nRegions reg C
      (fun r => (NR r).F ztzee zta) Lx DrvR.regCap
      (2 ^ ztxdm) := by
    refine ⟨hQ, hL, by rw [← hS]; omega, fun r hr => by rw [← hS]; exact hregs.1.1 r hr,
      hregs.1.2.1, fun U hU => hregs.1.2.2 U (by zvojf; exact hU), fun r hr => (hH r hr).2,
      fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · obtain ⟨-, -, -, hcan, -, hhi, -⟩ := hreg r hr
      exact ⟨hcan.1.1, hcan.2.1, fun U hU => (hcan.2.2.1.1 U hU).trans by_omega⟩
    · obtain ⟨-, -, -, -, -, -, hkept, -⟩ := hreg r hr
      exact hkept
    · obtain ⟨-, -, -, -, -, -, -, hnd, -⟩ := hreg r hr
      omega
    · obtain ⟨-, -, -, -, -, -, -, -, hatt, -⟩ := hreg r hr
      omega
  -- the sizes
  have hsize : ∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
      (Lx r).length * ztbfd ≤ 140 * ztfnk * ztldh := by
    zuz
    obtain ⟨-, -, -, hcan, hlo, -, hkept, hnd, -⟩ := hreg r hr
    exact lx_size (hH r hr).1 ⟨hcan.1.1, hcan.2.1, hcan.2.2.1⟩ hlo hkept hnd
  have hm : ∀ r, r < (BuildNF.buildNF ztwiq zta L E).nRegions →
      (C r).m + 1 = ((regHost ztwkl (Qof P).n
        ztbaja r).pts (Qof P).n).length := by
    zuz
    obtain ⟨hP, -, hm, -⟩ := hreg r hr
    rw [hm, hP]
    zulad
  refine ⟨fun r hr => ?_, X.ok, fun q _ => keyBkt_le _ _ _,
    fun q q' hq hq' h => codeLe_of_keyBkt _ _ hq hq' h, fun b => ?_, fun E' hperm' hsort' => ?_⟩
  · -- 3. the size of the kept lists
    zuffs

    have h4 := (host_facts B hr hdeg hwt).2.2.2
    calc (Lx r).length * ztbfd ≤ 140 * ztfnk * ztldh := h1
      _ ≤ 140 * ztfnk * (20 * 2 ^ DrvR.nextLvl lam + 17) :=
        Nat.mul_le_mul_left _ by_omega
  · -- the buckets
    exact bcnt_le_four hK hperm hsort hregs
      (fun r hr => (hreg r hr).2.2.2.2.2.2.2.2.2.2)
      (fun r hr => (hreg r hr).2.2.2.2.2.2.2.2.2.1) b
  · -- 4. the family after the splice
    have hF' : (BuildNF.buildNF ztwiq zta
        (L ++ (List.range (BuildNF.buildNF ztwiq zta L E).nRegions).flatMap
          Lx) E').F (interiorModel (Qof P)) (Qof P) =
        stepFam zta ztbapw
          (fun U => (NR (rOf (BuildNF.buildNF ztwiq zta L E).nRegions reg
            U)).F (chainModel (C (rOf (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions
              reg U))) (Qof P)) := by
      rw [Gran.F_of_map (BuildNF.isNF_goodModel ztbafb X.ok hperm' hsort').2.1,
        X.step]
    rw [hF', hS]
    refine ⟨Set.subset_union_left, X.down.2.1, X.down.2.2, X.count ztez⟩
    zuffs

    rw [pts_length B hr, hS] at h2
    rw [← h2]
    linarith
end
end DrvLM
namespace DrvLT
@[expose] public section
theorem le_lvNch {μ ℓ : ℕ} (h : ℓ * ztwtk ≤
    140 * ztfnk * ztdey) : ℓ ≤ DrvR.lvNch μ := by
  unfold DrvR.lvNch
  exact (Nat.le_div_iff_mul_le by_positivity).2 h
variable (Lx : ℕ → List (ℕ × ℕ × ℕ))
/-- The gathered list has at most `R M` triples. -/
theorem flat_length_le (R M : ℕ)
    (h : ∀ r, r < R → (Lx r).length ≤ M) : ((List.range R).flatMap Lx).length ≤ R * M := by
  rw [DrvLM.length_flatMap_range]
  calc ∑ r ∈ Finset.range R, (Lx r).length ≤ ∑ r ∈ Finset.range R, M :=
        Finset.sum_le_sum fun r hr => h r ztjix
    _ = R * M := by_simp

/-- A prefix of the gathered list is no longer than the list. -/
theorem flat_length_mono {j R : ℕ} (h : j ≤ R) :
    ((List.range j).flatMap Lx).length ≤ ((List.range R).flatMap Lx).length := by
  rw [DrvLM.length_flatMap_range, DrvLM.length_flatMap_range]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

/-- The gathered list grows by one kept list. -/
theorem flat_succ (j : ℕ) :
    (List.range ztl).flatMap Lx = (List.range j).flatMap Lx ++ Lx j := by
  zunno
  simp

/-- **(I3) at the next level.** -/
theorem i3_step {lam K K₁ K' n p γ₀ : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ p)
    (hK : K * 2 ^ Cost.ceilBeta lam ≤ DrvR.lvCnt lam * ztdyg)
    (hn : n ≤ 2 ^ p + 1) (hγ : γ₀ = 3 * 2 ^ ztyds)
    (h1 : K₁ * ztbfd ≤ K * ztbfd + 1120 * ztfnk * ztbhx)
    (h2 : K' + 1 ≤ 2 ^ ztnko * ztnmc) :
    K' * 2 ^ Cost.ceilBeta ztbbo ≤
      DrvR.lvCnt ztbbo * (2 ^ p + 2 ^ Cost.ceilBeta ztbbo) := by
  have hG : 2 ^ Cost.ceilBeta ztblw ≤ γ₀ + 1 := by
    rw [hγ]
    have : 2 ^ Cost.ceilBeta ztblw ≤
        2 ^ ztyds :=
      Nat.pow_le_pow_right by_norm_num (by unfold DrvR.nextLvl; omega)
    omega
  exact DownMath.cnt_step (A := 2 ^ ztnko) (B := 1120 * ztfnk)
    (Nat.one_le_two_pow) h16 hlp hK hn hG (DownMath.level_bound h1 h2)

/-- **The cost of the tail** against the budget `κ (K + 1) (lemma41Nat μ + 1)`: the gather (with
the reservation), the splice, the rounds, with `|Lx r| ≤ M ≤ ν = lvNch μ` and the three bounds of
`LvCostSpec`. -/
theorem cost_le {R K K₂ M ν Λ κc κS κr X : ℕ} (hR : R = K + 1) (hK₂ : K₂ ≤ R * M) (hM : M ≤ ν)
    (hΛ : 1 ≤ Λ) (h1 : ν ≤ κc * Λ) (h2 : ztdwp * ztenl ≤ κc * Λ)
    (h3 : ztdwp * X ≤ κc * Λ) :
    ztgzk + ztpuk +
      κS * ztdtg * ztxvp + 2 +
        κr * ztcte * X ≤
      ztbxw * R * Λ := by
  have hRν : K₂ ≤ R * ν := hK₂.trans (Nat.mul_le_mul_left _ hM)
  have hMR : M * R ≤ R * ν := by zuodt; simp_all
  have hz : R * ν ≤ κc * ztctm := by
    calc R * ν ≤ R * ztokw := Nat.mul_le_mul_left _ h1
      _ = κc * ztctm := by_ring
  zuiaw
  zuhxh
  -- the gather
  have hg : ztgzk + ztpuk + 2 ≤
      61 * ztctm + 48 * (κc * ztctm) := by
    grind
  -- the splice
  have hc : Nat.clog 2 zteli + 1 ≤ Nat.clog 2 (4 * ν + 4) + 1 :=
    Nat.add_le_add_right (Nat.clog_mono_right 2 by_omega) 1
  have hs1 : K + K₂ + (4 * K + 3) + 1 ≤ 5 * ztyps := by
    grind
  have hs : κS * ztdtg * ztxvp ≤
      5 * κS * κc * ztctm := by
    calc κS * ztdtg * ztxvp
        ≤ κS * (5 * ztyps) * ztenl :=
          Nat.mul_le_mul zttbb hc
      _ = 5 * κS * R * (ztdwp * ztenl) := by_ring
      _ ≤ 5 * κS * R * ztokw := Nat.mul_le_mul_left _ h2
      _ = 5 * κS * κc * ztctm := by_ring
  -- the rounds
  have hr1 : K + K₂ + 1 ≤ R * ztdwp := by
    grind
  have hr : κr * ztcte * X ≤ κr * κc * ztctm := by
    calc κr * ztcte * X ≤ κr * ztyps * X :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr1)
      _ = κr * R * (ztdwp * X) := by_ring
      _ ≤ κr * R * ztokw := Nat.mul_le_mul_left _ h3
      _ = κr * κc * ztctm := by_ring
  grind

/-- The word bounds the tail needs below its budget. -/
theorem room_small {R K M ν Λ κc κS κr : ℕ} (hR : R = K + 1) (hM : M ≤ ν) (hΛ : 1 ≤ Λ)
    (h1 : ν ≤ κc * Λ) :
    134 ≤ ztbxw * R * Λ ∧
      4 * K + 3 ≤ ztbxw * R * Λ ∧
      4 * M ≤ ztbxw * R * Λ := by
  zuiaw
  have hz : M ≤ κc * ztctm := by
    calc M ≤ κc * Λ := hM.trans h1
      _ ≤ κc * ztctm := Nat.mul_le_mul_left _ zttau
  grind
end
end DrvLT
namespace DrvLS
open Machine Machine.Stmt Programs
open BuildNF (codeLe)
open SortL (seg)
open DrvR
@[expose] public section
noncomputable def lvKb (κH κR κX lam : ℕ) : ℕ :=
  30 + κH + κR * ztwuz + κX * ztxoh +
    lvNch ztmc

/-- **The contract of the region loop** (the statement of `DrvR.lvLoop_exec`). -/
def LoopOK (O : OracleIface) (sH sR sX : Stmt) (κH κR κX : ℕ) : Prop :=
  ∀ (P : Polygon) (W : ℕ) (c₁ c : Config) (L : List zte) (E : List ℕ)
    (reg : ℕ → Set Point) (lam Kb : ℕ),
    LvCtx O P W c₁ L E reg lam →
    30 + κH + κR * ztwuz + κX * ztxoh +
      lvNch ztmc ≤ Kb →
    c₁.nreg ALLOC + ztkr * Kb ≤ W →
    LvInv O P W c₁ L E reg Kb 0 c →
    ∃ c' k, Exec P W ztlra c c' k ∧ LvInv O P W c₁ L E reg Kb ztkr c' ∧
      k ≤ ztkq * ztkr + 2 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k
theorem nextLvl_ge {lam : ℕ} (h : 16 ≤ lam) : 15 ≤ nextLvl lam := by
  unfold nextLvl
  have := ceilBeta_mono h
  have e : Cost.ceilBeta 16 = 4 := by zuovp
  omega

/-- The arithmetic of the cost of one level. -/
theorem lv_cost (K X κH κR κX κc κT N Kb : ℕ) (hX : 1 ≤ X) (hN : N ≤ κc * X)
    (hKb : Kb = 30 + κH + κR * X + κX * zttg + N) :
    9 * ztbr + 48 + ztkq * ztbr + κT * ztbr * X ≤
      (89 + κH + κR + κX + κX * κc + κc + κT) * ztxlo := by
  have h1 : Kb + 2 ≤ ztdsm * X := by
    rw [hKb]
    have a1 : κH ≤ κH * X := Nat.le_mul_of_pos_right _ hX
    have a2 : κX * zttg ≤ κX * κc * X + κX * X := by
      have : κX * zttg ≤ κX * (κc * X + X) := Nat.mul_le_mul_left _ by_omega
      grind
    grind
  have h2 : ztkq * ztbr ≤ ztdsm * ztxlo := by
    calc ztkq * ztbr ≤ ztdsm * X * ztbr :=
          Nat.mul_le_mul_right _ h1
      _ = _ := by_ring
  have h3 : 9 * ztbr + 48 ≤ 57 * ztxlo := by
    have : ztyyg := by_simp_all
    omega
  grind
theorem rd21 (c : Config) (i : ℕ) : rd c bDownDrv i = c.nreg ztjfn := rfl

/-- `L ≠ []` above the threshold. -/
theorem ne_nil_of_big {P : Polygon} {L : List zte} {E : List ℕ} {lam : ℕ}
    (hG : GoodEnv P) (hperm : E.Perm ztct)
    (hwt : (interiorModel zta).Semigranular
      ztbajd
      ztxuo)
    (hlp : lam ≤ topGrade P.n)
    (hbig : 2 ^ (Cost.ceilBeta ztcdz + 13) + 200 ≤ P.n) : L ≠ [] := by
  zumgs
  subst hL
  have hE : ztukl := by_simp_all
  zurr
  have h := DrvB.n_le_of_empty hQ hE hwt
  zubp
  zukve
  have h1 : 2 ^ ztcle ≤ 2 ^ ztzjs :=
    Nat.pow_le_pow_right by_norm_num (by have := ceilBeta_mono hlp; omega)
  grind

/-- The bounds `big`, `big2` of the context above the threshold. -/
theorem big_of {n lam : ℕ} (h16 : 16 ≤ lam) (hlp : lam ≤ topGrade n)
    (hbig : 2 ^ ztydt + 200 ≤ n) :
    3 * 2 ^ ztwqe + 129 ≤ n - 1 ∧
      2 ^ ztwnz ≤ n - 1 := by
  have hμ := nextLvl_lt h16
  have hc : Cost.ceilBeta ztmc ≤ Cost.ceilBeta ztcea :=
    ceilBeta_mono by_omega
  have h1 : 2 ^ ztwnz ≤ 2 ^ (Cost.ceilBeta ztcea + 12) :=
    Nat.pow_le_pow_right by_norm_num by_omega
  grind

/-- The `LeftInside` bit of the interior model descriptor. -/
theorem li_of_desc {m : ℕ → ℕ} {B : ℕ} {Q : Polygon}
    (h : ModelDescAt m B Q ztd) : m ztvf = 1 ↔ Mountain.LeftInside Q := by
  rcases h with ⟨-, H, C, -, hM⟩ | ⟨-, hli, -⟩
  · exact absurd hM.symm ztnou
  omega

/-- The constant of a level. -/
def κLv (κH κR κX κc κT : ℕ) : ℕ := 89 + κH + κR + κX + κX * κc + κc + κT
set_option maxHeartbeats 8000000 in
/-- **One level from its parts**, given the region loop's contract. -/
theorem levelSpec_of_loop {O : OracleIface} {sH sR sX : Stmt} {κH κR κX : ℕ}
    (hloop : LoopOK O sH sR sX κH κR κX) (hT : LvTailSpec O) (hC : LvCostSpec) :
    ∃ n₀, LevelSpec ztsy lvCnt n₀ := by
  obtain ⟨⟨n₀, hn₀⟩, hb⟩ := hC
  obtain ⟨κc, hκc⟩ := hb 0
  obtain ⟨sT, κT, hTm⟩ := hT
  refine ⟨n₀, .seq lvPar (.seq ztlra sT), κLv κH κR κX κc κT,
    fun P W c hw hpre hroom => ?_⟩
  obtain ⟨hE, hn, h16, hlp, hInv⟩ := hpre
  zubmr
  obtain ⟨hG, hW3, hWh, hS, hXh, hcap⟩ := hE
  obtain ⟨lam, hlam⟩ : ∃ lam, c.nreg 210000 = lam := by_grind
  simp only [rd21, Nat.reduceAdd] at h16 hlp hInv hroom
  rw [hlam] at h16 hlp hInv hroom
  obtain ⟨hD, hDa, L, E, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hN, hdeg, hwt, hcnt⟩ := hInv
  zurr
  obtain ⟨-, -, -, reg, g1, g2, g3, g4, -⟩ := DownMath.isNF_build hQ hok hperm hsort
  set X := lemma41Nat ztmc + 1 with hX
  zuvu
  zukav
  have hμ15 := nextLvl_ge h16
  have hNc : lvNch _ ≤ κc * X := (hκc _ hμ15).1
  set Kb := lvKb κH κR κX lam with hKb
  have hcost := lv_cost K X κH κR κX κc κT _ Kb hX1 hNc rfl
  have hκ : κLv κH κR κX κc κT = 89 + κH + κR + κX + κX * κc + κc + κT := rfl
  rw [← hκ] at hcost
  have hK' : c.nreg 210003 = K := hK
  replace hroom : c.nreg ALLOC + κLv κH κR κX κc κT * ztxlo ≤ W := by
    grind
  have hW11 : 11 ≤ W := by_omega
  -- 1. the parameters
  obtain ⟨c₁, k₁, e₁, hk₁, a00, a01, a02, a03, a04, a06, a07, b08, b08', a14, a15, a16, a17, d09,
    d11, d99, d10, d12, d13, w₁, hreg, hmm, F₁⟩ := lvPar_exec (P := P) c hw (S := c.nreg 230000)
      (n := P.n) rfl hlam (MD := c.nreg 210001) rfl (K := K) hK' hS.holds h16 hlp hD
      by_omega hW11
  have keep : ∀ q, 210000 ≤ q → q ≤ 210005 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    hreg q by_omega by_omega by_omega ztu
  have k230 : ∀ q, 230000 ≤ q → q ≤ 230001 → c₁.nreg q = c.nreg q := fun q h1 h2 =>
    hreg q by_omega by_omega by_omega ztu
  have hc0 : c₁.nreg ztcpu = c.nreg ztcpu := k230 230000 le_rfl by_norm_num
  have hc1 : c₁.nreg ztbzv = c.nreg ztbzv := k230 230001 by_norm_num le_rfl
  -- 2. the context
  have ctx : LvCtx O P W c₁ L E reg lam := by
    refine ⟨hG, hW3, hWh, ?_, ?_, ?_, h16, hlp, ne_nil_of_big hG hperm hwt hlp ztoba, hok,
      hperm, hsort, hdeg, hwt, ztono, ?_, by rw [keep _ le_rfl by_norm_num, hlam],
      a02, a04, a06, a07, b08, ?_, ?_, a14, (big_of h16 hlp ztoba).1,
      (big_of h16 hlp ztoba).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [d09, hmm, hc0]; exact hS
    · grind
    · grind
    · rw [d09, hmm, keep _ by_norm_num le_rfl]; exact hN
    · rw [b08']; exact li_of_desc hDa.holds
    · omega
    · zuncu; exact hDa
    · zunfa; exact hD
    · zumyo; exact hK
    · zunfa; exact hLb
    · zuncu; exact hLa
    · zunfa; exact hEb
    · zuncu; exact hEa
  -- 3. the loop invariant at the start
  zudov
  have inv0 : LvInv O P W c₁ L E reg Kb 0 c₁ := by
    refine ⟨w₁, d10, by rw [d11], by_omega, by_omega, by_grind,
      by omega, by_grind, rfl, le_rfl, by_simp,
      fun _ => ⟨Qof P, 0, 1, le_rfl, by_omega⟩,
      fun _ => BuildNF.buildNF ztwiq zta L E, fun _ => 0, fun _ => [],
      by rw [d12]; simp, by_omega, Or.inl d13,
      by omega⟩
  -- 4. the loop
  have hA₁ := d99
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hA₂⟩ := hloop P W c₁ c₁ L E reg lam Kb ctx le_rfl
    by_grind inv0
  -- 5. the tail
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, h00, hInv₃⟩ := hTm Kb P W c₁ c₂ L E reg lam ctx hcnt I₂
    by_grind
  obtain ⟨-, -, -, -, m₂, rm₂, r₂, rr₂, o₂, a₂, -, -⟩ := I₂
  have ex : ztpjl :=
    .seq e₁ ztcr
  have b21 := bDownDrv_mem_drvBands
  refine ⟨c₃, _, ex, ?_, ztcp, ?_⟩
  · -- the cost
    simp only [rd21, Nat.reduceAdd]
    rw [hlam, hK']
    generalize κLv κH κR κX κc κT * ztxlo = u at hcost hroom ⊢
    generalize ztkq * ztbr = v at hcost hk₂
    generalize κT * ztbr * X = w at hcost hk₃
    omega
  · simp only [rd21, Nat.reduceAdd]; omega
  · simp only [rd21, Nat.reduceAdd]; rw [hlam]; omega
  · -- the frame
    have hA9 := d09
    refine ⟨fun r hr hrA => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
    · rw [F₃.1 r hr hrA, r₂ r hr hrA, F₁.1 r (fun h => hr (by
        simp only [Finset.mem_singleton] at h; zvmwc; omega)) hrA]
    · rw [F₃.2.1 r hr, rr₂ r hr, F₁.2.1 r (fun h => hr (by
        simp only [Finset.mem_singleton] at h; zvmwc; omega))]
    · rw [F₃.2.2.1 a by_omega, m₂ a by_omega, hmm]
    · rw [F₃.2.2.2.1 a by_omega, rm₂ a by_omega, F₁.2.2.2.1 a ha]
    · rw [F₃.2.2.2.2.1, o₂, F₁.2.2.2.2.1]
    · have := F₃.2.2.2.2.2.1; omega
    · have := F₃.2.2.2.2.2.2; have := F₁.2.2.2.2.2.2; omega
theorem levelSpec_of {O : OracleIface} (hH : HostRamSpec) (hReg : RegionSpec O)
    (hX : ExtractRamSpec) (hT : LvTailSpec O) (hR1 : HostR1Spec) (hLM : LevelMathSpec)
    (hC : LvCostSpec) : ∃ n₀, LevelSpec ztsy lvCnt n₀ := by
  obtain ⟨sH, κH, hHm⟩ := hostMeets_of hH
  obtain ⟨sR, κR, hRm⟩ := regMeets_of hReg
  obtain ⟨sX, κX, hXm⟩ := extMeets_of hX
  exact levelSpec_of_loop (sH := sH) (sR := sR) (sX := sX) (κH := κH) (κR := κR) (κX := κX)
    (fun P W c₁ c L E reg lam Kb ctx hKb hroom hinv0 =>
      lvLoop_exec hHm hRm hXm hR1 hLM ctx hKb hroom hinv0) hT hC
end
end DrvLS
namespace DrvP
open Machine Machine.Stmt Programs
@[expose] public section
def descS : Stmt := block [.copyN 218010 ALLOC, .storeN 218010 218020, .addN 218060 218010 218021,
  .storeN 218060 218000, .addN 218060 218060 218021, .storeN 218060 218001,
  .addN 218060 218060 218021, .storeN 218060 218002, .addN 218060 218060 218021,
  .storeN 218060 218013, .addN 218060 218060 218021, .storeN 218060 218014,
  .addN ALLOC 218060 218021]
section exec
variable {P : Polygon} {W : ℕ}

/-- **The descriptor write.** -/
theorem descS_exec (c : Config) (hw : WordsBounded W c) (h20 : c.nreg 218020 = 0)
    (h21 : c.nreg 218021 = 1) (hA : c.nreg ALLOC + 6 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k = 13 ∧ c'.nreg 218010 = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      (∀ r, r ≠ 218010 → r ≠ 218060 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      zth ∧
      c'.nmem ztm = 0 ∧ c'.nmem ztccv = c.nreg 218000 ∧
      c'.nmem zteep = c.nreg 218001 ∧ c'.nmem zteeq = c.nreg 218002 ∧
      c'.nmem ztllf = c.nreg 218013 ∧ c'.nmem ztllg = c.nreg 218014 := by
  obtain ⟨A, hA'⟩ : ztgbe := zths
  rw [hA'] at hA ⊢
  zufsx
  zvmwe at hA'
  unfold descS
  zui
  exec_block
  all_goals first | (config_simp; rw [hA', h21]; omega) | skip
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals zvmwe at *
  all_goals config_simp
  all_goals simp only [hA', h20, h21]
  all_goals (zvmwf; split_ifs <;> first | rfl | omega)
end exec
end
end DrvP
end Chazelle.Core
section
set_option hygiene false
local macro "zqzv" : tactic => `(tactic| (have hW3 : ztsbf := by have := hE.hWh; unfold hostWords at this; omega))
local macro "zqzw" : tactic => `(tactic| (have i1 : ztgkp % l.length < l.length := Nat.mod_lt _ hpos
                                          have i2 : ztzri := Nat.mod_lt _ hpos))
local macro "zqzx" : tactic => `(tactic| refine ⟨_, _, ex, ?_, ?_, ?_, ?_, fun a ha => ?_⟩)
set_option hygiene true

/-!
# Down-phase base (D9), RAM: one point of a region

The points of the region are in the point array at `PA = r212015` (`PtArr`: three words per
point, kind `0` vertex / `1` edge point, then the indices), `NP = r212016` points, the current
point `k = r212017`.  One point (`ptS`):

1. `loadS`: the previous, current and next points (cyclically) into the register triples
   `212060`, `212063`, `212066`;
2. `vtxS`: the vertex test (`qvx`): a vertex `.vtx i`, or an edge point at the abscissa of its
   height vertex (two sign tests); flag `r212043`, vertex `i` into `212070`;
3. if a vertex: the corner test `cornerS` (bits `212084`, `212085` for the directions `+1`,
   `-1`), and for each direction code `d` whose bit is set (`dirS`): the far-end scan `farS` and
   the append `emitS`;
4. `k := k + 1`.
-/
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (ivB qE)
@[expose] public section
def PtAt (m : ℕ → ℕ) (a : ℕ) : SymPt → Prop
  | .vtx i => m a = 0 ∧ m ztdf = i
  | .onEdge e h => m a = 1 ∧ m ztdf = e ∧ m ztvj = h

/-- **The point array** at `PA`. -/
def PtArr (m : ℕ → ℕ) (PA : ℕ) (l : List SymPt) : Prop :=
  ∀ k, k < l.length → PtAt m ztqbl ztxad

/-! ## The records of a point -/
open Classical in
/-- The emitted indices at point `k`. -/
noncomputable def emAt (Q : Polygon) (l : List SymPt) (k : ℕ) : List ztw :=
  (List.range 2).filterMap fun d =>
    if (qvx Q ztxad).isSome ∧ emitAt Q l k d then some ztbub else none
theorem emIdx_eq (Q : Polygon) (l : List SymPt) :
    emIdx Q l = (List.range l.length).flatMap (emAt Q l) := rfl

/-- **The records of point `k`.** -/
noncomputable def ptRecs (li : Bool) (Q : Polygon) (l : List SymPt) (k : ℕ) :
    List zte :=
  (emAt Q l k).map ztrwn
theorem regList_eq_flatMap (li : Bool) (Q : Polygon) (l : List SymPt) :
    regList li Q l = (List.range l.length).flatMap (ptRecs li Q l) := by
  unfold regList ptRecs; rw [emIdx_eq, List.map_flatMap]
open Classical in
theorem emAt_eq (Q : Polygon) (l : List SymPt) (k : ℕ) :
    emAt Q l k = (if (qvx Q ztxad).isSome ∧ emitAt Q l k 0 then [(k, 0)] else []) ++
      (if (qvx Q ztxad).isSome ∧ emitAt Q l k 1 then [(k, 1)] else []) := by
  unfold emAt
  rw [show List.range 2 = [0, 1] from rfl]
  grind

/-! ## The program -/

/-- Load the point with index in `ir` into the register triple `x`. -/
def ldPtS (ir x : ℕ) : Stmt :=
  block [.addN 212042 ir ir, .addN 212042 212042 ir, .addN 212042 212042 212015,
    .loadN x 212042, .addN 212042 212042 212000, .loadN zthf 212042,
    .addN 212042 212042 212000, .loadN ztewm 212042]

/-- The indices of the neighbours, `k - 1` and `k + 1` cyclically. -/
def nbS : Stmt :=
  .seq (.ifLtN 212001 212017 ztnbo
      ztnbn)
    (.seq (.instr (.addN 212041 212017 212000))
      (.ifLtN 212041 212016 .skip (.instr (.constN 212041 0))))

/-- The three points of the corner. -/
def loadS : Stmt :=
  .seq nbS (.seq (ldPtS 212040 212060) (.seq (ldPtS 212017 212063) (ldPtS 212041 212066)))

/-- **The vertex test**: flag `212043` (`1` iff the point is a vertex of `Q`), the vertex into
`212070`. -/
def vtxS : Stmt :=
  .ifLtN 212063 212000
    (block [.constN 212043 1, .copyN 212070 212064])
    (.seq (block [.constN 212056 0, .copyN 212057 212065])
      (.seq (tstR 0 212063 212056 212056 212044)
        (.seq (tstR 0 212056 212063 212063 212045)
          (block [.subN 212043 212000 212044, .subN 212043 212043 212045,
            .copyN 212070 212065]))))

/-- One direction: if the bit `b` is set, the far-end scan and the append. -/
def dirS (d b : ℕ) : Stmt :=
  .ifLtN 212001 b (.seq ztotw (.seq farS emitS)) .skip

/-- **One point of the region.** -/
def ptS : Stmt :=
  .seq loadS (.seq vtxS (.seq (.ifLtN 212001 212043
    (.seq cornerS (.seq (dirS 0 212084) (dirS 1 212085))) .skip)
    (.instr (.addN 212017 212017 212000))))

/-- The registers `dirS` writes. -/
def Bdir (r : ℕ) : Bool := decide (r = 212086) || Bfar r || Bemit r

/-- The registers `ptS` writes. -/
def Bpt (r : ℕ) : Bool :=
  Bk r || decide (r = 212017) || decide (212036 ≤ r ∧ r ≤ 212112) || Bemit r
variable {q : ℕ} {E : BEnv} {r PA : ℕ} {c c' : Config}
theorem bpt_of_bk (h : Bk q = true) : Bpt q = true := by zunod
theorem bpt_of_range (h : 212036 ≤ q ∧ q ≤ 212112) : Bpt q = true := by
  zunod
theorem bpt_of_emit (h : Bemit q = true) : Bpt q = true := by zunod
theorem bpt_dir (h : Bdir q = true) : Bpt q = true := by
  unfold Bdir Bfar at h
  cases hk : Bk q
  · cases he : Bemit q
    · simp only [hk, he, Bool.or_false, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h
      zulet
    · exact bpt_of_emit he
  · zules

/-- The registers fixed during the points of a region. -/
def FixP (q : ℕ) : Prop :=
  FixB q ∨ q = 216031 ∨ q = 212033 ∨ q = 212034 ∨ q = 212015 ∨ q = 212016
theorem bdir_fix (h : FixP q) : Bdir q = false := by
  unfold FixP FixB at h
  simp only [Bdir, Bfar, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
    Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- The step bound of one direction. -/
def dirK (C : ℕ) : ℕ := (ztcom * C + 24) * 5 + 2 * ztjic * 5 + 60

/-- **The state at a point of region `r`**: the fixed registers, the region registers, the point
array at `PA` (above the output area), the output `T` so far. -/
structure PtSt (E : BEnv) (r PA : ℕ) (c : Config) (T : List ztwjg) : Prop where
  wb : WordsBounded E.W c
  regs : BRegs E c
  p31 : c.nreg 216031 = E.RP r
  lp : 0 < E.K → c.nreg 212033 = E.LP r
  nR : c.nreg 212034 = E.nRg r
  pa : c.nreg 212015 = PA
  np : c.nreg 212016 = (E.pts r).length
  arr : PtArr c.nmem PA ztdbu
  hPA : E.B₂ + 10 * E.P.n ≤ PA
  hPAW : PA + 3 * (E.pts r).length ≤ E.W
  out : OutSt E c T

/-- The state survives a change of the registers outside `FixP` and of the output area. -/
theorem PtSt.step {T T' : List ztwjg}
    (h : PtSt E r PA c T) (hw : WordsBounded E.W c') (hr : ∀ q, FixP q → c'.nreg q = c.nreg q)
    (hm : ∀ a, ztbee → c'.nmem a = c.nmem a)
    (hout : OutSt E c' T') : PtSt E r PA c' T' := by
  refine ⟨hw, h.regs.congr fun q hq => hr q ztjks, by rw [hr _ by_tauto, h.p31],
    fun hK => by rw [hr _ by_tauto, h.lp hK], by rw [hr _ by_tauto, h.nR],
    by rw [hr _ by_tauto, h.pa], by rw [hr _ by_tauto, h.np], fun k hk => ?_,
    h.hPA, h.hPAW, hout⟩
  have := h.arr k hk
  have hp := h.hPA
  have hk3 : 3 * k + 2 < 3 * (E.pts r).length := by_omega
  cases hs : (E.pts r).getD k _ with
  | vtx i =>
    zukwb
    exact ⟨(hm _ by_omega).trans this.1, (hm _ by_omega).trans this.2⟩
  | onEdge e g =>
    zukwb
    exact ⟨(hm _ by_omega).trans this.1, (hm _ by_omega).trans this.2.1,
      (hm _ by_omega).trans this.2.2⟩

/-- The step bound of one point. -/
def ptK (C : ℕ) : ℕ := 2 * dirK C + 2900

/-- The state survives a register-only change outside the fixed and output registers. -/
theorem PtSt.regStep {T : List ztwjg}
    (h : PtSt E r PA c T) (hw : WordsBounded E.W c')
    (hr : ∀ q, ztzjw → c'.nreg q = c.nreg q)
    (hm : c'.nmem = c.nmem) : PtSt E r PA c' T := by
  refine h.step hw by_simp_all by_simp_all ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h.out
  refine ⟨by_simp_all,
    by simp_all,
    by simp_all, by_simp_all,
    by simp_all, by_simp_all,
    by simp_all⟩

/-- The registers `vtxS` writes. -/
def Bvt (r : ℕ) : Bool :=
  Bk r || decide (212043 ≤ r ∧ r ≤ 212045) || decide (r = 212056 ∨ r = 212057 ∨ r = 212070)
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **Loading a point.** -/
theorem ldPtS_exec (c : Config) (hw : WordsBounded W c) {ir x idx PA : ℕ} {s : SymPt}
    (hir : c.nreg ir = idx) (hPA : c.nreg 212015 = PA) (c0 : c.nreg 212000 = 1)
    (hpt : PtAt c.nmem ztqbk s) (hb : PA + 3 * idx + 2 ≤ W) (hir' : ir ≠ 212042)
    (hx : 212043 ≤ x) :
    ∃ c' k, Exec P W (ldPtS ir x) c c' k ∧ k = 8 ∧ SymPtIn c' x s ∧
      FrameB (fun r => decide (r = 212042) || decide (x ≤ r ∧ r ≤ x + 2)) c c' := by
  obtain ⟨c', k, ex, hk, v0, v1, v2⟩ : ∃ c' k, Exec P W (ldPtS ir x) c c' k ∧ k = 8 ∧
      c'.nreg x = c.nmem ztqbk ∧ c'.nreg zthf = c.nmem (PA + 3 * idx + 1) ∧
      c'.nreg ztewm = c.nmem (PA + 3 * idx + 2) := by
    unfold ldPtS
    exec_block
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hir, hPA, c0]
    zubqj
    grind
  refine ⟨c', k, ex, hk, ?_, ?_⟩
  · cases s with
    | vtx i => exact ⟨v0.trans hpt.1, v1.trans hpt.2⟩
    | onEdge e h => exact ⟨v0.trans hpt.1, v1.trans hpt.2.1, v2.trans hpt.2.2⟩
  · refine exec_frameB ex ?_
    simp [ldPtS, block, wr, wrOK]

/-- **The neighbours.** -/
theorem nbS_exec (c : Config) (hw : WordsBounded W c) {k NP : ℕ} (hk : c.nreg 212017 = k)
    (hNP : c.nreg 212016 = NP) (hkN : k < NP) (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k', Exec P W nbS c c' k' ∧ k' ≤ 7 ∧ c'.nreg 212040 = ztqse % NP ∧
      c'.nreg 212041 = zts % NP ∧
      FrameB (fun r => decide (r = 212040) || decide (r = 212041)) c c' := by
  have hNW := hNP ▸ hw.1 212016
  -- `k - 1`
  obtain ⟨c₁, k₁, e₁, hk₁, v40, g₁⟩ : ∃ c₁ k₁, Exec P W (.ifLtN 212001 212017
      ztnbo ztnbn) c c₁ k₁ ∧
      k₁ ≤ 3 ∧ c₁.nreg 212040 = ztqse % NP ∧ ∀ r, r ≠ 212040 → c₁.nreg r = c.nreg r := by
    by_cases h0 : 0 < k
    · have e := Exec.subN (P := P) hw 212040 212017 212000
      refine ⟨_, _, .ifLtN_true by_omega e, by_omega, ?_, by_simp_all⟩
      simp only [Machine.upd_same, hk, c0]
      rw [show k + NP - 1 = ztie + NP by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    · have e := Exec.subN (P := P) hw 212040 212016 212000
      refine ⟨_, _, .ifLtN_false by_omega e, by_omega, ?_, by_simp_all⟩
      simp_all
  zud
  have k1 : c₁.nreg 212017 = k := by_simp_all
  have n1 : c₁.nreg 212016 = NP := by_simp_all
  have c0' : ztpmv := by_simp_all
  have e₂ := Exec.addN (P := P) w₁ 212041 212017 212000 by_omega
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 212041 _ }
    with hc₂
  zue
  have v41 : c₂.nreg 212041 = k + 1 := by_simp_all
  have n2 : c₂.nreg 212016 = NP := by_simp_all
  by_cases h1 : k + 1 < NP
  · have ex : Exec P W nbS c c₂ _ :=
      .seq e₁ (.seq e₂ ztzru)
    refine ⟨c₂, _, ex, by_omega, by_simp_all, by rw [v41, Nat.mod_eq_of_lt h1],
      exec_frameB ex by_decide⟩
  · have e₃ := Exec.constN (P := P) w₂ 212041 0 ztbg
    have ex : Exec P W nbS c _ _ :=
      .seq e₁ ztejy
    refine zthmh
    zuvz
    rw [show k + 1 = NP by omega, Nat.mod_self]

/-- The registers `loadS` writes. -/
def Bld (r : ℕ) : Bool := decide (212040 ≤ r ∧ r ≤ 212042) || decide (212060 ≤ r ∧ r ≤ 212068)
set_option maxHeartbeats 2000000 in
/-- **The three points of the corner.** -/
theorem loadS_exec (c : Config) (hw : WordsBounded W c) {k PA : ℕ} {l : List SymPt}
    (hk : c.nreg 212017 = k) (hNP : c.nreg 212016 = l.length) (hkN : k < l.length)
    (hPA : c.nreg 212015 = PA) (hb : PA + 3 * l.length ≤ W) (harr : PtArr c.nmem PA l)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) :
    ∃ c' k', Exec P W loadS c c' k' ∧ k' ≤ 32 ∧
      SymPtIn c' 212060 (l.getD ztbaaa ztga) ∧
      SymPtIn c' 212063 ztxad ∧
      SymPtIn c' 212066 (l.getD ztwnc ztga) ∧ FrameB Bld c c' := by
  zukes
  obtain ⟨c₁, k₁, e₁, hk₁, v40, v41, f₁⟩ := nbS_exec (P := P) c hw hk hNP hkN c0 c1
  have g₁ : ∀ r, r ≠ 212040 → r ≠ 212041 → c₁.nreg r = c.nreg r := fun r a b =>
    f₁.1 r by_simp_all
  zuesu
  zqzw
  obtain ⟨c₂, k₂, e₂, hk₂, s₂, f₂⟩ := ldPtS_exec (P := P) c₁ e₁.wb_right (ir := 212040)
    (x := 212060) v40 (by rw [g₁ _ by_norm_num by_norm_num, hPA])
    (by rw [g₁ _ by_norm_num by_norm_num, c0]) (by zvmxn; exact harr _ i1) by_omega
    by_norm_num by_norm_num
  have g₂ : ∀ r, r ≠ 212042 → (r < 212060 ∨ 212062 < r) → c₂.nreg r = c₁.nreg r := fun r a b =>
    f₂.1 r by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, s₃, f₃⟩ := ldPtS_exec (P := P) c₂ e₂.wb_right (ir := 212017)
    (x := 212063) (by rw [g₂ _ by_norm_num by_norm_num, g₁ _ by_norm_num by_norm_num, hk])
    (by rw [g₂ _ by_norm_num by_norm_num, g₁ _ by_norm_num by_norm_num, hPA])
    (by rw [g₂ _ by_norm_num by_norm_num, g₁ _ by_norm_num by_norm_num, c0])
    (by zunoe; exact harr _ hkN) by_omega by_norm_num by_norm_num
  have g₃ : ∀ r, r ≠ 212042 → (r < 212063 ∨ 212065 < r) → c₃.nreg r = c₂.nreg r := fun r a b =>
    f₃.1 r by_grind
  obtain ⟨c₄, k₄, e₄, hk₄, s₄, f₄⟩ := ldPtS_exec (P := P) c₃ e₃.wb_right (ir := 212041)
    (x := 212066) (by rw [g₃ _ by_norm_num by_norm_num, g₂ _ by_norm_num by_norm_num, v41])
    (by rw [g₃ _ by_norm_num by_norm_num, g₂ _ by_norm_num by_norm_num,
      g₁ _ by_norm_num by_norm_num, hPA])
    (by rw [g₃ _ by_norm_num by_norm_num, g₂ _ by_norm_num by_norm_num,
      g₁ _ by_norm_num by_norm_num, c0])
    (by zunyb; exact harr _ i2) by_omega by_norm_num by_norm_num
  have g₄ : ∀ r, r ≠ 212042 → (r < 212066 ∨ 212068 < r) → c₄.nreg r = c₃.nreg r := fun r a b =>
    f₄.1 r (by zvnam; omega)
  have ex : Exec P W loadS c c₄ _ := .seq e₁ ztcb
  have hBld : ∀ {B : ℕ → Bool} {c c' : Config}, FrameB B c c' →
      (∀ r, B r = true → Bld r = true) → FrameB Bld c c' := fbMono
  refine ⟨c₄, _, ex, by_omega, ?_, ?_, s₄, ?_⟩
  · refine symPtIn_copy s₂ ?_ ?_ ?_ <;>
      rw [g₄ _ by_norm_num by_norm_num, g₃ _ by_norm_num by_norm_num]
  · refine symPtIn_copy s₃ ?_ ?_ ?_ <;> rw [g₄ _ by_norm_num by_norm_num]
  · refine fbTrans (hBld f₁ ?_) (fbTrans (hBld f₂ ?_) (fbTrans (hBld f₃ ?_) (hBld f₄ ?_))) <;>
      intro r h <;> simp only [Bld, Bool.or_eq_true, decide_eq_true_eq] at h ⊢ <;> omega
set_option maxHeartbeats 4000000 in
/-- **The vertex test.** -/
theorem vtxS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    {s : SymPt} (hs : SymPtIn c 212063 s) (hsl : s.Lt P.n) (c0 : c.nreg 212000 = 1) :
    ∃ c' k, Exec P W vtxS c c' k ∧ k ≤ 500 ∧ FrameB Bvt c c' ∧ c'.nreg 212043 ≤ 1 ∧
      (c'.nreg 212043 = 1 → qvx zta s = some (c'.nreg 212070)) ∧
      (c'.nreg 212043 = 1 ↔ (qvx zta s).isSome) := by
  cases s with
  | vtx i =>
    obtain ⟨k0, k1⟩ := hs
    obtain ⟨c', k, e, hk, v43, v70⟩ : ∃ c' k, Exec P W (block [.constN 212043 1,
        .copyN 212070 212064]) c c' k ∧ k = 2 ∧ c'.nreg 212043 = 1 ∧ c'.nreg 212070 = i := by
      exec_block
      · omega
      simp_all
    have ex : Exec P W vtxS c c' _ := .ifLtN_true by_omega e
    refine ⟨c', _, ex, by_omega, exec_frameB ex by_decide, by_omega, fun _ => ?_, ?_⟩
    · zunru; rfl
    · simp [v43, qvx]
  | onEdge e h =>
    obtain ⟨k0, k1, k2⟩ := hs
    obtain ⟨c₁, k₁, e₁, hk₁, v56, v57, g₁⟩ : ∃ c₁ k₁, Exec P W (block [.constN 212056 0,
        .copyN 212057 212065]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212056 = 0 ∧ c₁.nreg 212057 = h ∧
        ∀ r, r ≠ 212056 → r ≠ 212057 → c₁.nreg r = c.nreg r := by
      exec_block
      · omega
      simp_all
    have hv : SymPtIn c₁ 212056 (.vtx h) := ⟨v56, v57⟩
    have hp : SymPtIn c₁ 212063 ztspt :=
      ⟨by_simp_all, by_simp_all,
        by simp_all⟩
    have o63 : OutK 212063 := Or.inr by_norm_num
    have o56 : OutK 212056 := Or.inr by_norm_num
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, b₂, t₂⟩ := tstR_exec hG hW (op := 0) by_norm_num
      o63 o56 o56 (d := 212044) c₁ e₁.wb_right hp hv hv hsl hsl.2 hsl.2
    have hv₂ : SymPtIn c₂ 212056 _ := symPtIn_copy hv (keep_bt f₂ by_norm_num
      by_norm_num) (keep_bt f₂ by_norm_num by_norm_num) (keep_bt f₂ by_norm_num by_norm_num)
    have hp₂ : SymPtIn c₂ 212063 _ := symPtIn_copy hp (keep_bt f₂ by_norm_num
      by_norm_num) (keep_bt f₂ by_norm_num by_norm_num) (keep_bt f₂ by_norm_num by_norm_num)
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, t₃⟩ := tstR_exec hG hW (op := 0) by_norm_num
      o56 o63 o63 (d := 212045) c₂ e₂.wb_right hv₂ hp₂ hp₂ hsl.2 hsl hsl
    have v44 : c₃.nreg 212044 = c₂.nreg 212044 := keep_bt f₃ by_norm_num by_norm_num
    have c0₃ : c₃.nreg 212000 = 1 := by
      rw [keep_bt f₃ by_norm_num by_norm_num, keep_bt f₂ by_norm_num by_norm_num,
        g₁ _ by_norm_num by_norm_num, c0]
    have h65 : c₃.nreg 212065 = h := by
      rw [keep_bt f₃ by_norm_num by_norm_num, keep_bt f₂ by_norm_num by_norm_num,
        g₁ _ by_norm_num by_norm_num, k2]
    obtain ⟨c₄, k₄, e₄, hk₄, v43, v70⟩ : ∃ c₄ k₄, Exec P W (block [.subN 212043 212000 212044,
        .subN 212043 212043 212045, .copyN 212070 212065]) c₃ c₄ k₄ ∧ k₄ = 3 ∧
        c₄.nreg 212043 = 1 - c₃.nreg 212044 - c₃.nreg 212045 ∧ c₄.nreg 212070 = h := by
      zubj
      exec_block
      simp_all
    have ex : Exec P W vtxS c c₄ _ :=
      .ifLtN_false by_omega ztwri
    have fr : FrameB Bvt c c₄ := by
      refine fbTrans ztduj (fbTrans (fbMono f₂ fun r hr => ?_)
        (fbTrans (fbMono f₃ fun r hr => ?_) ztjuw))
      · zueem

      · zueem

    have hx1 : c₃.nreg 212044 = 1 ↔ edgeXAt zta e h < ((Qof P).vtx h).1 := by
      rw [v44, t₂]; rfl
    have hx2 : c₃.nreg 212045 = 1 ↔ ((Qof P).vtx h).1 < edgeXAt zta e h := by
      zuout; rfl
    have b44 : c₃.nreg 212044 ≤ 1 := by_omega
    have hq : (c₄.nreg 212043 = 1) ↔ edgeXAt zta e h = ((Qof P).vtx h).1 := by
      grind
    refine ⟨c₄, _, ex, by_omega, fr, by_omega, fun h1 => ?_, ?_⟩
    · zunru; zuorh; grind
    · zvnck; zuorh; simp
variable {E : BEnv}
set_option maxHeartbeats 8000000 in
/-- The direction code and the far-end scan of `dirS`. -/
theorem dirS_far (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List ztwjg} (hS : PtSt E r PA c T) {k d i : ℕ} (hd : d ≤ 1)
    (hi : c.nreg 212070 = i) (hkd : ztbub ∈ emIdx E.Q ztdbu)
    (hqi : qvx E.Q ztwyp = some i) :
    ∃ c₁ c₂ k₂, Exec E.P E.W ztotw c c₁ 1 ∧ Exec E.P E.W farS c₁ c₂ k₂ ∧
      k₂ ≤ ztzhn * E.nRg r + 4 ∧
      FrameB (fun q => decide zttwt || Bfar q) c c₂ ∧
      c₂.nreg 212097 = farW E.li E.Q i d ∧ c₂.nreg 212086 = d ∧ i < E.P.n := by
  have R := hS.regs
  have O := hS.out
  zqzv
  have hn3 := hE.hn3
  have hBW := hE.hBW
  obtain ⟨i', hi', hin, -, hdir, hES⟩ := hE.far_ok hr hkd
  rw [hqi, Option.some.injEq] at hi'
  subst hi'
  have e₁ := Exec.constN (P := E.P) hS.wb 212086 d by_omega
  have g₁ : ∀ q, q ≠ 212086 → ztibn q = c.nreg q := by_simp_all
  have v₁ : ztibn 212086 = d := by_simp_all
  set c₁ : Config := { c with nreg := upd c.nreg 212086 d } with hc₁
  have R₁ : BRegs E c₁ := R.congr fun q hq => g₁ q zteqj
  have hld : ∀ t, t < E.nRg r → LdOK c₁ E.P.n t _ _ ∧
      (0 < c₁.nreg 212012 → c₁.nreg 216014 + 5 * c₁.nmem _ + 3 ≤ E.W) ∧
      (0 < c₁.nreg 212012 → c₁.nreg 212033 + E.nRg r ≤ E.W) := fun t ht =>
    hE.ld_ok hr c₁ O.low R₁.K R₁.d14 (fun hK => by
      show ztibn 212033 = _
      rw [g₁ _ by_norm_num]; exact hS.lp hK) ht
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂⟩ := farS_exec (P := E.P) hE.hG hW3 by_omega c₁
    e₁.wb_right (stF := E.stF r) (cntF := E.cntF r) (nR := E.nRg r) (i := i) (d := d)
    (Cm := E.Cm) (li := E.li) R₁.n
    (by show ztibn 212034 = _; rw [g₁ _ by_norm_num]; exact hS.nR)
    (fun t ht => (hld t ht).1) (hE.hCm r hr) (fun t ht => (hld t ht).2.1)
    (fun hK => by
      rcases Nat.eq_zero_or_pos ztpxm with h0 | h0
      · rw [h0, Nat.add_zero]; exact e₁.wb_right.1 _
      grind) R₁.li
    by_simp_all hin v₁ hd
    R₁.c0 R₁.c1 R₁.c2
  zucgm
  have hb₂' : BestOK E.Q E.Q.n i ztbgl E.li (ESr E.P.n ztuyc ztuxs ztpxm 0)
      (c₂.nreg 212099) (c₂.nreg 212097) (c₂.nreg 212098) := by_simp_all
  obtain ⟨-, hbw⟩ := far_found hE.hQ hE.hDH by_omega hdir hES hb₂'
  have f₁ : FrameB (fun q => decide zttwt) c c₁ :=
    ⟨by_simp_all, by_simp_all, rfl, rfl, rfl⟩
  refine ⟨c₁, c₂, k₂, e₁, e₂, hk₂, ?_, hbw, ?_, hin⟩
  · exact fbTrans (fbMono f₁ by_simp_all) (fbMono f₂ by_simp_all)
  · rw [f₂.1 _ by_rfl]; exact v₁
set_option maxHeartbeats 8000000 in
/-- **One direction of a vertex point**: if the corner bit `b` is set, the far end is `farW`
and the record `recAt (k, d)` is appended. -/
theorem dirS_on (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List ztwjg} (hS : PtSt E r PA c T) {k d b i : ℕ}
    (_hb : c.nreg b ≤ 1) (hd : d ≤ 1)
    (hi : c.nreg 212070 = i)
    (hem : c.nreg b = 1 → ztbub ∈ emIdx E.Q ztdbu)
    (hqi : c.nreg b = 1 → qvx E.Q ztwyp = some i)
    (hT : c.nreg b = 1 → T.length < 2 * E.P.n) (h1 : c.nreg b = 1) :
    ∃ c' k', Exec E.P E.W ztjua c c' k' ∧ k' ≤ dirK E.Cm ∧
      PtSt E r PA c' (T ++ [ztyrp]) ∧
      FrameM Bdir c c' ∧ ztwta := by
  have R := hS.regs
  have O := hS.out
  zqzv
  have hn3 := hE.hn3
  have hBW := hE.hBW
  · have hkd := hem h1
    obtain ⟨c₁, c₂, k₂, e₁, e₂, hk₂, f₂, hbw, h86, hin⟩ := dirS_far hE hr c hS hd hi hkd (hqi h1)
    zucgm
    have R₂ := R.congr fun q hq => f₂.1 q (by
      unfold FixB at hq; simp only [Bfar, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
    have k₂' : ∀ q, q ≠ 212086 → Bfar q = false → c₂.nreg q = c.nreg q := fun q a b =>
      f₂.1 q by_simp_all
    -- the record
    have hrec : recAt E.li E.Q ztdbu ztbub = vtrip E.li E.P.n i d ztgio := by
      zufdm
    have hxm : vtrip E.li E.P.n i d ztgio ∈ E.recs r := by
      rw [← hrec]; exact List.mem_map_of_mem hkd
    have hm₂ : ∀ a, a < E.B₂ → c₂.nmem a = E.m₀ a := fun a ha => by
      zuodc; exact O.low a ha
    zudio
    have hBK : E.BK = E.B₂ + 3 * (2 * E.P.n) := by unfold BEnv.BK; ring
    have hlist : ChordListAt c₂.nmem E.B₂ ztqcx := by zuodc; exact O.list
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, w₃, hm₃, d20, d21, d22, hL₃, hbk₃, hbk0₃⟩ := emitS_exec
      hE.hG hE.hWh c₂ e₂.wb_right
      (by zunjt; exact hi) hin
      h86 hd hbw R₂.li R₂.n R₂.K R₂.c0 R₂.c1 R₂.d02 R₂.d03
      R₂.d05 R₂.d14 R₂.d16 R₂.d17
      (by rw [k₂' _ by_norm_num by_decide, hS.p31]; rfl) R₂.md
      (by zunjt; exact O.cnt)
      (by zunjt; exact O.dst)
      (by rw [k₂' _ by_norm_num by_decide, O.dstB, hBK])
      hm₂ le_rfl (hT h1) by_omega by_omega
      (by have := hE.LP_lt hr; unfold BEnv.LP at this; omega)
      hlist (fun hK => by zuodd; exact O.bk hK)
      (fun hK q hq => by zuodd; exact O.bk0 hK q hq) (hE.nA_eq hr)
      (fun hK m hm hmW s hs => hE.scan_ok hK hr hxm hm hmW hs)
      (fun hK s hs => hE.hex_ok hK hr hxm hs)
    have ex : Exec E.P E.W ztjua c c₃ ztjzq := by
      have := Exec.ifLtN_true (b := b) (e := .skip)
        (by rw [R.c1, h1]; omega) ztwrj
      have e : 1 + zttl + 1 = k₂ + k₃ + 2 := by_ring
      zvmwe at this; exact this
    have hn5 := hE.nRg_le5 hr
    have ha5 := hE.arcs_le5 hr
    have FM : FrameM Bdir c c₃ :=
      ((FrameB.toM f₂).mono fun q h => by unfold Bdir; grind).trans
        (f₃.mono fun q h => by simp [Bdir, h])
    have hmem : ∀ a, ztbee → c₃.nmem a = c.nmem a := fun a ha => by
      rw [hm₃ a by_omega, f₂.2.2.1]
    refine ⟨c₃, _, ex, ?_, ?_, FM, hmem⟩
    · have m1 := Nat.mul_le_mul_left ztzhn hn5
      have m2 := Nat.mul_le_mul_left (2 * ztjic) ha5
      unfold dirK; omega
    · refine hS.step w₃ zteso hmem ⟨?_, ?_, ?_, ?_, fun hK => ?_, fun hK => ?_, fun a ha => ?_⟩
      · rw [FM.1 q (bdir_fix hq)]
      · grind
      · grind
      · grind
      · grind
      · grind
      · intro q hq; rw [hBK]; grind
      grind
set_option maxHeartbeats 8000000 in
/-- **One direction of a vertex point**: if the corner bit `b` is set, the far end is `farW`
and the record `recAt (k, d)` is appended. -/
theorem dirS_exec (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List ztwjg} (hS : PtSt E r PA c T) {k d b i : ℕ}
    (hb : c.nreg b ≤ 1) (hd : d ≤ 1)
    (hi : c.nreg 212070 = i)
    (hem : c.nreg b = 1 → ztbub ∈ emIdx E.Q ztdbu)
    (hqi : c.nreg b = 1 → qvx E.Q ztwyp = some i)
    (hT : c.nreg b = 1 → T.length < 2 * E.P.n) :
    ∃ c' k', Exec E.P E.W ztjua c c' k' ∧ k' ≤ dirK E.Cm ∧
      PtSt E r PA c' (T ++ if c.nreg b = 1 then [ztyrp] else []) ∧
      FrameM Bdir c c' ∧ ztwta := by
  zumap
  zuirf
  · zubel
    exact dirS_on hE hr c hS hb hd hi hem hqi hT h1
  · have h0 : ztuoq := by_omega
    rw [ite_eq_right h1, List.append_nil]
    have ex : Exec E.P E.W ztjua c c 2 :=
      .ifLtN_false by_omega (.skip hS.wb)
    refine ⟨c, 2, ex, by unfold dirK; omega, hS, FrameM.refl _ _, by_omega⟩
set_option maxHeartbeats 8000000 in
/-- **One point of a region**: its records `ptRecs k` are appended. -/
theorem ptS_exec (hE : BGood E) {r PA : ℕ} (hr : r < E.K + 1) (c : Config)
    {T : List ztwjg} (hS : PtSt E r PA c T) {k : ℕ} (hk : c.nreg 212017 = k)
    (hkn : k < (E.pts r).length)
    (hT : T.length + (ptRecs E.li E.Q ztdbu k).length ≤ 2 * E.P.n) :
    ∃ c' k', Exec E.P E.W ptS c c' k' ∧ k' ≤ ptK E.Cm ∧
      PtSt E r PA c' (T ++ (ptRecs E.li E.Q ztdbu k).map fun x => ztcof) ∧
      c'.nreg 212017 = k + 1 ∧ FrameM Bpt c c' ∧
      ztwta := by
  zumap
  zqzv
  zucgm
  zujna
  have hlt : ∀ s ∈ l, s.Lt E.P.n := by zvnof; exact hE.pts_lt hr
  have hgetD : ∀ j, j < l.length → (l.getD j ztga).Lt E.P.n := by_simp_all
  zukes
  -- 1. the three points
  obtain ⟨c₁, k₁, e₁, hk₁, sa, sv, sb, f₁⟩ := loadS_exec (P := E.P) c hS.wb hk hS.np hkn hS.pa
    hS.hPAW hS.arr R.c0 R.c1
  have S₁ := hS.regStep e₁.wb_right (fun q hq => f₁.1 q (by
    unfold FixP FixB at hq; simp only [Bld, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
    f₁.2.2.1
  -- 2. the vertex test
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hq₂, hs₂⟩ := vtxS_exec (P := E.P) hE.hG hW3 c₁ e₁.wb_right sv
    (hgetD k hkn) S₁.regs.c0
  have fx₂ : ∀ q, ztzjw → c₂.nreg q = c₁.nreg q := fun q hq =>
    f₂.1 q (by unfold FixP FixB at hq; simp only [Bvt, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have S₂ := S₁.regStep e₂.wb_right fx₂ f₂.2.2.1
  have keep₂ : ∀ q, 212060 ≤ q → q ≤ 212068 → c₂.nreg q = c₁.nreg q := fun q a b =>
    f₂.1 q (by simp only [Bvt, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  set C : Prop := (qvx E.Q (l.getD k _)).isSome = true with hC
  -- the records of the point
  have hrecs : ∀ (b0 b1 : Prop) [Decidable b0] [Decidable b1],
      ztlgb → ztlgc →
      (ptRecs E.li E.Q l k).map ztyez =
        (if b0 then [ztkdm] else []) ++
          (if b1 then [ztkdn] else []) := by
    zujav
    classical
    unfold ptRecs
    rw [emAt_eq]
    by_cases g0 : b0 <;> by_cases g1 : b1
    · rw [ite_eq_left ztvse, ite_eq_left ztvsh, ite_eq_left g0, ite_eq_left g1]; rfl
    · rw [ite_eq_left ztvse, ite_eq_right ztvsi, ite_eq_left g0, ite_eq_right g1]; rfl
    · rw [ite_eq_right ztvsf, ite_eq_left ztvsh, ite_eq_right g0, ite_eq_left g1]; rfl
    · rw [ite_eq_right ztvsf, ite_eq_right ztvsi, ite_eq_right g0, ite_eq_right g1]; rfl
  zuka
  zuja
  have FM₁ : FrameM Bpt c c₁ := (FrameB.toM f₁).mono fun q hq => bpt_of_range (by
    simp only [Bld, Bool.or_eq_true, decide_eq_true_eq] at hq; omega)
  have FM₂ : FrameM Bpt c₁ c₂ := (FrameB.toM f₂).mono fun q hq => by
    unfold Bvt at hq
    cases hk : Bk q
    · simp only [hk, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hq
      zulet
    · zules
  have hk₂ : c₂.nreg 212017 = k := by rw [f₂.1 _ by_decide, f₁.1 _ by_decide, hk]
  have c1₂ := S₂.regs.c1
  have c0₂ := S₂.regs.c0
  have hlenT : ∀ (b0 b1 : Prop) [Decidable b0] [Decidable b1],
      ztlgb → ztlgc →
      (ptRecs E.li E.Q l k).length = (if b0 then 1 else 0) + (if b1 then 1 else 0) := by
    zujav
    have := congrArg List.length (hrecs b0 b1 h0 h1)
    zubus
    rw [this, List.length_append]
    zujpl
  by_cases hf : c₂.nreg 212043 = 1
  · have hqv := hq₂ hf
    set i := c₂.nreg 212070 with hi
    have hCt : C := by_grind
    -- the corner
    zqzw
    have sa₂ := symPtIn_copy sa ztcns
      ztcns ztcns
    have sv₂ := symPtIn_copy sv ztcns
      ztcns ztcns
    have sb₂ := symPtIn_copy sb ztcns
      ztcns ztcns
    obtain ⟨c₃, k₃, e₃, hk₃, f₃, b84, b85, t84, t85⟩ := cornerS_exec hE.hG hW3 c₂ hw₂
      sa₂ sv₂ sb₂ by_grind by_grind by_grind c0₂ c1₂
    zuboe
    have S₃ := S₂.regStep hw₃ (fun q hq => f₃.1 q (by
      unfold FixP FixB at hq; simp only [Bcor, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega)) f₃.2.2.1
    have FM₃ : FrameM Bpt c₂ c₃ := (FrameB.toM f₃).mono fun q hq => by
      unfold Bcor at hq
      cases hk : Bk q
      · simp only [hk, Bool.false_or, decide_eq_true_eq] at hq
        zulet
      · zules
    have e0 : emitAt E.Q l k 0 ↔ c₃.nreg 212084 = 1 := by
      rw [t84]; rfl
    have e1 : emitAt E.Q l k 1 ↔ c₃.nreg 212085 = 1 := by
      rw [t85]; rfl
    have i₃ : ztury := f₃.1 _ by_decide
    have k₃' : c₃.nreg 212017 = k := by rw [f₃.1 _ by_decide, hk₂]
    -- the length of the records
    have hL := hlenT _ _
      ⟨by_grind, fun h => e0.1 h.2⟩ ⟨by_grind, fun h => e1.1 h.2⟩
    -- direction `+1`
    obtain ⟨c₄, k₄, e₄, hk₄, S₄, F₄, M₄⟩ := dirS_exec hE hr c₃ S₃ b84 by_norm_num i₃ (fun h => mem_emIdx.2 ⟨hkn, by_norm_num, hCt, e0.2 h⟩)
      by_grind ztbay
    have b85' : c₄.nreg 212085 = c₃.nreg 212085 := F₄.1 _ by_decide
    have i₄ : ztust := by rw [F₄.1 _ by_decide, i₃]
    -- direction `-1`
    obtain ⟨c₅, k₅, e₅, hk₅, S₅, F₅, M₅⟩ := dirS_exec hE hr c₄ S₄ by_omega by_norm_num i₄
      (fun h => mem_emIdx.2 ⟨hkn, by_norm_num, hCt, e1.2 (b85' ▸ h)⟩)
      by_grind (fun h => by
        rw [b85'] at h
        zujgr
        by_cases hA : c₃.nreg 212084 = 1
        · simp only [hA, h, ite_true] at hL ⊢; simp; omega
        · simp only [hA, h, ite_true, ite_false] at hL ⊢; simp; omega)
    -- the counter
    have k₅' : c₅.nreg 212017 = k := by rw [F₅.1 _ by_decide, F₄.1 _ by_decide, k₃']
    have c0₅ := S₅.regs.c0
    have hkW : k + 1 ≤ E.W := by
      have h1 : ztpkx := hS.hPAW; omega
    have e₆ := Exec.addN (P := E.P) S₅.wb 212017 212017 212000 by_omega
    have f₆ : FrameB ztfrt c₅ _ := exec_frameB e₆ by_decide
    have ex : ztpji :=
      .seq e₁ (.seq e₂ (.seq (.ifLtN_true by_omega ztbpd) e₆))
    have hT₂ : T ++ (ptRecs E.li E.Q l k).map ztyez =
        (T ++ if c₃.nreg 212084 = 1 then [ztkdm] else []) ++
          (if c₄.nreg 212085 = 1 then [ztkdn] else []) := by
      rw [List.append_assoc, hrecs _ _
        ⟨by_grind, fun h => e0.1 h.2⟩
        ⟨by_grind, fun h => b85' ▸ e1.1 h.2⟩]
    zqzx
    · zumtz
    · rw [hT₂]
      refine S₅.regStep e₆.wb_right ztnzi f₆.2.2.1
      zubht
      · zufdd
      grind
    · simp only [Machine.upd_same, k₅', c0₅]
    · refine FM₁.trans (FM₂.trans (FM₃.trans ((F₄.mono fun q hq => bpt_dir hq).trans
        ((F₅.mono fun q hq => bpt_dir hq).trans ((FrameB.toM f₆).mono fun q hq => ?_)))))
      zufpq
    · show c₅.nmem a = c.nmem a
      rw [M₅ a ha, M₄ a ha, f₃.2.2.1, f₂.2.2.1, f₁.2.2.1]
  · -- not a vertex: no records
    have hf0 : ¬ C := by_grind
    have hnil : (ptRecs E.li E.Q l k).map ztyez = [] := by
      rw [hrecs False False by_grind by_grind]
      simp
    have hf' : c₂.nreg 212043 = 0 := by_omega
    have e₆ := Exec.addN (P := E.P) hw₂ 212017 212017 212000 (by
      rw [hk₂, c0₂]; have h1 : ztpkx := hS.hPAW; omega)
    have f₆ : FrameB ztfrt c₂ _ := exec_frameB e₆ by_decide
    have ex : ztpji :=
      .seq e₁ (.seq e₂ (.seq (.ifLtN_false by_omega ztuvp) e₆))
    zqzx
    · zumtz
    · rw [hnil, List.append_nil]
      refine S₂.regStep e₆.wb_right ztnzi f₆.2.2.1
      zubht
      · zufdd
      grind
    · simp only [Machine.upd_same, hk₂, c0₂]
    · exact FM₁.trans (FM₂.trans ((FrameB.toM f₆).mono fun q hq => by
        zvmwo at hq; subst hq; decide))
    · show c₂.nmem a = c.nmem a
      zuoit
end exec
end
end DrvB
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbkl" : tactic => `(tactic| (rw [side_out hda0 hdaL ztruf hu0 huL] at hGu
                                           rw [side_out hda0 hdaL ztruf hx0 hxL] at hGx))
local macro "zqbkm" : tactic => `(tactic| set w := sidePt M.W p t with hw)
set_option hygiene true

/-!
# WP-E, Lemma 3.2 part 17: rays from inside an arc

The descent tests positions strictly inside the arc `Aᵢ` of the region `R` (the ends of node
chords of a piece's canonical normal form).  For the completeness clause of the test, the ray
from such a position into its left sector must give an admissible chord outside `S` whose domain
part lies in `R`.

* `sector_sub_region`: near the point of a position strictly inside an arc of `R`, its left
  sector lies in `R`;
* `ray_avoids`: a ray into the left sector of a non-cut position meets no chord of `S` before it
  leaves the domain (such a chord would be attached at the position);
* `ray_in_region`: the ray's chord is not in `S` and its domain part lies in `R`;
* `ray_adm`: the ray's chord is admissible (chain models: at a height not above the chain top).
-/
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (sidePt SideAttach sideLeft sideLeftOf sideCcw sidePrev sideNext sideInArc
  freeIn regionsIn TouchesIn sideKey_inj)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)
open Chazelle.Jordan (offset)
variable {M : Model}

/-- **The left sector at a position strictly inside an arc of `R` lies in `R`** near its
point. -/
theorem sector_sub_region (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm)
    (hfin : S.Finite) {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ} (harc : M.IsArc S R l r)
    {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hin : sideInArc l r ztk) :
    ∃ r₁ > 0, ∀ x ∈ ball ztbp r₁, sideLeft M.W p t x → x ∈ R := by
  zuhyh
  have hB := fun c hc hA => hcut ztcxr
  zubla

  obtain ⟨-, hpre, hoff⟩ := Chazelle.Chain.sideSector (S := (freeIn M.D S)ᶜ) hav hbv hr₁ (by
    zuddp

    exact ⟨hxD, by_simp_all⟩)
  set L := ball ztbp r₁ ∩
    {x | sideLeftOf (sidePrev M.W p t) ztbp ztohw x} with hL
  have hLfree : ztsbz := by
    zuh
    zufyi
    exact ⟨hxD, by_grind⟩
  have hscale : Tendsto (fun s : ℝ => s * (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    zuloq
    · have : Tendsto (fun δ : ℝ => δ * (1 - t)) _ (𝓝 (0 * (1 - t))) :=
        (continuous_id.mul continuous_const).tendsto 0
      zudvn
      zuhv
    simp_all
  have hfR : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 ∧ M.Faces p ztwlx R := by
    zudmr

    refine ⟨hs.2, harc.2.2.2.2.2.2 p _ hp by_nlinarith
      ztiid ?_⟩
    grind
  obtain ⟨s, hs1, hs2⟩ := (hoff.and hfR).exists
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      offset _ _ _ _ ∈ R :=
    hscale.eventually hs2.2
  zubrw
  have e : offset ztbp ztohw s ztckn =
      offset ztpr ztoa ztwlx ztxlw := by
    zuedr

  have hLR :=
    Chazelle.Chain.subset_regionsIn_of_inter hR hpre hLfree ⟨_, hδ1.2, by_grind⟩
  exact ⟨r₁, hr₁, fun x hx hxl => hLR ⟨hx, hxl⟩⟩

/-- A point level with `w` whose signed offset `σ (x.1 - w.1)` is `s` is the ray point at `s`. -/
theorem eq_rayPt {w x : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hx : x.2 = w.2) :
    x = rayPt w σ (σ * ztuee) := by
  zubjw
  · rw [rayPt_fst, ← mul_assoc]
    grind
  simp_all

/-- The signed offset is affine along a level segment. -/
theorem off_lerp (w u v : Point) (σ μ : ℝ) :
    σ * ((lerp u v μ).1 - w.1) = ztndo * (σ * ztojb) + μ * (σ * ztuct) := by
  rw [lerp_fst]; ring

/-- **A ray into the left sector of a non-cut position meets no chord of `S`** before it leaves
the domain. -/
theorem ray_avoids (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hcut : ¬ M.IsCut S ztk) {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hsec : sideLeft M.W p t ztwyg)
    (hdom : ∀ s, 0 < s → s < T → rayPt ztbp σ s ∈ M.D) :
    ∀ c ∈ S, ∀ s, 0 < s → s < T → rayPt ztbp σ s ∉ c := by
  intro c hc s₀ hs₀ hs₀T hz
  zqbkm
  have hwD := hM.trace p hp t ht0 ht1.le
  obtain ⟨u, v, huv, hcuv, hy, hopen, hu, hv⟩ := hM.ends c ztbkp
  have hout : ztlcb := by
    zucjc

  have huD := hout u hu
  have hvD := hout v hv
  rw [hcuv] at hz
  obtain ⟨μ₀, hμ0, hμ1, hz⟩ := Geometry.mem_segment_iff_lerp.1 hz
  -- the chord is level with `w`
  have hu2 : u.2 = w.2 := by
    have := congrArg Prod.snd hz
    rw [rayPt_snd, lerp_snd, ← hy, sub_self, mul_zero, add_zero] at this
    simp_all
  have hv2 : v.2 = w.2 := by_simp_all
  set f : Point → ℝ := fun x => σ * ztuee with hf
  -- the ends are not ray points before the exit
  have hnot : ∀ x, x.2 = w.2 → x ∉ M.D → f x ≤ 0 ∨ T ≤ f x := by
    intro x hx hxD
    by_contra hh
    zumin
    exact hxD (by rw [eq_rayPt hσ hx]; grind)
  have hfz : f (rayPt w σ s₀) = s₀ := by
    simp only [hf, rayPt_fst]
    grind
  have hlin : s₀ = (1 - μ₀) * f u + μ₀ * f v := by
    rw [← hfz, hz]; exact off_lerp w u v σ μ₀
  -- the key step, for the end `a` before the ray and `b` after it
  have key : ∀ a b : Point, c = Chazelle.segment a b → a.2 = w.2 → b.2 = w.2 →
      ztgnm → f a ≤ 0 → T ≤ f b → False := by
    intro a b hcab ha2 hb2 hab hfa hfb
    have hT : ztphq := by_grind
    -- `w` is on the segment, hence its end `a`
    have hfa0 : f a = 0 := by
      zuct
      have hneg : f a < 0 := by_grind
      set μ := - f a / (f b - f a) with hμ
      have hden : 0 < f b - f a := by_linarith
      have hμ0 : ztrzr := div_pos by_linarith hden
      have hμ1 : μ < 1 := (div_lt_one hden).2 by_linarith
      have hwl : lerp a b μ = w := by
        have hf0 : f (lerp a b μ) = 0 := by
          show σ * ((lerp a b μ).1 - w.1) = 0
          zumou
          grind
        have h2 : (lerp a b μ).2 = w.2 := by zunzz; ring
        grind
      grind
    have haw : a = w := by
      grind
    -- so the chord is attached at the position: a cut
    apply hcut
    refine ⟨c, hc, p, t, ⟨hp, ht0, ht1, ?_, 1, one_pos, ?_⟩, rfl⟩
    · rw [hcab, haw]; exact Geometry.left_mem_segment _ _
    · intro x hx hxw _
      zugdr
      obtain ⟨l₁, hl0, hl1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
      have hl : 0 < l₁ := by
        rcases hl0.lt_or_eq with h | h
        · zubh
        · exfalso; apply hxw; rw [← h, Geometry.lerp_zero, haw]
      have h2 : (lerp a b l₁).2 = w.2 := by zunzz; ring
      have hfx : 0 < f (lerp a b l₁) := by
        show 0 < σ * ((lerp a b l₁).1 - w.1)
        zumou
        show 0 < (1 - l₁) * f a + l₁ * f b
        rw [hfa0]; nlinarith
      rw [eq_rayPt hσ h2]
      exact (Sweep.sideLeft_rayPt_iff M.W p t σ hfx one_pos).2 hsec
  rcases hnot u hu2 huD with hfu | hfu
  · have hfv : T ≤ f v := by
      zuhil
      · nlinarith
      omega
    exact key u v hcuv hu2 hv2 hopen hfu hfv
  · have hfv : f v ≤ 0 := by
      zuhil
      · omega
      · nlinarith
    refine key v u (by rw [hcuv, Geometry.segment_comm]) hv2 hu2 ztjwm hfv hfu
    zumlg
    grind

/-- **The chord of a ray from a position strictly inside an arc of `R`** is not in `S` and its
domain part lies in `R`. -/
theorem ray_in_region (hM : WalkAx M) {S : Set ztf} (hS : S ⊆ M.Adm) (hfin : S.Finite)
    {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ} (harc : M.IsArc S R l r) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1) (hin : sideInArc l r ztk) {σ T : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) (hsec : sideLeft M.W p t ztwyg)
    (hdom : ∀ s, 0 < s → s < T → rayPt ztbp σ s ∈ M.D)
    (hout : rayPt ztbp σ T ∉ M.D) :
    chordOf ztbp σ T ∉ S ∧ chordOf ztbp σ T ∩ M.D ⊆ R := by
  zqbkm
  zuhyh
  have hav := ray_avoids hM hS hp ht0 ht1 hcut hσ hsec hdom
  constructor
  · zuhgp
    exact hav _ hmem _ by_linarith by_linarith
      ((mem_chordOf hσ hT.le).2 ⟨T / 2, by_linarith, by_linarith, rfl⟩)
  · -- the open ray is connected, free, and starts in `R`
    set I : Set Point := (rayPt w σ) '' Ioo 0 T with hI
    have hIc : IsPreconnected I := by
      refine isPreconnected_Ioo.image _ (Continuous.continuousOn ?_)
      zumuc
    have hIf : I ⊆ freeIn M.D S := by
      zubyg
      exact ztkjb
    obtain ⟨r₁, hr₁, hsub⟩ := sector_sub_region hM hS hfin hR harc hp ht0 ht1 hin
    set s₁ := min ztld (r₁ / 2) with hs₁
    have hs₁0 : 0 < s₁ := by_simp_all
    have hs₁T : s₁ < T := by_grind
    have hs₁r : s₁ < r₁ := by_grind
    have hmeet : (I ∩ R).Nonempty := by
      refine ⟨rayPt w σ s₁, by_grind, hsub _ ?_ ?_⟩
      · rw [mem_ball, Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq,
          add_sub_cancel_left]
        zur
        · rw [one_mul, abs_of_pos hs₁0, max_eq_left hs₁0.le]; omega
        · rw [neg_one_mul, abs_neg, abs_of_pos hs₁0, max_eq_left hs₁0.le]; omega
      · exact (Sweep.sideLeft_rayPt_iff M.W p t σ hs₁0 one_pos).2 hsec
    have hIR := Chazelle.Chain.subset_regionsIn_of_inter hR hIc hIf hmeet
    zujgi
    obtain ⟨s, hs0, hsT, rfl⟩ := (mem_chordOf hσ hT.le).1 hx
    have hs0' : ztxx := by
      zuvl
      · zubh
      · exfalso; rw [← h, rayPt_zero'] at hxD
        exact hM.trace p hp t ht0 ht1.le hxD
    grind

/-! ## Arrival on the piece's chain (M2') -/

/-- The point of a level segment is the ray point at the proportional offset. -/
theorem lerp_rayPt (a : Point) (σ L μ : ℝ) : lerp a (rayPt a σ L) μ = rayPt a σ (μ * L) := by
  zubjw
  · rw [lerp_fst, rayPt_fst, rayPt_fst]; ring
  simp

/-- The chord of a ray up to `T` is the segment to the ray point at `T`. -/
theorem chordOf_eq_segment {z : Point} {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hT : 0 < T) :
    chordOf z σ T = Chazelle.segment z ztxn := by
  zumx
  rw [mem_chordOf hσ hT.le, Geometry.mem_segment_iff_lerp]
  constructor
  · zugtj
    refine ⟨s / T, div_nonneg hs0 hT.le, (div_le_one hT).2 hsT, ?_⟩
    rw [lerp_rayPt, div_mul_cancel₀ _ hT.ne']
  · rintro ⟨μ, hμ0, hμ1, rfl⟩
    exact ⟨μ * T, by_positivity, by_nlinarith, lerp_rayPt _ _ _ _⟩

/-- The chain avoids the domain of its model. -/
theorem set_not_dom {C : Chain} {x : Point} (hx : x ∈ C.set) : x ∉ C.dom :=
  fun h => h.2 zthrs

/-- **Arrival on the chain (M2').**  Let `k = [a, o]` be a level chord of the chain model of `Cα`
from the chain point `a`, and let a ray from `a` in the direction of `o` stay in the domain of a
model `M` (in which the chain points are outside the domain) up to `T`, where it reaches a chain
point.  Then it reaches `o`: before `o` it is in `Cα`'s domain, and beyond `o` it would leave the
box of `Cα`'s model (`o` is not on the slit: the slit is above the chain). -/
theorem arrive_other {D : Set Point} {Cα : Chain} (hsetD : ∀ x ∈ Cα.set, x ∉ D)
    {a o : Point} (hoy : o.2 = a.2) (haC : a ∈ Cα.set)
    (hkopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a o s ∈ Cα.dom) (hoD : o ∉ Cα.dom)
    {σ T : ℝ} (hσ : σ = 1 ∨ σ = -1) (hdir : 0 < σ * ztodv) (hT : 0 < T)
    (hdom : ∀ s, 0 < s → s < T → rayPt a σ s ∈ D) (hfar : rayPt a σ T ∈ Cα.set) :
    rayPt a σ T = o := by
  set L₀ := σ * ztodv with hL₀
  have ho := eq_rayPt hσ hoy
  rcases lt_trichotomy T L₀ with h | h | h
  · exfalso
    have hin := hkopen _ ⟨div_pos hT hdir, (div_lt_one hdir).2 h⟩
    rw [ho, lerp_rayPt, div_mul_cancel₀ _ hdir.ne'] at hin
    exact set_not_dom hfar hin
  · grind
  · exfalso
    have hoM : o ∈ D := by_grind
    -- `o` is not a chain point
    have hoC : o ∉ Cα.set := by_grind
    -- `o` is not on the slit
    have hoS : o ∉ Cα.slit := by
      zumgt
      obtain ⟨h1, h2, -⟩ := Cα.mem_slit_iff.1 hs
      have h3 := hoy ▸ Cα.snd_le_top_of_mem_set haC
      exact hoC (by
        have : o = Cα.top := by_grind
        zvmwk; exact Cα.top_mem_set)
    -- so `o` is off the box, and so is the farther ray point
    have hob : o ∉ Chazelle.Chain.box Cα.radius := fun hb =>
      hoD ⟨hb, fun hh => hh.elim hoC hoS⟩
    have hab := Cα.set_subset_box haC
    have hfb := Cα.set_subset_box hfar
    rw [Chazelle.Chain.mem_box_iff] at hab hfb
    rw [Chazelle.Chain.mem_box_iff, hoy] at hob
    push Not at hob
    have ho1 : Cα.radius ≤ |o.1| := by
      grind
    have e1 : o.1 = a.1 + σ * L₀ := by_grind
    rw [rayPt_fst] at hfb
    zur
    · grind
    grind

/-! ## Choosing the child (cyclic order in offsets) -/

/-- On the open stretch `(0, L)`, an interval from a stretch point to a point outside the open
stretch contains exactly the offsets after it. -/
theorem side_out {d α v L : ℝ} (hd : 0 < d) (hdL : d < L) (hα : α = 0 ∨ L ≤ α) (hv0 : 0 < v)
    (hvL : v < L) : sideInArc d α v ↔ d < v := by
  zuiq

/-- **All the candidate offsets left by the tests are on one side of the node chord.**  Offsets
`0 < v < L` of the stretch; the node chord has the end `da` in the open stretch and the other end
at offset `βb` (in `Cα`'s rotated keys); the test at `da` arrived at `α'` (in `M`'s rotated keys;
by M2' an arrival in the open stretch is at `βb`), leaving the offsets `v` with
`sideInArc da α' v ↔ sA`; if `βb` is in the open stretch, the test at it leaves the offsets
satisfying `GB`.  Then the side `sideInArc da βb v` of the node chord is the same for all offsets
left by both tests. -/
theorem witness_side {L da βb α' : ℝ} (hda0 : 0 < da) (hdaL : da < L) (hβ0 : 0 ≤ βb)
    (hne : da ≠ βb)
    (hα0 : 0 ≤ α') (hα' : 0 < α' → α' < L → α' = βb) {sA : Prop} {GB : ℝ → Prop}
    (hGB : 0 < βb → βb < L → ∃ β' : ℝ, ∃ sB : Prop, 0 ≤ β' ∧ (0 < β' → β' < L → β' = da) ∧
      ∀ v, GB v ↔ (sideInArc βb β' v ↔ sB))
    {u x : ℝ} (hu0 : 0 < u) (huL : u < L) (hx0 : 0 < x) (hxL : x < L) (hua : u ≠ da)
    (hub : u ≠ βb) (hxa : x ≠ da) (hxb : x ≠ βb)
    (hGu : sideInArc da α' u ↔ sA) (hGx : sideInArc da α' x ↔ sA) (hBu : GB u) (hBx : GB x) :
    sideInArc da βb u ↔ sideInArc da βb x := by
  have out : ∀ y : ℝ, 0 ≤ y → ¬ ztndj → y = 0 ∨ L ≤ y := by
    grind
  zugji
  · obtain ⟨β', sB, hβ'0, hβ', hGBeq⟩ := hGB hb.1 hb.2
    by_cases ha' : 0 < α' ∧ α' < L
    · grind
    · by_cases hb' : 0 < β' ∧ β' < L
      · have e := hβ' hb'.1 hb'.2
        rw [hGBeq, e] at hBu hBx
        have cu :=
          Chazelle.Chain.sideInArc_swap ztnr hub hua
        have cx :=
          Chazelle.Chain.sideInArc_swap ztnr hxb hxa
        grind
      · zqbkl
        rw [hGBeq, side_out hb.1 hb.2 ztrug hu0 huL] at hBu
        rw [hGBeq, side_out hb.1 hb.2 ztrug hx0 hxL] at hBx
        have nu : u < βb ↔ ¬ βb < u := by_grind
        have nx : x < βb ↔ ¬ βb < x := by_grind
        have e1 := hGu.trans hGx.symm
        have e2 := hBu.trans hBx.symm
        zuiq

  · have hb' := out βb hβ0 hb
    have ha' : ¬ (0 < α' ∧ α' < L) := by_grind
    zqbkl
    rw [side_out hda0 hdaL hb' hu0 huL, side_out hda0 hdaL hb' hx0 hxL]
    grind

/-! ## The arc just after a walk vertex (the leaf) -/

/-- A key interval containing `x` and no end in `(p, x]` contains `(p, x]`, and `p` is its start
or inside it. -/
theorem cyc_after_vertex {a b p x : ℝ} (hin : sideInArc a b x) (ha : ¬ (p < a ∧ a ≤ x))
    (hb : ¬ (p < b ∧ b ≤ x)) (hpx : p < x) :
    ClosedArc a b p ∧ ∀ y, p < y → y ≤ x → sideInArc a b y := by
  refine ⟨?_, fun y hy1 hy2 => ?_⟩
  · by_cases hpa : p = a
    · tauto
    · left
      rcases lt_or_gt_of_ne hpa with hpa | hpa
      · zucrh
        grind
      · zucrh
        grind
  · zucrh
    grind

/-- **The arc just after a walk vertex**: the keys just after the vertex `p` are inside an arc
of a region `U` of `F`, and `p` is on the closed arc. -/
theorem arc_after (hGM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hFam : M.ChordFamily Q F) {p : ℕ} (hp : p < M.W.n) :
    ∃ U ∈ M.regions F, ∃ a b : ℝ, M.IsArc F U a b ∧ ClosedArc a b p ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (p + ε) := by
  zubm
  obtain ⟨t', ht', hno⟩ := hM.exists_after hFam.2.1 hFam.1 hp le_rfl zero_lt_one
  zvncl at hno
  have hx0 : (0 : ℝ) < p + t' := by_grind
  have hxcut : ztpqv := fun h => hno _ h ⟨by_simp_all, le_rfl⟩
  obtain ⟨U, hU, a, b, harc, hin⟩ := WalkEmbed.exists_arc_around hGM hFam hx0 hxcut
  refine ⟨U, hU, a, b, harc, ?_⟩
  rcases F.eq_empty_or_nonempty with hF | hne
  · -- the arc of the empty family is the whole walk
    zutn
    · simp_all
    · zujx
      · by_cases h0 : (p : ℝ) = 0
        · tauto
        · left; unfold sideInArc; grind
      · zulg
        have  := hε
        zujv
  · obtain ⟨hca, hcb, -⟩ := WalkAx.arc_cuts hne harc
    have hpx : (p : ℝ) < p + t' := by_simp_all
    obtain ⟨h1, h2⟩ := cyc_after_vertex hin by_simp_all by_simp_all hpx
    zujfv
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ht'.1] with ε hε hε'
    grind

/-! ## The test at a node end is valid and hits (M1) -/

/-- The domain of a good model is bounded in abscissa. -/
theorem goodModel_bounded (hGM : GoodModel M) : ∃ B : ℝ, ∀ x ∈ M.D, |x.1| < B := by
  rcases hGM with ⟨C, -, rfl⟩ | ⟨Q, -, rfl⟩
  · exact ⟨C.radius, fun x hx => hx.1.1⟩
  · refine ⟨Chazelle.Jordan.coordBound Q + 1, fun x hx => ?_⟩
    have := (Chazelle.Jordan.filled_subset_square Q hx.1).1
    linarith

/-- A horizontal ray leaves a good model's domain. -/
theorem ray_leaves (hGM : GoodModel M) (z : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ t₁ > (0 : ℝ), rayPt z σ t₁ ∉ M.D := by
  obtain ⟨B, hB⟩ := goodModel_bounded hGM
  refine ⟨|B| + |z.1| + 1, by_positivity, fun h => ?_⟩
  have h1 := hB _ h
  rw [rayPt_fst, abs_lt] at h1
  have h2 := le_abs_self B
  have h3 := neg_abs_le z.1
  have h4 := le_abs_self z.1
  rcases hσ with rfl | rfl <;> linarith [h1.1, h1.2]

/-- **The test at a position strictly inside an arc of `R`, in a direction of its left sector,
finds an exit** whose chord is admissible, not in `S`, with its domain part in `R` (the
hypotheses of the test's completeness clause). -/
theorem inner_exit (hGM : GoodModel M) {Q : Polygon} {S : Set ztf}
    (hFam : M.ChordFamily Q S) {R : Set Point} (hR : R ∈ M.regions S) {l r : ℝ}
    (harc : M.IsArc S R l r) {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hin : sideInArc l r ztk) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft M.W p t ztwyg)
    (htop : ∀ C : Chain, M = chainModel C → (sidePt M.W p t).2 ≤ C.top.2) :
    ∃ T > (0 : ℝ), (∀ s, 0 < s → s < T → rayPt ztbp σ s ∈ M.D) ∧
      rayPt ztbp σ T ∉ M.D ∧ chordOf ztbp σ T ∈ M.Adm ∧
      chordOf ztbp σ T ∉ S ∧ chordOf ztbp σ T ∩ M.D ⊆ R := by
  zubm
  zqbkm
  obtain ⟨r₁, hr₁, hsub⟩ := sector_sub_region hM hFam.2.1 hFam.1 hR harc hp ht0 ht1 hin
  have hini : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt w σ s ∈ R := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr₁] with s hs hs'
    zuesg
    refine hsub _ ?_ ((Sweep.sideLeft_rayPt_iff M.W p t σ hs0 one_pos).2 hsec)
    rw [mem_ball, Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq,
      add_sub_cancel_left]
    grind
  obtain ⟨t₁, ht₁, hout₁⟩ := ray_leaves hGM w hσ
  obtain ⟨T, hT, -, hTD, hRT, hadm, -⟩ := local_exit hGM hFam hR hσ
    (hM.trace p hp t ht0 ht1.le) hini ht₁ hout₁ htop
  have hdom : ∀ s, 0 < s → s < T → rayPt w σ s ∈ M.D := fun s h1 h2 =>
    (Chazelle.Chain.regionsIn_subset hR by_simp_all).1
  obtain ⟨h1, h2⟩ := ray_in_region hM hFam.2.1 hFam.1 hR harc hp ht0 ht1 hin hσ hT hsec hdom hTD
  grind

/-! ## Agreeing stretches: positions -/

/-- Positions at the same offset of agreeing stretches have the same parameter. -/
theorem param_agree {M M' : Model} {Q : Polygon} {g g' L : ℕ}
    (hA : WalkEmbed.Agree M.W M'.W g g' L) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.param Q ztwvk = M'.param Q ztxia := by
  zujpx
  zubi
  zuelf

/-- Positions at the same offset of agreeing stretches have the same point. -/
theorem pos_agree {M M' : Model} {Q : Polygon} {g g' L : ℕ}
    (hA : WalkEmbed.Agree M.W M'.W g g' L) {d : ℕ} (hd : d < L) (h : ℕ) :
    M.pos Q ztwvk = M'.pos Q ztxia := by
  zueew
  rw [param_agree hA hd h]
  zujqa
  zubi
  zuelf

/-- The point of a position is the walk point at its edge and parameter. -/
theorem pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge ztbyt := rfl

/-- The distance from `w` of a ray point. -/
theorem dist_rayPt (w : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {s : ℝ} (hs : 0 ≤ s) :
    dist (rayPt w σ s) w = s := by
  rw [Prod.dist_eq, rayPt_fst, rayPt_snd, dist_self, Real.dist_eq, add_sub_cancel_left]
  zur
  · simp_all
  simp_all

/-- **An attached level segment leaves into the left sector**: the ray towards its other end is
in the left sector of the attachment. -/
theorem attach_ray_left {W : Polygon} {c : Set Point} {p : ℕ} {t : ℝ} (hA : SideAttach W c p t)
    {σ L₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hL₀ : 0 < L₀)
    (hc : c = Chazelle.segment ztia (rayPt ztia σ L₀)) :
    sideLeft W p t ztxoo := by
  zudds
  set w := sidePt W p t
  set s := min (L₀ / 2) ztzr with hs
  zucmo
  have hsL : s < L₀ := by_simp_all
  have hsr : ztjan := by_simp_all
  have hmem : rayPt w σ s ∈ c := by
    zuktp
    refine ⟨s / L₀, by_positivity, (div_le_one hL₀).2 hsL.le, ?_⟩
    rw [lerp_rayPt, div_mul_cancel₀ _ hL₀.ne']
  have hd := dist_rayPt w hσ hs0.le
  have hne : rayPt w σ s ≠ w := fun h => by rw [h, dist_self] at hd; linarith
  exact (Sweep.sideLeft_rayPt_iff W p t σ hs0 one_pos).1 by_grind
end
end Restore
end Chazelle.Core
end
namespace Chazelle.Core
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs

/-- A fixed register of the search: the caller's registers `80000 … 80999`, the inputs
`81000 … 81006` and the data `81011 … 81027` set once at the start (constants, model and region
data). -/
def FFix (q : ℕ) : Prop := (80000 ≤ q ∧ q < 81007) ∨ (81011 ≤ q ∧ q < 81028)

/-- **The search invariant**, relative to the configuration `c₀` reached after the
initialisation. -/
structure FInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, FFix q → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a

/-- **A run step of the search.** -/
def FRS (B : Finset ℕ) (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ FInv W c₀ c' ∧ RF B ztdq c c' k ∧ Q c'
variable {B : Finset ℕ} {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {s : Stmt} {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
theorem FRS.mono {K K' : ℕ} {Q Q' : Config → Prop} (h : FRS B P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : FRS B P W c₀ s c K' Q' := by
  zuw
  exact ⟨c', k, ex, by_omega, hI, hrf, by_simp_all⟩
theorem FRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : FRS B P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, FInv W c₀ c₁ → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ → Q₁ c₁ →
      FRS B P W c₀ t c₁ K₂ Q₂) : FRS B P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  zudf
theorem FRS.ifT
    (ht : c.nreg a < c.nreg b) (h : FRS B P W c₀ t c K Q) :
    FRS B P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcou
theorem FRS.ifF
    (ht : ¬ c.nreg a < c.nreg b) (h : FRS B P W c₀ e c K Q) :
    FRS B P W c₀ ztva c ztnu Q := by
  zuw
  exact ztcov
theorem FRS.skip (hI : FInv W c₀ c) (hq : Q c) :
    FRS B P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by_omega, hI, RF.refl c 0, hq⟩

/-- A scratch register of the search: band `bRestore` from `81028` on, or a register of an
oracle band (the arguments of the cutter). -/
def FScr (r : ℕ) : Prop := (81028 ≤ r ∧ r < 90000) ∨ bandOf r ∈ oracleBands

/-- An output register of the search (the flag and the triple). -/
def FOut (r : ℕ) : Prop := 81007 ≤ r ∧ r < 81011
theorem FInv.regs (hB : dBands ⊆ B) {c' : Config} {k : ℕ} (hI : FInv W c₀ c)
    (hw : WordsBounded W c')
    (hr : ∀ r, ¬ FOut r → ¬ FScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : FInv W c₀ c' ∧ RF B ztdq c c' k := by
  have keep : ztlbw := fun q hq => hr q
    (by unfold FOut; unfold FFix at hq; omega)
    (by unfold FScr; unfold FFix at hq; rintro (h | h)
        · omega
        · exact band8_not_oracle by_omega by_omega h)
  have hA := hr ALLOC (by unfold FOut ALLOC; omega)
    (by unfold FScr ALLOC; decide)
  refine ⟨⟨hw, fun q hq => (keep q hq).trans ztfsi, by zvmze; exact hI.hA,
    fun a ha => by zvmwi; exact hI.hm a ha⟩,
    (rf_of_regs' (fun r hr' => hr r ?_ ?_) hrr hm hrm ho).mono hB le_rfl⟩
  · unfold FOut; intro h
    exact hr' ztlgu
  · unfold FScr; rintro (h | h)
    · exact hr' ztlgu
    tauto

/-- **One register instruction** on a scratch or output register. -/
theorem FRS.reg (hB : dBands ⊆ B) {i : Instr} {r v : ℕ} (hI : FInv W c₀ c)
    (hr : FScr r ∨ FOut r)
    (hex : Exec P W ztbgj c { c with nreg := upd c.nreg r v } 1) :
    FRS B P W c₀ ztbgj c 1 (fun c' => c' = { c with nreg := upd c.nreg r v }) := by
  obtain ⟨hI', hrf⟩ := hI.regs hB (k := 1) hex.wb_right
    (fun q h1 h2 => by
      zuby
      grind) rfl rfl rfl rfl
  exact ztinj

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem FRS.while {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, FInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      FRS B P W c₀ body c Kb ztesi)
    (hI : FInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + ztkq * μ c ≤ W) :
    FRS B P W c₀ ztpx c ztxrk
      ztcpy := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zukht
      obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hrf₁, hc₁, hμ₁⟩ := hbody c hI hc ht (by
        zuhdn
        omega)
      zumbn
      have hroom₁ : ztxiw := by
        zudxq

      zucbf
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, ?_, hI',
        (hrf₁.trans hrf₂).mono subset_rfl by_omega, hq⟩
      zucfy

    · exact ztfwc

/-- **A call of a statement with a `Meets` contract** whose postcondition keeps the inputs and
the constants of the search. -/
theorem FRS.call {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ B) (hI : FInv W c₀ c) (hpre : Pre P W c)
    (hroom : c.nreg ALLOC + cost P c ≤ W)
    (hprot : ∀ c', Post P c c' → ∀ q, FFix q → c'.nreg q = c.nreg q) :
    FRS B P W c₀ s c ztnxg (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) := by
  zute
  have hp := hprot c' hpost
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hp q hq).trans ztfsi,
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a ztftc).trans ztduw⟩,
    (RF.of_frame hfr hI.hA).mono hB le_rfl, hpost, hfr.2.2.2.2.2.1, hfr.2.2.1⟩

/-! ## Straight-line blocks -/

/-- The register effect of a straight-line register instruction (memory `m`). -/
def regI (m : ℕ → ℕ) : Instr → ztjx → ztjx
  | .constN r k, f => upd f r k
  | .copyN r a, f => upd f r ztbaa
  | .addN r a b, f => upd f r ztqmu
  | .subN r a b, f => upd f r ztqmv
  | .loadN r a, f => upd f r ztbaia
  | _, f => f

/-- The register effect of a block. -/
def regB (m : ℕ → ℕ) : List Instr → ztjx → ztjx
  | [], f => f
  | i :: l, f => regB m l ztefz

/-- An instruction the block lemma covers: a register instruction writing a scratch or output
register, with its value within the word bound. -/
def okI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN r k => ztpyr ∧ k ≤ W
  | .copyN r _ => FScr r ∨ FOut r
  | .addN r a b => ztpyr ∧ f a + f b ≤ W
  | .subN r _ _ => FScr r ∨ FOut r
  | .loadN r _ => FScr r ∨ FOut r
  | _ => False

/-- The side conditions of a block, along its run. -/
def okB (W : ℕ) (m : ℕ → ℕ) : List Instr → ztjx → Prop
  | [], _ => True
  | i :: l, f => okI W f i ∧ okB W m l ztefz

/-- One covered instruction. -/
theorem FRS.instr1 (hB : dBands ⊆ B) {i : Instr} (hI : FInv W c₀ c) (hi : okI W c.nreg i) :
    FRS B P W c₀ ztbgj c 1 (fun c' => c' = { c with nreg := regI c.nmem i c.nreg }) := by
  cases i with
  | constN r k => exact FRS.reg hB hI hi.1 ztpxt
  | copyN r a => exact FRS.reg hB hI hi zthqx
  | addN r a b => exact FRS.reg hB hI hi.1 ztows
  | subN r a b => exact FRS.reg hB hI hi ztjin
  | loadN r a => exact FRS.reg hB hI hi ztlel
  | _ => exact absurd hi by_tauto

/-- **A straight-line block** of register instructions. -/
theorem FRS.block (hB : dBands ⊆ B) : ∀ (l : List Instr) {c : Config}, FInv W c₀ c →
    okB W c.nmem l c.nreg →
    FRS B P W c₀ ztqcu c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg })
  | [], c, hI, _ => FRS.skip hI rfl
  | i :: l, c, hI, hok => by
    zuicq
    have h := FRS.seq (FRS.instr1 hB hI hi) (fun c₁ hI₁ _ h₁ => by
      subst h₁
      exact FRS.block hB l hI₁ hl)
    zugzd

/-- The destination register of a covered instruction. -/
def dstI : Instr → ℕ
  | .constN r _ => r
  | .copyN r _ => r
  | .addN r _ _ => r
  | .subN r _ _ => r
  | .loadN r _ => r
  | _ => 0
theorem regI_other (m f : ℕ → ℕ) (i : Instr) {q : ℕ} (hq : dstI i ≠ q) :
    regI m i f q = f q := by
  cases i <;> simp only [regI, dstI] at hq ⊢ <;> exact upd_ne ztvbm

/-- **A block leaves the registers it does not write.** -/
theorem regB_other (m : ℕ → ℕ) : ∀ (l : List Instr) (f : ℕ → ℕ) {q : ℕ},
    ztluv → regB m l f q = f q
  | [], _, _, _ => rfl
  | i :: l, f, q, h => by
    zudvf

/-- **A primitive call** (a step framed by the bands of the primitives). -/
theorem FRS.prim (hB : dBands ⊆ B) {s : Stmt} {c' : Config} {k k' K : ℕ} {Q : Config → Prop}
    (hI : FInv W c₀ c) (hex : Exec P W s c c' k) (hf₀ : Frame SweepPrim.primBands c c' k')
    (hkk : k' ≤ k)
    (hk : k ≤ K) (hq : Q c') : FRS B P W c₀ s c K Q := by
  have hf : Frame SweepPrim.primBands c c' k := ⟨hf₀.1, hf₀.2.1, hf₀.2.2.1, hf₀.2.2.2.1,
    hf₀.2.2.2.2.1,
    hf₀.2.2.2.2.2.1, by have := hf₀.2.2.2.2.2.2; omega⟩
  have h8 := fun q h1 h2 =>
    hf.1 q (by
      zukqg
      decide) (by unfold ALLOC; omega)
  refine ⟨c', k, hex, hk, ⟨hex.wb_right, fun q hq => ?_, hI.hA.trans hf.2.2.2.2.2.1,
    fun a ha => (hf.2.2.1 a (by have := hI.hA; omega)).trans ztduw⟩,
    (RF.of_frame hf hI.hA).mono (primBands_sub.trans hB) le_rfl, hq⟩
  unfold FFix at hq
  rw [h8 q by_omega by_omega]; exact hI.hin q by_tauto
