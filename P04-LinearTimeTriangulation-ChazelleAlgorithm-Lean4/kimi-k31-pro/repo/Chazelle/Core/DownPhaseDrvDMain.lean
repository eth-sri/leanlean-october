module

public import Chazelle.Core.DownPhaseDrvDRound3
public import Chazelle.Core.DownPhaseOracleIO
public import Chazelle.Core.RestoreFindOK
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.GradeCtx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 16000000

/-!
# Down-phase restoration rounds (D8), part 14: the contract `RoundsSpec`

`roundsS sF sB` runs `d₀` rounds (`rounds_exec`, from `round_step`).

* **`roundsSpec_of`**: for a splitting step `sF` meeting `Restore.FindOK` with the interior
  oracles' bands, and a sorted build `sB` (`DrvR.SortedMeets`), on a context with local
  capacity and oracle costs `F γ, G γ ≥ 1`: `DrvR.RoundsSpec X F G H`, with the constant
  `κR κf κB d₀`.
* **`roundsSpec`**: `DrvR.IntOraclesSpec O → ∃ κo, DrvR.RoundsSpec (gradeCtx O) (shCost κo)
  (cuCost κo) cutGran` (the splitting step `Restore.findSpec` with the interior oracles, the
  sorted build `buildNFSorted`).
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

/-- The constants and the round counter. -/
theorem initS_exec (c : Config) (hw : WordsBounded W c) (hW : 5 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k = 6 ∧ c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧
      c'.nreg 216004 = 4 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧ c'.nreg 216010 = 0 ∧
      FrameB (fun r => decide (216002 ≤ r ∧ r ≤ 216010)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W initS c c' k ∧ k = 6 ∧
      (c'.nreg 216002 = 1 ∧ c'.nreg 216003 = 0 ∧
      c'.nreg 216004 = 4 ∧ c'.nreg 216005 = 2 ∧ c'.nreg 216006 = 5 ∧ c'.nreg 216010 = 0) := by
    unfold initS
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2,
    exec_frameB ex (by decide)⟩

end exec

/-- The level state depends only on the registers `210001 … 210005`, the memory and the
allocator. -/
theorem stateAt_congr {P : Polygon} {c c' : Config} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (h : DrvR.StateAt P c L E)
    (hr : ∀ i, 1 ≤ i → i ≤ 5 → c'.nreg (210000 + i) = c.nreg (210000 + i))
    (hm : c'.nmem = c.nmem) (hA : c'.nreg ALLOC = c.nreg ALLOC) : DrvR.StateAt P c' L E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e1 := hr 1 (by norm_num) (by norm_num)
  have e2 := hr 2 (by norm_num) (by norm_num)
  have e3 := hr 3 (by norm_num) (by norm_num)
  have e4 := hr 4 (by norm_num) (by norm_num)
  have e5 := hr 5 (by norm_num) (by norm_num)
  simp only [Nat.reduceAdd] at e1 e2 e3 e4 e5
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at h1 h2 h3 h4 h5 h6 h7 h11 ⊢
  unfold DrvR.StateAt
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd]
  rw [e1, e2, e3, e4, e5, hm, hA]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **All rounds.** -/
theorem rounds_exec {E : DEnv} (hE : DGood E) {c : Config} (hI : RInv E 0 c) :
    ∃ c' k, Exec E.P E.W (.whileLtN 216010 216000 (roundBody E.sF E.sB)) c c' k ∧
      RInv E E.d0 c' ∧ Restore.RF DrvR.drvBands E.A₀ c c' k ∧ k ≤ (E.Br + 2) * E.d0 + 2 := by
  obtain ⟨c', k, e, ⟨t, I'⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame (P := E.P) (W := E.W)
    (a := 216010) (b := 216000) (body := roundBody E.sF E.sB) (B := DrvR.drvBands) (A₀ := E.A₀)
    (fun c => ∃ t, RInv E t c) (fun c => E.d0 - c.nreg 216010) E.Br
    (fun c ⟨_, h⟩ => h.wb)
    (fun c ⟨t, I⟩ ht => by
      rw [I.r10, I.r00] at ht
      obtain ⟨c', k, e, I', RF', hk⟩ := round_step hE I ht
      exact ⟨c', k, e, ⟨t + 1, I'⟩, RF', hk, by rwo [I.r10, I'.r10]⟩) ⟨0, hI⟩
  have ht : t = E.d0 := by
    rw [I'.r10, I'.r00] at hx; have := I'.t_le; omega
  subst ht
  refine ⟨c', k, e, I', RFl, ?_⟩
  rw [hI.r10] at hk
  simpa using hk

/-! ## The cost -/

/-- The per-round constant. -/
def C2 (κf : ℕ → ℕ) (κB d0 : ℕ) : ℕ :=
  κf d0 + 2 * ((scanK + 2) * (d0 + 1)) + 70 + 8 * DrvR.κSpl κB

/-- **The constant of the rounds.** -/
def κR (κf : ℕ → ℕ) (κB : ℕ) (d0 : ℕ) : ℕ := 20 + d0 * (42 + C2 κf κB d0 * 2 ^ d0)

/-- The round bound is linear in the chord count, with the oracle factor. -/
theorem Br_le (E : DEnv) (hA : 1 ≤ E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + 1)) :
    E.Br + 2 ≤ (42 + C2 E.κf E.κB E.d0 * 2 ^ E.d0) * (E.K₀ + 1) *
      (E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + 1)) := by
  set A := E.F E.γ * E.G E.γ * (E.Hc E.γ + Nat.clog 2 E.γ + 1) with hAd
  set T := 2 ^ E.d0 with hT
  set K1 := E.K₀ + 1 with hK1
  have hBr : E.Br = 40 + (E.Bf + 10) * (T * K1) + 8 * DrvR.κSpl E.κB * (T * K1) := rfl
  have hBf : E.Bf = E.κf E.d0 * A + 2 * ((scanK + 2) * (E.d0 + 1)) + 60 := by
    show Restore.costF E.κf E.F E.G E.Hc E.d0 E.γ + _ + 60 = _
    urring Restore.costF [hAd]
  have hTK : 1 ≤ T * K1 := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h1 : E.Bf + 10 ≤ (E.κf E.d0 + 2 * ((scanK + 2) * (E.d0 + 1)) + 70) * A := by
    have e : (E.κf E.d0 + 2 * ((scanK + 2) * (E.d0 + 1)) + 70) * A =
        E.κf E.d0 * A + (2 * ((scanK + 2) * (E.d0 + 1)) + 70) * A := by ring
    have : 2 * ((scanK + 2) * (E.d0 + 1)) + 70 ≤ (2 * ((scanK + 2) * (E.d0 + 1)) + 70) * A :=
      Nat.le_mul_of_pos_right _ hA
    omega
  have h2 : (E.Bf + 10) * (T * K1) + 8 * DrvR.κSpl E.κB * (T * K1) ≤
      C2 E.κf E.κB E.d0 * A * (T * K1) := by
    have h3 := Nat.mul_le_mul_right (T * K1) h1
    have h4 : 8 * DrvR.κSpl E.κB * (T * K1) ≤ 8 * DrvR.κSpl E.κB * A * (T * K1) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hA)
    have h5 : C2 E.κf E.κB E.d0 * A * (T * K1) =
        (E.κf E.d0 + 2 * ((scanK + 2) * (E.d0 + 1)) + 70) * A * (T * K1) +
          8 * DrvR.κSpl E.κB * A * (T * K1) := by ufring C2
    omega
  have h6 : 42 ≤ 42 * K1 * A := by
    have : 1 ≤ K1 * A := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : 42 * K1 * A = 42 * (K1 * A) := by ring
    omega
  have h7 : (42 + C2 E.κf E.κB E.d0 * T) * K1 * A =
      42 * K1 * A + C2 E.κf E.κB E.d0 * A * (T * K1) := by ring
  rw [h7, hBr]
  omega

/-! ## The contract -/

/-- **The restoration rounds meet their contract**, for a splitting step with the interior
oracles' bands and a sorted build. -/
theorem roundsSpec_of {sF sB : Stmt} {κf : ℕ → ℕ} {κB : ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    (hF : Restore.FindOK sF κf F G H X DrvR.OkInt DrvR.ioBandsD) (hB : DrvR.SortedMeets sB κB)
    (hloc : X.CapLocal) (hF1 : ∀ γ, 1 ≤ F γ) (hG1 : ∀ γ, 1 ≤ G γ) :
    DrvR.RoundsSpec X F G H := by
  refine ⟨roundsS sF sB, κR κf κB, ?_⟩
  intro P W c hw pre hroom
  obtain ⟨hEnv, hd4, hγ1, hγn, L₀, E₀, hSt, hdeg, hsg⟩ := pre
  obtain ⟨hG, hW3, hWh, -, hXh, hcap⟩ := hEnv
  beta_reduce at hroom ⊢
  have hSt₀ := hSt
  obtain ⟨hD6, hDa, hK, -, -, -, -, -, -, -, -⟩ := hSt₀
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at hD6 hDa hK
  have hc1 : coreReg 1 = 230001 := rfl
  rw [hc1] at hXh hcap
  -- the data
  set E : DEnv := ⟨P, W, c.nreg ALLOC, c.nmem, c.nreg, c.nreg 210001, c.nreg 216001,
    c.nreg 216000, c.nreg 230001, sF, sB, κf, κB, F, G, H, X,
    (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L₀ E₀).F (interiorModel (Qof P)) (Qof P),
    L₀.length⟩ with hEd
  have hMD : ModelDescAt c.nmem (c.nreg 210001) (Qof P) (interiorModel (Qof P)) := hDa.holds
  have hone : c.nmem (c.nreg 210001) = 1 := desc_one hMD
  have hE : DGood E := by
    refine ⟨hF, hB, hG, hWh, hXh, fun m hm => ?_, ⟨hD6, fun h0 => ?_⟩, hMD, hd4⟩
    · show c.nreg 216001 ≤ X.cap P m (c.nreg 230001)
      rwo [hloc P c.nmem m _ _ hm hXh]
    · exact absurd (hone.symm.trans h0) (by norm_num)
  -- the cost factor
  have hA1 : 1 ≤ F (c.nreg 216001) * G (c.nreg 216001) *
      (H (c.nreg 216001) + Nat.clog 2 (c.nreg 216001) + 1) := by
    have := hF1 (c.nreg 216001); have := hG1 (c.nreg 216001)
    have : 1 ≤ F (c.nreg 216001) * G (c.nreg 216001) := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hBr := Br_le E hA1
  set A := F (c.nreg 216001) * G (c.nreg 216001) *
    (H (c.nreg 216001) + Nat.clog 2 (c.nreg 216001) + 1) with hAd
  have hcost : κR κf κB (c.nreg 216000) * (c.nreg 210003 + 1) * F (c.nreg 216001) *
      G (c.nreg 216001) * (H (c.nreg 216001) + Nat.clog 2 (c.nreg 216001) + 1) =
      κR κf κB (c.nreg 216000) * (L₀.length + 1) * A := by rwring [hK, hAd]
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at hroom ⊢
  rw [hcost] at hroom ⊢
  have hBig : (E.Br + 2) * E.d0 + 10 ≤ κR κf κB (c.nreg 216000) * (L₀.length + 1) * A := by
    have h1 : (E.Br + 2) * E.d0 ≤
        ((42 + C2 κf κB (c.nreg 216000) * 2 ^ (c.nreg 216000)) * (L₀.length + 1) * A) *
          c.nreg 216000 := Nat.mul_le_mul_right _ hBr
    have h2 : κR κf κB (c.nreg 216000) * (L₀.length + 1) * A =
        20 * ((L₀.length + 1) * A) + ((42 + C2 κf κB (c.nreg 216000) * 2 ^ (c.nreg 216000)) *
          (L₀.length + 1) * A) * c.nreg 216000 := by ufring κR
    have h3 : 1 ≤ (L₀.length + 1) * A := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  -- initialisation
  have hW5 : 5 ≤ W := le_trans (by ufo hostWords) hWh
  obtain ⟨c₁, k₁, e₁, hk₁, i02, i03, i04, i05, i06, i10, f₁⟩ := initS_exec (P := P) c hw hW5
  have g₁ : ∀ q, ¬ (216002 ≤ q ∧ q ≤ 216010) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q (by simpa using hq)
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (by ufo ALLOC)
  have hI0 : RInv E 0 c₁ := by
    refine ⟨e₁.wb_right, g₁ _ (by omega), g₁ _ (by omega), g₁ _ (by omega), i02, i03, i04, i05,
      i06, i10, g₁ _ (by omega), fun q hq => g₁ q (by ufo KeepR at hq),
      ⟨L₀, E₀, stateAt_congr hSt (fun i h1 h2 => g₁ _ (by omega)) m₁ A₁, subset_rfl,
        Model.DegLe.mono _ hdeg (by show c.nreg 216000 ≤ max 4 (c.nreg 216000 - 0); omega), hsg,
        by show L₀.length + 1 ≤ 2 ^ 0 * (L₀.length + 1); simp⟩, fun a _ => by rw [m₁], by rw [A₁],
      Nat.zero_le _, ?_⟩
    rw [A₁]
    show c.nreg ALLOC + (c.nreg 216000 - 0) * (E.Br + 2) + 3 ≤ W
    have : (c.nreg 216000 - 0) * (E.Br + 2) = (E.Br + 2) * E.d0 := by
      show (c.nreg 216000 - 0) * (E.Br + 2) = (E.Br + 2) * c.nreg 216000
      rw [Nat.sub_zero, mul_comm]
    omega
  -- the rounds
  obtain ⟨c₂, k₂, e₂, I₂, RF₂, hk₂⟩ := rounds_exec hE hI0
  have RF₁ : Restore.RF DrvR.drvBands (c.nreg ALLOC) c c₁ k₁ :=
    rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨mem_drvBands (by omega) (by omega), by ufo ALLOC⟩) f₁
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, ⟨I₂.keep, fun L E hSt' => ?_⟩,
    (RF₁.trans RF₂).to_frame⟩
  -- the post
  have hSt'' := hSt'
  obtain ⟨-, -, hK', -, hLa', -, hEa', -, -, -, -⟩ := hSt''
  obtain ⟨-, -, -, -, hLa, -, hEa, -, -, -, -⟩ := hSt
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at hK' hLa' hEa' hLa hEa
  have hLL : L₀ = L := BuildNF.chordListAt_unique hLa.holds hLa'.holds (by rw [← hK, hK'])
  subst hLL
  have hEE : E₀ = E := hEa.holds.symm.trans hEa'.holds
  subst hEE
  obtain ⟨L', E', hSt₂, hsub, hdeg₂, hsg₂, hcnt₂⟩ := I₂.state
  refine ⟨L', E', hSt₂, hsub, Model.DegLe.mono _ hdeg₂ (by show max 4 (E.d0 - E.d0) ≤ 4; simp),
    hsg₂, hcnt₂⟩

/-! ## The restoration rounds of the down phase -/

theorem shCost_mono (κ γ : ℕ) : DrvR.shCost κ γ ≤ DrvR.shCost (κ + 1) γ := by
  unfold DrvR.shCost
  have := Nat.mul_le_mul_right (rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3))
    (Nat.mul_le_mul_right (Nat.clog 2 γ + 1) (show κ ≤ κ + 1 by omega))
  omega

theorem cuCost_mono (κ γ : ℕ) : DrvR.cuCost κ γ ≤ DrvR.cuCost (κ + 1) γ := by
  unfold DrvR.cuCost
  exact Nat.mul_le_mul_right _ (show κ ≤ κ + 1 by omega)

theorem shCost_pos (κ γ : ℕ) : 1 ≤ DrvR.shCost (κ + 1) γ := by
  ufo DrvR.shCost

theorem cuCost_pos (κ γ : ℕ) : 1 ≤ DrvR.cuCost (κ + 1) γ := by
  unfold DrvR.cuCost
  exact Nat.one_le_iff_ne_zero.2 (by positivity)

/-- **D8: the restoration rounds of a down-phase level**, from the interior oracles. -/
theorem roundsSpec {O : OracleIface} (hio : DrvR.IntOraclesSpec O) :
    ∃ κo, DrvR.RoundsSpec (gradeCtx O) (DrvR.shCost κo) (DrvR.cuCost κo) cutGran := by
  obtain ⟨sh, cu, κ, hsh, hcu⟩ := hio
  obtain ⟨mkF, κf, hmk⟩ := Restore.findSpec
  have hsh' := IOrc.shooterOK_weaken hsh (fun _ _ => id) (shCost_mono κ)
  have hcu' := IOrc.cutterOK_weaken hcu (fun _ _ => id) (cuCost_mono κ)
  have hF := hmk sh cu DrvR.ioBandsD DrvR.ioBandsD (DrvR.shCost (κ + 1)) (DrvR.cuCost (κ + 1))
    cutGran (gradeCtx O) DrvR.OkInt DrvR.ioBandsD DrvR.oracleBands_subset_ioBandsD
    DrvR.bRestore_notin_ioBandsD (gradeCtx_capLocal O) (ShootCut.gradeCtx_halves O)
    (fun _ _ h => Or.inr h) subset_rfl subset_rfl hsh' hcu'
  obtain ⟨sB, κB, hB⟩ := DrvR.sortedMeets_of buildNFSorted
  exact ⟨κ + 1, roundsSpec_of hF hB (gradeCtx_capLocal O) (shCost_pos κ) (cuCost_pos κ)⟩

end

end DrvD

end Chazelle.Core
