module

public import Chazelle.Core.DownPhaseDrvPFront
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Down-phase pieces (D4), part 11: the normal form of a leaf and the chord list of a piece

* `bruteCall_exec`: brute force on the leaf `v_a … v_{a+m}` (`m ≤ 64`), `γ' = 1` or `2`;
* `l41Call_exec`: Lemma 4.1 on the leaf (`m > 64`) at grade `g = ⌈log₂ m⌉ ≤ μ`;
* `listS_exec`: the chord list of a piece: empty for a connector, the wall-filtered chords of
  the leaf's normal form for a leaf (`leaf_list`), with its validity in the chain model of the
  piece, degree `≤ 4`, `γ`-semigranularity and the size bound against `lemma41Nat μ`.
-/


namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs NFLoc SignK WalkKey
open BuildRegions (famOf)

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

/-- A store-free piece of the program writing registers of the driver's bands only. -/
theorem frame_of_wr {s : Stmt} {B : ℕ → Bool} {c c' : Config} {k : ℕ} (e : Exec P W s c c' k)
    (hs : wr B s = true) (hB : ∀ r, B r = true → bandOf r ∈ DrvR.drvBands)
    (hA : B ALLOC = false) : Frame DrvR.drvBands c c' k :=
  let F := exec_frameB e hs
  DrvT.frame_drv ⟨F.1, F.2.1, F.2.2.2.1, F.2.2.2.2⟩ hB hA (fun a _ => by rw [F.2.2.1])

theorem band21_not_brute : (21 : ℕ) ∉ bruteBands := by decide
theorem band21_not_l41 : (21 : ℕ) ∉ l41Bands := by decide
theorem brute_sub : bruteBands ⊆ DrvR.drvBands := by decide
theorem l41_sub : l41Bands ⊆ DrvR.drvBands := by decide

theorem rdB0 (c : Config) : rd c bBrute 0 = c.nreg 180000 := rfl
theorem rdB1 (c : Config) : rd c bBrute 1 = c.nreg 180001 := rfl
theorem rdB2 (c : Config) : rd c bBrute 2 = c.nreg 180002 := rfl
theorem rdB3 (c : Config) : rd c bBrute 3 = c.nreg 180003 := rfl
theorem rdL0 (c : Config) : rd c bL41 0 = c.nreg 160000 := rfl
theorem rdL1 (c : Config) : rd c bL41 1 = c.nreg 160001 := rfl
theorem rdL2 (c : Config) : rd c bL41 2 = c.nreg 160002 := rfl
theorem rdL3 (c : Config) : rd c bL41 3 = c.nreg 160003 := rfl
theorem rdL4 (c : Config) : rd c bL41 4 = c.nreg 160004 := rfl

/-- **Brute force on a short leaf.** -/
theorem bruteCall_exec {sB : Stmt} {κB : ℕ} (hBm : BruteM sB κB) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (h21 : c.nreg 218021 = 1) (hm1 : 1 ≤ c.nreg 218002) (hm64 : c.nreg 218002 ≤ 64)
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hroom : c.nreg ALLOC + κB * 274625 + 10 ≤ W) :
    ∃ c' k, Exec P W (bruteCall sB) c c' k ∧ k ≤ κB * 274625 + 10 ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218015 → c'.nreg r = c.nreg r) ∧
      ∃ CQ N₀ γ', CQ.P = Qof P ∧ CQ.s = c.nreg 218004 ∧ CQ.m = c.nreg 218002 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg 218015) N₀) ∧
        IsCanonicalNF (chainModel CQ) (Qof P) N₀ γ' 4 ∧
        ((c.nreg 218002 = 1 ∧ γ' = 1) ∨ (2 ≤ c.nreg 218002 ∧ γ' = 2)) := by
  have hW1 : 10 ≤ W := by ufo hostWords at hW
  -- the granularity
  obtain ⟨c₁, k₁, e₁, hk₁, v02, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      (.ifLtN 218021 218002 (block [.constN 180002 2]) (block [.constN 180002 1])) c c₁ k₁ ∧
      k₁ ≤ 3 ∧ ((c.nreg 218002 = 1 ∧ c₁.nreg 180002 = 1) ∨
        (2 ≤ c.nreg 218002 ∧ c₁.nreg 180002 = 2)) ∧
      (∀ r, r ≠ 180002 → c₁.nreg r = c.nreg r) ∧ FrameB (fun r => r == 180002) c c₁ := by
    by_cases h : c.nreg 218021 < c.nreg 218002
    · obtain ⟨c₁, k₁, e₁, hk₁, v, r⟩ : ∃ c₁ k₁, Exec P W (block [.constN 180002 2]) c c₁ k₁ ∧
          k₁ = 1 ∧ c₁.nreg 180002 = 2 ∧ (∀ r, r ≠ 180002 → c₁.nreg r = c.nreg r) := by
        exec_block
        · omega
        exact ⟨rfl, by config_simp, fun r hr => by simp [Config.nreg_mk, upd, ite_eq_right hr]⟩
      have ex := Exec.ifLtN_true (e := block [.constN 180002 1]) h e₁
      exact ⟨c₁, _, ex, by omega, Or.inr ⟨by omega, v⟩, r, exec_frameB ex (by decide)⟩
    · obtain ⟨c₁, k₁, e₁, hk₁, v, r⟩ : ∃ c₁ k₁, Exec P W (block [.constN 180002 1]) c c₁ k₁ ∧
          k₁ = 1 ∧ c₁.nreg 180002 = 1 ∧ (∀ r, r ≠ 180002 → c₁.nreg r = c.nreg r) := by
        exec_block
        · omega
        exact ⟨rfl, by config_simp, fun r hr => by simp [Config.nreg_mk, upd, ite_eq_right hr]⟩
      have ex := Exec.ifLtN_false (t := block [.constN 180002 2]) h e₁
      exact ⟨c₁, _, ex, by omega, Or.inl ⟨by omega, v⟩, r, exec_frameB ex (by decide)⟩
  have w₁ := e₁.wb_right
  -- the inputs
  obtain ⟨c₂, k₂, e₂, hk₂, v00, v01, v02'⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 180000 218004, .copyN 180001 218002]) c₁ c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg 180000 = c.nreg 218004 ∧ c₂.nreg 180001 = c.nreg 218002 ∧
      c₂.nreg 180002 = c₁.nreg 180002 := by
    exec_block
    exact ⟨rfl, by config_simp; exact r₁ _ (by norm_num), by config_simp; exact r₁ _ (by norm_num),
      by config_simp⟩
  have w₂ := e₂.wb_right
  have F₁₂ : FrameB (fun r => decide (180000 ≤ r ∧ r < 180003)) c c₂ :=
    (exec_frameB (Exec.seq e₁ e₂) (by decide) : FrameB (fun r => decide (180000 ≤ r ∧ r < 180003))
      c c₂)
  have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := F₁₂.1 _ (by decide)
  -- the call
  have hγ1 : 1 ≤ c₂.nreg 180002 ∧ (c₂.nreg 180001 = 1 ∨ 2 ≤ c₂.nreg 180002) := by
    rw [v02', v01]; rcases v02 with ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  have hpow : (c₂.nreg 180001 + 1) ^ 3 ≤ 274625 := by
    rw [v01]
    calc (c.nreg 218002 + 1) ^ 3 ≤ 65 ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 274625 := by norm_num
  have hcost : κB * (c₂.nreg 180001 + 1) ^ 3 ≤ κB * 274625 := Nat.mul_le_mul_left _ hpow
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨CQ, N₀, hCQ, hCs, hCm, hN₀, hcan⟩, F₃⟩ := hBm P W c₂ w₂
    ⟨hG, hW, by rwx [rdB1, v01], by rwx [rdB0, rdB1, v00, v01],
      by rw [rdB2]; exact hγ1.1, by rw [rdB1, rdB2]; exact hγ1.2⟩
    (by show c₂.nreg ALLOC + κB * (rd c₂ bBrute 1 + 1) ^ 3 ≤ W
        rw [rdB1, hA₂]; have := hcost; omega)
  replace hk₃ : k₃ ≤ κB * 274625 := hk₃.trans (by show κB * (rd c₂ bBrute 1 + 1) ^ 3 ≤ _
                                                  rwx [rdB1])
  have w₃ := e₃.wb_right
  -- the output
  obtain ⟨c₄, k₄, e₄, hk₄, v15, r₄⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 218015 180003]) c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 218015 = c₃.nreg 180003 ∧
      c₄ = { c₃ with nreg := upd c₃.nreg 218015 (c₃.nreg 180003) } := by
    exec_block
    exact ⟨rfl, by config_simp, rfl⟩
  have ex : Exec P W (bruteCall sB) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have G₁ : Frame DrvR.drvBands c c₂ (k₁ + k₂) := DrvT.frame_drv
    ⟨F₁₂.1, F₁₂.2.1, F₁₂.2.2.2.1, F₁₂.2.2.2.2⟩
    (fun r hr => by simp [decide_eq_true_eq] at hr; rw [DrvT.mem_drvBands]; unfold bandOf
                    omega) (by decide) (fun a _ => by rw [F₁₂.2.2.1])
  have G₂ : Frame DrvR.drvBands c₂ c₃ k₃ := F₃.mono brute_sub le_rfl
  have G₃ : Frame DrvR.drvBands c₃ c₄ k₄ := frame_of_wr e₄ (B := fun r => r == 218015)
    (by decide) (fun r hr => by simp [beq_iff_eq] at hr; subst hr; decide) (by decide)
  refine ⟨c₄, _, ex, by omega, (G₁.trans (G₂.trans G₃)).mono (by simp) (by omega), ?_,
    CQ, N₀, c₂.nreg 180002, hCQ, by rw [hCs, rdB0, v00], by rw [hCm, rdB1, v01], ?_, ?_, ?_⟩
  · intro r hr h15
    rw [r₄]; simp [upd, ite_eq_right h15]
    rw [F₃.1 r (by rw [hr]; exact band21_not_brute) (by ufo ALLOC bandOf at *),
      F₁₂.1 r (by simp [decide_eq_false_iff_not]; ufo bandOf at hr)]
  · rw [r₄]; simp [upd_same]
    have hA₄ : upd c₃.nreg 218015 (c₃.nreg 180003) ALLOC = c₃.nreg ALLOC := by simp [upd, ALLOC]
    rw [hA₄]
    rw [rdB3] at hN₀
    exact hN₀
  · rw [rdB2] at hcan; exact hcan
  · rwx [v02']

theorem seven_le_clog {m : ℕ} (hm : 65 ≤ m) : 7 ≤ Nat.clog 2 m := by
  by_contra h
  push Not at h
  have h1 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
  have h2 : 2 ^ Nat.clog 2 m ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (2 : ℕ) ^ 6 = 64 := by norm_num
  omega

/-- **Lemma 4.1 on a long leaf.** -/
theorem l41Call_exec {O : OracleIface} {sL : Stmt} {κL : ℕ} (hLm : L41M O sL κL) (c : Config)
    (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC))
    (h21 : c.nreg 218021 = 1) (hm65 : 65 ≤ c.nreg 218002) {μ : ℕ}
    (hμm : c.nreg 218002 ≤ 2 ^ μ) (hμΛ : μ ≤ c.nmem (c.nreg 218008))
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hroom : c.nreg ALLOC + 4 * μ + 9 + κL * (lemma41Nat μ + 1) ≤ W) :
    ∃ c' k, Exec P W (l41Call sL) c c' k ∧ k ≤ 4 * μ + 9 + κL * (lemma41Nat μ + 1) ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218015 → r ≠ 218019 → r ≠ 218023 → c'.nreg r = c.nreg r) ∧
      ∃ CQ N₀ g, CQ.P = Qof P ∧ CQ.s = c.nreg 218004 ∧ CQ.m = c.nreg 218002 ∧
        Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg 218015) N₀) ∧
        IsCanonicalNF (chainModel CQ) (Qof P) N₀ (gradeGran g) 4 ∧ 1 ≤ g ∧ g ≤ μ ∧
        c.nreg 218002 ≤ 2 ^ g := by
  have hWh := hW
  unfold hostWords at hWh
  obtain ⟨m, hm⟩ : ∃ m, c.nreg 218002 = m := ⟨_, rfl⟩
  rw [hm] at hm65 hμm ham ⊢
  set g := Nat.clog 2 m with hg
  have hg7 := seven_le_clog hm65
  have hgμ : g ≤ μ := Nat.clog_le_of_le_pow hμm
  have hmg : m ≤ 2 ^ g := Nat.le_pow_clog (by norm_num) m
  have hgm : 2 ^ (g - 1) < m := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := m) (by omega)
    rw [← hg] at this
    simpa [Nat.pred_eq_sub_one] using this
  -- the grade
  obtain ⟨c₁, k₁, e₁, hk₁, v19, r₁, m₁, rr₁, rm₁, o₁⟩ := clogS_exec (P := P) c hw hm (by omega)
    h21 (by omega)
  rw [← hg] at v19 hk₁
  have w₁ := e₁.wb_right
  -- the inputs
  obtain ⟨c₂, k₂, e₂, hk₂, v0, v1, v2, v3, r₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 160000 218008, .copyN 160001 218004, .copyN 160002 218002,
        .copyN 160003 218019]) c₁ c₂ k₂ ∧ k₂ = 4 ∧
      c₂.nreg 160000 = c.nreg 218008 ∧ c₂.nreg 160001 = c.nreg 218004 ∧
      c₂.nreg 160002 = m ∧ c₂.nreg 160003 = g ∧
      (∀ r, (r < 160000 ∨ 160004 ≤ r) → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; exact r₁ _ (by norm_num) (by norm_num)
    · config_simp; exact r₁ _ (by norm_num) (by norm_num)
    · config_simp; rw [r₁ _ (by norm_num) (by norm_num), hm]
    · config_simp; exact v19
    · simp [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  have w₂ := e₂.wb_right
  have hA₂ : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [r₂ _ (by ufo ALLOC), r₁ _ (by decide) (by decide)]
  have hm₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  have hcost : κL * (lemma41Nat g + 1) ≤ κL * (lemma41Nat μ + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (lemma41Nat_mono hgμ) 1)
  -- the call
  obtain ⟨c₃, k₃, e₃, hk₃, ⟨CQ, N₀, hCQ, hCs, hCm, hN₀, hcan⟩, F₃⟩ := hLm P W c₂ w₂
    ⟨hG, hW, by rwx [rdL0, v0, hm₂, hA₂], by rwo [rdL0, rdL3, v0, v3, hm₂],
      by rwx [rdL3, v3], by rwx [rdL1, rdL2, v1, v2],
      by rwx [rdL2, rdL3, v2, v3], by rwx [rdL2, rdL3, v2, v3]⟩
    (by show c₂.nreg ALLOC + κL * (lemma41Nat (rd c₂ bL41 3) + 1) ≤ W
        rwo [rdL3, v3, hA₂])
  replace hk₃ : k₃ ≤ κL * (lemma41Nat μ + 1) := hk₃.trans (by
    show κL * (lemma41Nat (rd c₂ bL41 3) + 1) ≤ _
    rwx [rdL3, v3])
  rw [rdL1, v1] at hCs
  rw [rdL2, v2] at hCm
  rw [rdL3, v3] at hcan
  rw [rdL4] at hN₀
  have w₃ := e₃.wb_right
  -- the output
  obtain ⟨c₄, k₄, e₄, hk₄, v15, r₄⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 218015 160004]) c₃ c₄ k₄ ∧
      k₄ = 1 ∧ c₄.nreg 218015 = c₃.nreg 160004 ∧
      c₄ = { c₃ with nreg := upd c₃.nreg 218015 (c₃.nreg 160004) } := by
    exec_block
    exact ⟨rfl, by config_simp, rfl⟩
  have ex : Exec P W (l41Call sL) c c₄ (k₁ + (k₂ + (k₃ + k₄))) :=
    .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have G₁ : Frame DrvR.drvBands c c₂ (k₁ + k₂) := by
    refine ⟨fun r hr hra => ?_, fun r _ => by rw [rr₂, rr₁], fun a _ => by rw [hm₂],
      fun a _ => by rw [rm₂, rm₁], by rw [o₂, o₁], by rw [hA₂], by rwo [hA₂]⟩
    have h1 : r < 160000 ∨ 160004 ≤ r := by
      by_contra h; exact hr (by ruo [DrvT.mem_drvBands] bandOf)
    rw [r₂ r h1, r₁ r (fun h => hr (by rwd [h])) (fun h => hr (by rwd [h]))]
  have G₂ : Frame DrvR.drvBands c₂ c₃ k₃ := F₃.mono l41_sub le_rfl
  have G₃ : Frame DrvR.drvBands c₃ c₄ k₄ := frame_of_wr e₄ (B := fun r => r == 218015)
    (by decide) (fun r hr => by simp [beq_iff_eq] at hr; subst hr; decide) (by decide)
  refine ⟨c₄, _, ex, by omega, (G₁.trans (G₂.trans G₃)).mono (by simp) (by omega), ?_,
    CQ, N₀, g, hCQ, hCs, hCm, ?_, hcan, by omega, hgμ, hmg⟩
  · intro r hr h15 h19 h23
    rw [r₄]; simp [upd, ite_eq_right h15]
    rw [F₃.1 r (by rw [hr]; exact band21_not_l41) (by ufo ALLOC bandOf at *),
      r₂ r (by ufo bandOf at hr), r₁ r h19 h23]
  · rw [r₄]; simp [upd_same]
    have hA₄ : upd c₃.nreg 218015 (c₃.nreg 160004) ALLOC = c₃.nreg ALLOC := by simp [upd, ALLOC]
    rw [hA₄]
    exact hN₀

/-- Lemma 2.3 on the normal form of a leaf. -/
theorem k0_count {Q : Polygon} {CQ : Chain} {N₀ : NF} {γ' : ℕ} (hP : CQ.P.Simple)
    (hcan : IsCanonicalNF (chainModel CQ) Q N₀ γ' 4) :
    N₀.chords.length * (γ' + 1) ≤ 840 * (2 * CQ.m + 1) := by
  have := DownMath.trans_count hP hcan
  rwa [DrvT.ncard_F hcan.1.2.1] at this

theorem gradeGran_ge (g : ℕ) : 2 ^ Cost.ceilBeta g ≤ gradeGran g := by
  ufo gradeGran

theorem gradeGran_ge_one (g : ℕ) : 1 ≤ gradeGran g :=
  (Nat.one_le_two_pow).trans (gradeGran_ge g)

theorem gradeGran_ge_two {g : ℕ} (hg : 1 ≤ g) : 2 ≤ gradeGran g := by
  have h1 := DrvT.le_gradeGran g
  have h2 : 1 ≤ 2 ^ Cost.ceilBeta g := Nat.one_le_two_pow
  have : gradeGran g = 2 ^ Cost.ceilBeta g + fuseLoss * (g * (Nat.clog 2 g + 2)) := rfl
  have hf : fuseLoss = 1 := rfl
  rw [this, hf, one_mul]
  have : g ≤ g * (Nat.clog 2 g + 2) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The normal form of a leaf** (brute force or Lemma 4.1) and the facts of its wall-filtered
chord list in the chain model of the piece. -/
theorem nf0_exec {O : OracleIface} {sL sB : Stmt} {κL κB : ℕ} (hLm : L41M O sL κL)
    (hBm : BruteM sB κB) (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC))
    (h21 : c.nreg 218021 = 1) (h22 : c.nreg 218022 = 65) (hm1 : 1 ≤ c.nreg 218002)
    (hμm : c.nreg 218002 ≤ 2 ^ c.nreg 218005) (hμΛ : c.nreg 218005 ≤ c.nmem (c.nreg 218008))
    (ham : c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n)
    (hγ : 2 * gradeGran (c.nreg 218005) ≤ c.nreg 218007)
    (CH : Chain) (hCHs : CH.P.Simple)
    (htwin : ∀ CQ : Chain, CQ.P = Qof P → CQ.s = c.nreg 218004 → CQ.m = c.nreg 218002 →
      BoxT.Twin CQ CH)
    (hroom : c.nreg ALLOC + κB * 274625 + 12 + 4 * c.nreg 218005 +
      κL * (lemma41Nat (c.nreg 218005) + 1) ≤ W) :
    ∃ c' k, Exec P W (.ifLtN 218002 218022 (bruteCall sB) (l41Call sL)) c c' k ∧
      k ≤ κB * 274625 + 12 + 4 * c.nreg 218005 + κL * (lemma41Nat (c.nreg 218005) + 1) ∧
      Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → r ≠ 218015 → r ≠ 218019 → r ≠ 218023 → c'.nreg r = c.nreg r) ∧
      ∃ N₀ : NF, Robust (c'.nreg ALLOC) c'.nmem (fun m => NFAt m (c'.nreg 218015) N₀) ∧
        ChordTriplesOK (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀)) ∧
        (chainModel CH).DegLe
          (famOf (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀))) 4 ∧
        (chainModel CH).Semigranular
          (famOf (chainModel CH) (Qof P) (BoxT.dropWalls (DrvT.triplesOf N₀))) (c.nreg 218007) ∧
        N₀.chords.length * (Nat.clog 2 N₀.chords.length + 1) ≤
          1950480 * (lemma41Nat (c.nreg 218005) + 1) ∧
        N₀.chords.length ≤ 108360 * (lemma41Nat (c.nreg 218005) + 1) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, c.nreg 218005 = μ := ⟨_, rfl⟩
  rw [hμ] at hμm hμΛ hγ hroom ⊢
  have hQs : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  by_cases h64 : c.nreg 218002 < c.nreg 218022
  · rw [h22] at h64
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, CQ, N₀, γ', hCQ, hCs, hCm, hN₀, hcan, hγ'⟩ :=
      bruteCall_exec hBm c hw hG hW h21 hm1 (by omega) ham (by omega)
    have hT := htwin CQ hCQ hCs hCm
    obtain ⟨hok, hdeg, hwt⟩ := leaf_list hG hCQ hT hCHs hcan
    have hK := k0_count (by rwx [hCQ]) hcan
    rw [hCm] at hK
    have hK₀ : N₀.chords.length ≤ 108360 := by
      have : N₀.chords.length ≤ N₀.chords.length * (γ' + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hKc : N₀.chords.length * (Nat.clog 2 N₀.chords.length + 1) ≤ 1950480 := by
      have h1 := kcost_mono hK₀
      have h2 : Nat.clog 2 108360 ≤ 17 := Nat.clog_le_of_le_pow (by norm_num)
      have : 108360 * (Nat.clog 2 108360 + 1) ≤ 1950480 := by
        calc 108360 * (Nat.clog 2 108360 + 1) ≤ 108360 * 18 := Nat.mul_le_mul_left _ (by omega)
          _ = 1950480 := by norm_num
      omega
    have hγle : 2 * γ' ≤ c.nreg 218007 := by
      rcases hγ' with ⟨h1, rfl⟩ | ⟨h2, rfl⟩
      · have := gradeGran_ge_one μ; omega
      · have hμ1 : 1 ≤ μ := by
          by_contra h0
          have : μ = 0 := by omega
          rw [this] at hμm; sio at hμm
        have := gradeGran_ge_two hμ1; omega
    refine ⟨c₁, _, Exec.ifLtN_true (by rwx [h22]) e₁, by omega,
      Frame.mono F₁ le_rfl (by omega), fun r hr a b d => r₁ r hr a, N₀, hN₀, hok, hdeg,
      semigranular_mono hwt hγle, ?_, ?_⟩
    · have : 1950480 ≤ 1950480 * (lemma41Nat μ + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have : 108360 ≤ 108360 * (lemma41Nat μ + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · rw [h22] at h64
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, CQ, N₀, g, hCQ, hCs, hCm, hN₀, hcan, hg1, hgμ, hmg⟩ :=
      l41Call_exec hLm c hw hG hW hgr h21 (by omega) hμm hμΛ ham (by omega)
    have hT := htwin CQ hCQ hCs hCm
    obtain ⟨hok, hdeg, hwt⟩ := leaf_list hG hCQ hT hCHs hcan
    have hK := k0_count (by rwx [hCQ]) hcan
    rw [hCm] at hK
    have hK2 : N₀.chords.length * 2 ^ Cost.ceilBeta g ≤ 2520 * 2 ^ g := by
      have h1 : N₀.chords.length * 2 ^ Cost.ceilBeta g ≤ N₀.chords.length * (gradeGran g + 1) :=
        Nat.mul_le_mul_left _ (by have := gradeGran_ge g; omega)
      have h2 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
      omega
    have hKc := kcost_le hg1 hK2
    have hmono := lemma41Nat_mono hgμ
    have hγle : 2 * gradeGran g ≤ c.nreg 218007 := (Nat.mul_le_mul_left 2 (gradeGran_mono hgμ)).trans hγ
    refine ⟨c₁, _, Exec.ifLtN_false (by rwx [h22]) e₁, by omega,
      Frame.mono F₁ le_rfl (by omega), r₁, N₀, hN₀, hok, hdeg, semigranular_mono hwt hγle, ?_, ?_⟩
    · have : 35280 * lemma41Nat g ≤ 1950480 * (lemma41Nat μ + 1) := by nlinarith
      omega
    · have h0 : N₀.chords.length ≤ N₀.chords.length * (Nat.clog 2 N₀.chords.length + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have : 35280 * lemma41Nat g ≤ 108360 * (lemma41Nat μ + 1) := by nlinarith
      omega

/-- The constant of the chord list of a piece. -/
def κLst (κL κB : ℕ) : ℕ := κB * 274625 + κL + 4659540

theorem lst_cost (κL κB μ X : ℕ) (hX : μ + 1 ≤ X) :
    κB * 274625 + 12 + 4 * μ + κL * X + 43 * (108360 * X) + 22 ≤ κLst κL κB * X := by
  unfold κLst
  have e : (κB * 274625 + κL + 4659540) * X = κB * 274625 * X + κL * X + 4659540 * X := by ring
  rw [e]
  have h2 : 43 * (108360 * X) = 4659480 * X := by ring
  rw [h2]
  have h1 : κB * 274625 ≤ κB * 274625 * X := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : 4659480 * X + 60 * X = 4659540 * X := by ring
  generalize κB * 274625 * X = A at h1 ⊢
  generalize κL * X = B
  generalize κB * 274625 = D at *
  generalize 4659480 * X = E at *
  generalize 4659540 * X = F at *
  omega

/-- **The chord list of a piece**: empty (connector) or the wall-filtered chords of the normal
form of the leaf, at `218016` (length `218017`), below the allocator. -/
theorem listS_exec {O : OracleIface} {sL sB : Stmt} {κL κB : ℕ} (hLm : L41M O sL κL)
    (hBm : BruteM sB κB) (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC))
    (h21 : c.nreg 218021 = 1) (h22 : c.nreg 218022 = 65)
    (hm1 : 1 ≤ c.nreg 218002) (hkind : c.nreg 218003 ≤ 1)
    (hleaf : c.nreg 218003 = 1 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem (c.nreg 218008) ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ P.n ∧
      2 * gradeGran (c.nreg 218005) ≤ c.nreg 218007)
    (hconn : c.nreg 218003 = 0 → c.nreg 218002 ≤ 64 ∧ 2 * c.nreg 218002 ≤ c.nreg 218007)
    (CH : Chain) (hCHs : CH.P.Simple) (hCm : CH.m = c.nreg 218002)
    (htwin : c.nreg 218003 = 1 → ∀ CQ : Chain, CQ.P = Qof P → CQ.s = c.nreg 218004 →
      CQ.m = c.nreg 218002 → BoxT.Twin CQ CH)
    (hroom : c.nreg ALLOC + κLst κL κB * (lemma41Nat (c.nreg 218005) + 1) ≤ W) :
    ∃ c' k, Exec P W (listS sL sB) c c' k ∧
      k ≤ κLst κL κB * (lemma41Nat (c.nreg 218005) + 1) ∧ Frame DrvR.drvBands c c' k ∧
      (∀ r, bandOf r = 21 → (r < 218015 ∨ 218024 ≤ r) → (r < 218070 ∨ 218081 ≤ r) →
        c'.nreg r = c.nreg r) ∧
      ∃ L : List (ℕ × ℕ × ℕ), ChordListAt c'.nmem (c'.nreg 218016) L ∧
        c'.nreg 218017 = L.length ∧ c'.nreg 218016 + 3 * L.length ≤ c'.nreg ALLOC ∧
        ChordTriplesOK (chainModel CH) (Qof P) L ∧
        (chainModel CH).DegLe (famOf (chainModel CH) (Qof P) L) 4 ∧
        (chainModel CH).Semigranular (famOf (chainModel CH) (Qof P) L) (c.nreg 218007) ∧
        L.length * (Nat.clog 2 L.length + 1) ≤ 1950480 * (lemma41Nat (c.nreg 218005) + 1) := by
  obtain ⟨μ, hμ⟩ : ∃ μ, c.nreg 218005 = μ := ⟨_, rfl⟩
  rw [hμ] at hleaf hroom ⊢
  have hμl := le_lemma41Nat μ
  unfold listS
  by_cases hk : c.nreg 218003 < c.nreg 218021
  · -- a connector
    have hk0 : c.nreg 218003 = 0 := by omega
    obtain ⟨h64, h2m⟩ := hconn hk0
    obtain ⟨c₁, k₁, e₁, hk₁, v16, v17, r₁⟩ : ∃ c₁ k₁, Exec P W connS c c₁ k₁ ∧ k₁ = 2 ∧
        c₁.nreg 218016 = 0 ∧ c₁.nreg 218017 = 0 ∧
        (∀ r, r ≠ 218016 → r ≠ 218017 → c₁.nreg r = c.nreg r) := by
      unfold connS
      exec_block
      all_goals first | omega | skip
      refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_⟩
      simp [Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2]
    have ex := Exec.ifLtN_true (e := leafS sL sB) hk e₁
    obtain ⟨hok, hdeg, hwt⟩ := conn_list (P := P) hCHs (γ := c.nreg 218007) (by rwx [hCm])
    have G₁ : Frame DrvR.drvBands c c₁ k₁ := frame_of_wr e₁
      (B := fun r => decide (218016 ≤ r ∧ r < 218018))
      (by sid only [connS, wr, block, wrOK]) (fun r hr => by
        simp [decide_eq_true_eq] at hr; ruo [DrvT.mem_drvBands] bandOf)
      (by decide)
    refine ⟨c₁, _, ex, ?_, G₁.mono le_rfl (by omega), fun r _ h1 _ => r₁ r (by omega) (by omega),
      [], fun i hi => by simp at hi, by rwr [v17], by rws [v16], hok, hdeg, hwt,
      by simp⟩
    have := lst_cost κL κB μ (lemma41Nat μ + 1) (by omega)
    omega
  · -- a leaf
    have hk1 : c.nreg 218003 = 1 := by omega
    obtain ⟨hμm, hμΛ, ham, hγ⟩ := hleaf hk1
    refine spec_ifLtN_false hk ?_
    unfold leafS
    have hroom' : c.nreg ALLOC + κB * 274625 + 12 + 4 * c.nreg 218005 +
        κL * (lemma41Nat (c.nreg 218005) + 1) ≤ W := by
      rw [hμ]
      have := lst_cost κL κB μ (lemma41Nat μ + 1) (by omega)
      omega
    obtain ⟨c₁, k₁, e₁, hk₁, F₁, r₁, N₀, hN₀, hok, hdeg, hwt, hKc, hK₀⟩ := nf0_exec hLm hBm c hw
      hG hW hgr h21 h22 hm1 (by rw [hμ]; exact hμm) (by rw [hμ]; exact hμΛ) ham
      (by rw [hμ]; exact hγ) CH hCHs (htwin hk1) hroom'
    rw [hμ] at hk₁ hKc hK₀
    have w₁ := e₁.wb_right
    have h21₁ : c₁.nreg 218021 = 1 := by
      rwx [r₁ _ (by decide) (by decide) (by decide) (by decide)]
    have hA₁ := F₁.2.2.2.2.2.2
    obtain ⟨c₂, k₂, e₂, hk₂, hk₂', v16, v17, v99, hCL, hlow, r₂, rr₂, rm₂, o₂⟩ :=
      dropS_exec (P := P) c₁ w₁ hN₀ h21₁ (by
        have := lst_cost κL κB μ (lemma41Nat μ + 1) (by omega)
        omega)
    set L := BoxT.dropWalls (DrvT.triplesOf N₀) with hL
    have hLK : L.length ≤ N₀.chords.length := by
      have := List.length_filter_le keepW (DrvT.triplesOf N₀)
      unfold DrvT.triplesOf at this; rw [List.length_map] at this
      rwx [hL, dropWalls_eq]
    have G₂ : Frame DrvR.drvBands c₁ c₂ k₂ := by
      refine ⟨fun r hr hra => ?_, fun r _ => by rw [rr₂], hlow, fun a _ => by rw [rm₂], o₂,
        by rwo [v99], by rwo [v99]⟩
      have hb : bandOf r ≠ 21 := fun h => hr (by rwd [h])
      exact r₂ r (by ufo bandOf at hb) (by ufo bandOf at hb)
        (by ufo bandOf at hb) hra
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, ?_, (F₁.trans G₂).mono (by simp) (by omega), ?_, L, ?_, ?_, ?_,
      hok, hdeg, hwt, (kcost_mono hLK).trans hKc⟩
    · have := lst_cost κL κB μ (lemma41Nat μ + 1) (by omega)
      omega
    · intro r hr h1 h2
      rw [r₂ r (by omega) (by omega) h2 (by ufo ALLOC bandOf at *),
        r₁ r hr (by omega) (by omega) (by omega)]
    · rwx [v16]
    · rw [v17]
    · rw [v16, v99]

end exec

end

end DrvP

end Chazelle.Core
