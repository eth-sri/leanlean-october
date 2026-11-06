module

public import Chazelle.Core.DownPhaseDrvBRegB

/-!
# Down-phase base (D9), RAM: one region of the region loop

`regB sH sE`: the region record (`rdS`), the host (`hostS sH`), `MX` (`mxS`), the point array
(`resPS`, the expansion `sE`), the points (`ptLoop`), the next region (`incS`).

**`regStep`**: `RegStepSpec (regB sH sE) κR` for the host RAM `sH` (`HostOK`) and the expansion
`sE` (`ExpOK`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs SignK WalkKey
open BuildRam (FrameM FrameM.mono FrameM.trans FrameB.toM)
open DrvR (regHost)

@[expose] public section

/-- **One region.** -/
def regB (sH sE : Stmt) : Stmt :=
  .seq rdS (.seq (hostS sH) (.seq mxS (.seq resPS (.seq sE (.seq ptLoop incS)))))

/-! ## Facts -/

theorem bktOK_congr {M : Model} {Q : Polygon} {N : NF} {T : List (ℕ × (ℕ × ℕ × ℕ))}
    {bk bk' : ℕ → ℕ} (h : DrvD.BktOK M Q N T bk) (he : ∀ q, q < 2 * T.length → bk' q = bk q) :
    DrvD.BktOK M Q N T bk' :=
  ⟨fun q hq => by rw [he q hq]; exact h.key q hq, fun q hq => by rw [he q hq]; exact h.arc q hq⟩

/-- The output survives a change of the registers outside `216020 … 216022` and of the memory
at or above the end of the output area. -/
theorem OutSt.congr {E : BEnv} {c c' : Config} {T : List (ℕ × (ℕ × ℕ × ℕ))} (h : OutSt E c T)
    (hT : T.length ≤ 2 * E.P.n)
    (hr : ∀ q, 216020 ≤ q → q ≤ 216022 → c'.nreg q = c.nreg q)
    (hm : ∀ a, a < E.B₂ + 10 * E.P.n → c'.nmem a = c.nmem a) : OutSt E c' T := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  have hBK : E.BK = E.B₂ + 6 * E.P.n := rfl
  refine ⟨?_, ?_, ?_, ?_, fun hK => ?_, fun hK q hq => ?_, fun a ha => ?_⟩
  · rw [hr _ le_rfl (by norm_num)]; exact a1
  · rw [hr _ (by norm_num) (by norm_num)]; exact a2
  · rw [hr _ (by norm_num) le_rfl]; exact a3
  · refine Gran.ChordListAt.congr a4 fun a h1 h2 => hm a ?_
    rw [List.length_map] at h2; omega
  · exact bktOK_congr (a5 hK) fun q hq => hm _ (by rw [hBK]; omega)
  · rw [hm _ (by rw [hBK]; omega)]; exact a6 hK q hq
  · rw [hm a (by omega)]; exact a7 a ha

/-- **At most `2 n` new chords.** -/
theorem newLB_len {E : BEnv} (hE : BGood E) : (newLB E.li E.Q E.L E.E).length ≤ 2 * E.P.n := by
  rw [← hE.hQn]
  apply length_le_of_chords
  · rcases Nat.eq_zero_or_pos E.K with hK | hK
    · rw [newLB_zero _ _ _ hK]; exact (newL0_ok hE.hQ hE.hDH hE.hli).2.1
    · rw [newLB_pos _ _ _ hK]
      have := (newL_ok (hE.ctx hK)).2.1
      rw [List.map_append] at this
      exact (List.nodup_append.1 this).2.1
  · intro x hx
    rw [newLB_eq_flatMap] at hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
    have hr' : r < E.K + 1 := List.mem_range.1 hr
    obtain ⟨S, R, hFam, hR⟩ := hE.regOK hr'
    exact (regList_sound hE.hQ hE.hDH hE.hli hFam hR (hE.pts_lt hr') hxr).1

/-- **The tagged records of the regions `< r`** are at most `2 n`. -/
theorem TL_len {E : BEnv} (hE : BGood E) {r : ℕ} (hr : r ≤ E.K + 1) :
    (E.TL r).length ≤ 2 * E.P.n := by
  have h1 := flatMap_range_length_mono (fun r' => (E.recs r').map fun x => (r', x)) hr
  have h2 : (E.TL (E.K + 1)).length = (newLB E.li E.Q E.L E.E).length := by
    rw [BEnv.TL_all]; unfold newLB; rw [List.length_map]
  have := newLB_len hE
  unfold BEnv.TL at h2
  unfold BEnv.TL
  omega

theorem inDrv_of {B : ℕ → Bool} (h : ∀ r, B r = true → 10000 ≤ r ∧ r < 230000) : DrvD.InDrv B :=
  fun r hr => ⟨DrvD.mem_drvBands (h r hr).1 (h r hr).2, by
    have := (h r hr).1; unfold ALLOC; omega⟩

theorem inDrv_pt : DrvD.InDrv Bpt := inDrv_of fun r h => by
  simp only [Bpt, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
    Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- The step bound of one region. -/
def regK (E : BEnv) (κH κE : ℕ) : ℕ := κH + κE * (2 * E.S₀ + 1) + (ptK E.Cm + 8) * E.S₀ + 50


section exec

theorem rf21 {A₀ : ℕ} {c c' : Config} {k : ℕ} (h : Frame {bDownDrv} c c' k)
    (hA : A₀ ≤ c.nreg ALLOC) : Restore.RF DrvR.drvBands A₀ c c' k :=
  (Restore.RF.of_frame h hA).mono (Finset.singleton_subset_iff.2 DrvR.bDownDrv_mem_drvBands) le_rfl

set_option maxHeartbeats 16000000 in
/-- **One region of the region loop.** -/
theorem regB_exec {sH sE : Stmt} {κH κE : ℕ} (hH : HostOK sH κH) (hX : ExpOK sE κE)
    {E : BEnv} (hE : BGood E) {r : ℕ} (hr : r < E.K + 1) (c : Config) (S : RSt E r c)
    (hroom : c.nreg ALLOC + regK E κH κE ≤ E.W) :
    ∃ c' k, Exec E.P E.W (regB sH sE) c c' k ∧ k ≤ regK E κH κE ∧ RSt E (r + 1) c' ∧
      Restore.RF DrvR.drvBands E.B₂ c c' k ∧
      (∀ q, (FixB q ∨ q = 212013 ∨ q = 216006) → c'.nreg q = c.nreg q) := by
  have R := S.regs
  have O := S.out
  have hQn := hE.hQn
  have hn3 := hE.hn3
  have hS₀ := hE.hS₀ r hr
  have hTr := TL_len hE (r := r) (by omega)
  have hTr1 := TL_len hE (r := r + 1) (by omega)
  obtain ⟨a1, a2⟩ := hE.areas hr
  have hLP := hE.LP_lt hr
  have hAc := S.alloc
  have hBW := hE.hBW
  unfold regK at hroom
  have hmul : 8 * E.S₀ ≤ (ptK E.Cm + 8) * E.S₀ := Nat.mul_le_mul_right _ (by omega)
  -- 1. the region record
  have hRP2 : E.RP r - 2 = E.m₀ (E.H + 5) + 5 * r := by unfold BEnv.RP; omega
  have hRP1 : E.RP r - 1 = E.m₀ (E.H + 5) + 5 * r + 1 := by unfold BEnv.RP; omega
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v33, f₁⟩ := rdS_exec (P := E.P) c S.wb S.p31 R.d16 R.K
    (by unfold BEnv.RP; omega) R.c0 R.c1 R.c2
    (by rw [hRP1, O.low _ (by omega)]; unfold BEnv.LP at hLP; omega)
  rw [hRP2, O.low _ (by omega)] at v34
  rw [hRP1, O.low _ (by omega)] at v33
  have g₁ : ∀ q, (q < 212032 ∨ 212034 < q) → c₁.nreg q = c.nreg q := fun q h =>
    f₁.1 q (by simp only [decide_eq_false_iff_not]; omega)
  have hnR : c₁.nreg 212034 = E.nRg r := by
    rw [v34]; unfold BEnv.nRg
    split_ifs
    · rfl
    · exact (hE.nA_eq hr).symm
  have hlp : c₁.nreg 212033 = E.LP r := v33
  have R₁ : BRegs E c₁ := R.congr fun q hq => g₁ q (by unfold FixB at hq; omega)
  have A₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (by unfold ALLOC; omega)
  -- 2. the host
  obtain ⟨c₂, k₂, H, e₂, hk₂, hHA, hwf, h21, h16, hpts, hHB1, hHB2, keep₂, F₂⟩ :=
    hostS_exec hH hE hr c₁ e₁.wb_right R₁ (by rw [g₁ _ (by omega)]; exact S.r14)
      (fun a ha => by rw [f₁.2.2.1]; exact O.low a ha) (by rw [A₁]; omega)
      (by rw [A₁]; omega)
  have hNPl : (E.pts r).length = (H.pts E.P.n).length := by rw [hpts, wlist_length]
  have hHl := host_len_le E.P.n H
  have K2 : ∀ q, (q < 215000 ∨ 216000 ≤ q) → q ≠ 212016 → q ≠ 212021 → q ≠ 212022 →
      q ≠ 212032 → q ≠ 212035 → q ≠ ALLOC → c₂.nreg q = c₁.nreg q := by
    intro q h1 a b d e f g
    by_cases hb : bandOf q = bDownDrv
    · exact keep₂ q hb h1 a b d e f
    · exact F₂.1 q (by simpa using hb) g
  have A₂ : c₂.nreg ALLOC ≤ c₁.nreg ALLOC + k₂ := F₂.2.2.2.2.2.2
  have A₂' : c₁.nreg ALLOC ≤ c₂.nreg ALLOC := F₂.2.2.2.2.2.1
  -- 3. `MX`
  obtain ⟨c₃, k₃, e₃, hk₃, v18, f₃⟩ := mxS_exec (P := E.P) c₂ e₂.wb_right
  have g₃ : ∀ q, q ≠ 212018 → c₃.nreg q = c₂.nreg q := fun q h => f₃.1 q (by simpa using h)
  -- 4. the point array
  obtain ⟨c₄, k₄, e₄, hk₄, v15, vA₄, f₄, F₄⟩ := resPS_exec (P := E.P) c₃ e₃.wb_right
    (NP := (H.pts E.P.n).length) (by rw [g₃ _ (by norm_num), h16])
    (by rw [g₃ _ (by norm_num), K2 _ (by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by unfold ALLOC; norm_num), R₁.c0])
    (by rw [g₃ _ (by unfold ALLOC; norm_num)]; omega)
  have g₄ : ∀ q, q ≠ 212015 → q ≠ 212035 → q ≠ 9999 → c₄.nreg q = c₃.nreg q := fun q a b d =>
    f₄.1 q (by simp [a, b, d])
  set PA := c₃.nreg ALLOC with hPAd
  have hPA2 : PA = c₂.nreg ALLOC := g₃ _ (by unfold ALLOC; norm_num)
  -- the registers kept from `c₁` to `c₄`
  have K4 : ∀ q, (q < 215000 ∨ 216000 ≤ q) → q ≠ 212015 → q ≠ 212016 → q ≠ 212018 →
      q ≠ 212021 → q ≠ 212022 → q ≠ 212032 → q ≠ 212035 → q ≠ 9999 →
      c₄.nreg q = c₁.nreg q := fun q h1 a b d e f g i j => by
    rw [g₄ q a i j, g₃ q d, K2 q h1 b e f g i (by unfold ALLOC; exact j)]
  -- 5. the expansion
  obtain ⟨c₅, k₅, e₅, hk₅, harr, hm₅, FM₅⟩ := hX E.P E.W c₄ H E.li e₄.wb_right
    (by rw [g₄ _ (by norm_num) (by norm_num) (by norm_num), g₃ _ (by norm_num), f₄.2.2.1,
      f₃.2.2.1]; exact hHA) hwf
    (by rw [g₄ _ (by norm_num) (by norm_num) (by norm_num), g₃ _ (by norm_num), h21])
    (by rw [g₄ _ (by norm_num) (by norm_num) (by norm_num), g₃ _ (by norm_num), h16])
    (by rw [K4 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact R₁.li)
    (by rw [K4 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact R₁.n)
    (by rw [K4 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact R₁.c0)
    (by rw [K4 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact R₁.c1)
    (by rw [K4 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact R₁.c2)
    (by rw [g₄ _ (by norm_num) (by norm_num) (by norm_num), g₃ _ (by norm_num), v15, hPA2]
        exact hHB2)
    (by rw [v15]; omega)
  have g₅ : ∀ q, (q < 212023 ∨ 212031 < q) → c₅.nreg q = c₄.nreg q := fun q h =>
    FM₅.1 q (by simp only [decide_eq_false_iff_not]; omega)
  have K5 : ∀ q, (FixB q ∨ q = 216031 ∨ q = 212033 ∨ q = 212034 ∨ q = 212013 ∨ q = 216006 ∨
      q = 212014 ∨ (216020 ≤ q ∧ q ≤ 216022)) → c₅.nreg q = c₁.nreg q := fun q hq => by
    unfold FixB at hq
    rw [g₅ q (by omega), K4 q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
  have A₄ : c₄.nreg ALLOC = PA + 3 * (H.pts E.P.n).length := vA₄
  have A₅ : c₅.nreg ALLOC = c₄.nreg ALLOC := g₅ _ (by unfold ALLOC; omega)
  have hmem5 : ∀ a, a < c.nreg ALLOC → c₅.nmem a = c.nmem a := fun a ha => by
    rw [hm₅ a (Or.inl (by rw [v15]; omega)), f₄.2.2.1, f₃.2.2.1, F₂.2.2.1 a (by rw [A₁]; exact ha),
      f₁.2.2.1]
  have S₅ : PtSt E r PA c₅ (E.TL r) := by
    refine ⟨e₅.wb_right, R₁.congr fun q hq => K5 q (Or.inl hq), ?_, fun hK => ?_, ?_, ?_, ?_,
      ?_, by omega, by rw [hNPl]; omega, ?_⟩
    · rw [K5 _ (by simp), g₁ _ (by omega)]; exact S.p31
    · rw [K5 _ (by simp)]; exact hlp
    · rw [K5 _ (by simp)]; exact hnR
    · rw [g₅ _ (by omega)]; exact v15
    · rw [g₅ _ (by omega), g₄ _ (by norm_num) (by norm_num) (by norm_num), g₃ _ (by norm_num),
        h16, hNPl]
    · intro k hk
      rw [hNPl] at hk
      have := harr k (by rw [wlist_length]; exact hk)
      rw [v15, ← hpts] at this
      cases hs : (E.pts r).getD k (.vtx 0) <;> rw [hs] at this <;> exact this
    · exact O.congr hTr (fun q h1 h2 => by rw [K5 _ (by omega), g₁ _ (by omega)])
        (fun a ha => hmem5 a (by omega))
  -- 6. the points
  have hT : (E.TL r).length + (E.recs r).length ≤ 2 * E.P.n := by
    rw [BEnv.TL_succ, List.length_append, List.length_map] at hTr1; exact hTr1
  obtain ⟨c₆, k₆, e₆, hk₆, S₆, FM₆, hm₆⟩ := ptLoop_exec hE hr c₅ S₅ hT
  rw [← BEnv.TL_succ] at S₆
  have g₆ : ∀ q, Bpt q = false → c₆.nreg q = c₅.nreg q := FM₆.1
  -- 7. the next region
  have r14 : c₆.nreg 212014 = r := by
    rw [g₆ _ (by decide), K5 _ (by simp), g₁ _ (by omega)]; exact S.r14
  have r31 : c₆.nreg 216031 = E.RP r := S₆.p31
  have r06 : c₆.nreg 216006 = 5 := by
    rw [g₆ _ (by decide), K5 _ (by simp), g₁ _ (by omega)]; exact S.c6
  obtain ⟨c₇, k₇, e₇, hk₇, u14, u31, f₇⟩ := incS_exec (P := E.P) c₆ S₆.wb r14 r31 S₆.regs.c0 r06
    (by omega) (by unfold BEnv.RP; omega)
  have g₇ : ∀ q, q ≠ 212014 → q ≠ 216031 → c₇.nreg q = c₆.nreg q := fun q a b =>
    f₇.1 q (by simp [a, b])
  have ex : Exec E.P E.W (regB sH sE) c c₇ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  -- the allocator
  have A₆ : c₆.nreg ALLOC = c₅.nreg ALLOC := g₆ _ (by decide)
  have A₇ : c₇.nreg ALLOC = c₆.nreg ALLOC := g₇ _ (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  -- the cost
  have hNS : (H.pts E.P.n).length ≤ E.S₀ := by rw [← hNPl]; exact hS₀
  have hk₅' : k₅ ≤ κE * (2 * E.S₀ + 1) := hk₅.trans (Nat.mul_le_mul_left _ (by omega))
  have hk₆' : k₆ ≤ (ptK E.Cm + 2) * E.S₀ + 3 :=
    hk₆.trans (by have := Nat.mul_le_mul_left (ptK E.Cm + 2) hS₀; omega)
  have hsplit : (ptK E.Cm + 8) * E.S₀ = (ptK E.Cm + 2) * E.S₀ + 6 * E.S₀ := by ring
  have hcost : k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))) ≤ regK E κH κE := by
    unfold regK; omega
  -- the frame
  have RF₁ : Restore.RF DrvR.drvBands E.B₂ c c₁ k₁ :=
    DrvD.rf_of_frameB (inDrv_of fun q h => by simp only [decide_eq_true_eq] at h; omega) f₁
  have RF₂ : Restore.RF DrvR.drvBands E.B₂ c₁ c₂ k₂ := rf21 F₂ (by rw [A₁]; omega)
  have RF₃ : Restore.RF DrvR.drvBands E.B₂ c₂ c₃ k₃ :=
    DrvD.rf_of_frameB (inDrv_of fun q h => by simp only [decide_eq_true_eq] at h; omega) f₃
  have RF₄ : Restore.RF DrvR.drvBands E.B₂ c₃ c₄ k₄ := rf21 F₄ (by omega)
  have RF₅ : Restore.RF DrvR.drvBands E.B₂ c₄ c₅ k₅ :=
    DrvD.rf_of_frameM (inDrv_of fun q h => by simp only [decide_eq_true_eq] at h; omega) FM₅
      (fun a ha => hm₅ a (Or.inl (by rw [v15]; omega)))
  have RF₆ : Restore.RF DrvR.drvBands E.B₂ c₅ c₆ k₆ :=
    DrvD.rf_of_frameM inDrv_pt FM₆ (fun a ha => hm₆ a (Or.inl ha))
  have RF₇ : Restore.RF DrvR.drvBands E.B₂ c₆ c₇ k₇ :=
    DrvD.rf_of_frameB (inDrv_of fun q h => by simp only [decide_eq_true_eq] at h; omega) f₇
  have RF := RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans (RF₅.trans (RF₆.trans RF₇)))))
  -- registers kept
  have keep : ∀ q, (FixB q ∨ q = 212013 ∨ q = 216006) → c₇.nreg q = c.nreg q := fun q hq => by
    have hq' : FixB q ∨ q = 212013 ∨ q = 216006 := hq
    unfold FixB at hq
    rw [g₇ q (by omega) (by omega), g₆ q (by
      simp only [Bpt, Bemit, Brec, DrvD.Bapp, DrvD.BappT, DrvD.Bscan, BuildRam.Bhalf, Bk,
        Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
      K5 q (by rcases hq' with h | h | h <;> simp [h]), g₁ q (by omega)]
  refine ⟨c₇, _, ex, hcost, ?_, RF, keep⟩
  -- the state of the next region
  have v18 : c₇.nreg 212018 = max (c.nreg 212018) (H.pts E.P.n).length := by
    rw [g₇ _ (by norm_num) (by norm_num), g₆ _ (by decide), g₅ _ (by omega),
      g₄ _ (by norm_num) (by norm_num) (by norm_num), v18, h16,
      K2 _ (by omega) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by unfold ALLOC; norm_num), g₁ _ (by omega)]
  refine ⟨e₇.wb_right, S₆.regs.congr fun q hq => g₇ q (by unfold FixB at hq; omega)
      (by unfold FixB at hq; omega), by rw [g₇ _ (by norm_num) (by norm_num)]; exact r06, u14,
    by rw [u31]; unfold BEnv.RP; ring, fun r' hr' => ?_, ?_, ?_, ?_⟩
  · rw [v18]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with h | h
    · exact (S.mx r' h).trans (le_max_left _ _)
    · subst h; rw [hNPl]; exact le_max_right _ _
  · rw [v18]; exact max_le S.mxS hNS
  · exact S₆.out.congr hTr1 (fun q h1 h2 => g₇ q (by omega) (by omega)) (fun a _ => by
      rw [f₇.2.2.1])
  · rw [A₇, A₆, A₅, A₄]; omega

end exec


/-- The constant of the per-point bound. -/
def ptA : ℕ := 10 * (visK + 2) + 20 * (DrvD.scanK + 2) + 3300

theorem ptK_le (C : ℕ) : ptK C + 8 ≤ ptA * (C + 1) := by
  unfold ptK dirK ptA; ring_nf; omega

/-- The constant of one region. -/
def κR (κH κE : ℕ) : ℕ := κH + 3 * κE + ptA + 50

theorem regK_le (E : BEnv) (κH κE : ℕ) :
    regK E κH κE ≤ κR κH κE * (E.S₀ + 1) * (E.Cm + 1) := by
  unfold regK κR
  have h1 := ptK_le E.Cm
  have h2 : (ptK E.Cm + 8) * E.S₀ ≤ ptA * (E.Cm + 1) * E.S₀ := Nat.mul_le_mul_right _ h1
  set X := E.S₀ + 1 with hXd
  set Y := E.Cm + 1 with hYd
  have hY : 1 ≤ Y := by omega
  have e1 : κH ≤ κH * X * Y := by
    calc κH = κH * 1 * 1 := by ring
      _ ≤ κH * X * Y := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hY
  have e2 : κE * (2 * E.S₀ + 1) ≤ 3 * κE * X * Y := by
    calc κE * (2 * E.S₀ + 1) ≤ 3 * κE * X * 1 := by rw [hXd]; nlinarith
      _ ≤ 3 * κE * X * Y := Nat.mul_le_mul_left _ hY
  have e3 : ptA * Y * E.S₀ ≤ ptA * X * Y := by
    calc ptA * Y * E.S₀ ≤ ptA * Y * X := Nat.mul_le_mul_left _ (by omega)
      _ = ptA * X * Y := by ring
  have e4 : 50 ≤ 50 * X * Y := by
    calc 50 = 50 * 1 * 1 := by ring
      _ ≤ 50 * X * Y := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hY
  have e5 : (κH + 3 * κE + ptA + 50) * X * Y = κH * X * Y + 3 * κE * X * Y + ptA * X * Y +
      50 * X * Y := by ring
  omega

/-- **One region of the region loop meets its contract.** -/
theorem regStep {sH sE : Stmt} {κH κE : ℕ} (hH : HostOK sH κH) (hX : ExpOK sE κE) :
    RegStepSpec (regB sH sE) (κR κH κE) := by
  intro E hE r c hr S hroom
  have hle := regK_le E κH κE
  obtain ⟨c', k, ex, hk, S', RF, keep⟩ := regB_exec hH hX hE hr c S (by omega)
  exact ⟨c', k, ex, hk.trans hle, S', RF, keep⟩

/-- **The region step**, from the host RAM and the expansion. -/
theorem regStepSpec_of (hHR : DrvR.HostRamSpec) (hEx : ExpSpec) :
    ∃ s κ, RegStepSpec s κ := by
  obtain ⟨sH, κH, hH⟩ := hostOK_of hHR
  obtain ⟨sE, κE, hX⟩ := expOK_of hEx
  exact ⟨regB sH sE, κR κH κE, regStep hH hX⟩

end

end DrvB

end Chazelle.Core
