module

public import Chazelle.Core.DownPhaseDrvPCalls
public import Chazelle.Core.DownPhaseDrvTMain

/-!
# Down-phase pieces (D4), part 10: the descriptor part of a piece

`frontS = cntS ; topS ; betaS ; descS`: the host count, the top offset (scan for `m ≤ 64`, the
grade table for a longer leaf), the orientation bit, and the model descriptor at the allocator.
`frontS_exec`: the descriptor describes the chain `C = ⟨H.poly Q, s, m⟩` of the host (its top
index and bit), within `1204 μ + 140000` steps.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace DrvP

open Machine Machine.Stmt Programs NFLoc SignK WalkKey

@[expose] public section

/-- The registers written by the top computations (scan or grade table). -/
def Btp (r : ℕ) : Bool :=
  decide (50046 ≤ r ∧ r < 50080) || Bk r || decide (170000 ≤ r ∧ r < 170100) ||
    decide (r = 218013) || decide (218030 ≤ r ∧ r < 218050)

/-- The registers written by the count, the top and the bit. -/
def Ball (r : ℕ) : Bool := Bsc r || Btp r || Bbit r

theorem bscan_btp {r : ℕ} (h : Bscan r = true) : Btp r = true := by
  simp only [Bscan, Btp, Bhost, Bk, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega

theorem bg_btp {r : ℕ} (h : Bg r = true) : Btp r = true := by
  simp only [Bg, Btp, Bk, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢; omega

theorem frameB_mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2⟩
  · cases hb : B r
    · rfl
    · rw [hB r hb] at hr; exact absurd hr (by decide)
  · cases hb : B r
    · rfl
    · rw [hB r hb] at hr; exact absurd hr (by decide)

theorem ball_band {r : ℕ} (h : Ball r = true) : bandOf r ∈ DrvR.drvBands := by
  simp only [Ball, Bsc, Btp, Bbit, Bk, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [DrvT.mem_drvBands]; unfold bandOf; omega

theorem ball_false {r : ℕ} (h1 : r < 10000 ∨ 10500 ≤ r) (h2 : r < 50046 ∨ 50080 ≤ r)
    (h3 : r < 170000 ∨ 170100 ≤ r) (h4 : r < 218012 ∨ 218100 ≤ r) : Ball r = false := by
  simp only [Ball, Bsc, Btp, Bbit, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The descriptor part of a piece.** -/
theorem frontS_exec {O : OracleIface} (c : Config) (hw : WordsBounded W c)
    (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hgr : (gradeCtx O).holds P c.nmem (c.nreg 218008) (c.nreg ALLOC))
    (hm1 : 1 ≤ c.nreg 218002) {H : Host}
    (hH : Robust (c.nreg ALLOC) c.nmem (fun m => HostAt m (c.nreg 218000) H))
    (hHA : c.nreg 218000 + 3 * H.length + 4 ≤ c.nreg ALLOC) (hl : H.length ≤ 64)
    (hwf : HostWF (Qof P).n H)
    (hsm : c.nreg 218001 + c.nreg 218002 + 1 ≤ (H.pts (Qof P).n).length)
    (hleaf : ¬ c.nreg 218002 < 65 → c.nreg 218002 ≤ 2 ^ c.nreg 218005 ∧
      c.nreg 218005 ≤ c.nmem (c.nreg 218008) ∧ c.nreg 218004 + c.nreg 218002 + 1 ≤ (Qof P).n ∧
      ∀ k, k ≤ c.nreg 218002 →
        (H.pts (Qof P).n).getD (c.nreg 218001 + k) (.vtx 0) = .vtx (c.nreg 218004 + k))
    (hroom : c.nreg ALLOC + 1204 * c.nreg 218005 + 140000 ≤ W)
    (CH : Chain) (hCH : CH.P = H.poly (Qof P)) (hCs : CH.s = c.nreg 218001)
    (hCm : CH.m = c.nreg 218002) :
    ∃ c' k, Exec P W frontS c c' k ∧ k ≤ 1204 * c.nreg 218005 + 140000 ∧
      Frame DrvR.drvBands c c' k ∧
      c'.nreg 218010 = c.nreg ALLOC ∧ c'.nreg ALLOC = c.nreg ALLOC + 6 ∧
      (∀ r, 218000 ≤ r → r < 218010 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 218000 ∨ 219000 ≤ r) → (r < 10000 ∨ 10500 ≤ r) → (r < 50046 ∨ 50080 ≤ r) →
        (r < 170000 ∨ 170100 ≤ r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.nreg 218021 = 1 ∧ c'.nreg 218022 = 65 ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      c'.nmem (c.nreg ALLOC) = 0 ∧ c'.nmem (c.nreg ALLOC + 1) = c.nreg 218000 ∧
      c'.nmem (c.nreg ALLOC + 2) = CH.s ∧ c'.nmem (c.nreg ALLOC + 3) = CH.m ∧
      c'.nmem (c.nreg ALLOC + 4) = CH.topIdx ∧
      (c'.nmem (c.nreg ALLOC + 5) = 1 ↔ CH.sideBeta = true) := by
  have hn : (Qof P).n = P.n := qof_n P
  rw [hn] at hwf hsm hleaf
  have hWh := hW
  unfold hostWords at hWh
  have hA := hw.1 ALLOC
  obtain ⟨HB, hHB⟩ : ∃ HB, c.nreg 218000 = HB := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, c.nreg 218001 = s := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, c.nreg 218002 = m := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, c.nreg 218005 = μ := ⟨_, rfl⟩
  rw [hHB] at hH hHA ⊢
  rw [hs] at hsm hleaf hCs
  rw [hm] at hm1 hsm hleaf hCm
  rw [hμ] at hleaf hroom ⊢
  have E : ScE P W H c.nmem HB := ⟨hG, hW, hH.holds, hwf, hl, by omega⟩
  -- 1. the count
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, v12, v20, v21, v22, E₁⟩ := cntS_exec (P := P) c hw (H := H)
    (by rw [hHB]; exact hH.holds) (by rw [hHB]; omega) E.hN (by omega)
  rw [hHB] at E₁
  have k₁' : ∀ r, Bsc r = false → c₁.nreg r = c.nreg r := F₁.1
  have g₁ : ∀ r, 218000 ≤ r → r < 218012 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    k₁' r (by simp only [Bsc, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have w₁ := e₁.wb_right
  -- 2. the top
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, hT, hTm⟩ : ∃ c₂ k₂, Exec P W topS c₁ c₂ k₂ ∧
      k₂ ≤ 1204 * μ + 129240 ∧ FrameB Btp c₁ c₂ ∧ HostEnv W HB H.length c.nmem c₂ ∧
      c₂.nreg 218013 = CH.topIdx ∧ c₂.nreg 218013 ≤ m := by
    unfold topS
    by_cases h64 : c₁.nreg 218002 < c₁.nreg 218022
    · have hm64 : m < 65 := by
        rwa [g₁ 218002 (by norm_num) (by norm_num), hm, v22] at h64
      refine spec_ifLtN_true h64 ?_
      have a01 : c₁.nreg 218001 = s := by rw [g₁ 218001 (by norm_num) (by norm_num), hs]
      have a02 : c₁.nreg 218002 = m := by rw [g₁ 218002 (by norm_num) (by norm_num), hm]
      obtain ⟨c₂, k₂, e₂, hk₂, F₂, E₂, hT, hle, hlt⟩ := scanS_exec E c₁ E₁ v20 v21
        (by rwa [a01, a02])
      rw [a01, a02] at hle
      rw [a01] at hlt
      rw [a02] at hk₂ hT
      refine ⟨c₂, k₂, e₂, by omega, frameB_mono F₂ (fun r hr => bscan_btp hr), E₂, ?_, hT⟩
      exact (hchain_topIdx hCH (by rw [hCs, hCm]; omega) (by rwa [hCm])
        (by rwa [hCs, hCm]) (by rwa [hCs])).symm
    · have hm64 : ¬ m < 65 := by
        rwa [g₁ 218002 (by norm_num) (by norm_num), hm, v22] at h64
      refine spec_ifLtN_false h64 ?_
      obtain ⟨hμm, hμΛ, ham, hpts⟩ := hleaf hm64
      have hμ1 : 1 ≤ μ := by
        by_contra h0
        have : μ = 0 := by omega
        rw [this] at hμm; simp at hμm; omega
      obtain ⟨c₂, k₂, e₂, hk₂, F₂, hT, hle⟩ := gTop_exec (P := P) (W := W) (O := O)
        (s := ⟨c.nreg ALLOC, c.nmem, c.nreg 218008⟩) c₁ w₁ hG hW
        (fun a _ => by rw [F₁.2.2.1]) (by rw [F₁.1 _ (by decide)]) hgr
        (g₁ 218008 (by norm_num) (by norm_num)) hμ1 (μ := μ)
        (by rwa [g₁ 218002 (by norm_num) (by norm_num), hm]) hμΛ
        (by rw [g₁ 218002 (by norm_num) (by norm_num), g₁ 218004 (by norm_num) (by norm_num), hm]
            exact ham)
      rw [g₁ 218002 (by norm_num) (by norm_num), hm] at hT hle
      rw [g₁ 218004 (by norm_num) (by norm_num)] at hle
      have hg : ∀ r, Bg r = false → c₂.nreg r = c₁.nreg r := F₂.1
      have E₂ : HostEnv W HB H.length c.nmem c₂ := by
        have g : ∀ r, 50060 ≤ r → r < 50070 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
          hg r (by simp only [Bg, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            beq_eq_false_iff_ne]; omega)
        exact ⟨e₂.wb_right, by rw [g _ (by norm_num) (by norm_num)]; exact E₁.h60,
          by rw [g _ (by norm_num) (by norm_num)]; exact E₁.h61,
          by rw [g _ (by norm_num) (by norm_num)]; exact E₁.h67,
          by rw [g _ (by norm_num) (by norm_num)]; exact E₁.h68,
          by rw [g _ (by norm_num) (by norm_num)]; exact E₁.h69, by rw [F₂.2.2.1]; exact E₁.mem⟩
      refine ⟨c₂, k₂, e₂, by omega, frameB_mono F₂ (fun r hr => bg_btp hr), E₂, ?_, hT⟩
      have hD : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
      refine (hchain_topIdx_leaf hCH (by rw [hCs, hCm]; omega) hD (a := c.nreg 218004)
        (by rw [hCm]; omega) (fun k hk => ?_) (by rwa [hCm]) (by rwa [hCm])).symm
      rw [hCs]; unfold pt; exact hpts k (by rwa [hCm] at hk)
  have g₂ : ∀ r, 218000 ≤ r → r < 218013 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by simp only [Btp, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have g₂' : ∀ r, 218020 ≤ r → r < 218023 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂.1 r (by simp only [Btp, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  -- 3. the bit
  obtain ⟨c₃, k₃, e₃, hk₃, F₃, b₃, hb₃⟩ := betaS_exec E c₂ E₂
    (by rw [g₂ 218012 (by norm_num) (by norm_num), v12])
    (by rw [g₂' _ (by norm_num) (by norm_num), v20])
    (by rw [g₂' _ (by norm_num) (by norm_num), v21])
    (by rw [g₂ 218001 (by norm_num) (by norm_num), g₁ 218001 (by norm_num) (by norm_num), hs, hT]
        have := CH.topIdx_le; rw [hCm] at this; omega)
  rw [g₂ 218001 (by norm_num) (by norm_num), g₁ 218001 (by norm_num) (by norm_num), hs, hT] at hb₃
  have w₃ := e₃.wb_right
  have g₃ : ∀ r, 218000 ≤ r → r < 218014 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    F₃.1 r (by simp only [Bbit, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have g₃' : ∀ r, 218020 ≤ r → r < 218023 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    F₃.1 r (by simp only [Bbit, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have hβ : (c₃.nreg 218014 = 1 ↔ CH.sideBeta = true) := by
    rw [hb₃]
    rcases Nat.eq_zero_or_pos CH.topIdx with h0 | h0
    · rw [Brute.sideBeta_of_top_zero h0, h0]; simp
    · rw [hchain_beta hCH h0 (by rw [hCs]; have := CH.topIdx_le; rw [hCm] at this; omega),
        hCs]
      exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩
  -- 4. the descriptor
  have c₃20 : c₃.nreg 218020 = 0 := by
    rw [g₃' _ (by norm_num) (by norm_num), g₂' _ (by norm_num) (by norm_num), v20]
  have c₃21 : c₃.nreg 218021 = 1 := by
    rw [g₃' _ (by norm_num) (by norm_num), g₂' _ (by norm_num) (by norm_num), v21]
  have c₃22 : c₃.nreg 218022 = 65 := by
    rw [g₃' _ (by norm_num) (by norm_num), g₂' _ (by norm_num) (by norm_num), v22]
  have F₁₃ : FrameB Ball c c₃ :=
    (frameB_mono F₁ (fun r hr => by simp [Ball, hr])).trans
      ((frameB_mono F₂ (fun r hr => by simp [Ball, hr])).trans
        (frameB_mono F₃ (fun r hr => by simp [Ball, hr])))
  have hA₃ : c₃.nreg ALLOC = c.nreg ALLOC := F₁₃.1 _ (by decide)
  obtain ⟨c₄, k₄, e₄, hk₄, v10, v99, r₄, rr₄, rm₄, o₄, ml₄, d0, d1, d2, d3, d4, d5⟩ :=
    descS_exec (P := P) c₃ w₃ c₃20 c₃21 (by rw [hA₃]; omega)
  rw [hA₃] at v10 v99 ml₄ d0 d1 d2 d3 d4 d5
  have ex : Exec P W frontS c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have gin : ∀ r, 218000 ≤ r → r < 218010 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [g₃ r h1 (by omega), g₂ r h1 (by omega), g₁ r h1 (by omega)]
  refine ⟨c₄, _, ex, by omega, ?_, v10, v99, fun r h1 h2 => ?_, fun r h1 h2 h3 h4 h5 => ?_,
    ?_, ?_, fun a ha => ?_, d0, ?_, ?_, ?_, ?_, ?_⟩
  · -- the frame
    have G₁ : Frame DrvR.drvBands c c₃ (k₁ + (k₂ + k₃)) :=
      DrvT.frame_drv ⟨F₁₃.1, F₁₃.2.1, F₁₃.2.2.2.1, F₁₃.2.2.2.2⟩ (fun r hr => ball_band hr)
        (by decide) (fun a _ => by rw [F₁₃.2.2.1])
    have G₂ : Frame DrvR.drvBands c₃ c₄ k₄ := by
      have ml₄' : ∀ a, a < c₃.nreg ALLOC → c₄.nmem a = c₃.nmem a := fun a ha =>
        ml₄ a (by rwa [hA₃] at ha)
      refine ⟨fun r hr hra => ?_, fun r _ => by rw [rr₄], ml₄', fun a _ => by rw [rm₄], o₄,
        by rw [v99, hA₃]; omega, by rw [v99, hA₃]; omega⟩
      refine r₄ r ?_ ?_ hra
      · rintro rfl; exact hr (by rw [DrvT.mem_drvBands]; unfold bandOf; omega)
      · rintro rfl; exact hr (by rw [DrvT.mem_drvBands]; unfold bandOf; omega)
    exact G₁.trans G₂ |>.mono (by simp) (by omega)
  · rw [r₄ r (by omega) (by omega) (by unfold ALLOC; omega), gin r h1 h2]
  · rw [r₄ r (by omega) (by omega) h5, F₁₃.1 r (ball_false h2 h3 h4 (by omega))]
  · rwa [r₄ _ (by norm_num) (by norm_num) (by decide)]
  · rwa [r₄ _ (by norm_num) (by norm_num) (by decide)]
  · rw [ml₄ a ha, F₁₃.2.2.1]
  · rw [d1, gin _ (by norm_num) (by norm_num), hHB]
  · rw [d2, gin _ (by norm_num) (by norm_num), hs, hCs]
  · rw [d3, gin _ (by norm_num) (by norm_num), hm, hCm]
  · rw [d4, g₃ _ (by norm_num) (by norm_num), hT]
  · rwa [d5]

end exec

end

end DrvP

end Chazelle.Core
