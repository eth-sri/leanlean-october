module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleCuR2

/-!
# WP-M (E7-B, RAM part 17): copying the translated pieces of a slot

`cpLoop`: with a slot's list address `L` (`170230`), number of pieces `q` (`170231`) and stretch
starts `g₀`, `u₀` (`170232`, `170233`), copies its `q` piece records from `L + 1` (`170234`) to the
output pointer `170222`, translating the two edge words of each record (`trI`: `trE n u₀ g₀`),
counting the pieces in `170223`.

* `whileLtN_pot2`: the loop rule with a potential and a measure growing at most by the steps;
* `cpLoop_exec`: the records written are those of `trPcR n u₀ g₀ (rdPc m L j)`, `j < q`; the
  memory below the output pointer is unchanged; the output pointer grows by `7 q` within the steps.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-! ## A loop rule with a lower bound -/

/-- **Loop rule with a potential**, also bounding the growth of a measure `ψ` by the steps. -/
theorem whileLtN_pot2 {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ, hψ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hψ'⟩ := ih (Φ c₁) (⋄) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', ⋄, ⋄⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, ⋄, ⋄⟩

/-! ## The programs -/

/-- The translation of the word in `170236` into `170237`. -/
def trI : Stmt :=
  .seq (block [.subN 170237 170236 170232, .addN 170237 170233 170237])
    (.ifLtN 170237 170010 .skip (block [.subN 170237 170237 170010]))

/-- Copy one word. -/
def mvW : Stmt :=
  block [.loadN 170236 170234, .storeN 170222 170236, .addN 170234 170234 170011,
    .addN 170222 170222 170011]

/-- Copy one translated word. -/
def mvT : Stmt :=
  .seq (block [.loadN 170236 170234]) (.seq trI
    (block [.storeN 170222 170237, .addN 170234 170234 170011, .addN 170222 170222 170011]))

/-- Copy one piece record. -/
def cpBody : Stmt :=
  .seq mvT (.seq mvW (.seq mvT (.seq mvW (.seq mvW (.seq mvW (.seq mvW
    (block [.addN 170235 170235 170011, .addN 170223 170223 170011])))))))

/-- **Copy the pieces of a slot.** -/
def cpLoop : Stmt := .whileLtN 170235 170231 cpBody

/-- The registers the copy writes. -/
def Bcp (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170223 ∨ (170234 ≤ r ∧ r < 170238))

/-- The registers one word copy writes. -/
def Bmv (r : ℕ) : Bool := decide (r = 170222 ∨ r = 170234 ∨ r = 170236 ∨ r = 170237)

theorem wrM_mvW : BuildRam.wrM Bmv mvW = true := ⌖

theorem frameM_mono {B B' : ℕ → Bool} {c c' : Config} (h : BuildRam.FrameM B c c')
    (hB : ∀ r, B r = true → B' r = true) : BuildRam.FrameM B' c c' := by
  refine ⟨fun r hr => h.1 r ?_, fun r hr => h.2.1 r ?_, h.2.2.1, h.2.2.2⟩
  · cases hb : B r
    · rfl
    · Ξ' hB r hb at hr; exact absurd hr (✓)
  · cases hb : B r
    · rfl
    · Ξ' hB r hb at hr; exact absurd hr (✓)

theorem bmv_bcp (r : ℕ) (h : Bmv r = true) : Bcp r = true := by
  ϴ' Bmv, Bcp, decide_eq_true_eq at h ⊢; omega

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

theorem trI_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ w : ℕ}
    (h10 : c.nreg 170010 = n) (h32 : c.nreg 170232 = g₀) (h33 : c.nreg 170233 = u₀)
    (h36 : c.nreg 170236 = w) (hW : u₀ + (w - g₀) ≤ W) :
    ∃ c' k, Exec P W trI c c' k ∧ 3 ≤ k ∧ k ≤ 5 ∧ c'.nreg 170237 = trE n u₀ g₀ w ∧
      c'.nmem = c.nmem ∧ BuildRam.FrameM (fun r => decide (r = 170237)) c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a37, a10, am⟩ : ∃ c₁ k₁, Exec P W
      (block [.subN 170237 170236 170232, .addN 170237 170233 170237]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 170237 = u₀ + (w - g₀) ∧ c₁.nreg 170010 = n ∧ c₁.nmem = c.nmem := by
    exec_block
    · config_simp; rw [h33, h36, h32]; omega
    refine ⟨rfl, ?_, ?_, rfl⟩ <;> config_simp <;> simp only [h33, h36, h32, h10]
  have w₁ := e₁.wb_right
  have F₁ := BuildRam.exec_frameM e₁ (by decide : BuildRam.wrM (fun r => decide (r = 170237))
    (block [.subN 170237 170236 170232, .addN 170237 170233 170237]) = true)
  by_cases hlt : c₁.nreg 170237 < c₁.nreg 170010
  · have ex : Exec P W trI c c₁ (k₁ + (0 + 1)) := .seq e₁ (.ifLtN_true hlt (.skip w₁))
    refine ⟨c₁, _, ex, ⋄, by omega, ?_, am, F₁⟩
    rw [a37]; unfold trE; rw [ite_eq_left (by rw [← a37, ← a10]; exact hlt)]
  · obtain ⟨c₂, k₂, e₂, hk₂, b37, bm⟩ : ∃ c₂ k₂, Exec P W (block [.subN 170237 170237 170010])
        c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg 170237 = c₁.nreg 170237 - c₁.nreg 170010 ∧
        c₂.nmem = c₁.nmem := by
      exec_block
      exact ⟨rfl, by config_simp, rfl⟩
    have F₂ := BuildRam.exec_frameM e₂ (by decide : BuildRam.wrM (fun r => decide (r = 170237))
      (block [.subN 170237 170237 170010]) = true)
    have ex : Exec P W trI c c₂ (k₁ + (k₂ + 2)) := .seq e₁ (.ifLtN_false hlt e₂)
    refine ⟨c₂, _, ex, ⋄, by omega, ?_, by rw [bm, am], F₁.trans F₂⟩
    rw [b37, a37, a10]; unfold trE; rw [ite_eq_right (by rw [← a37, ← a10]; exact hlt)]

theorem mvW_exec (c : Config) (hw : WordsBounded W c) {src dst : ℕ}
    (h11 : c.nreg 170011 = 1) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hs : src + 1 ≤ W) (hd : dst + 1 ≤ W) :
    ∃ c' k, Exec P W mvW c c' k ∧ k = 4 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst (c.nmem src) ∧
      BuildRam.FrameM Bmv c c' := by
  suffices h : ∃ c' k, Exec P W mvW c c' k ∧ k = 4 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst (c.nmem src) by
    obtain ⟨c', k, e, h1, h2, h3, h4⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, BuildRam.exec_frameM e wrM_mvW⟩
  unfold mvW
  exec_block
  · config_simp; rw [h34, h11]; omega
  · config_simp; rw [h22, h11]; omega
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp <;> ϴ h34, h22, h11

theorem mvT_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ src dst : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h32 : c.nreg 170232 = g₀)
    (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hs : src + 1 ≤ W) (hd : dst + 1 ≤ W) (ht : u₀ + (c.nmem src - g₀) ≤ W) :
    ∃ c' k, Exec P W mvT c c' k ∧ 7 ≤ k ∧ k ≤ 9 ∧ c'.nreg 170234 = src + 1 ∧
      c'.nreg 170222 = dst + 1 ∧ c'.nmem = upd c.nmem dst (trE n u₀ g₀ (c.nmem src)) ∧
      BuildRam.FrameM Bmv c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, a36, ar, am⟩ : ∃ c₁ k₁, Exec P W (block [.loadN 170236 170234]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170236 = c.nmem src ∧ (∀ r, r ≠ 170236 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, ?_, fun r hr => ?_, rfl⟩
    · config_simp; rw [h34]
    · config_simp; simp [upd, hr]
  have F₁ := BuildRam.exec_frameM e₁ (by decide : BuildRam.wrM Bmv
    (block [.loadN 170236 170234]) = true)
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', b37, bm, F₂⟩ := trI_exec (P := P) c₁ e₁.wb_right
    ((ar _ (⌖)).trans h10) ((ar _ (by decide)).trans h32)
    ((ar _ (⌖)).trans h33) a36 ht
  have f₂ : ∀ r, r ≠ 170237 → c₂.nreg r = c₁.nreg r := fun r hr => F₂.1 r (⊚ hr)
  have w₂ := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, d34, d22, dm⟩ : ∃ c₃ k₃, Exec P W
      (block [.storeN 170222 170237, .addN 170234 170234 170011, .addN 170222 170222 170011])
      c₂ c₃ k₃ ∧ k₃ = 3 ∧ c₃.nreg 170234 = src + 1 ∧ c₃.nreg 170222 = dst + 1 ∧
      c₃.nmem = upd c₂.nmem dst (trE n u₀ g₀ (c.nmem src)) := by
    have g34 : c₂.nreg 170234 = src := (f₂ _ (⌖)).trans ((ar _ (by decide)).trans h34)
    have g22 : c₂.nreg 170222 = dst := (f₂ _ (⌖)).trans ((ar _ (by decide)).trans h22)
    have g11 : c₂.nreg 170011 = 1 := (f₂ _ (⌖)).trans ((ar _ (by decide)).trans h11)
    exec_block
    · config_simp; rw [g34, g11]; omega
    · config_simp; rw [g22, g11]; omega
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp <;> simp only [g34, g22, g11, b37]
  have F₃ := BuildRam.exec_frameM e₃ (by decide : BuildRam.wrM Bmv
    (block [.storeN 170222 170237, .addN 170234 170234 170011,
      .addN 170222 170222 170011]) = true)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), ⋄, by omega, d34, d22, by rw [dm, bm, am],
    (F₁.trans (frameM_mono F₂ (fun r hr => by simp at hr; simp [Bmv, hr]))).trans F₃⟩

/-- Seven consecutive updates, away from them. -/
theorem upd7_lo {m : ℕ → ℕ} {d a v0 v1 v2 v3 v4 v5 v6 : ℕ} (h : a < d) :
    upd (upd (upd (upd (upd (upd (upd m d v0) (d + 1) v1) (d + 2) v2) (d + 3) v3) (d + 4) v4)
      (d + 5) v5) (d + 6) v6 a = m a := by
  rw [upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
    upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
    upd_other _ _ _ (⋄)]

/-- Seven consecutive updates, at them. -/
theorem upd7_at {m : ℕ → ℕ} {d v0 v1 v2 v3 v4 v5 v6 : ℕ} :
    let M := upd (upd (upd (upd (upd (upd (upd m d v0) (d + 1) v1) (d + 2) v2) (d + 3) v3)
      (d + 4) v4) (d + 5) v5) (d + 6) v6
    M d = v0 ∧ M (d + 1) = v1 ∧ M (d + 2) = v2 ∧ M (d + 3) = v3 ∧ M (d + 4) = v4 ∧
      M (d + 5) = v5 ∧ M (d + 6) = v6 := by
  intro M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ϴ M
    rw [upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
      upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_same]
  · ϴ M
    rw [upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
      upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_same]
  · ϴ M
    rw [upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
      upd_other _ _ _ (⋄), upd_same]
  · ϴ M
    rw [upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_other _ _ _ (⋄),
      upd_same]
  · ϴ M
    Ξ upd_other _ _ _ (⋄), upd_other _ _ _ (⋄), upd_same
  · ϴ M
    Ξ upd_other _ _ _ (⋄), upd_same
  · ϴ M
    Ξ upd_same

/-- **One piece record copied.** -/
theorem cpBody_exec (c : Config) (hw : WordsBounded W c) {n u₀ g₀ src dst : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h32 : c.nreg 170232 = g₀)
    (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = src) (h22 : c.nreg 170222 = dst)
    (hsd : src + 7 ≤ dst) (hdW : dst + 7 ≤ W)
    (ht0 : u₀ + (c.nmem src - g₀) ≤ W) (ht2 : u₀ + (c.nmem (src + 2) - g₀) ≤ W)
    (h35 : c.nreg 170235 + 1 ≤ W) (h23 : c.nreg 170223 + 1 ≤ W) :
    ∃ c' k, Exec P W cpBody c c' k ∧ 36 ≤ k ∧ k ≤ 40 ∧
      c'.nreg 170234 = src + 7 ∧ c'.nreg 170222 = dst + 7 ∧
      c'.nreg 170235 = c.nreg 170235 + 1 ∧ c'.nreg 170223 = c.nreg 170223 + 1 ∧
      (∀ a, a < dst → c'.nmem a = c.nmem a) ∧
      c'.nmem dst = trE n u₀ g₀ (c.nmem src) ∧ c'.nmem (dst + 1) = c.nmem (src + 1) ∧
      c'.nmem (dst + 2) = trE n u₀ g₀ (c.nmem (src + 2)) ∧
      c'.nmem (dst + 3) = c.nmem (src + 3) ∧ c'.nmem (dst + 4) = c.nmem (src + 4) ∧
      c'.nmem (dst + 5) = c.nmem (src + 5) ∧ c'.nmem (dst + 6) = c.nmem (src + 6) ∧
      BuildRam.FrameM Bcp c c' := by
  -- the registers the steps keep
  have keep : ∀ {d d' : Config}, BuildRam.FrameM Bmv d d' →
      d'.nreg 170010 = d.nreg 170010 ∧ d'.nreg 170011 = d.nreg 170011 ∧
      d'.nreg 170232 = d.nreg 170232 ∧ d'.nreg 170233 = d.nreg 170233 ∧
      d'.nreg 170235 = d.nreg 170235 ∧ d'.nreg 170223 = d.nreg 170223 := fun F =>
    ⟨F.1 _ (⌖), F.1 _ (⌖), F.1 _ (⌖), F.1 _ (⌖),
      F.1 _ (⌖), F.1 _ (⌖)⟩
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', a34, a22, am, F₁⟩ := mvT_exec (P := P) c hw h10 h11 h32 h33 h34 h22
    (⋄) (⋄) ht0
  obtain ⟨q10, q11, q32, q33, q35, q23⟩ := keep F₁
  have m1 : c₁.nmem (src + 1) = c.nmem (src + 1) := Ρ am, upd_other _ _ _ (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, b34, b22, bm, F₂⟩ := mvW_exec (P := P) c₁ e₁.wb_right
    (Ρ q11, h11) a34 a22 (⋄) (⋄)
  obtain ⟨p10, p11, p32, p33, p35, p23⟩ := keep F₂
  have m2 : c₂.nmem (src + 2) = c.nmem (src + 2) := by
    Ξ bm, upd_other _ _ _ (⋄), am, upd_other _ _ _ (⋄)
  obtain ⟨c₃, k₃, e₃, hk₃, hk₃', d34, d22, dm, F₃⟩ := mvT_exec (P := P) c₂ e₂.wb_right
    (Ρ p10, q10, h10) (Ρ p11, q11, h11) (Ρ p32, q32, h32) (Ρ p33, q33, h33)
    b34 b22 (⋄) (⋄) (by rw [m2]; exact ht2)
  obtain ⟨s10, s11, s32, s33, s35, s23⟩ := keep F₃
  have m3 : c₃.nmem (src + 3) = c.nmem (src + 3) := by
    rw [dm, upd_other _ _ _ (⋄), bm, upd_other _ _ _ (⋄), am,
      upd_other _ _ _ (⋄)]
  obtain ⟨c₄, k₄, e₄, hk₄, f34, f22, fm, F₄⟩ := mvW_exec (P := P) c₃ e₃.wb_right
    (Ρ s11, p11, q11, h11) d34 d22 (⋄) (⋄)
  obtain ⟨t10, t11, t32, t33, t35, t23⟩ := keep F₄
  have m4 : c₄.nmem (src + 4) = c.nmem (src + 4) := by
    rw [fm, upd_other _ _ _ (⋄), dm, upd_other _ _ _ (⋄), bm,
      upd_other _ _ _ (⋄), am, upd_other _ _ _ (⋄)]
  obtain ⟨c₅, k₅, e₅, hk₅, g34, g22, gm, F₅⟩ := mvW_exec (P := P) c₄ e₄.wb_right
    (Ρ t11, s11, p11, q11, h11) f34 f22 (⋄) (⋄)
  obtain ⟨u10, u11, u32, u33, u35, u23⟩ := keep F₅
  have m5 : c₅.nmem (src + 5) = c.nmem (src + 5) := by
    rw [gm, upd_other _ _ _ (⋄), fm, upd_other _ _ _ (⋄), dm,
      upd_other _ _ _ (⋄), bm, upd_other _ _ _ (⋄), am, upd_other _ _ _ (⋄)]
  obtain ⟨c₆, k₆, e₆, hk₆, i34, i22, im, F₆⟩ := mvW_exec (P := P) c₅ e₅.wb_right
    (Ρ u11, t11, s11, p11, q11, h11) g34 g22 (⋄) (⋄)
  obtain ⟨v10, v11, v32, v33, v35, v23⟩ := keep F₆
  have m6 : c₆.nmem (src + 6) = c.nmem (src + 6) := by
    rw [im, upd_other _ _ _ (⋄), gm, upd_other _ _ _ (⋄), fm,
      upd_other _ _ _ (⋄), dm, upd_other _ _ _ (⋄), bm, upd_other _ _ _ (⋄),
      am, upd_other _ _ _ (⋄)]
  obtain ⟨c₇, k₇, e₇, hk₇, j34, j22, jm, F₇⟩ := mvW_exec (P := P) c₆ e₆.wb_right
    (Ρ v11, u11, t11, s11, p11, q11, h11) i34 i22 (⋄) (⋄)
  obtain ⟨w10, w11, w32, w33, w35, w23⟩ := keep F₇
  have r35 : c₇.nreg 170235 = c.nreg 170235 := Ρ w35, v35, u35, t35, s35, p35, q35
  have r23 : c₇.nreg 170223 = c.nreg 170223 := Ρ w23, v23, u23, t23, s23, p23, q23
  have r11 : c₇.nreg 170011 = 1 := Ρ w11, v11, u11, t11, s11, p11, q11, h11
  have w₇ := e₇.wb_right
  obtain ⟨c₈, k₈, e₈, hk₈, l35, l23, lr, lm⟩ : ∃ c₈ k₈, Exec P W
      (block [.addN 170235 170235 170011, .addN 170223 170223 170011]) c₇ c₈ k₈ ∧ k₈ = 2 ∧
      c₈.nreg 170235 = c.nreg 170235 + 1 ∧ c₈.nreg 170223 = c.nreg 170223 + 1 ∧
      (∀ r, r ≠ 170235 → r ≠ 170223 → c₈.nreg r = c₇.nreg r) ∧ c₈.nmem = c₇.nmem := by
    exec_block
    · config_simp; rw [r35, r11]; omega
    · config_simp; rw [r23, r11]; omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; Ξ r35, r11
    · config_simp; Ξ r23, r11
    · config_simp; Θ upd, h1, h2
  have F₈ := BuildRam.exec_frameM e₈ (by decide : BuildRam.wrM Bcp
    (block [.addN 170235 170235 170011, .addN 170223 170223 170011]) = true)
  have ex : Exec P W cpBody c c₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  -- the memory
  have mem : ∀ a, c₈.nmem a = upd (upd (upd (upd (upd (upd (upd c.nmem dst
      (trE n u₀ g₀ (c.nmem src))) (dst + 1) (c.nmem (src + 1)))
      (dst + 2) (trE n u₀ g₀ (c.nmem (src + 2)))) (dst + 3) (c.nmem (src + 3)))
      (dst + 4) (c.nmem (src + 4))) (dst + 5) (c.nmem (src + 5))) (dst + 6) (c.nmem (src + 6)) a := by
    intro a
    Ξ lm, jm, ← m6, im, ← m5, gm, ← m4, fm, ← m3, dm, ← m2, bm, ← m1, am
  refine ⟨c₈, _, ex, ⋄, ⋄, by rw [lr _ (⌖) (⌖)]; exact j34,
    by rw [lr _ (⌖) (⌖)]; exact j22, l35, l23, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, (frameM_mono (F₁.trans (F₂.trans (F₃.trans (F₄.trans (F₅.trans (F₆.trans F₇))))))
      bmv_bcp).trans F₈⟩
  · rw [mem]; exact upd7_lo ha
  all_goals (rw [mem])
  all_goals first
    | exact upd7_at.1 | exact upd7_at.2.1 | exact upd7_at.2.2.1 | exact upd7_at.2.2.2.1
    | exact upd7_at.2.2.2.2.1 | exact upd7_at.2.2.2.2.2.1 | exact upd7_at.2.2.2.2.2.2

/-- **The pieces of a slot copied**, translated. -/
theorem cpLoop_exec (c : Config) (hw : WordsBounded W c) {n L q g₀ u₀ O : ℕ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (h31 : c.nreg 170231 = q)
    (h32 : c.nreg 170232 = g₀) (h33 : c.nreg 170233 = u₀) (h34 : c.nreg 170234 = L + 1)
    (h35 : c.nreg 170235 = 0)
    (hLO : L + 1 + 7 * q ≤ O) (hOd : O < c.nreg 170222) (hdW : c.nreg 170222 + 7 * q ≤ W)
    (hcnt : c.nreg 170223 + q ≤ W) (hu : u₀ < n) (hnW : 2 * n ≤ W)
    (hed : ∀ i, i < q → c.nmem (L + 1 + 7 * i) - g₀ < n ∧ c.nmem (L + 1 + 7 * i + 2) - g₀ < n) :
    ∃ c' k, Exec P W cpLoop c c' k ∧ k ≤ 42 * q + 2 ∧ 7 * q ≤ k ∧
      c'.nreg 170222 = c.nreg 170222 + 7 * q ∧ c'.nreg 170223 = c.nreg 170223 + q ∧
      (∀ a, a < c.nreg 170222 → c'.nmem a = c.nmem a) ∧
      (∀ j, j < q → ∀ f, f < 7 →
        c'.nmem (c.nreg 170222 + 7 * j + f) = pcW (trPcR n u₀ g₀ (rdPc c.nmem L j)) f) ∧
      BuildRam.FrameM Bcp c c' := by
  set d₀ := c.nreg 170222 with hd₀
  set n₀ := c.nreg 170223 with hn₀
  set m₀ := c.nmem with hm₀
  let I : Config → Prop := fun d => WordsBounded W d ∧ ∃ i, i ≤ q ∧ d.nreg 170235 = i ∧
    d.nreg 170234 = L + 1 + 7 * i ∧ d.nreg 170222 = d₀ + 7 * i ∧ d.nreg 170223 = n₀ + i ∧
    (∀ a, a < d₀ → d.nmem a = m₀ a) ∧
    (∀ j, j < i → ∀ f, f < 7 → d.nmem (d₀ + 7 * j + f) = pcW (trPcR n u₀ g₀ (rdPc m₀ L j)) f) ∧
    BuildRam.FrameM Bcp c d
  obtain ⟨c', k, e, ⟨w', i, hiq, r35, r34, r22, r23, hlo, hout, F⟩, hex, hk, hψ⟩ :=
    whileLtN_pot2 (P := P) (a := 170235) (b := 170231) (body := cpBody) I
      (fun d => 42 * (q - d.nreg 170235)) (fun d => d.nreg 170222) (fun _ h => h.1)
      (fun d ⟨wd, i, hiq, d35, d34, d22, d23, dlo, dout, dF⟩ hlt => by
        have d31 : d.nreg 170231 = q := by rw [dF.1 _ (by decide)]; exact h31
        rw [d35, d31] at hlt
        have dsrc : ∀ f, f < 7 → d.nmem (L + 1 + 7 * i + f) = m₀ (L + 1 + 7 * i + f) :=
          fun f hf => dlo _ (by omega)
        obtain ⟨he0, he2⟩ := hed i hlt
        obtain ⟨d', k', e', hk', hk'', a34, a22, a35, a23, alo, a0, a1, a2, a3, a4, a5, a6, aF⟩ :=
          cpBody_exec (P := P) d wd ((dF.1 _ (by decide)).trans h10)
            ((dF.1 _ (by decide)).trans h11) ((dF.1 _ (by decide)).trans h32)
            ((dF.1 _ (by decide)).trans h33) d34 d22 (by omega) (by omega)
            (by have := dsrc 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; omega)
            (by rw [dsrc 2 (by omega)]; omega)
            (by rw [d35]; have := hw.1 170231; omega) (by rw [d23]; omega)
        refine ⟨d', k', e', ⟨e'.wb_right, i + 1, by omega, by rw [a35, d35],
          by rw [a34]; ring, by rw [a22]; ring, by rw [a23, d23]; ring,
          fun a ha => by rw [alo a (by omega)]; exact dlo a ha, fun j hj f hf => ?_, dF.trans aF⟩,
          by rw [a35, d35]; omega, by rw [a22, d22]; omega⟩
        rcases (show j < i ∨ j = i by omega) with hj' | rfl
        · rw [alo _ (by omega)]; exact dout j hj' f hf
        · interval_cases f
          · simp only [Nat.add_zero]; rw [a0]
            have := dsrc 0 (by omega); simp only [Nat.add_zero] at this; rw [this]; rfl
          · rw [a1, dsrc 1 (by omega)]; rfl
          · rw [a2, dsrc 2 (by omega)]; rfl
          · rw [a3, dsrc 3 (by omega)]; rfl
          · rw [a4, dsrc 4 (by omega)]; rfl
          · rw [a5, dsrc 5 (by omega)]; rfl
          · rw [a6, dsrc 6 (by omega)]; rfl)
      (c := c) ⟨hw, 0, by omega, h35, by omega, by omega, by omega, fun a _ => rfl,
        fun j hj => absurd hj (by omega), BuildRam.FrameM.refl _ _⟩
  have r31 : c'.nreg 170231 = q := by rw [F.1 _ (by decide)]; exact h31
  rw [r35, r31] at hex
  have hi : i = q := by omega
  subst hi
  refine ⟨c', k, e, by rw [h35] at hk; simpa using hk, by rw [r22] at hψ; omega, r22, r23, hlo,
    hout, F⟩

end exec

end

end IOrc

end Chazelle.Core
