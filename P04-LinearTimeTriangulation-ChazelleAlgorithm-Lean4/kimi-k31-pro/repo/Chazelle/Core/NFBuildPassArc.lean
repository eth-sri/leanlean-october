module

public import Chazelle.Core.NFBuildPassRam
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-C (BuildNF), RAM part 10: executions of the pieces of the main pass (arc part)

`arcS_exec`: the arc record at `AT + 5 A` and its weight `wtF` at `WT + A`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK WalkKey NFLoc

@[expose] public section

/-- The registers `arcS` writes. -/
def Barc (r : ℕ) : Bool :=
  BpzR r || decide (43121 ≤ r ∧ r < 43128) || decide (r = 43150 ∨ r = 43151 ∨ r = 43102) ||
    decide (r = 41110 ∨ r = 41111)

theorem wr_arcS : wrM Barc arcS = true := by
  have h1 : wrM Barc pzR = true := wrM_of_wr (wr_mono (fun r hr => by
    simp [Barc, hr, Bool.true_or]) wr_pzR)
  have h2 : wrM Barc wtS = true := wrM_of_wr (wr_mono (fun r hr => by
    sio only [Barc, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢) wr_wtS)
  simp [arcS, wrM, block, h1, h2, Bool.and_true, Bool.true_and]
  decide

theorem Barc_false {r : ℕ} (h : r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40100 ≤ r ∧ r < 41110) ∨
    (41120 ≤ r ∧ r < 43102) ∨ (43102 < r ∧ r < 43121) ∨ (43128 ≤ r ∧ r < 43150) ∨ 43151 < r) :
    Barc r = false := by
  have : BpzR r = false := by
    cases hb : BpzR r
    · rfl
    · have := BpzR_true hb; omega
  simp [Barc, this, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

section exec

variable {P : Polygon} {W : ℕ}

/-- **The arc record and its weight.** -/
theorem arcS_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (d : Config)
    (hw : WordsBounded W d) {M : Model} {D H A AT WT : ℕ}
    (hD : d.nreg 40000 = D) (hwf : ModelDescWF P H d.nmem D) (hM : ModelDescAt d.nmem D (Qof P) M)
    (hHW : H ≤ W) (h23 : d.nreg 41023 = d.nmem D) (h19 : d.nreg 41019 = 1)
    (hA : d.nreg 43102 = A) (hAT : d.nreg 44002 = AT) (hWT : d.nreg 44007 = WT)
    (h1 : d.nreg 43011 = 1) (hlt : d.nreg 43120 ≤ 1)
    (he : d.nreg 42113 < M.W.n) (hh : d.nreg 42114 ≤ P.n)
    (hATH : H ≤ AT) (_hWTH : H ≤ WT) (hATW : AT + 5 * A + 4 ≤ W) (hWTW : WT + A + 1 ≤ W)
    (hcI : ∀ p, p < M.W.n → (M.counted p ↔ d.nreg 44020 ≤ p ∧ p < d.nreg 44020 + d.nreg 44021)) :
    ∃ d' k, Exec P W arcS d d' k ∧ k ≤ 6040 ∧ FrameM Barc d d' ∧ d'.nreg 43102 = A + 1 ∧
      ∃ pz, pz ≤ 1 ∧ (pz = 1 ↔ M.counted (d.nreg 42113) ∧
          M.param (Qof P) ⟨d.nreg 42113, d.nreg 42114⟩ ≠ 0) ∧
        d'.nmem = upd (wr5 d.nmem (AT + 5 * A) (d.nreg 43117) (d.nreg 42110) (d.nreg 42111)
          (d.nreg 42113) (d.nreg 42114)) (WT + A)
          (wtG (d.nreg 44020) (d.nreg 44021) (d.nreg 42110) (d.nreg 42113) pz (d.nreg 43120)) := by
  -- the record
  obtain ⟨d₁, k₁, x₁, hk₁, m₁, r₁, v110, v111⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ ∧ k₁ = 15 ∧
      d₁.nmem = wr5 d.nmem (AT + 5 * A) (d.nreg 43117) (d.nreg 42110) (d.nreg 42111)
          (d.nreg 42113) (d.nreg 42114) ∧
      FrameM (fun r => decide (r = 43150 ∨ r = 41110 ∨ r = 41111)) d d₁ ∧
      d₁.nreg 41110 = d.nreg 42113 ∧ d₁.nreg 41111 = d.nreg 42114 := by
    have hfr : ∀ {d₁ k₁}, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ →
        FrameM (fun r => decide (r = 43150 ∨ r = 41110 ∨ r = 41111)) d d₁ :=
      fun x => exec_frameM x (by decide)
    suffices H : ∃ d₁ k₁, Exec P W
      (block [.addN 43150 43102 43102, .addN 43150 43150 43150, .addN 43150 43150 43102,
        .addN 43150 43150 44002,
        .storeN 43150 43117, .addN 43150 43150 43011, .storeN 43150 42110,
        .addN 43150 43150 43011, .storeN 43150 42111, .addN 43150 43150 43011,
        .storeN 43150 42113, .addN 43150 43150 43011, .storeN 43150 42114,
        .copyN 41110 42113, .copyN 41111 42114]) d d₁ k₁ ∧ k₁ = 15 ∧
      d₁.nmem = wr5 d.nmem (AT + 5 * A) (d.nreg 43117) (d.nreg 42110) (d.nreg 42111)
          (d.nreg 42113) (d.nreg 42114) ∧
      d₁.nreg 41110 = d.nreg 42113 ∧ d₁.nreg 41111 = d.nreg 42114 by
      obtain ⟨d₁, k₁, x, hk, hm, h10, h11⟩ := H
      exact ⟨d₁, k₁, x, hk, hm, hfr x, h10, h11⟩
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hA, hAT, h1]; omega)
      | skip
    refine ⟨rfl, ?_, by config_simp, by config_simp⟩
    config_simp
    funext a
    simp [hA, hAT, h1, upd_apply, wr5]
    by_cases e0 : a = AT + 5 * A
    · subst e0; ifs_omega
    by_cases e1 : a = AT + 5 * A + 1
    · subst e1; ifs_omega
    by_cases e2 : a = AT + 5 * A + 2
    · subst e2; ifs_omega
    by_cases e3 : a = AT + 5 * A + 3
    · subst e3; ifs_omega
    by_cases e4 : a = AT + 5 * A + 4
    · subst e4; ifs_omega
    ifs_omega
  have w₁ := x₁.wb_right
  have g₁ : ∀ r, r ≠ 43150 → r ≠ 41110 → r ≠ 41111 → d₁.nreg r = d.nreg r := fun r a1 a2 a3 =>
    r₁.1 r (by sio only [decide_eq_false_iff_not])
  have mH₁ : ∀ a, a < H → d₁.nmem a = d.nmem a := fun a ha => by
    rw [m₁]; unfold wr5; ifs_omega
  obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM mH₁
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf₁ hHW hWn
  have hD6 := hwf.1
  have hW' : P.n + 3 ≤ W := by ufo hostWords at hWn
  -- the parameter test
  obtain ⟨d₂, k₂, x₂, hk₂, f₂, pz1, pziff⟩ := pzR_exec (P := P) (M := M) hG hW' d₁ w₁
    (D := D) (e := d.nreg 42113) (h := d.nreg 42114)
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num), hD]) hM₁
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num), h23, mH₁ D (by omega)])
    (by rw [g₁ _ (by norm_num) (by norm_num) (by norm_num), h19]) v110 v111 he hh hDW hCW
  have w₂ := x₂.wb_right
  have g₂  := f₂.1
  have bz : ∀ r, (r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40100 ≤ r ∧ r < 41110) ∨
      41120 ≤ r) → BpzR r = false := fun r hr => by
    cases hb : BpzR r
    · rfl
    · have := BpzR_true hb; omega
  -- the weight
  have e₁₁ : d₂.nreg 43011 = 1 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num), h1]
  have e₁₂₀ : d₂.nreg 43120 = d.nreg 43120 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num)]
  have e₁₁₃ : d₂.nreg 42113 = d.nreg 42113 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num)]
  have e₁₁₀ : d₂.nreg 42110 = d.nreg 42110 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num)]
  have e₂₀ : d₂.nreg 44020 = d.nreg 44020 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num)]
  have e₂₁ : d₂.nreg 44021 = d.nreg 44021 := by
    rw [g₂ _ (bz _ (by omega)), g₁ _ (by norm_num) (by norm_num) (by norm_num)]
  have hbound : d.nreg 42113 - d.nreg 44020 + d₂.nreg 41112 ≤ W := by
    by_cases hp : d₂.nreg 41112 = 1
    · have := ((hcI _ he).1 (pziff.1 hp).1)
      have := hw.1 44021
      omega
    · have := hw.1 42113
      omega
  obtain ⟨d₃, k₃, x₃, hk₃, v₃, f₃⟩ := wtS_exec (P := P) d₂ w₂ e₁₁ (by rwx [e₁₂₀])
    (by rwx [e₁₁₃, e₂₀])
  have w₃ := x₃.wb_right
  have g₃ : ∀ r, (r < 43121 ∨ 43128 ≤ r) → d₃.nreg r = d₂.nreg r := fun r hr =>
    f₃.1 r (by sio only [decide_eq_false_iff_not])
  have g₃₁ : ∀ r, (r < 10000 ∨ (10503 ≤ r ∧ r ≤ 40000) ∨ (40100 ≤ r ∧ r < 41110) ∨
      (41120 ≤ r ∧ r < 43121) ∨ 43128 ≤ r) → r ≠ 43150 → d₃.nreg r = d.nreg r := fun r hr hr' => by
    rw [g₃ r (by omega), g₂ _ (bz _ (by omega)), g₁ _ hr' (by omega) (by omega)]
  -- the weight into its table
  obtain ⟨d₄, k₄, x₄, hk₄, v₄, m₄, a₄⟩ : ∃ d₄ k₄, Exec P W
      (block [.addN 43151 44007 43102, .storeN 43151 43121, .addN 43102 43102 43011]) d₃ d₄ k₄ ∧
      k₄ = 3 ∧ d₄.nreg 43102 = A + 1 ∧ d₄.nmem = upd d₃.nmem (WT + A) (d₃.nreg 43121) ∧
      (∀ r, r ≠ 43151 → r ≠ 43102 → d₄.nreg r = d₃.nreg r) := by
    have r1 := g₃₁ 44007 (by omega) (by norm_num)
    have r2 := g₃₁ 43102 (by omega) (by norm_num)
    have r3 := g₃₁ 43011 (by omega) (by norm_num)
    exec_block
    · rwo [r1, r2, hWT, hA]
    · config_simp; rwo [r2, r3, hA, h1]
    · refine ⟨rfl, ?_, ?_, fun r a1 a2 => ?_⟩ <;> config_simp
      · rw [r2, r3, hA, h1]
      · rw [r1, r2, hWT, hA]
      · simp (disch := omega) only [upd_other]
  have X : Exec P W arcS d d₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq x₁ (.seq x₂ (.seq x₃ x₄))
  refine ⟨d₄, _, X, by omega, exec_frameM X wr_arcS, v₄, d₂.nreg 41112, pz1, pziff, ?_⟩
  rw [m₄, f₃.2.2.1, f₂.2.2.1, m₁, v₃, e₁₁₀, e₁₁₃, e₂₀, e₂₁, e₁₂₀]

end exec

end

end BuildRam

end Chazelle.Core
