module

public import Chazelle.Core.DownPhaseDrvLTLoop

/-!
# Down-phase level tail (D12), part 5: the gather

**`gather_exec`**: `gatherS` writes the gathered list `L₂ = Lx 0 ++ … ++ Lx (R-1)` at the entry
allocator `A₀` and its buckets at `A₀ + 3 K₂`, reserves `5 K₂` words, and sets the arguments of
the splice (`210020 … 210024`).
-/

namespace Chazelle.Core

namespace DrvLT

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

theorem nRegions_build (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) :
    (BuildNF.buildNF M Q L E).nRegions = L.length + 1 := by
  simp [NF.nRegions, BuildNF.buildNF]

set_option maxHeartbeats 4000000 in
/-- **The gather.** -/
theorem gather_exec {G : GEnv} (hG : GGood G) {c : Config} (hw : WordsBounded G.W c)
    (hA : c.nreg ALLOC = G.A₀) (hm : c.nmem = G.m₀) (hr : c.nreg = G.r₀)
    (h12 : c.nreg 211012 = G.K₂) (h11 : c.nreg 211011 = G.R) (h09 : c.nreg 211009 = G.T)
    (h13 : c.nreg 211013 = G.Mx) {K : ℕ} (h03 : c.nreg 210003 = K) (hWK : 4 * K + 3 ≤ G.W)
    (hWM : 4 * G.Mx ≤ G.W) :
    ∃ e k, Exec G.P G.W gatherS c e k ∧ k ≤ 8 * G.K₂ + (35 * G.Mx + 32) * G.R + 26 ∧
      WordsBounded G.W e ∧
      e.nreg 210020 = G.A₀ ∧ e.nreg 210021 = G.K₂ ∧ e.nreg 210022 = G.A₀ + 3 * G.K₂ ∧
      e.nreg 210023 = 4 * K + 3 ∧ e.nreg 210024 = 4 * G.Mx ∧
      e.nreg ALLOC = G.A₀ + 5 * G.K₂ ∧
      (∀ r, BL r = false → r ≠ ALLOC → e.nreg r = c.nreg r) ∧
      (∀ a, a < G.A₀ → e.nmem a = G.m₀ a) ∧
      ChordListAt e.nmem G.A₀ (G.flat G.R) ∧
      (∀ q, q < 2 * G.K₂ →
        e.nmem (G.A₀ + 3 * G.K₂ + q) = DrvR.keyBkt G.Q G.N (DrvR.endPos (G.flat G.R) q)) ∧
      Restore.RF DrvR.drvBands G.A₀ c e k := by
  have hroom := hG.room
  -- 1. constants
  obtain ⟨c₁, k₁, x₁, hk₁, i00, i01, i34, i10, i11, f₁⟩ :=
    ltInit_exec (P := G.P) c hw (by omega)
  have g₁ : ∀ r, ¬ (r = 211100 ∨ r = 211101 ∨ r = 210034 ∨ r = 211110 ∨ r = 211111) →
      c₁.nreg r = c.nreg r := fun r h => f₁.1 r (by simpa using h)
  have w₁ := x₁.wb_right
  have A₁ : c₁.nreg ALLOC = G.A₀ := by rw [g₁ _ (by unfold ALLOC; omega), hA]
  -- 2. the reservation
  obtain ⟨c₂, k₂, x₂, hk₂, A₂, j11, f₂, RF₂⟩ := ltRes_exec (P := G.P) w₁ (K₂ := G.K₂)
    (by rw [g₁ _ (by omega), h12]) i11 i00 (by rw [A₁]; omega) G.A₀
  rw [A₁] at A₂
  have g₂ : ∀ r, r ≠ 211111 → r ≠ 9999 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r (by simp [Bres, h1, h2])
  have w₂ := x₂.wb_right
  -- 3. the set-up
  obtain ⟨c₃, k₃, x₃, hk₃, s12, s13, s14, s30, s31, f₃⟩ := ltMid_exec (P := G.P) c₂ w₂
    (K₂ := G.K₂) (A := G.A₀) (T := G.T)
    (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by omega), h12])
    (by rw [g₂ _ (by norm_num) (by norm_num), i10, hA])
    (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by omega), h09]) (by omega)
  have g₃ : ∀ r, ¬ (r = 211147 ∨ (211112 ≤ r ∧ r ≤ 211114) ∨ r = 211130 ∨ r = 211131) →
      c₃.nreg r = c₂.nreg r := fun r h => f₃.1 r (by simpa using h)
  have w₃ := x₃.wb_right
  have back : ∀ r, BL r = false → r ≠ ALLOC → c₃.nreg r = c.nreg r := by
    intro r hr hra
    simp only [BL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    unfold ALLOC at hra
    rw [g₃ r (by omega), g₂ r (by omega) hra, g₁ r (by omega)]
  have I0 : LInv G 0 c₃ := by
    refine ⟨w₃, s30, ?_, by rw [s31]; omega, ?_, ?_, ?_, ?_, s12, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Nat.zero_le _⟩
    · rw [g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), g₁ _ (by omega), h11]
    · rw [g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), i00]
    · rw [g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), i01]
    · rw [g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), i34]
    · rw [g₃ _ (by omega), g₂ _ (by norm_num) (by norm_num), i10, hA]
    · rw [s13]; simp [GEnv.flat]
    · rw [s14]; simp [GEnv.flat]
    · rw [g₃ _ (by unfold ALLOC; omega), A₂]
    · intro r hb hra; rw [back r hb hra, hr]
    · intro a _
      rw [f₃.2.2.1, f₂.2.2.1, f₁.2.2.1, hm]
    · intro i hi; simp [GEnv.flat] at hi
    · intro q hq; simp [GEnv.flat] at hq
  -- 4. the loop
  obtain ⟨c₄, k₄, x₄, I₄, RF₄, hk₄⟩ := loop_exec hG I0
  -- 5. the arguments
  obtain ⟨c₅, k₅, x₅, hk₅, v20, v21, v22, v23, v24, m₅, f₅⟩ := ltArgs_exec (P := G.P) c₄ I₄.wb
    (A := G.A₀) (K₂ := G.K₂) (BB := G.A₀ + 3 * G.K₂) (K := K) (M := G.Mx) I₄.r10
    (by rw [I₄.keep _ (by decide) (by decide), ← hr, h12]) I₄.r12
    (by rw [I₄.keep _ (by decide) (by decide), ← hr, h03])
    (by rw [I₄.keep _ (by decide) (by decide), ← hr, h13]) I₄.r01 hWK hWM
  have g₅ : ∀ r, ¬ ((210020 ≤ r ∧ r ≤ 210024) ∨ r = 211150 ∨ r = 211151) →
      c₅.nreg r = c₄.nreg r := fun r h => f₅.1 r (by simpa using h)
  -- frames
  have RF₁ : Restore.RF DrvR.drvBands G.A₀ c c₁ k₁ :=
    DrvD.rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨DrvD.mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₁
  have RF₃ : Restore.RF DrvR.drvBands G.A₀ c₂ c₃ k₃ :=
    DrvD.rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨DrvD.mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₃
  have RF₅ : Restore.RF DrvR.drvBands G.A₀ c₄ c₅ k₅ :=
    DrvD.rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨DrvD.mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₅
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), Exec.seq x₁ (Exec.seq x₂ (Exec.seq x₃
    (Exec.seq x₄ x₅))), by omega, x₅.wb_right, v20, v21, v22, v23, v24, ?_, ?_, ?_, ?_, ?_,
    RF₁.trans (RF₂.trans (RF₃.trans (RF₄.trans RF₅)))⟩
  · rw [g₅ _ (by unfold ALLOC; omega), I₄.alloc]
  · intro r hb hra
    have hb' := hb
    simp only [BL, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb'
    rw [g₅ r (by omega), I₄.keep r hb hra, ← hr]
  · intro a ha; rw [m₅, I₄.low a ha]
  · rw [m₅]; exact I₄.list
  · intro q hq; rw [m₅]; exact I₄.bkt q (by unfold GEnv.K₂ at hq; omega)

end

end DrvLT

end Chazelle.Core
