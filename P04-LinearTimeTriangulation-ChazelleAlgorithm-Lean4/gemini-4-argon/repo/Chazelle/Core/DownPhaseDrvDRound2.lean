module

public import Chazelle.Core.DownPhaseDrvDRound

/-!
# Down-phase restoration rounds (D8), part 12: helpers for one round

* `RF.base`: a relative frame for a larger base is one for a smaller base;
* `arcs_length_le`: `buildNF` has at most `2 K + 1` arcs;
* `chordListAt_robust`, `seg_robust`, `desc_robust`: facts read below the allocator are robust;
* `stateAt_of`: the level state from the splice's output.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

theorem RF.base {B : Finset ℕ} {A A' : ℕ} {c c' : Config} {k : ℕ} (h : Restore.RF B A c c' k)
    (hA : A' ≤ A) : Restore.RF B A' c c' k :=
  ⟨h.1, h.2.1, fun a ha => h.2.2.1 a (by omega), fun a ha => h.2.2.2.1 a (by omega),
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- `buildNF` has at most `2 K + 1` arcs. -/
theorem arcs_length_le {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    (hE : E.length = 2 * L.length) : (BuildNF.buildNF M Q L E).arcs.length ≤ 2 * L.length + 1 := by
  show (BuildNF.arcList M Q L E).length ≤ _
  unfold BuildNF.arcList
  split_ifs with h
  · simp
  · rw [List.length_map]
    unfold BuildNF.gapStarts
    exact (List.length_filter_le _ _).trans (by simp [hE])

theorem chordListAt_robust {m : ℕ → ℕ} {A B : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : ChordListAt m A L) (hB : A + 3 * L.length ≤ B) :
    Robust B m (fun m' => ChordListAt m' A L) := by
  intro m' hm' i hi
  obtain ⟨a1, a2, a3⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rwa [hm' _ (by omega)]
  · rwa [hm' _ (by omega)]
  · rwa [hm' _ (by omega)]

theorem seg_robust {m : ℕ → ℕ} {a n B : ℕ} (hB : a + n ≤ B) :
    Robust B m (fun m' => seg m' a n = seg m a n) :=
  fun m' hm' => SortL.seg_congr fun i hi => hm' _ (by omega)

theorem desc_robust {P : Polygon} {A A' : ℕ} {m₀ m : ℕ → ℕ} {D : ℕ} {M : Model}
    (hwf : ModelDescWF P A m₀ D) (hM : ModelDescAt m₀ D (Qof P) M)
    (hm : ∀ a, a < A → m a = m₀ a) (hA : A ≤ A') :
    Robust A' m (fun m' => ModelDescAt m' D (Qof P) M) := fun m' hm' =>
  (Gran.desc_agree' hwf hM (fun a ha => (hm' a (by omega)).trans (hm a ha))).1

end

end DrvD

end Chazelle.Core

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

/-- The region-loop data of a round. -/
def renvOf (E : DEnv) (L : List (ℕ × ℕ × ℕ)) (Ev : List ℕ) (reg : ℕ → Set Point) (B₀ H : ℕ) :
    REnv :=
  ⟨E.P, E.W, L, Ev, reg, E.A₀, E.m₀, B₀, E.MD, H, E.γ, E.d0, E.ctx, E.sF, E.κf, E.F, E.G, E.Hc,
    E.X⟩

set_option maxHeartbeats 16000000 in
/-- **The first part of a round**: header, reservation, set-up of the region loop. -/
theorem round_A {E : DEnv} (hE : DGood E) {t : ℕ} {c : Config} (hI : RInv E t c)
    (ht : t < E.d0) {L : List (ℕ × ℕ × ℕ)} {Ev : List ℕ} (hSt : DrvR.StateAt E.P c L Ev)
    (hdeg : E.M.DegLe ((BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q) (max 4 (E.d0 - t)))
    (hsg : E.M.Semigranular ((BuildNF.buildNF E.M E.Q L Ev).F E.M E.Q) E.γ)
    (hcnt : L.length + 1 ≤ 2 ^ t * (E.K₀ + 1)) {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs E.M E.Q (BuildNF.buildNF E.M E.Q L Ev) reg) :
    ∃ c₃ k, (∀ (rest : Stmt) (c' : Config) (k' : ℕ), Exec E.P E.W rest c₃ c' k' →
        Exec E.P E.W (.seq hdS (.seq resS (.seq midS rest))) c c' (k + k')) ∧
      RGood (renvOf E L Ev reg (c.nreg ALLOC) (c.nreg 210005)) c₃ ∧
      Restore.RF DrvR.drvBands E.A₀ c c₃ k ∧ k ≤ 8 * (L.length + 1) + 25 ∧
      c₃.nreg ALLOC = c.nreg ALLOC + 5 * (L.length + 1) ∧
      (∀ q, (210000 ≤ q ∧ q < 216012) ∨ (216034 ≤ q ∧ q < 220000) ∨ q = 230001 →
        c₃.nreg q = c.nreg q) ∧ c₃.nmem = c.nmem := by
  obtain ⟨hD6, hDa, hK, hLb, hLa, hEb, hEa, hok, hperm, hsort, hNW⟩ := hSt
  simp only [rd, bandReg, bDownDrv, Nat.reduceMul, Nat.reduceAdd] at hD6 hDa hK hLb hLa hEb hEa hNW
  set B₀ := c.nreg ALLOC
  set H := c.nreg 210005
  set N := BuildNF.buildNF E.M E.Q L Ev with hN
  set R := L.length + 1 with hR
  have hareas := Gran.nf_areas hNW
  have hNAt := hNW.nfAt
  have hRN : N.regions.length = R := by simp [hN, BuildNF.buildNF, hR]
  have hW := hI.wb
  have hBW : B₀ ≤ E.W := hW.1 ALLOC
  have hRKc : R ≤ E.Kc := by
    unfold DEnv.Kc
    have : 2 ^ t ≤ 2 ^ E.d0 := Nat.pow_le_pow_right (by norm_num) ht.le
    calc R ≤ 2 ^ t * (E.K₀ + 1) := hcnt
      _ ≤ 2 ^ E.d0 * (E.K₀ + 1) := Nat.mul_le_mul_right _ this
  have hroom : B₀ + E.Br + 2 ≤ E.W := by
    have := hI.room
    have : E.Br + 2 ≤ (E.d0 - t) * (E.Br + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hBr : 40 + (E.Bf + 10) * E.Kc ≤ E.Br := by unfold DEnv.Br; omega
  have hBfR : (E.Bf + 10) * R ≤ (E.Bf + 10) * E.Kc := Nat.mul_le_mul_left _ hRKc
  have h5R : 10 * R ≤ (E.Bf + 10) * R := Nat.mul_le_mul_right _ (by omega)
  -- 1. the header
  obtain ⟨c₁, k₁, e₁, hk₁, a12, a17, a13, a14, a15, a16, a18, a21, a20, a23, f₁⟩ :=
    hdS_exec (P := E.P) c hW (H := H) rfl hI.r02 hI.r05 (by have := hareas.1; omega)
  have w₁ := e₁.wb_right
  have g₁ : ∀ q, ¬ (216012 ≤ q ∧ q ≤ 216033) → c₁.nreg q = c.nreg q := fun q hq =>
    f₁.1 q (by simpa using hq)
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  rw [hNAt.2.2.1, hRN] at a13
  rw [hNAt.2.1] at a17
  -- 2. the reservation
  obtain ⟨c₂, k₂, e₂, hk₂, A₂, r23, f₂, RF₂⟩ := resS_exec (P := E.P) w₁ a13 a23
    (by rw [g₁ _ (by omega), hI.r02]) (by rw [g₁ _ (by unfold ALLOC; omega)]; omega) E.A₀
  have w₂ := e₂.wb_right
  have g₂ : ∀ q, q ≠ 216023 → q ≠ 9999 → c₂.nreg q = c₁.nreg q := fun q h1 h2 =>
    f₂.1 q (by simp [Bres, h1, h2])
  have m₂ : c₂.nmem = c₁.nmem := f₂.2.2.1
  have A₁ : c₁.nreg ALLOC = B₀ := g₁ _ (by unfold ALLOC; omega)
  rw [A₁] at A₂
  -- 3. the set-up
  obtain ⟨c₃, k₃, e₃, hk₃, b19, b22, b30, b31, f₃⟩ := midS_exec (P := E.P) c₂ w₂ (R := R)
    (B := B₀) (RB := c.nmem (H + 5)) (by rw [g₂ _ (by norm_num) (by norm_num), a13])
    (by rw [g₂ _ (by norm_num) (by norm_num), a18])
    (by rw [g₂ _ (by norm_num) (by norm_num), a15])
    (by rw [g₂ _ (by norm_num) (by norm_num), g₁ _ (by omega), hI.r05]) (by omega)
    (by have := hareas.2.2.1 0 (by rw [show N.nRegions = N.regions.length from rfl, hRN]; omega)
        omega)
  have w₃ := e₃.wb_right
  have g₃ : ∀ q, q ≠ 216019 → q ≠ 216022 → q ≠ 216030 → q ≠ 216031 → q ≠ 216033 →
      c₃.nreg q = c₂.nreg q := fun q h1 h2 h3 h4 h5 => f₃.1 q (by simp [h1, h2, h3, h4, h5])
  have m₃ : c₃.nmem = c.nmem := by rw [f₃.2.2.1, m₂, m₁]
  have A₃ : c₃.nreg ALLOC = B₀ + 5 * R := by
    rw [g₃ _ (by unfold ALLOC; omega) (by unfold ALLOC; omega) (by unfold ALLOC; omega)
      (by unfold ALLOC; omega) (by unfold ALLOC; omega), A₂]
  -- the kept registers
  have K3 : ∀ q, (210000 ≤ q ∧ q < 216012) ∨ (216034 ≤ q ∧ q < 220000) ∨ q = 230001 →
      c₃.nreg q = c.nreg q := fun q hq => by
    rw [g₃ q (by omega) (by omega) (by omega) (by omega) (by omega),
      g₂ q (by omega) (by omega), g₁ q (by omega)]
  have K3' : ∀ q, 216012 ≤ q → q ≤ 216033 → q ≠ 216019 → q ≠ 216022 → q ≠ 216030 →
      q ≠ 216031 → q ≠ 216033 → q ≠ 216023 → c₃.nreg q = c₁.nreg q := fun q _ _ h1 h2 h3 h4 h5 h6 => by
    rw [g₃ q h1 h2 h3 h4 h5, g₂ q h6 (by omega)]
  -- frames
  have RF₁ : Restore.RF DrvR.drvBands E.A₀ c c₁ k₁ :=
    rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₁
  have RF₃ : Restore.RF DrvR.drvBands E.A₀ c₂ c₃ k₃ :=
    rf_of_frameB (fun r hr => by
      simp only [decide_eq_true_eq] at hr
      exact ⟨mem_drvBands (by omega) (by omega), by unfold ALLOC; omega⟩) f₃
  have hlow : ∀ a, a < E.A₀ → c₃.nmem a = E.m₀ a := fun a ha => by rw [m₃]; exact hI.low a ha
  have hA0B : E.A₀ ≤ B₀ := hI.alloc
  refine ⟨c₃, k₁ + (k₂ + k₃), fun rest c' k' h => (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ h))).cast
    (by ring), ?_, RF₁.trans (RF₂.trans RF₃), by omega, A₃, K3, m₃⟩
  -- the region-loop facts
  have hk3 : ∀ q, q < 216012 → 210000 ≤ q → c₃.nreg q = c.nreg q := fun q h1 h2 =>
    K3 q (Or.inl ⟨h2, h1⟩)
  refine ⟨hE.hF, hE.hG, hE.hWh, hE.hX, hE.hcap, hA0B, hE.hwf, hE.hMD, hok, hperm, hsort, hregs,
    Model.DegLe.mono _ hdeg (max_le hE.hd0 (Nat.sub_le _ _)), hsg, by rwa [m₃], hlow,
    w₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c₃.nreg 210001 = E.MD; rw [hk3 _ (by norm_num) (by norm_num), hI.r001]
  · show c₃.nreg 216000 = E.d0; rw [hk3 _ (by norm_num) (by norm_num), hI.r00]
  · show c₃.nreg 216001 = E.γ; rw [hk3 _ (by norm_num) (by norm_num), hI.r01]
  · rw [hk3 _ (by norm_num) (by norm_num), hI.r02]
  · rw [hk3 _ (by norm_num) (by norm_num), hI.r03]
  · rw [hk3 _ (by norm_num) (by norm_num), hI.r04]
  · rw [hk3 _ (by norm_num) (by norm_num), hI.r05]
  · rw [hk3 _ (by norm_num) (by norm_num), hI.r06]
  · show c₃.nreg 216012 = H
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a12]
  · show c₃.nreg 216013 = R
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a13]
  · show c₃.nreg 216014 = c₃.nmem (H + 4)
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a14, m₃]
  · show c₃.nreg 216016 = c₃.nmem (H + 7)
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a16, m₃]
  · show c₃.nreg 216017 = N.arcs.length
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a17]
  · show c₃.nreg 216018 = B₀
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a18]
  · show c₃.nreg 216019 = B₀ + 3 * R; exact b19
  · show c₃.nreg 216020 = 0
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a20]
  · show c₃.nreg 216021 = B₀
    rw [K3' _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), a21]
  · show c₃.nreg 216022 = B₀ + 3 * R; exact b22
  · exact b30
  · show c₃.nreg 216031 = c₃.nmem (H + 5) + 2; rw [b31, m₃]
  · show c₃.nreg 230001 = E.ctx; rw [K3 _ (Or.inr (Or.inr rfl)), hI.rctx]
  · show B₀ + 3 * R + 2 * R ≤ c₃.nreg ALLOC; rw [A₃]; omega
  · show c₃.nreg ALLOC + (E.Bf + 2) * R + 2 ≤ E.W
    rw [A₃]
    have : (E.Bf + 10) * R = (E.Bf + 2) * R + 8 * R := by ring
    omega

end

end DrvD

end Chazelle.Core
