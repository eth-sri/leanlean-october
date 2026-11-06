module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvLTProg
public import Chazelle.Core.DownPhaseDrvLTMath
public import Chazelle.Core.DownPhaseDrvDMain

/-!
# Down-phase level tail (D12), part 3: the straight-line pieces and the reservation

`ltInit_exec`, `ltRes_exec` (the reservation of `5 K₂` words), `ltMid_exec`, `ltB1_exec`,
`ltB2_exec`, `ltB3_exec`, `ltArgs_exec`, `ltRd_exec`.
-/

namespace Chazelle.Core

namespace DrvLT

open Machine Machine.Stmt Programs SignK BuildRam
open SortL (seg)

@[expose] public section

theorem inDrv_BL : DrvD.InDrv BL := by
  intro r hr
  simp only [BL, Bool.or_eq_true, decide_eq_true_eq] at hr
  exact ⟨DrvD.mem_drvBands (⋄) (⋄), by unfold ALLOC; omega⟩

theorem BL_mono {B : ℕ → Bool} (h : ∀ r, B r = true → BL r = true) {c c' : Config}
    (hf : FrameM B c c') : FrameM BL c c' := hf.mono h

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem ltInit_exec (c : Config) (hw : WordsBounded W c) (hW : 3 ≤ W) :
    ∃ c' k, Exec P W ltInit c c' k ∧ k = 5 ∧ c'.nreg 211100 = 1 ∧ c'.nreg 211101 = 3 ∧
      c'.nreg 210034 = 1 ∧ c'.nreg 211110 = c.nreg ALLOC ∧ c'.nreg 211111 = 0 ∧
      FrameB (fun r => decide (r = 211100 ∨ r = 211101 ∨ r = 210034 ∨ r = 211110 ∨
        r = 211111)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltInit c c' k ∧ k = 5 ∧
      (c'.nreg 211100 = 1 ∧ c'.nreg 211101 = 3 ∧ c'.nreg 210034 = 1 ∧
        c'.nreg 211110 = c.nreg ALLOC ∧ c'.nreg 211111 = 0) := by
    unfold ltInit
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp; rfl
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex (⌖)⟩

/-- The registers of the reservation. -/
def Bres (r : ℕ) : Bool := decide (r = 211111) || decide (r = 9999)

/-- **The reservation** of `5 K₂` words. -/
theorem ltRes_exec {c : Config} (hw : WordsBounded W c) {K₂ : ℕ} (h12 : c.nreg 211012 = K₂)
    (h11 : c.nreg 211111 = 0) (h00 : c.nreg 211100 = 1) (hW : c.nreg ALLOC + 5 * K₂ + 1 ≤ W)
    (A₀ : ℕ) :
    ∃ c' k, Exec P W ltRes c c' k ∧ k ≤ 8 * K₂ + 2 ∧ c'.nreg ALLOC = c.nreg ALLOC + 5 * K₂ ∧
      c'.nreg 211111 = K₂ ∧ FrameB Bres c c' ∧ Restore.RF DrvR.drvBands A₀ c c' k := by
  let Inv : ℕ → Config → Prop := fun j e => WordsBounded W e ∧ e.nreg 211111 = j ∧
    e.nreg 211012 = K₂ ∧ e.nreg 211100 = 1 ∧ e.nreg ALLOC = c.nreg ALLOC + 5 * j ∧
    FrameB Bres c e ∧ j ≤ K₂
  have key : ∀ j e, j < K₂ → Inv j e → ∃ e' k, Exec P W ltResBody e e' k ∧ Inv (j + 1) e' ∧
      Restore.RF DrvR.drvBands A₀ e e' k ∧ k = 6 := by
    intro j e hj ⟨hw, h1, h2, h3, h4, hf, _⟩
    have h4' : e.nreg 9999 = c.nreg ALLOC + 5 * j := h4
    obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltResBody e e' k ∧ k = 6 ∧
        (e'.nreg 211111 = j + 1 ∧ e'.nreg 9999 = c.nreg ALLOC + 5 * (j + 1)) := by
      unfold ltResBody
      exec_block
      all_goals try (config_simp; (try simp only [h1, h3, h4']); omega)
      refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> simp only [h1, h3, h4']; omega
    have hf' : FrameB Bres e e' := exec_frameB ex (by decide)
    have hnot : ∀ r, bandOf r ∉ DrvR.drvBands → r ≠ ALLOC → Bres r = false := fun r hr hra => by
      simp only [Bres, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨fun h => hr (by rw [h]; exact DrvD.mem_drvBands (by norm_num) (by norm_num)), hra⟩
    refine ⟨e', k, ex, ⟨ex.wb_right, q.1, (hf'.1 _ (by decide)).trans h2,
      (hf'.1 _ (by decide)).trans h3, by show e'.nreg 9999 = _; rw [q.2], hf.trans hf', hj⟩,
      ⟨fun r hr hra => hf'.1 r (hnot r hr hra), fun r _ =>
        WalkKey.exec_rframe ex (B := fun _ => false) (by decide) r rfl, fun a _ => by rw [hf'.2.2.1],
        fun a _ => by rw [hf'.2.2.2.1], hf'.2.2.2.2, ?_, ?_⟩, hk⟩
    · show e.nreg 9999 ≤ e'.nreg 9999
      rw [q.2, h4']; omega
    · show e'.nreg 9999 ≤ e.nreg 9999 + k
      rw [q.2, h4', hk]; omega
  have I0 : Inv 0 c := ⟨hw, h11, h12, h00, by simp, FrameB.refl _ _, Nat.zero_le _⟩
  obtain ⟨c', k, ex, ⟨j, w', h1, h2, -, h4, hf, hjle⟩, hx, RFl, hk⟩ := Restore.whileLtN_frame
    (P := P) (W := W) (a := 211111) (b := 211012) (body := ltResBody) (B := DrvR.drvBands)
    (A₀ := A₀) (fun e => ∃ j, Inv j e) (fun e => K₂ - e.nreg 211111) 6 (fun e ⟨_, h⟩ => h.1)
    (fun e ⟨j, hI⟩ ht => by
      obtain ⟨hw, h1, h2, -⟩ := id hI
      rw [h1, h2] at ht
      obtain ⟨e', k, ex, hI', RF', hk⟩ := key j e ht hI
      exact ⟨e', k, ex, ⟨j + 1, hI'⟩, RF', by omega, by rw [h1, hI'.2.1]; omega⟩) ⟨0, I0⟩
  have hjR : j = K₂ := by rw [h1, h2] at hx; omega
  subst hjR
  refine ⟨c', k, ex, ?_, h4, h1, hf, RFl⟩
  rw [h11] at hk
  simpa using hk

set_option maxHeartbeats 1000000 in
theorem ltMid_exec (c : Config) (hw : WordsBounded W c) {K₂ A T : ℕ}
    (h12 : c.nreg 211012 = K₂) (h10 : c.nreg 211110 = A) (h09 : c.nreg 211009 = T)
    (hW : A + 3 * K₂ ≤ W) :
    ∃ c' k, Exec P W ltMid c c' k ∧ k = 7 ∧ c'.nreg 211112 = A + 3 * K₂ ∧
      c'.nreg 211113 = A ∧ c'.nreg 211114 = A + 3 * K₂ ∧ c'.nreg 211130 = 0 ∧
      c'.nreg 211131 = T ∧
      FrameB (fun r => decide (r = 211147 ∨ (211112 ≤ r ∧ r ≤ 211114) ∨ r = 211130 ∨
        r = 211131)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltMid c c' k ∧ k = 7 ∧
      (c'.nreg 211112 = A + 3 * K₂ ∧ c'.nreg 211113 = A ∧ c'.nreg 211114 = A + 3 * K₂ ∧
        c'.nreg 211130 = 0 ∧ c'.nreg 211131 = T) := by
    unfold ltMid
    exec_block
    all_goals try (config_simp; (try simp only [h12, h10, h09]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;> (try simp only [h12, h10, h09]) <;>
      omega
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, exec_frameB ex (⌖)⟩

/-- The registers `ltB1` writes. -/
def B1 (r : ℕ) : Bool := decide (211140 ≤ r ∧ r ≤ 211145) || decide (210061 ≤ r ∧ r ≤ 210063)

set_option maxHeartbeats 2000000 in
theorem ltB1_exec (e : Config) (hw : WordsBounded W e) {p D : ℕ} (h31 : e.nreg 211131 = p)
    (h00 : e.nreg 211100 = 1) (h13 : e.nreg 211113 = D) (hW : p + 2 ≤ W)
    (hW3 : 3 * e.nmem (p + 1) ≤ W) :
    ∃ e' k, Exec P W ltB1 e e' k ∧ k = 11 ∧ e'.nreg 211140 = e.nmem p ∧
      e'.nreg 211143 = e.nmem (p + 1 + 1) ∧ e'.nreg 211144 = 3 * e.nmem (p + 1) ∧
      e'.nreg 211145 = 2 * e.nmem (p + 1) ∧ e'.nreg 210061 = 3 * e.nmem (p + 1) ∧
      e'.nreg 210062 = e.nmem p ∧ e'.nreg 210063 = D ∧ e'.nmem = e.nmem ∧ FrameB B1 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB1 e e' k ∧ k = 11 ∧
      (e'.nreg 211140 = e.nmem p ∧
      e'.nreg 211143 = e.nmem (p + 1 + 1) ∧ e'.nreg 211144 = 3 * e.nmem (p + 1) ∧
      e'.nreg 211145 = 2 * e.nmem (p + 1) ∧ e'.nreg 210061 = 3 * e.nmem (p + 1) ∧
      e'.nreg 210062 = e.nmem p ∧ e'.nreg 210063 = D) := by
    unfold ltB1
    exec_block
    all_goals try (config_simp; (try simp only [h31, h00, h13]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h31, h00, h13]) <;> (try omega)
  have hf := exec_frameB ex (B := B1) (⌖)
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2.1, q.2.2.2.2.2.1,
    q.2.2.2.2.2.2, hf.2.2.1, hf⟩

/-- The registers `ltB2` writes. -/
def B2 (r : ℕ) : Bool := decide (r = 211113) || decide (210061 ≤ r ∧ r ≤ 210063)

set_option maxHeartbeats 1000000 in
theorem ltB2_exec (e : Config) (hw : WordsBounded W e) {a ℓ b D₂ : ℕ}
    (h13 : e.nreg 211113 = a) (h44 : e.nreg 211144 = 3 * ℓ) (h45 : e.nreg 211145 = 2 * ℓ)
    (h43 : e.nreg 211143 = b) (h14 : e.nreg 211114 = D₂) (hW : a + 3 * ℓ ≤ W) :
    ∃ e' k, Exec P W ltB2 e e' k ∧ k = 4 ∧ e'.nreg 211113 = a + 3 * ℓ ∧
      e'.nreg 210061 = 2 * ℓ ∧ e'.nreg 210062 = b ∧ e'.nreg 210063 = D₂ ∧ e'.nmem = e.nmem ∧
      FrameB B2 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB2 e e' k ∧ k = 4 ∧
      (e'.nreg 211113 = a + 3 * ℓ ∧ e'.nreg 210061 = 2 * ℓ ∧ e'.nreg 210062 = b ∧
        e'.nreg 210063 = D₂) := by
    unfold ltB2
    exec_block
    all_goals try (config_simp; (try simp only [h13, h44, h45, h43, h14]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h13, h44, h45, h43, h14])
  have hf := exec_frameB ex (B := B2) (⌖)
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2, hf.2.2.1, hf⟩

/-- The registers `ltB3` writes. -/
def B3 (r : ℕ) : Bool := decide (r = 211114) || decide (r = 211131) || decide (r = 211130)

set_option maxHeartbeats 1000000 in
theorem ltB3_exec (e : Config) (hw : WordsBounded W e) {D₂ ℓ p j : ℕ}
    (h14 : e.nreg 211114 = D₂) (h45 : e.nreg 211145 = 2 * ℓ) (h31 : e.nreg 211131 = p)
    (h01 : e.nreg 211101 = 3) (h30 : e.nreg 211130 = j) (h00 : e.nreg 211100 = 1)
    (hW : D₂ + 2 * ℓ ≤ W) (hW2 : p + 3 ≤ W) (hW3 : j + 1 ≤ W) :
    ∃ e' k, Exec P W ltB3 e e' k ∧ k = 3 ∧ e'.nreg 211114 = D₂ + 2 * ℓ ∧
      e'.nreg 211131 = p + 3 ∧ e'.nreg 211130 = j + 1 ∧ e'.nmem = e.nmem ∧
      FrameB B3 e e' := by
  obtain ⟨e', k, ex, hk, q⟩ : ∃ e' k, Exec P W ltB3 e e' k ∧ k = 3 ∧
      (e'.nreg 211114 = D₂ + 2 * ℓ ∧ e'.nreg 211131 = p + 3 ∧ e'.nreg 211130 = j + 1) := by
    unfold ltB3
    exec_block
    all_goals try (config_simp; (try simp only [h14, h45, h31, h01, h30, h00]); omega)
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h14, h45, h31, h01, h30, h00])
  have hf := exec_frameB ex (B := B3) (⌖)
  exact ⟨e', k, ex, hk, q.1, q.2.1, q.2.2, hf.2.2.1, hf⟩

set_option maxHeartbeats 2000000 in
theorem ltArgs_exec (c : Config) (hw : WordsBounded W c) {A K₂ BB K M : ℕ}
    (h10 : c.nreg 211110 = A) (h12 : c.nreg 211012 = K₂) (h112 : c.nreg 211112 = BB)
    (h03 : c.nreg 210003 = K) (h13 : c.nreg 211013 = M) (h01 : c.nreg 211101 = 3)
    (hW : 4 * K + 3 ≤ W) (hW' : 4 * M ≤ W) :
    ∃ c' k, Exec P W ltArgs c c' k ∧ k = 10 ∧ c'.nreg 210020 = A ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = BB ∧ c'.nreg 210023 = 4 * K + 3 ∧ c'.nreg 210024 = 4 * M ∧
      c'.nmem = c.nmem ∧
      FrameB (fun r => decide ((210020 ≤ r ∧ r ≤ 210024) ∨ r = 211150 ∨ r = 211151)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltArgs c c' k ∧ k = 10 ∧
      (c'.nreg 210020 = A ∧ c'.nreg 210021 = K₂ ∧
      c'.nreg 210022 = BB ∧ c'.nreg 210023 = 4 * K + 3 ∧ c'.nreg 210024 = 4 * M) := by
    unfold ltArgs
    exec_block
    all_goals try (config_simp; (try simp only [h10, h12, h112, h03, h13, h01]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      (try simp only [h10, h12, h112, h03, h13, h01]) <;> (try omega)
  have hf := exec_frameB ex
    (B := fun r => decide ((210020 ≤ r ∧ r ≤ 210024) ∨ r = 211150 ∨ r = 211151)) (⌖)
  exact ⟨c', k, ex, hk, q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2, hf.2.2.1, hf⟩

set_option maxHeartbeats 1000000 in
theorem ltRd_exec (c : Config) (hw : WordsBounded W c) (hW : 134 ≤ W) :
    ∃ c' k, Exec P W ltRd c c' k ∧ k = 2 ∧ c'.nreg 216000 = 134 ∧
      c'.nreg 216001 = c.nreg 211007 ∧ c'.nmem = c.nmem ∧
      FrameB (fun r => decide (r = 216000 ∨ r = 216001)) c c' := by
  obtain ⟨c', k, ex, hk, q⟩ : ∃ c' k, Exec P W ltRd c c' k ∧ k = 2 ∧
      (c'.nreg 216000 = 134 ∧ c'.nreg 216001 = c.nreg 211007) := by
    unfold ltRd
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp
  have hf := exec_frameB ex (B := fun r => decide (r = 216000 ∨ r = 216001)) (⌖)
  exact ⟨c', k, ex, hk, q.1, q.2, hf.2.2.1, hf⟩

end exec

end

end DrvLT

end Chazelle.Core
