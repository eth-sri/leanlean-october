module

public import Chazelle.Core.MergeAsmCost
public import Chazelle.Core.SortRam

/-!
# WP-F fusion assembly, part 26: cost arithmetic of the fusion

With `S = K₁ + K₂ + 1` and `Y = F γ + ⌈log₂ S⌉ + 1`, every stage of the fusion costs
`O((κ_sweep D + κ_build + 1) · S · Y)` (`piece_le`, `nlog_le`, `fuse_total`).
-/

namespace Chazelle.Core

namespace FuseAsm

open MergeAsm

@[expose] public section

theorem piece_le (κ T S Fg : ℕ) (hT : T ≤ 8 * S) :
    κ * T * (Fg + Nat.clog 2 T + 1) ≤ 32 * κ * (S * (Fg + Nat.clog 2 S + 1)) := by
  have hc : Nat.clog 2 T ≤ 3 + Nat.clog 2 S := (clog_mono hT).trans (clog_8 S)
  have h4 : Fg + Nat.clog 2 T + 1 ≤ 4 * (Fg + Nat.clog 2 S + 1) := by omega
  calc κ * T * (Fg + Nat.clog 2 T + 1) ≤ κ * (8 * S) * (4 * (Fg + Nat.clog 2 S + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hT) h4
    _ = 32 * κ * (S * (Fg + Nat.clog 2 S + 1)) := by ring

theorem nlog_le (K S Fg : ℕ) (hK : K ≤ 8 * S) :
    K * (Nat.clog 2 K + 1) ≤ 32 * (S * (Fg + Nat.clog 2 S + 1)) := by
  have := piece_le 1 K S Fg hK
  have h2 : K * (Nat.clog 2 K + 1) ≤ 1 * K * (Fg + Nat.clog 2 K + 1) := by
    rw [Nat.one_mul]; exact Nat.mul_le_mul le_rfl (by omega)
  omega

/-- The cost bound of the fusion. -/
def fuseκ (κs : ℕ → ℕ) (κB : ℕ) (D : ℕ) : ℕ := 400000 * (κs D + κB + 1)

/-- **The total cost of the fusion.** -/
theorem fuse_total {κs : ℕ → ℕ} {κB D K₁ K₂ L₀ L₁ Kc Kd Fg k₁ k₂ k₃ k₄ k₅ k₆ k₇ : ℕ}
    (hL₀ : L₀ ≤ 2 * K₁ + 5) (hL₁ : L₁ ≤ 2 * K₂ + 3) (hKc : Kc ≤ L₀ + L₁) (hKd : Kd ≤ Kc)
    (h₁ : k₁ ≤ 22 * K₁ + 200000)
    (h₂ : k₂ ≤ 13 + κs D * (K₁ + K₂ + L₀ + 1) * (Fg + Nat.clog 2 (K₁ + K₂ + L₀ + 1) + 1))
    (h₃ : k₃ ≤ 22 * K₂ + 120000)
    (h₄ : k₄ ≤ 13 + κs D * (K₁ + K₂ + L₁ + 1) * (Fg + Nat.clog 2 (K₁ + K₂ + L₁ + 1) + 1))
    (h₅ : k₅ ≤ 24 * (L₀ + L₁) + 20)
    (h₆ : k₆ ≤ 2 + (SortR.sortCost 40 Kc + 70 * Kc + 30))
    (h₇ : k₇ ≤ 40 + κB * (Kd * (Nat.clog 2 Kd + 1) + 1)) :
    k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))) ≤
      fuseκ κs κB D * (K₁ + K₂ + 1) * (Fg + Nat.clog 2 (K₁ + K₂ + 1) + 1) := by
  obtain ⟨S, hS⟩ : ∃ S, S = K₁ + K₂ + 1 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Fg + Nat.clog 2 S + 1 := ⟨_, rfl⟩
  rw [← hS, ← hY]
  have p₂ := piece_le (κs D) (K₁ + K₂ + L₀ + 1) S Fg (by omega)
  have p₄ := piece_le (κs D) (K₁ + K₂ + L₁ + 1) S Fg (by omega)
  have p₆ := nlog_le Kc S Fg (by omega)
  have p₇ := nlog_le Kd S Fg (by omega)
  rw [← hY] at p₂ p₄ p₆ p₇
  obtain ⟨SY, hSY⟩ : ∃ x, x = S * Y := ⟨_, rfl⟩
  rw [← hSY] at p₂ p₄ p₆ p₇
  have hS1 : S ≤ SY := by rw [hSY]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hS0 : 1 ≤ S := by omega
  unfold SortR.sortCost at h₆
  have e7 : κB * (Kd * (Nat.clog 2 Kd + 1) + 1) ≤ κB * (32 * SY + 1) :=
    Nat.mul_le_mul le_rfl (by omega)
  have e7' : κB * (32 * SY + 1) ≤ 33 * (κB * SY) := by nlinarith
  have e6 : (40 + 30) * (Kc * (Nat.clog 2 Kc + 1) + 1) ≤ 70 * (32 * SY + 1) :=
    Nat.mul_le_mul le_rfl (by omega)
  obtain ⟨A, hA⟩ : ∃ x, x = κs D * SY := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, x = κB * SY := ⟨_, rfl⟩
  have eA : 32 * κs D * SY = 32 * A := by rw [hA]; ring
  rw [eA] at p₂ p₄
  rw [← hB] at e7'
  have goal : fuseκ κs κB D * S * Y = 400000 * A + 400000 * B + 400000 * SY := by
    unfold fuseκ; rw [hA, hB, hSY]; ring
  rw [goal]
  omega

theorem sweepc_mono (κ A Fg : ℕ) {L L' : ℕ} (h : L ≤ L') :
    κ * (A + L + 1) * (Fg + Nat.clog 2 (A + L + 1) + 1) ≤
      κ * (A + L' + 1) * (Fg + Nat.clog 2 (A + L' + 1) + 1) :=
  Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega))
    (by have := clog_mono (show A + L + 1 ≤ A + L' + 1 by omega); omega)

theorem nlogc_mono (κ : ℕ) {K K' : ℕ} (h : K ≤ K') :
    κ * (K * (Nat.clog 2 K + 1) + 1) ≤ κ * (K' * (Nat.clog 2 K' + 1) + 1) :=
  Nat.mul_le_mul le_rfl (by
    have := clog_mono h
    have := Nat.mul_le_mul h (show Nat.clog 2 K + 1 ≤ Nat.clog 2 K' + 1 by omega)
    omega)

theorem sortc_mono (κ : ℕ) {K K' : ℕ} (h : K ≤ K') :
    SortR.sortCost κ K ≤ SortR.sortCost κ K' := by
  unfold SortR.sortCost; exact nlogc_mono _ h

end

end FuseAsm

end Chazelle.Core
