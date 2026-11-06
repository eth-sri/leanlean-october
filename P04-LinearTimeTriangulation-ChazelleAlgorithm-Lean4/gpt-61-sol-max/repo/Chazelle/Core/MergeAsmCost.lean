module

public import Chazelle.Core.MergeAsmMath

/-!
# WP-F merge assembly, part 4: the cost arithmetic

With `S = K₁ + K₂ + 1`, `Y = F · G · (H + ⌈log₂ (m + 1)⌉ + 1)` (`F, G ≥ 1`) and
`S ≤ β (m + 1)`, each stage of the merge costs at most a constant (depending on `D`) times
`S Y`:

* fusion `κF S (F + ⌈log₂ S⌉ + 1) ≤ κF (β + 2) S Y` (`fuse_le`);
* restoration `κR (K + 1) F G (H + ⌈log₂ γ_R⌉ + ⌈log₂ (K + 1)⌉ + 1) ≤ 8 (β + 7) κR S Y` for
  `K + 1 ≤ 8 S` and `γ_R ≤ 8 (m + 1)` (`restore_le`);
* granularity enforcement `κG (K' (⌈log₂ K'⌉ + 1) + 1) ≤ κG (8 c (8 c β + 1) + 1) S Y` for
  `K' ≤ 8 c S` (`gran_le`).
-/

namespace Chazelle.Core

namespace MergeAsm

@[expose] public section

/-- `⌈log₂ S⌉ ≤ β + ⌈log₂ (m + 1)⌉` for `S ≤ β (m + 1)`. -/
theorem clog_S {S β m : ℕ} (h : S ≤ β * (m + 1)) : Nat.clog 2 S ≤ β + Nat.clog 2 (m + 1) :=
  (clog_mono h).trans (clog_mul_le' β (m + 1))

theorem clog_8 (x : ℕ) : Nat.clog 2 (8 * x) ≤ 3 + Nat.clog 2 x := by
  refine (clog_mul_le 8 x).trans ?_
  aesop

/-- The fusion stage. -/
theorem fuse_le {κ S β m F₀ F G H : ℕ} (hS : S ≤ β * (m + 1)) (hF : F₀ ≤ F) (hF1 : 1 ≤ F)
    (hG1 : 1 ≤ G) :
    κ * S * (F₀ + Nat.clog 2 S + 1) ≤
      κ * (β + 2) * S * (F * G * (H + Nat.clog 2 (m + 1) + 1)) := by
  have hc := clog_S hS
  set L := Nat.clog 2 (m + 1)
  have hY1 : F ≤ F * G * (H + L + 1) := by
    calc F = F * 1 * 1 := by ring
      _ ≤ F * G * (H + L + 1) := by gcongr; omega
  have hY2 : L + 1 ≤ F * G * (H + L + 1) := by
    calc L + 1 = 1 * 1 * (L + 1) := by ring
      _ ≤ F * G * (H + L + 1) := by gcongr; omega
  
  set Y := F * G * (H + L + 1)
  have : F₀ + Nat.clog 2 S + 1 ≤ (β + 2) * Y := by nlinarith
  calc κ * S * (F₀ + Nat.clog 2 S + 1) ≤ κ * S * ((β + 2) * Y) := Nat.mul_le_mul_left _ this
    _ = κ * (β + 2) * S * Y := by ring

/-- The restoration stage. -/
theorem restore_le {κ K S β m γ F₀ G₀ H₀ F G H : ℕ} (hS : S ≤ β * (m + 1)) (hK : K + 1 ≤ 8 * S)
    (hγ : γ ≤ 8 * (m + 1)) (hF : F₀ ≤ F) (hG : G₀ ≤ G) (hH : H₀ ≤ H) :
    κ * (K + 1) * F₀ * G₀ * (H₀ + Nat.clog 2 γ + Nat.clog 2 (K + 1) + 1) ≤
      8 * (β + 7) * κ * S * (F * G * (H + Nat.clog 2 (m + 1) + 1)) := by
  set L := Nat.clog 2 (m + 1)
  have h1 : Nat.clog 2 γ ≤ 3 + L := (clog_mono hγ).trans (clog_8 _)
  have h2 : Nat.clog 2 (K + 1) ≤ 3 + β + L :=
    (clog_mono hK).trans ((clog_8 S).trans (by have := clog_S hS; omega))
  have hp : H₀ + Nat.clog 2 γ + Nat.clog 2 (K + 1) + 1 ≤ (β + 7) * (H + L + 1) := by nlinarith
  calc κ * (K + 1) * F₀ * G₀ * (H₀ + Nat.clog 2 γ + Nat.clog 2 (K + 1) + 1)
      ≤ κ * (8 * S) * F * G * ((β + 7) * (H + L + 1)) := by gcongr
    _ = 8 * (β + 7) * κ * S * (F * G * (H + L + 1)) := by ring

/-- The granularity stage. -/
theorem gran_le {κ K c S β m F G H : ℕ} (hS : S ≤ β * (m + 1)) (hK : K ≤ 8 * c * S)
    (hF1 : 1 ≤ F) (hG1 : 1 ≤ G) (hS1 : 1 ≤ S) :
    κ * (K * (Nat.clog 2 K + 1) + 1) ≤
      κ * (8 * c * (8 * c * β + 1) + 1) * S * (F * G * (H + Nat.clog 2 (m + 1) + 1)) := by
  set L := Nat.clog 2 (m + 1)
  have hl : Nat.clog 2 K ≤ 8 * c * β + L := by
    have : K ≤ (8 * c * β) * (m + 1) := by
      calc K ≤ 8 * c * S := hK
        _ ≤ 8 * c * (β * (m + 1)) := Nat.mul_le_mul_left _ hS
        _ = (8 * c * β) * (m + 1) := by ring
    exact (clog_mono this).trans (clog_mul_le' _ _)
  have hY : L + 1 ≤ F * G * (H + L + 1) := by
    calc L + 1 = 1 * 1 * (L + 1) := by ring
      _ ≤ F * G * (H + L + 1) := by gcongr; omega
  set Y := F * G * (H + L + 1)
  have e1 : K * (Nat.clog 2 K + 1) ≤ 8 * c * S * ((8 * c * β + 1) * (L + 1)) := by
    calc K * (Nat.clog 2 K + 1) ≤ 8 * c * S * (8 * c * β + L + 1) := by gcongr
      _ ≤ 8 * c * S * ((8 * c * β + 1) * (L + 1)) := by
        ring_nf <;> omega
  have e2 : K * (Nat.clog 2 K + 1) + 1 ≤ (8 * c * (8 * c * β + 1) + 1) * S * Y := by
    have : (8 * c * (8 * c * β + 1) + 1) * S * (L + 1) ≤ (8 * c * (8 * c * β + 1) + 1) * S * Y :=
      Nat.mul_le_mul_left _ hY
    nlinarith
  calc κ * (K * (Nat.clog 2 K + 1) + 1) ≤ κ * ((8 * c * (8 * c * β + 1) + 1) * S * Y) :=
        Nat.mul_le_mul_left _ e2
    _ = κ * (8 * c * (8 * c * β + 1) + 1) * S * Y := by ring

/-- `S ≤ β (m + 1)` from Lemma 2.3's bounds on `K₁`, `K₂`. -/
theorem S_le {K₁ K₂ a m₁ m₂ : ℕ} (h₁ : K₁ ≤ a * (2 * m₁ + 8)) (h₂ : K₂ ≤ a * (2 * m₂ + 8)) :
    K₁ + K₂ + 1 ≤ (16 * a + 1) * (m₁ + m₂ + 1) := by
  nlinarith

end

end MergeAsm

end Chazelle.Core
