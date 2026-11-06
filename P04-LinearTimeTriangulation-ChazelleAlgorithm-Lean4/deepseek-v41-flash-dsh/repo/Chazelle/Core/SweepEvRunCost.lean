module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvRun

/-!
# The sweep (WP-D), stages 2–3: the cost of the run steps (arithmetic)

`run_cost`: the cost of `prep ; mk2 ; start ; loop` is at most
`κR D · (K₁ + K₂ + 1) · (F γ + ⌈log₂ (K₁ + K₂ + 1)⌉ + 1)`.
-/

namespace Chazelle.Core

namespace SweepEv

@[expose] public section

/-- The per-unit cost of one iteration. -/
def iterA (D κWD κGD κO κK : ℕ) : ℕ :=
  4 * κWD + 2 + (12 * D + 8) * ((2 * D + 3) * 500016 + 166500 + 4 * κGD + κO) + κO + κK

/-- The constant of the run steps. -/
def runA (D κWD κGD κO κK κP κSD κS0D : ℕ) : ℕ :=
  10 * iterA D κWD κGD κO κK + 22 + 4 * κS0D + κP + κSD

theorem odK_le {Fg D KG Z : ℕ} (hF : Fg + 1 ≤ Z) :
    odK Fg D KG ≤ ((2 * D + 3) * 500016 + 166500) * Z + KG := by
  unfold odK orgDoK evCandK evShotK ShotList.shotCost
  have h1 : 16 * Fg + 500000 ≤ 500016 * Z := ⋄
  have h2 : (2 * (D + 1) + 1) * (16 * Fg + 500000) ≤ (2 * (D + 1) + 1) * (500016 * Z) :=
    Nat.mul_le_mul_left _ h1
  nlinarith

theorem iterK_le {Fg D T L KG κWD κGD κO κK Z : ℕ} (hZ : Z = Fg + L + 1) (hT : T ≤ L + 3)
    (hKG : KG = κGD * (Fg + T + 1)) :
    iterK (κWD * (T + 1)) κK κO Fg D KG ≤ iterA D κWD κGD κO κK * Z := by
  have hZ1 : 1 ≤ Z := ⋄
  have hT4 : T + 1 ≤ 4 * Z := ⋄
  have hF4 : Fg + T + 1 ≤ 4 * Z := ⋄
  have hW : κWD * (T + 1) ≤ κWD * (4 * Z) := Nat.mul_le_mul_left _ hT4
  have hG : KG ≤ κGD * (4 * Z) := by rw [hKG]; exact Nat.mul_le_mul_left _ hF4
  have hO := odK_le (Fg := Fg) (D := D) (KG := KG) (Z := Z) (⋄)
  have hO2 : odK Fg D KG + κO ≤ ((2 * D + 3) * 500016 + 166500 + 4 * κGD + κO) * Z := by
    have : κO ≤ κO * Z := Nat.le_mul_of_pos_right _ hZ1
    nlinarith
  have hO3 : (12 * D + 8) * (odK Fg D KG + κO) ≤
      (12 * D + 8) * (((2 * D + 3) * 500016 + 166500 + 4 * κGD + κO) * Z) :=
    Nat.mul_le_mul_left _ hO2
  have hk1 : κO ≤ κO * Z := Nat.le_mul_of_pos_right _ hZ1
  have hk2 : κK ≤ κK * Z := Nat.le_mul_of_pos_right _ hZ1
  unfold iterK iterA
  nlinarith

/-- **The cost of the run steps.** -/
theorem run_cost {D Fg L T K' n κWD κGD κO κK κP κSD κS0D Z KG : ℕ} (hZ : Z = Fg + L + 1)
    (hT : T ≤ L + 3) (hK : 1 ≤ K') (hn : n + 1 ≤ 10 * K') (hKG : KG = κGD * (Fg + T + 1)) :
    κP * K' + (κSD * K' * Z + (κS0D * (T + 1) +
      ((iterK (κWD * (T + 1)) κK κO Fg D KG + 2) * (n + 1) + 2))) ≤
      runA D κWD κGD κO κK κP κSD κS0D * K' * Z := by
  have hZ1 : 1 ≤ Z := ⋄
  have hit := iterK_le (Fg := Fg) (D := D) (T := T) (L := L) (KG := KG) (κWD := κWD) (κGD := κGD)
    (κO := κO) (κK := κK) (Z := Z) hZ hT hKG
  set A := iterA D κWD κGD κO κK with hA
  set I := iterK (κWD * (T + 1)) κK κO Fg D KG with hI
  have hKZ : 1 ≤ K' * Z := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (⋄) (⋄))
  have h1 : (I + 2) * (n + 1) ≤ (A * Z + 2) * (10 * K') :=
    Nat.mul_le_mul (⋄) hn
  have h2 : (A * Z + 2) * (10 * K') + 2 ≤ (10 * A + 22) * (K' * Z) := ⊞
  have h3 : κS0D * (T + 1) ≤ 4 * κS0D * (K' * Z) := by
    have : T + 1 ≤ 4 * (K' * Z) := ⊞
    nlinarith
  have h4 : κP * K' ≤ κP * (K' * Z) := Nat.mul_le_mul_left _ (⊞)
  unfold runA
  Ξ ← hA
  nlinarith

end

end SweepEv

end Chazelle.Core
