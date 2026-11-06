module

public import Chazelle.Core.SweepIoCand0
public import Chazelle.Core.SweepIoS0MathMain
public import Chazelle.UnfoldTactics

/-!
# The sweep RAM (WP-D), answers: `Cand0Spec`

* `cand0Spec (hM : Side0MathSpec) (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec`: the
  initialisation and `Aux` of `S0CandSpec`, the per-query procedure `cand0 lab0 candC`
  (`cand0_irs`), the cost constant `κ0 κL κS`;
* `cand0Spec_of (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec` (with `side0Math`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

/-- The cost constant of the candidate step of side `0`. -/
def κ0 (κL κS : ℕ → ℕ) (D : ℕ) : ℕ :=
  3 * (8 + localK 0 0 (D + 1) D + 5500 + 16 * (3 * (D + 1) + 1)) + κL D + κS D + 62750

theorem localK_lin' (T Fg Da Dc : ℕ) :
    localK T Fg Da Dc = localK 0 0 Da Dc + 5500 * T + (3 * Da + 1) * (16 * Fg) := by
  unfold localK lh1K shotOfferK ShotList.shotCost
  ring

/-- **The cost bound.** -/
theorem kc0_le (κL κS : ℕ → ℕ) (c₀ : Config) (F : ℕ → ℕ) :
    Kc0 κL κS c₀ F ≤ κ0 κL κS (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) := by
  unfold Kc0 Kcls Kbr Kmain Klh lhsK κ0
  rw [localK_lin']
  set D := c₀.nreg (sw 6)
  set Fg := F (c₀.nreg (sw 5))
  set T := c₀.nreg TLR
  have e : (3 * (D + 1) + 1) * (16 * Fg) = (16 * (3 * (D + 1) + 1)) * Fg := by ring
  rw [e]
  set A := localK 0 0 (D + 1) D
  set B := 16 * (3 * (D + 1) + 1)
  set a := κL D
  set b := κS D
  have h1 : (8 + A) ≤ (8 + A) * (Fg + T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : 5500 * T ≤ 5500 * (Fg + T + 1) := Nat.mul_le_mul_left _ (by omega)
  have h3 : B * Fg ≤ B * (Fg + T + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : b * (T + 1) ≤ b * (Fg + T + 1) := Nat.mul_le_mul_left _ (by omega)
  have h5 : 62750 ≤ 62750 * (Fg + T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (3 * (8 + A + 5500 + B) + a + b + 62750) * (Fg + T + 1) =
      3 * ((8 + A) * (Fg + T + 1)) + 3 * (5500 * (Fg + T + 1)) + 3 * (B * (Fg + T + 1)) +
        a * (Fg + T + 1) + b * (Fg + T + 1) + 62750 * (Fg + T + 1) := by ring
  rw [e2]
  omega

/-- A larger cost constant keeps an initialisation contract. -/
theorem initSpec_mono {init : Stmt} {Aux : Polygon → Merge.Junction → NF → Config → Prop}
    {κ κ' : ℕ → ℕ} (h : InitSpec init Aux κ) (hle : ∀ D, κ D ≤ κ' D) : InitSpec init Aux κ' := by
  refine ⟨fun P W X Ok J H N₁ N₂ E c hw hA hroom => ?_, h.2⟩
  have hk : κ (c.nreg (sw 6)) * (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) *
      (c.nreg TLR + 1) ≤
      κ' (c.nreg (sw 6)) * (rd c bSweep 201 + rd c bSweep 301 + 2 * N₂.nChords + 1) *
      (c.nreg TLR + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (hle _)) le_rfl
  obtain ⟨c', k, ex, hk', fr, hfix, haux⟩ := h.1 P W X Ok J H N₁ N₂ E c hw hA (by omega)
  exact ⟨c', k, ex, by omega, fr, hfix, haux⟩

/-- **The candidate step of side `0`.** -/
theorem cand0Spec (hM : Side0MathSpec) (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec := by
  obtain ⟨initC, candC, Aux, κS, hInit, hRob, hSC⟩ := s0CandSpec_iff.1 hS
  obtain ⟨lab0, κL, hLab⟩ := lab0Spec_iff.1 hL
  refine ⟨initC, cand0 lab0 candC, Aux, κ0 κL κS,
    initSpec_mono hInit (fun D => by ufo κ0), hRob, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E z hA hAux hI hQ h0 hroom
  have hk := kc0_le κL κS c₀ F
  exact (cand0_irs hM hLab hSC hsh hBs hXl hA hAux hI hQ h0 (by omega)).mono hk (fun _ => id)

/-- **The candidate step of side `0`**, with the mathematics of side `0` (`side0Math`). -/
theorem cand0Spec_of (hS : S0CandSpec) (hL : Lab0Spec) : Cand0Spec :=
  cand0Spec side0Math hS hL

end

end SweepIo

end Chazelle.Core
