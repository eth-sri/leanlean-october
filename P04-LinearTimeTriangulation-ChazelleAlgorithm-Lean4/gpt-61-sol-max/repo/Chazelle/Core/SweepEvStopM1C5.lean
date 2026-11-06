module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopM1C4
public import Chazelle.Core.SweepEvGen

/-!
# The sweep (WP-D), stage 2: the candidate of `C₁` of a stop origin (`M1Task`)

**`m1Task : M1Task`**: the program `m1cP br` (`br` the brute-force shot of `bruteTask`), cost
constant `κ D = κGen D + κB + 60000`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

theorem m1c_lhRunK_le (T Fg D : ℕ) : lhRunK T Fg D ≤ κGen D * (Fg + T + 1) := by
  have := genK_le Fg D T
  core_grind [genK]

set_option maxRecDepth 20000 in
/-- **Task M1: the candidate of `C₁`** of a stop origin. -/
theorem m1Task : M1Task := by
  obtain ⟨br, κB, hBr⟩ := stbBody_of bruteTask
  refine ⟨m1cP br, fun D => κGen D + κB + 60000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hD hpos hroom
  beta_reduce at hroom ⊢
  have hkd : c.nreg oKd ≤ 2 := hD.ok.1
  have hK := E.hK.fix hI
  obtain ⟨M, hMd⟩ : ∃ M, M = (if c.nreg oKd = 1 then 1 else N₁.nChords + N₂.nChords + 1) :=
    ⟨_, rfl⟩
  rw [← hMd] at hroom ⊢
  have hM1 : 1 ≤ M := by grind
  have hLK := m1c_lhRunK_le (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))
  set Q := F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1 with hQ
  set G := κGen (c₀.nreg (sw 6)) with hG
  
  have hMQ : 1 ≤ M * Q := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (G + κB + 60000) * M * Q = G * M * Q + κB * M * Q + 60000 * (M * Q) := by ring
  have hp2 : G * Q ≤ G * M * Q := by
    rw [show G * M * Q = M * (G * Q) by ring]; exact Nat.le_mul_of_pos_left _ (by omega)
  set B := (G + κB + 60000) * M * Q with hB
  unfold m1cP
  refine (IRS.ite (K := B - 2) (fun h0 => ?_) (fun h0 => ?_)).mono (by omega) (fun _ h => h)
  · rw [hK.2.1] at h0
    exact m1cK0_irs E hI hD (by omega) (by omega) (by omega)
  · rw [hK.2.1] at h0
    refine (IRS.ite (K := B - 4) (fun h1 => ?_) (fun h1 => ?_)).mono (by omega) (fun _ h => h)
    · rw [hK.2.2.2.2.2.1] at h1
      exact m1cK1_irs E hI hD hpos (by omega) (by omega) (by omega)
    · rw [hK.2.2.2.2.2.1] at h1
      have hk2 : c.nreg oKd = 2 := by omega
      have hMe : M = N₁.nChords + N₂.nChords + 1 := by grind
      have hp1 : κB * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ κB * M * Q :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      exact m1cK2_irs hBr E hI hD hk2 (by omega) (by omega)

end

end SweepEv

end Chazelle.Core
