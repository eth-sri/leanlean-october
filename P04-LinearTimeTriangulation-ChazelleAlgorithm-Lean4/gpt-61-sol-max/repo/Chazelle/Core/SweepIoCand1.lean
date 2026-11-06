module

public import Chazelle.Core.SweepIoCand1R
public import Chazelle.Core.SweepIoCand1Tab
public import Chazelle.Core.SweepIoCand1Shr
public import Chazelle.Core.SweepEvGen

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`

**`cand1Spec (hB : BruteSpec) : Cand1Spec`**: the program `cand1P tabB shrB bruteS` (the local hit
in the model of `C₂`, then the classes box wall / shared vertex / regular endpoint query /
brute force), from the table step (`tabStep`), the shared-vertex step (`shrStep`) and the
brute-force shot (`BruteSpec`).  Cost constant `κ D = 2 κGen D + κB + κT + κS + 30000`.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

/-- The cost of a local hit with its inputs is linear. -/
theorem lhsK_le (T Fg D : ℕ) : lhsK T Fg D ≤ SweepEv.κGen D * (Fg + T + 1) := by
  have := SweepEv.genK_le Fg D T
  unfold SweepEv.genK at this
  unfold lhsK
  omega

end Cand1

set_option maxRecDepth 200000 in
open Classical in
/-- **The candidate step of side `1`**, from the contracts of its parts. -/
theorem cand1Spec_of (hB : BruteSpec) (hT : TabStepSpec) (hS : ShrStepSpec) : Cand1Spec := by
  obtain ⟨bruteS, κB, hBr⟩ := Cand1.bruteBody_of hB
  obtain ⟨tabB, κT, hTb⟩ := Cand1.tabBody_of hT
  obtain ⟨shrB, κS, hSb⟩ := Cand1.shrBody_of hS
  refine ⟨Cand1.cand1P tabB shrB bruteS,
    fun D => 2 * SweepEv.κGen D + κB + κT + κS + 30000, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E z hA hI hq hend hacc0 hroom
  beta_reduce at hroom ⊢
  obtain ⟨KB, hKB⟩ : ∃ KB, KB = (if BruteQ J N₂ (c.nreg qJ) z then
      (2 * SweepEv.κGen (c₀.nreg (sw 6)) + κB + κT + κS + 30000) * (N₁.arcs.length + 1) *
        (F (c₀.nreg (sw 5)) + 1) else 0) := ⟨_, rfl⟩
  rw [← hKB] at hroom ⊢
  have hKB' : BruteQ J N₂ (c.nreg qJ) z →
      κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ KB := by
    intro h
    rw [hKB, ite_eq_left h]
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) le_rfl
  have hLK := Cand1.lhsK_le (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))
  have h1 : κB + κT + κS + 30000 ≤
      (κB + κT + κS + 30000) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e : (2 * SweepEv.κGen (c₀.nreg (sw 6)) + κB + κT + κS + 30000) *
      (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) =
      2 * (SweepEv.κGen (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) +
        (κB + κT + κS + 30000) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) := by ring
  have hcost : Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) +
      (Cand1.kD κT κS (Cand1.lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB +
        11076) ≤
      (2 * SweepEv.κGen (c₀.nreg (sw 6)) + κB + κT + κS + 30000) *
        (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1) + KB := by
    unfold Cand1.kD; omega
  exact (Cand1.cand1P_irs hTb hSb hBr hsh hBs hXl hA hI hq hend hKB' hacc0
    (by omega)).mono hcost (fun _ h => h)

/-- **The candidate step of side `1`** (piece F). -/
theorem cand1Spec (hB : BruteSpec) : Cand1Spec := cand1Spec_of hB tabStep shrStep

end

end SweepIo

end Chazelle.Core
