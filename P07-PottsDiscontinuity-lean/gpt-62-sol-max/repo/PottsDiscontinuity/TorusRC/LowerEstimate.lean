module

public import PottsDiscontinuity.TorusRC.BarrierLower
public import PottsDiscontinuity.TorusRC.TopologyBounds

/-! # The complete finite-volume lower estimate for U=1 -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

noncomputable section

abbrev torusRCUOneProbability {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hMp : 0 < M) : ℝ :=
  torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1}

abbrev nativeDiagonalProbability (q : Set.Ici (1 : ℝ)) (R n : ℕ) : ℝ :=
  liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin R
    rotatedLatticeOrigin (rotatedDiagonalSite n)

/-- Height-independent cost of the primal and dual surgeries. The barrier uses
`n` for its block size; the primal chain uses `n+1` to leave room for the terminal zigzag. -/
def surgeryCost (q : Set.Ici (1 : ℝ)) (N n : ℕ) : ℝ :=
  fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (N/4 + 2*(n+1))) *
    torusRCSurgeryEnergy q ^ (2*n+N) / q.val^2

theorem surgeryCost_pos (q : Set.Ici (1 : ℝ)) (N n : ℕ) : 0 < surgeryCost q N n :=
  div_pos (mul_pos (pow_pos (fkOpenEnergy_pos _) _) (pow_pos (torusRCSurgeryEnergy_pos _) _))
    (pow_pos (zero_lt_one.trans_le q.property) _)

theorem torusRCU_one_lower_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (_ : 8 ∣ N) (_ : 0 < n) (_ : 8*(n+1) ≤ N) (_ : 4*(n+1) ≤ M) (_ : N/2 < M),
      surgeryCost q N n * blockPenalty c n ^ ((M : ℝ) / n) *
        nativeDiagonalProbability q (N/4) (n+1) ^ (M/(2*(n+1))) ≤
      torusRCUOneProbability hN hM q (by omega) := by
  obtain ⟨c, hc, hB⟩ := barrier_lower_of_h319 q hh319
  refine ⟨c, hc, fun N M n hN hM hdiv hn hwidth hheight hNM => ?_⟩
  have h := torusRCU_one_probability_ge_chain hN hM (by omega) (by omega) (by omega)
    (by omega) hdiv q (n+1) (by omega) hwidth hNM
  have hb := hB N M n hN hM (by omega) (by omega) hn (by omega) (by omega)
  have hnneg := liftedBoxFreeConnectionProbability_nonneg (torusRCBridgeParameters q)
    rotatedLatticeOrigin (N/4) rotatedLatticeOrigin (rotatedDiagonalSite (n+1))
  convert (mul_le_mul_of_nonneg_left hb (mul_nonneg
    (pow_nonneg (fkOpenEnergy_pos (torusRCBridgeParameters q)).le (2 * (N/4 + 2*(n+1))))
    (pow_nonneg hnneg _))).trans h using 1
  simp only [surgeryCost, nativeDiagonalProbability]
  ring

end
end PottsDiscontinuity.TorusRC
