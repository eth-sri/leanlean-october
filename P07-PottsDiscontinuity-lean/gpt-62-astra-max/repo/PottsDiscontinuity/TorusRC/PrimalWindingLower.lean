module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PottsDiscontinuity.TorusRC.BlockGeometry
public import PottsDiscontinuity.TorusRC.WindingEnergy

/-! # The source event-A lower bound from h319 and finite energy -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ))
include q

/-- A uniform surgery factor covering both openings and closings. Its square
allows one complete block to be reserved for the seam-free terminal surgery. -/
noncomputable def torusRCSurgeryEnergy : ℝ :=
  (min (1-(rcCriticalParameter q).val) (fkOpenEnergy (torusRCBridgeParameters q))) ^ 2

theorem torusRCSurgeryEnergy_pos : 0 < torusRCSurgeryEnergy q :=
  pow_pos (lt_min (sub_pos.mpr (criticalParameter_lt_one q)) (fkOpenEnergy_pos _)) _

theorem torusRCSurgeryEnergy_le_one : torusRCSurgeryEnergy q ≤ 1 := by
  apply pow_le_one₀
  · exact (lt_min (sub_pos.mpr (criticalParameter_lt_one q)) (fkOpenEnergy_pos _)).le
  · grind

include hN4 hM4 in
/-- Finite-energy completion with k=floor(M/(2n))-1. Reserving the final
complete block guarantees that the chain itself never uses the seam. -/
theorem primalWinding_probability_ge_double (n : ℕ) (hn : 0 < n) (h4n : 4*n ≤ M)
    (i : Fin (3*n+1)) (hi : Even (i.val : ℤ)) :
    torusRCSurgeryEnergy q ^ (2*n+N) *
      torusRCProbability hN hM q (rectangleDoubleConnection hNp hMp i) ^
        (M/(2*n)-1) ≤
      torusRCProbability hN hM q (primalWindingSingleSeam hNp hMp hM (3*n+1)) := by
  let k := M/(2*n)-1
  have hdiv : 2 ≤ M/(2*n) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hk : k+1 = M/(2*n) := by omega
  have hmod := Nat.mod_lt M (show 0 < 2*n by omega)
  have hsplit := Nat.mod_add_div M (2*n)
  rw [← hk,Nat.mul_add,Nat.mul_one] at hsplit
  let d := min (1-(rcCriticalParameter q).val) (fkOpenEnergy (torusRCBridgeParameters q))
  have hd0 : 0 ≤ d :=
    (lt_min (sub_pos.mpr (criticalParameter_lt_one q)) (fkOpenEnergy_pos _)).le
  have hc0 := (sub_pos.mpr (criticalParameter_lt_one q)).le
  have ho0 := (fkOpenEnergy_pos (torusRCBridgeParameters q)).le
  have hfac : torusRCSurgeryEnergy q ^ (2*n+N) ≤
      (1-(rcCriticalParameter q).val)^N *
        fkOpenEnergy (torusRCBridgeParameters q)^(M-2*n*k) := by
    change (d^2)^(2*n+N) ≤ _
    rw [← pow_mul]
    apply (pow_le_pow_of_le_one hd0 ((min_le_right _ _).trans (fkOpenEnergy_le_one _)) (show N+(M-2*n*k) ≤ 2*(2*n+N) by omega)).trans
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hd0 (min_le_left _ _) N)
      (pow_le_pow_left₀ hd0 (min_le_right _ _) _)
      (pow_nonneg hd0 _) (pow_nonneg hc0 N)
  have hmul := mul_le_mul hfac (boundedRectangleChain_probability_ge hN hM hNp hMp q n i hi k)
    (pow_nonneg (torusRCProbability_nonneg hN hM q _) _)
    (by positivity)
  exact hmul.trans (primalWinding_probability_ge_boundedChain hN hM hN4 hM4
    hNp hMp q n i hi k (by omega))

end

/-- The event-A estimate with a real M/n exponent, with h319 as its only
unproved premise. The strip is enlarged by one lattice unit for the explicit
terminal zigzag; this is absorbed by a one-unit margin in the barrier strip. -/
theorem primal_winding_lower_of_h319 (q : Set.Ici 1) (hh319 : h319 q) :
    ∃ c, 0 < c ∧ c ≤ 1 ∧ ∀ N M n hN hM
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hn : 0 < n)
      (h3nN : 3*n ≤ N) (h4nM : 4*n ≤ M),
      let hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      torusRCSurgeryEnergy q ^ (2*n+N) *
        (c/(9*n^2)) ^ (M/(n:ℝ)) ≤
        torusRCProbability hN hM q (primalWindingSingleSeam hNp hMp hM (3*n+1)) := by
  obtain ⟨c₀,hc₀,hdouble⟩ := double_connection_of_h319 q hh319
  let c := min c₀ 1
  refine ⟨c,(lt_min hc₀ zero_lt_one),min_le_right _ _,?_⟩
  intro N M n hN hM hN4 hM4 hn h3nN h4nM
  let hNp : 0 < N := by omega
  let hMp : 0 < M := by omega
  obtain ⟨i,hp⟩ := hdouble N M n hN hM hN4 hM4 hn h3nN (by omega)
  have hbase : 0 < c/(9*n^2) := by positivity
  have hp' :=
    (pow_le_pow_left₀ hbase.le
      (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) 2).trans hp
  let k := M/(2*n)-1
  have hk :=
    (Nat.mul_le_mul_left (2*n) (show k ≤ M/(2*n) from Nat.sub_le _ _)).trans
      (by simpa [Nat.mul_comm] using Nat.div_mul_le_self M _)
  have hkR : (2*k:ℕ) ≤ M/(n:ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h : (2:ℝ)*n*k ≤ M := by exact_mod_cast hk
    push_cast
    nlinarith
  have hrpow := Real.rpow_le_rpow_of_exponent_ge hbase (by
    have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    apply (div_le_one (by positivity)).mpr
    have hc1 : c ≤ 1 := min_le_right _ _
    nlinarith) hkR
  rw [Real.rpow_natCast] at hrpow
  have hpow := pow_le_pow_left₀ (sq_nonneg _) hp' k
  rw [← pow_mul] at hpow
  have hconn := primalWinding_probability_ge_double hN hM hN4 hM4 hNp hMp q n hn h4nM i (rectangleDoubleConnection_endpoint_even hNp hMp n i ((torusRCProbability_pos_iff hN hM q _).mp ((pow_pos hbase 2).trans_le hp')))
  exact (mul_le_mul_of_nonneg_left (hrpow.trans hpow)
    (pow_nonneg (torusRCSurgeryEnergy_pos q).le _)).trans hconn

end PottsDiscontinuity.TorusRC
