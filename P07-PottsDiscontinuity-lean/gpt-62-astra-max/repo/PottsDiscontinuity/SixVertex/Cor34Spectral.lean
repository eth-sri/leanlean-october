module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Continuity
public import PottsDiscontinuity.SixVertex.BlockPerronFrobenius
public import PottsDiscontinuity.SixVertex.InfinityLimit

/-!
# Corollary 3.4: analytic spectral family

This file proves the analyticity of the concrete Perron root on the finite-anisotropy range and
records the normalized matrix family at infinite anisotropy.
-/

@[expose] public section

open Filter Matrix Set
open scoped Topology
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ} (ε : ℝ) (x y : State N n) (hn : n ≤ N) {Δ : ℝ} (hΔ : Δ < -1)

private theorem cor34_transferBlock_sqrt_entry
    (hΔ : Δ < 1) :
    transferBlock N (Real.sqrt (2 - 2 * Δ)) n x y =
      if x = y then 2 else
        if Interlaced x.1 y.1 then (2 - 2 * Δ) ^ (x.1 \ y.1).card else 0 := by
  classical
  rw [transferBlock_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · grind
  · have hval : x.1 ≠ y.1 := by grind
    simp [hxy, hval]
    by_cases hi : Interlaced x.1 y.1
    · have hcard : (Finset.univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card =
          2 * (x.1 \ y.1).card := arrowDistance_state x y
      rw [hcard, pow_mul, Real.sq_sqrt]
      · linarith
    · grind

include hΔ in
private theorem cor34_transferBlock_entry_analyticAt :
    AnalyticAt ℝ (fun d => transferBlock N (Real.sqrt (2 - 2 * d)) n x y) Δ := by
  classical
  let P : ℝ → ℝ := fun d =>
    if x = y then 2 else
      if Interlaced x.1 y.1 then (2 - 2 * d) ^ (x.1 \ y.1).card else 0
  have hP : AnalyticAt ℝ P Δ := by
    by_cases hxy : x = y
    · simpa [P, hxy] using
        analyticAt_const
    · by_cases hi : Interlaced x.1 y.1
      · have hlin : AnalyticAt ℝ (fun d : ℝ => 2 - 2 * d) Δ := by fun_prop
        have hpow : AnalyticAt ℝ
            (fun d : ℝ => (2 - 2 * d) ^ (x.1 \ y.1).card) Δ := by
          convert hlin.pow _ using 1
        grind
      · simpa [P, hxy, hi] using
          analyticAt_const
  have hEq :
      (fun d => transferBlock N (Real.sqrt (2 - 2 * d)) n x y) =ᶠ[𝓝 Δ] P := by
    filter_upwards [Iio_mem_nhds (show Δ < 1 by linarith)] with d hd
    exact cor34_transferBlock_sqrt_entry x y hd
  exact hP.congr hEq.symm

include hn hΔ in
/-- For every `n ≤ N` and `Δ < -1`, the Perron root of the transfer block is a simple
characteristic root. The proof uses primitivity of the block at `c = √(2 - 2Δ)`. -/
theorem cor34_transferBlock_pfRoot_simple :
    (transferBlock N (Real.sqrt (2 - 2 * Δ)) n).charpoly.rootMultiplicity
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * Δ)) n)) = 1 := by
  have hc : 0 < Real.sqrt (2 - 2 * Δ) := Real.sqrt_pos.2 (by linarith)
  obtain ⟨_, _, _, _, hsimple, _⟩ := transferBlock_perronFrobenius hc hn
  exact hsimple

include hn hΔ in
/-- The transfer-block Perron root is real-analytic at every `Δ < -1`, hence real-analytic on
the whole source interval `(-∞,-1)`. -/
theorem cor34_analyticAt_pfRoot_transferBlock :
    AnalyticAt ℝ (fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)) Δ := by
  classical
  have : Nonempty (State N n) := ⟨packed hn⟩
  let A := fun d =>
    transferBlock N (Real.sqrt (2 - 2 * d)) n
  have hHerm : ∀ d, (A d).IsHermitian := fun d => transferBlock_isHermitian n
  have hanalytic := AnalyticTools.analyticAt_pfRoot_of_simple (by
    solve_by_elim [cor34_transferBlock_entry_analyticAt]) (hHerm Δ)
    (Filter.Eventually.of_forall hHerm) (by exact cor34_transferBlock_pfRoot_simple hn hΔ)
  assumption

/-- Polynomial extension in ε = 1/Δ of the normalized transfer block. -/
noncomputable def cor34_normalizedTransferBlock (N n : ℕ) (ε : ℝ) :
    Matrix (State N n) (State N n) ℝ :=
  fun x y =>
    if x = y then 2 * (-ε / 2) ^ n
    else if Interlaced x.1 y.1 then
      (-ε / 2) ^ (n - (x.1 \ y.1).card) * (1 - ε) ^ (x.1 \ y.1).card
    else 0

private theorem cor34_state_sdiff_le :
    (x.1 \ y.1).card ≤ n :=
  (Finset.card_le_card Finset.sdiff_subset).trans_eq x.2

/-- The polynomial family has the infinity block as its value at zero. -/
theorem cor34_normalizedTransferBlock_zero (N n : ℕ) :
    cor34_normalizedTransferBlock N n 0 = infinityBlock N n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hn0 : n = 0 <;> simp [cor34_normalizedTransferBlock, infinityBlock, hn0]
  · by_cases hi : Interlaced x.1 y.1
    · let m := (x.1 \ y.1).card
      have hdis : m = n ↔ Disjoint x.1 y.1 := by
        constructor
        · intro hm
          apply (arrowDistance_eq_two_mul_iff x y).1
          have hmc : (x.1 \ y.1).card = n := by assumption
          rw [arrowDistance_state, hmc]
        · intro hd
          have h := (arrowDistance_eq_two_mul_iff x y).2 hd
          grind [arrowDistance_state]
      by_cases hd : Disjoint x.1 y.1
      · simp_all [cor34_normalizedTransferBlock, infinityBlock, m]
      · have hmn := lt_of_le_of_ne (cor34_state_sdiff_le x y) (by grind)
        have hexp := Nat.sub_ne_zero_of_lt hmn
        simp_all [cor34_normalizedTransferBlock, infinityBlock, m]
    · simp_all [cor34_normalizedTransferBlock, infinityBlock]

/-- Every matrix entry of the normalized family is analytic at every real ε. -/
theorem cor34_normalizedTransferBlock_entry_analyticAt
    (ε : ℝ) :
    AnalyticAt ℝ (fun t => cor34_normalizedTransferBlock N n t x y) ε := by
  classical
  by_cases hxy : x = y
  · simp [cor34_normalizedTransferBlock, hxy]
    fun_prop
  · by_cases hi : Interlaced x.1 y.1
    · simp [cor34_normalizedTransferBlock, hxy, hi]
      fun_prop
    · simpa [cor34_normalizedTransferBlock, hxy, hi] using
        analyticAt_const

/-- The normalized family is symmetric for every ε. -/
theorem cor34_normalizedTransferBlock_symm :
    cor34_normalizedTransferBlock N n ε x y =
      cor34_normalizedTransferBlock N n ε y x := by
  classical
  by_cases hxy : x = y <;> simp [cor34_normalizedTransferBlock, hxy, eq_comm, interlaced_comm, (Finset.card_sdiff_comm (x.2.trans y.2.symm))]

/-- The power identity for a normalized off diagonal transfer entry. -/
private theorem cor34_normalized_power_identity {n m : ℕ} (hm : m ≤ n)
    {ε : ℝ} (hε : ε < 0) :
    (-ε / 2) ^ (n - m) * (1 - ε) ^ m =
      ((-2 / ε) ^ n)⁻¹ * (2 - 2 / ε) ^ m := by
  let q := -2 / ε
  have hq : q ≠ 0 := by
    exact by grind
  have hbase : 2 - 2 / ε = q * (1 - ε) := by
    grind
  have hn : n = m + (n - m) := by omega
  have hqpow : q ^ n = q ^ m * q ^ (n - m) := by
    grind
  calc
    _ =
        (q⁻¹) ^ (n - m) * (1 - ε) ^ m := by grind
    _ = (q ^ (n - m))⁻¹ * (1 - ε) ^ m := by simp
    _ = (q ^ n)⁻¹ * (q ^ m * (1 - ε) ^ m) := by
      rw [hqpow]
      field_simp [hq]
    _ = (q ^ n)⁻¹ * (2 - 2 / ε) ^ m := by rw [← mul_pow, hbase]
    _ = _ := rfl

/-- For ε < 0, the polynomial matrix is exactly the transfer block divided by
(-2/ε)^n, that is, by (-2Δ)^n with Δ = 1/ε. -/
theorem cor34_normalizedTransferBlock_eq_scaled_transferBlock
    (hε : ε < 0) :
    cor34_normalizedTransferBlock N n ε =
      ((-2 / ε) ^ n)⁻¹ •
        transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    have hqinv : ((-2 / ε)⁻¹) = -ε / 2 := by
      grind
    have hqpow : ((-2 / ε) ^ n)⁻¹ = (-ε / 2) ^ n := by
      rw [← inv_pow, hqinv]
    simp [cor34_normalizedTransferBlock, Matrix.smul_apply, smul_eq_mul,
      transferBlock_apply_self, hqpow]
    ring
  · have hval : x.1 ≠ y.1 := by grind
    by_cases hi : Interlaced x.1 y.1
    · have hdelta : 1 / ε < 1 := by
        have hinv := one_div_neg.mpr hε
        linarith
      have hraw :
          transferBlock N (Real.sqrt (2 - 2 / ε)) n x y =
            (2 - 2 / ε) ^ ((x.1 \ y.1).card) := by
        grind [cor34_transferBlock_sqrt_entry]
      simp only [cor34_normalizedTransferBlock, hxy, hi, Matrix.smul_apply,
        smul_eq_mul]
      grind [cor34_normalized_power_identity]
    · simp_all [cor34_normalizedTransferBlock, Matrix.smul_apply, transferBlock_apply, transferMatrix_apply]

end PottsDiscontinuity.SixVertex
