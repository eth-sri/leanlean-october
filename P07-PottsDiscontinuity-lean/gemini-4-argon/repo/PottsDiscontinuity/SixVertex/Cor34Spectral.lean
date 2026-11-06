module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Continuity
public import PottsDiscontinuity.SixVertex.BlockPerronFrobenius
public import PottsDiscontinuity.SixVertex.InfinityLimit

@[expose] public section

open Filter Matrix Set
open scoped Topology
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

private theorem cor34_transferBlock_sqrt_entry {N n : ℕ} (x y : State N n) {Δ : ℝ}
    (hΔ : Δ < 1) :
    transferBlock N (Real.sqrt (2 - 2 * Δ)) n x y =
      if x = y then 2 else
        if Interlaced x.1 y.1 then (2 - 2 * Δ) ^ (x.1 \ y.1).card else 0 := by
  classical
  rw [transferBlock_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    by_cases hi : Interlaced x.1 y.1
    · have hcard : (Finset.univ.filter fun i => Psi x.1 i ≠ Psi y.1 i).card =
          2 * (x.1 \ y.1).card := by
        simpa [arrowDistance] using arrowDistance_state x y
      simp [hxy, hval, hi, hcard, pow_mul, Real.sq_sqrt (by linarith : 0 ≤ 2 - 2 * Δ)]
    · simp [hxy, hval, hi]

private theorem cor34_transferBlock_entry_analyticAt {N n : ℕ} (x y : State N n)
    {Δ : ℝ} (hΔ : Δ < -1) :
    AnalyticAt ℝ (fun d => transferBlock N (Real.sqrt (2 - 2 * d)) n x y) Δ := by
  classical
  let P : ℝ → ℝ := fun d =>
    if x = y then 2 else
      if Interlaced x.1 y.1 then (2 - 2 * d) ^ (x.1 \ y.1).card else 0
  have hP : AnalyticAt ℝ P Δ := by
    by_cases hxy : x = y
    · simpa [P, hxy] using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (2 : ℝ)) Δ)
    · by_cases hi : Interlaced x.1 y.1
      · simpa [P, hxy, hi] using
          (by fun_prop : AnalyticAt ℝ (fun d : ℝ => (2 - 2 * d) ^ (x.1 \ y.1).card) Δ)
      · simpa [P, hxy, hi] using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) Δ)
  refine hP.congr ?_
  filter_upwards [Iio_mem_nhds (by linarith : Δ < 1)] with d hd
  exact (cor34_transferBlock_sqrt_entry x y hd).symm

theorem cor34_transferBlock_pfRoot_simple {N n : ℕ} (hn : n ≤ N) {Δ : ℝ}
    (hΔ : Δ < -1) :
    (transferBlock N (Real.sqrt (2 - 2 * Δ)) n).charpoly.rootMultiplicity
      (pfRoot (transferBlock N (Real.sqrt (2 - 2 * Δ)) n)) = 1 :=
  (transferBlock_perronFrobenius (Real.sqrt_pos.2 (by linarith)) hn).2.2.2.2.1

theorem cor34_analyticAt_pfRoot_transferBlock {N n : ℕ} (hn : n ≤ N) {Δ : ℝ}
    (hΔ : Δ < -1) :
    AnalyticAt ℝ (fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)) Δ := by
  classical
  have : Nonempty (State N n) := ⟨packed hn⟩
  simpa [pfRoot] using AnalyticTools.analyticAt_pfRoot_of_simple
    (fun i j => cor34_transferBlock_entry_analyticAt i j hΔ)
    (transferBlock_isHermitian n)
    (Filter.Eventually.of_forall fun _ => transferBlock_isHermitian n)
    (by simpa [pfRoot] using cor34_transferBlock_pfRoot_simple hn hΔ)

noncomputable def cor34_normalizedTransferBlock (N n : ℕ) (ε : ℝ) :
    Matrix (State N n) (State N n) ℝ :=
  fun x y =>
    if x = y then 2 * (-ε / 2) ^ n
    else if Interlaced x.1 y.1 then
      (-ε / 2) ^ (n - (x.1 \ y.1).card) * (1 - ε) ^ (x.1 \ y.1).card
    else 0

private theorem cor34_state_sdiff_le {N n : ℕ} (x y : State N n) :
    (x.1 \ y.1).card ≤ n :=
  (Finset.card_le_card Finset.sdiff_subset).trans_eq x.2

theorem cor34_normalizedTransferBlock_zero (N n : ℕ) :
    cor34_normalizedTransferBlock N n 0 = infinityBlock N n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y; by_cases hn0 : n = 0 <;> simp [cor34_normalizedTransferBlock, infinityBlock, hn0]
  · by_cases hi : Interlaced x.1 y.1
    · let m := (x.1 \ y.1).card
      have hmle : m ≤ n := cor34_state_sdiff_le x y
      have hdis : m = n ↔ Disjoint x.1 y.1 := by
        rw [← arrowDistance_eq_two_mul_iff, arrowDistance_state]
        dsimp [m]; omega
      by_cases hd : Disjoint x.1 y.1
      · simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi, hd, m, hdis.mpr hd]
      · have hexp : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hmle (mt hdis.mp hd))
        simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi, hd, m, hexp]
    · simp [cor34_normalizedTransferBlock, infinityBlock, hxy, hi]

theorem cor34_normalizedTransferBlock_entry_analyticAt {N n : ℕ} (x y : State N n)
    (ε : ℝ) :
    AnalyticAt ℝ (fun t => cor34_normalizedTransferBlock N n t x y) ε := by
  classical
  by_cases hxy : x = y
  · simp [cor34_normalizedTransferBlock, hxy]; fun_prop
  · by_cases hi : Interlaced x.1 y.1
    · simp [cor34_normalizedTransferBlock, hxy, hi]; fun_prop
    · simpa [cor34_normalizedTransferBlock, hxy, hi] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (0 : ℝ)) ε)

theorem cor34_normalizedTransferBlock_isHermitian {N n : ℕ} (ε : ℝ) :
    (cor34_normalizedTransferBlock N n ε).IsHermitian := by
  classical
  rw [Matrix.isHermitian_iff_isSymm]
  ext x y
  by_cases hxy : y = x
  · subst y; rfl
  · simp [cor34_normalizedTransferBlock, hxy, Ne.symm hxy, interlaced_comm,
      Finset.card_sdiff_comm (y.2.trans x.2.symm)]

private theorem cor34_normalized_power_identity {n m : ℕ} (hm : m ≤ n)
    {ε : ℝ} (hε : ε < 0) :
    (-ε / 2) ^ (n - m) * (1 - ε) ^ m =
      ((-2 / ε : ℝ) ^ n)⁻¹ * (2 - 2 / ε) ^ m := by
  let q : ℝ := -2 / ε
  have hεne : ε ≠ 0 := hε.ne
  have hq : q ≠ 0 := div_ne_zero (by norm_num) hεne
  have hqinv : -ε / 2 = q⁻¹ := by dsimp [q]; field_simp [hεne]
  have hbase : 2 - 2 / ε = q * (1 - ε) := by dsimp [q]; field_simp [hεne]; ring
  have hqpow : q ^ n = q ^ m * q ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  rw [hqinv, inv_pow, hbase, mul_pow]
  change (q ^ (n - m))⁻¹ * (1 - ε) ^ m = (q ^ n)⁻¹ * (q ^ m * (1 - ε) ^ m)
  rw [hqpow]
  field_simp [hq]

theorem cor34_normalizedTransferBlock_eq_scaled_transferBlock {N n : ℕ} (ε : ℝ)
    (hε : ε < 0) :
    cor34_normalizedTransferBlock N n ε =
      ((-2 / ε : ℝ) ^ n)⁻¹ •
        transferBlock N (Real.sqrt (2 - 2 / ε)) n := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    have hqpow : ((-2 / ε : ℝ) ^ n)⁻¹ = (-ε / 2) ^ n := by
      rw [← inv_pow, show (-2 / ε : ℝ)⁻¹ = -ε / 2 by field_simp [hε.ne]]
    simp [cor34_normalizedTransferBlock, Matrix.smul_apply, smul_eq_mul,
      transferBlock_apply_self, hqpow]
    ring
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    by_cases hi : Interlaced x.1 y.1
    · have hdelta : 1 / ε < 1 := lt_trans (one_div_neg.mpr hε) zero_lt_one
      have hraw : transferBlock N (Real.sqrt (2 - 2 / ε)) n x y =
          (2 - 2 / ε) ^ (x.1 \ y.1).card := by
        simpa [div_eq_mul_inv, hxy, hval, hi] using cor34_transferBlock_sqrt_entry x y hdelta
      simp only [cor34_normalizedTransferBlock, hxy, hi, Matrix.smul_apply, smul_eq_mul, hraw]
      exact cor34_normalized_power_identity (cor34_state_sdiff_le x y) hε
    · simp [cor34_normalizedTransferBlock, hxy, hval, hi, Matrix.smul_apply,
        transferBlock_apply, transferMatrix_apply]

theorem cor34_pfRoot_normalizedTransferBlock_eq {N n : ℕ} (hn : n ≤ N)
    {ε : ℝ} (hε : ε < 0) :
    pfRoot (cor34_normalizedTransferBlock N n ε) =
      pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n := by
  classical
  have : Nonempty (State N n) := ⟨packed hn⟩
  have hbase : 0 < (-2 / ε : ℝ) := div_pos_of_neg_of_neg (by norm_num) hε
  have hq : 0 ≤ ((-2 / ε : ℝ) ^ n)⁻¹ := (inv_pos.mpr (pow_pos hbase n)).le
  have hA : (transferBlock N (Real.sqrt (2 - 2 / ε)) n).IsHermitian := transferBlock_isHermitian n
  have hspec : (spectrum ℝ (transferBlock N (Real.sqrt (2 - 2 / ε)) n)).Nonempty := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.range_nonempty _
  rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
  change sSup (spectrum ℝ (((-2 / ε : ℝ) ^ n)⁻¹ • _)) = _
  rw [spectrum.smul_eq_smul _ _ hspec, Real.sSup_smul_of_nonneg hq, smul_eq_mul,
    div_eq_mul_inv, mul_comm]
  rfl

end PottsDiscontinuity.SixVertex
