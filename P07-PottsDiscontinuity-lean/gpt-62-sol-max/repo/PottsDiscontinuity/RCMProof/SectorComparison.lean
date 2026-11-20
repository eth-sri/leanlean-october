module

public import PottsDiscontinuity.Torus.Corollary313Final
public import PottsDiscontinuity.TorusLoops.LoopDensityExpectation
public import PottsDiscontinuity.TorusRC.ElementaryTail
public import PottsDiscontinuity.TorusTopology.UnitWindingContract
public import PottsDiscontinuity.SixVertex.Sec33Ratios

@[expose] public section

namespace PottsDiscontinuity.RCMProof

open Finset Torus TorusRC TorusLoops SixVertex
open scoped Classical

noncomputable section

variable {N M : ℕ} (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
  (q : Set.Ici (1 : ℝ))

local notation "c₀" => Real.sqrt (2 + Real.sqrt q.val)
local notation "D" => windingLoopDensityWeight hN hM hNp hMp q
local notation "Z" => torusRCPartition hN hM q
local notation "w" => torusRCWeight hN hM q
local notation "e" => phi_T_windingLoopDensityExpectation hN hM hNp hMp q
local notation "C" => torusNormalization q N M
local notation "P" => torusRCProbability hN hM q
local notation "U" => rcVerticalWinding hN hM (Fin.mk 0 hMp)
local notation "W" => torusCorrectedRCWeight hN hM (Fin.mk 0 hNp) (Fin.mk 0 hMp) q

private theorem corrected_weight (A : RCConfig N M) : W A = w A * D A := by
  unfold torusCorrectedRCWeight windingLoopDensityWeight windingLoopDensityBase
  ring

private theorem probability_mul_partition (E : Set (RCConfig N M)) :
    P E * Z = ∑ A : E, w A.val := by
  rw [torusRCProbability_eq_sum]
  simp only [Set.indicator_apply, ← sum_filter, sum_mul]
  rw [← sum_subtype (p := (· ∈ E)) (univ.filter (· ∈ E)) (by simp)]
  apply sum_congr rfl
  intro A _
  exact div_mul_cancel₀ _ (torusRCPartition_pos hN hM q).ne'

private theorem densityWeight_le_one (hq : 4 < q.val) (A : RCConfig N M) : D A ≤ 1 := by
  have hq0 : 0 < q.val := zero_lt_one.trans_le q.property
  have hs : 2 < Real.sqrt q.val := (Real.lt_sqrt (by norm_num)).2 (by grind)
  exact (div_le_one (by positivity)).2
    ((pow_le_one₀ (by positivity) ((div_le_one (by positivity)).2 hs.le)).trans
      (one_le_pow₀ q.property))

private theorem densityWeight_exactOne (A : RCConfig N M) (h : U A = 1) :
    4 / q.val ^ 2 ≤ D A := by
  have hq0 : 0 < q.val := zero_lt_one.trans_le q.property
  unfold windingLoopDensityWeight windingLoopDensityBase
  rw [TorusTopology.windingLoopCount_eq_two_of_U_eq_one hN hM (Fin.mk 0 hNp) (Fin.mk 0 hMp) A h,
    div_pow, Real.sq_sqrt (by positivity : 0 ≤ q.val)]
  rw [div_div, show (2 : ℝ) ^ 2 = 4 by norm_num]
  gcongr
  rw [pow_two]
  gcongr
  simpa using pow_le_pow_right₀ q.property (rcNetIndicator_le_one hN hM A)

private theorem expectation_mul_partition (hq : 4 < q.val) : e * Z = C * Z6V c₀ N M := by
  unfold phi_T_windingLoopDensityExpectation
  rw [sum_mul, ← corollary_313_i_final hN hM q hq (Fin.mk 0 hNp) (Fin.mk 0 hMp)]
  apply sum_congr rfl
  intro A _
  rw [corrected_weight, torusRCMass, mul_right_comm, div_mul_cancel₀ _ (torusRCPartition_pos hN hM q).ne']

private theorem expectation_le_one (hq : 4 < q.val) : e ≤ 1 := by
  rw [← sum_torusRCMass hN hM q]
  exact sum_le_sum fun A _ => mul_le_of_le_one_right (torusRCMass_pos hN hM q A).le
    (densityWeight_le_one hN hM hNp hMp q hq A)

include hNp in
theorem exactOneProbability_le_sector_ratio (hq : 4 < q.val) :
    P {A | U A = 1} ≤ q.val ^ 2 * (Z6Vr c₀ N M 1 / Z6V c₀ N M) := by
  have hZ := torusRCPartition_pos hN hM q
  have hV := Z6V_pos (c := c₀) (by positivity) hNp hMp
  let B := {A | U A = 1}
  have h₁ : (4 / q.val ^ 2) * (P B * Z) ≤ 4 * C * Z6Vr c₀ N M 1 := by
    rw [probability_mul_partition, mul_sum]
    refine (sum_le_sum (g := fun A : B => W A.val) fun A _ => ?_).trans ?_
    · rw [corrected_weight, mul_comm (4 / q.val ^ 2)]
      exact mul_le_mul_of_nonneg_left (densityWeight_exactOne hN hM hNp hMp q A
        A.property) (torusRCWeight_pos hN hM q A).le
    · convert corollary_313_ii_final hN hM q hq (Fin.mk 0 hNp) (Fin.mk 0 hMp) using 1
      exact sum_congr (by ext; simp) fun _ _ => rfl
  have h₂ : C * Z6V c₀ N M ≤ Z := by
    rw [← expectation_mul_partition hN hM hNp hMp q hq]
    exact mul_le_of_le_one_left hZ.le (expectation_le_one hN hM hNp hMp q hq)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hV).2
  have h₃ : P B * Z ≤ q.val ^ 2 * (C * Z6Vr c₀ N M 1) := by
    apply (mul_le_mul_iff_of_pos_left (show (0 : ℝ) < 4 / q.val ^ 2 by positivity)).mp
    convert h₁ using 1
    field_simp
  have h₄ := (mul_le_mul_of_nonneg_left h₂ (torusRCProbability_nonneg hN hM q B)).trans h₃
  apply (mul_le_mul_iff_left₀ (torusNormalization_pos q N M)).mp
  convert h₄ using 1 <;> ring

theorem sector_ratio_mul_expectation_le_tail (hq : 4 < q.val) {k r : ℕ} (hkr : k ≤ r) :
    (Z6Vr c₀ N M r / Z6V c₀ N M) * e ≤ P (torusRCVerticalTail hN hM (Fin.mk 0 hMp) k) := by
  have hZ := torusRCPartition_pos hN hM q
  have hV := Z6V_pos (c := c₀) (by positivity) hNp hMp
  apply (mul_le_mul_iff_of_pos_right hZ).mp
  rw [mul_assoc, expectation_mul_partition hN hM hNp hMp q hq]
  have he : (Z6Vr c₀ N M r / Z6V c₀ N M) * (C * Z6V c₀ N M) = C * Z6Vr c₀ N M r := by
    field_simp
  rw [he]
  let B := {A | r ≤ U A}
  have h : C * Z6Vr c₀ N M r ≤ P B * Z := by
    rw [probability_mul_partition]
    refine (corollary_313_iii_final hN hM q hq (Fin.mk 0 hNp) (Fin.mk 0 hMp) r).trans ?_
    calc
      _ = ∑ A : B, W A.val := sum_congr (by ext; simp) fun _ _ => rfl
      _ ≤ ∑ A : B, w A.val := sum_le_sum fun (A : B) _ => (corrected_weight hN hM hNp hMp q A).le.trans
        (mul_le_of_le_one_right (torusRCWeight_pos hN hM q A).le
          (densityWeight_le_one hN hM hNp hMp q hq A))
      _ = _ := sum_congr (by ext; simp) fun _ _ => rfl
  exact h.trans (mul_le_mul_of_nonneg_right (torusRCProbability_mono hN hM q
    fun A (ha : r ≤ U A) => hkr.trans ha) hZ.le)

end
end PottsDiscontinuity.RCMProof
