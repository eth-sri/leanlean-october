module

public import NearlyMinimax.PoissonEnergyBounds

@[expose] public section

/-! The explicit fixed constant and factorial bookkeeping in the paper's
raw-energy lemma. All constants are chosen before the sample size. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable (CB C5 C6 C7 cf ch : ℝ)

def rawCostConstants : Fin 7 → ℝ :=
  ![1, C6, ch, 1 + CB ^ 2, 3 * (C5 + C7) * cf ^ 4,
    3 * C6 ^ 2 * cf ^ 4, Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2]

def rawCostConstant : ℝ :=
  Finset.univ.sup' (by simp) (rawCostConstants CB C5 C6 C7 cf ch)

theorem rawCostConstant_ge (i : Fin 7) :
    rawCostConstants CB C5 C6 C7 cf ch i ≤ rawCostConstant CB C5 C6 C7 cf ch :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem rawCostConstant_ge_one :
    1 ≤ rawCostConstant CB C5 C6 C7 cf ch := rawCostConstant_ge _ _ _ _ _ _ 0

end

variable {n v mu eta4 h4s B Bl E Fdef Fal CB C5 C6 C7 cf c C F ch : ℝ} (hv : 0 < v) (hmu : mu = n * v)
    (hn : 0 ≤ n) (hB : 1 ≤ B) (hcf : 0 ≤ cf) (hp4s : 0 ≤ h4s) (heta : eta4 = cf ^ 4 * h4s)

include hv hmu hn hcf hp4s heta in
theorem factorial_succ_energy_reduction
    (hc : 0 ≤ c) (hcC : c ≤ C) (hF : 0 ≤ F) (m : ℕ) :
    v⁻¹ * (eta4 * F * (c * mu) ^ (m + 1) / (m + 1).factorial) ≤
      c * cf ^ 4 * n * h4s * F * (C * mu) ^ m / (m + 1).factorial := by
  have hmu0 : 0 ≤ mu := by bound
  have hp : (c * mu) ^ (m + 1) ≤ c * mu * (C * mu) ^ m := by
    rw [pow_succ]
    have hh : (c * mu) ^ m ≤ (C * mu) ^ m :=
      by bound
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (mul_nonneg hc hmu0)
  calc
    _ ≤ v⁻¹ * (eta4 * F * (c * mu * (C * mu) ^ m) / (m + 1).factorial) := by
      bound
    _ = _ := by rw [heta, hmu]; field_simp

include hv hmu heta in
theorem inverse_volume_pair_energy :
    v⁻¹ * (eta4 * mu ^ 2 * F) = cf ^ 4 * (n ^ 2 * v * h4s * F) := by
  rw [heta, hmu]
  field_simp

include hB in
theorem activity_plus_one_bound
    (hCB : 0 ≤ CB) (hBl : 0 ≤ Bl) (hcost : Bl ≤ CB * B) :
    (Bl + 1) ^ 2 ≤ (CB + 1) ^ 2 * B ^ 2 := by
  nlinarith

include hv hmu hn hp4s heta in
theorem raw_energy_cost_bound (hB : 1 ≤ B) (hBl : 0 ≤ Bl)
    (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6) (hC7 : 0 ≤ C7)
    (hcf : 0 ≤ cf) (hch : 0 ≤ ch) (hFdef : 0 ≤ Fdef) (hFal : 0 ≤ Fal)
    (hcost : Bl ≤ CB * B) {M D : ℕ}
    (hE : E ≤ 3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef +
      3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial +
      Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) / (D + 1).factorial) :
    let CG := rawCostConstant CB C5 C6 C7 cf ch
    1 + Bl ^ 2 + v⁻¹ * E ≤ CG * (B ^ 2 + n ^ 2 * v * h4s * Fdef +
      n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial +
      n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) := by
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  have hCG : 1 ≤ CG := rawCostConstant_ge_one ..
  have hC6G : C6 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 1
  have hchG : ch ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 2
  have hBG : 1 + CB ^ 2 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 3
  have hpG : 3 * (C5 + C7) * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 4
  have haG : 3 * C6 ^ 2 * cf ^ 4 ≤ CG := rawCostConstant_ge _ _ _ _ _ _ 5
  have htG : Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2 ≤ CG :=
    rawCostConstant_ge _ _ _ _ _ _ 6
  have hB0 : 0 ≤ B := by positivity
  have hmu0 : 0 ≤ mu := by bound
  have hb2 : Bl ^ 2 ≤ CB ^ 2 * B ^ 2 := by
    exact Trans.trans ((sq_le_sq₀ hBl (mul_nonneg hCB hB0)).mpr hcost) (mul_pow CB B 2)
  have hb1 : 1 ≤ B ^ 2 := by nlinarith only [hB]
  have hbase : 1 + Bl ^ 2 ≤ CG * B ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hBG (sq_nonneg B)
    bound
  have hp : v⁻¹ * (3 * (C5 + C7) * eta4 * mu ^ 2 * Fdef) ≤
      CG * (n ^ 2 * v * h4s * Fdef) := by
    calc
      _ = 3 * (C5 + C7) * (cf ^ 4 * (n ^ 2 * v * h4s * Fdef)) := by
        grind
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hpG
          (by positivity : 0 ≤ n ^ 2 * v * h4s * Fdef) using 1 <;> ring
  have ha : v⁻¹ * (3 * C6 * eta4 * Fal * (C6 * mu) ^ (M + 1) / (M + 1).factorial) ≤
      CG * (n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) := by
    have hh := mul_le_mul_of_nonneg_left (factorial_succ_energy_reduction hv hmu hn hcf hp4s heta hC6 hC6G hFal M) (by positivity : 0 ≤ 3 * C6)
    apply le_trans (by convert hh using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right haG
      (by positivity : 0 ≤ n * h4s * Fal * (CG * mu) ^ M / (M + 1).factorial) using 1 <;> ring
  let ratio := n * h4s * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial
  have ht : v⁻¹ * (Real.exp ch * eta4 * (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) /
      (D + 1).factorial) ≤
      CG * (ratio) := by
    have hr := factorial_succ_energy_reduction hv hmu hn hcf hp4s heta hch hchG
      (show 0 ≤ 1 by norm_num) D
    have hh := mul_le_mul_of_nonneg_left hr
      (by positivity : 0 ≤ Real.exp ch * (Bl + 1) ^ 2)
    have hk := mul_le_mul_of_nonneg_right ((by nlinarith : (Bl + 1) ^ 2 ≤ (CB + 1) ^ 2 * B ^ 2))
      (by positivity : 0 ≤ Real.exp ch * ch * cf ^ 4 * n * h4s *
        (CG * mu) ^ D / (D + 1).factorial)
    apply le_trans (by convert hh using 1 <;> ring)
    apply le_trans (by convert hk using 1 <;> ring)
    convert mul_le_mul_of_nonneg_right htG
      (by positivity : 0 ≤ ratio) using 1 <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr hv.le)
  grind

end NearlyMinimax
