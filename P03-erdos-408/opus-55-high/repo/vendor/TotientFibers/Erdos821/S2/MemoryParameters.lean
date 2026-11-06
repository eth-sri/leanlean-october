module

public import Erdos821.Blueprint.Graph

/-! A common damping parameter and Schur weight for the memory evolution. -/

@[expose] public section

noncomputable section

namespace Erdos821.Blueprint.Graph

theorem memory_parameters_exist_proof : Erdos821.Blueprint.Graph.memory_parameters_exist_statement := by
  intro F
  let a : ℝ := Real.sqrt F.q
  have ha0 : 0 < a := Real.sqrt_pos.mpr F.q_pos
  have ha1 : a < 1 := by
    have h := Real.sqrt_lt_sqrt F.q_pos.le F.q_lt
    simpa only [Real.sqrt_one] using h
  let b : ℝ := (1 + a) / 2
  have hb0 : 0 < b := by dsimp only [b]; linarith
  have hba : a < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  let rho : ℝ := Real.sqrt b
  have hrho0 : 0 < rho := Real.sqrt_pos.mpr hb0
  have hrho1 : rho < 1 := by
    have h := Real.sqrt_lt_sqrt hb0.le hb1
    simpa only [Real.sqrt_one] using h
  have hrhosq : rho ^ (2 : ℕ) = b := Real.sq_sqrt hb0.le
  let delta : ℝ := 1 - a / b
  have hd0 : 0 < delta := sub_pos.mpr ((div_lt_one hb0).mpr hba)
  let M : ℝ := max 1 F.vMax
  have hM0 : 0 < M := by positivity
  let v : ℝ := 2 + 2 * M / (rho * delta)
  have ht0 : 0 < 2 * M / (rho * delta) :=
    by positivity
  have hv1 : 1 < v := by dsimp only [v]; linarith
  have hv0 : 0 < v := lt_trans zero_lt_one hv1
  have hcross : delta * (rho * v) = 2 * M + 2 * (rho * delta) := by
    dsimp only [v]
    field_simp; ring
  have hfrac : 2 * M / (rho * v) < delta := by
    apply (div_lt_iff₀ (by positivity)).mpr
    rw [hcross]
    nlinarith
  have hqa : F.q ≤ a := by
    have ha2 : a ^ (2 : ℕ) = F.q := Real.sq_sqrt F.q_pos.le
    have hp := mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)
    nlinarith
  refine ⟨{
    rho := rho
    v := v
    rho_pos := hrho0
    rho_lt := hrho1
    rho_q := by linarith
    v_gt := hv1
    damping := ?_
  }⟩
  intro q' hq'
  have hq0 : 0 ≤ q' := by
    rcases hq' with rfl | rfl
    · exact F.q_pos.le
    · simp
  have hq'a : q' ≤ a := by
    rcases hq' with rfl | rfl
    · omega
    · linarith
  have hnum : 2 * M * (1 - q') ≤ 2 * M := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (sub_le_self 1 hq0) (mul_nonneg (by norm_num) hM0.le)
  rw [hrhosq]
  calc
    q' / b + 2 * M * (1 - q') / (rho * v) ≤ a / b + 2 * M / (rho * v) :=
      add_le_add (div_le_div_of_nonneg_right hq'a hb0.le)
        (div_le_div_of_nonneg_right hnum (by positivity))
    _ < a / b + delta := by linarith
    _ = 1 := by linarith

end Erdos821.Blueprint.Graph
