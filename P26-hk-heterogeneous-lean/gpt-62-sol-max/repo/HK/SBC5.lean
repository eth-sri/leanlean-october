module

public import HK.Basic

/-!
# Five SBC agents with oscillating convergence

The fixed table and the negative mode are shared by the entire family. Its member at amplitude 1
is the original five-agent example, while amplitudes tending to 0 give arbitrarily small spreads
between the confidence bounds.
-/

@[expose] public section

namespace HK

open Filter Topology

local notation "N" => ![{0}, {0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {4}]
local notation "R[" δ "]" => sbc5Family_r δ
local notation "Y[" δ "]" => traj Model.sbc R[δ] (sbc5Family_x0 δ)

private theorem root_bound : Real.sqrt 2 < 3 / 2 := by norm_num [Real.sqrt_lt']

private theorem rate_bounds : -1 < sbc5Rate ∧ sbc5Rate < 0 := by
  have hlo : 1 < Real.sqrt 2 := by norm_num [Real.lt_sqrt]
  unfold sbc5Rate
  constructor <;> linarith [root_bound]

attribute [local simp] sbc5Family_r sbc5_lim sbc5_v sbc5Rate sbc5Family_x0 in
private theorem orbit {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ModeOrbit .sbc R[δ] (sbc5Family_x0 δ) sbc5_lim (δ • sbc5_v) sbc5Rate (fun _ => N) where
  rate := rate_bounds
  table t := by
    have hu : |sbc5Rate ^ t * δ| ≤ δ := by
      rw [abs_mul, abs_pow, abs_of_pos hδ]
      exact mul_le_of_le_one_left hδ.le (pow_le_one₀ (abs_nonneg _) (abs_lt_one_of_rate rate_bounds).le)
    obtain ⟨_, _⟩ := abs_le.mp hu
    have := Real.sqrt_nonneg 2
    have := root_bound
    simp only [← mul_smul]
    check_neighbors [-sbc5Rate]

theorem sbc5Family_closed_form (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (t : ℕ) :
    Y[δ] t = profile sbc5_lim (sbc5Rate ^ t * δ) sbc5_v := by
  change _ = sbc5_lim + (sbc5Rate ^ t * δ) • sbc5_v
  rw [mul_smul]
  exact (orbit hδ0 hδ1).form t

theorem sbc5Family_neighbors (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (t : ℕ) :
    neighbors .sbc R[δ] (Y[δ] t) = N :=
  (orbit hδ0 hδ1).neighborhoods t

/-- The pairwise bounds say that the ratio between the largest and smallest is less than `1+ε`. -/
theorem sbc5_near_homogeneous (ε : ℝ) (hε : 0 < ε) :
    ∃ r x₀ : Fin 5 → ℝ,
      (∀ i, 0 < r i) ∧ (∀ i j, r i < (1 + ε) * r j) ∧ r 0 < r 1 ∧
      (∀ t, proximityDigraph .sbc r (traj .sbc r x₀ t) = proximityDigraph .sbc r x₀) ∧
      Tendsto (traj .sbc r x₀) atTop (𝓝 sbc5_lim) ∧
      (∀ τ, ¬ FixedFrom (traj .sbc r x₀) τ) ∧
      (∀ xinf τ, ¬ PseudoStableAfter (traj .sbc r x₀) xinf τ) := by
  let δ : ℝ := min (1 / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left ..
  have hδε : δ ≤ ε / 4 := min_le_right ..
  have hδ1 : δ ≤ 1 := by linarith
  have h := orbit hδ hδ1
  refine ⟨R[δ], sbc5Family_x0 δ, ?_, ?_, ?_, digraph_constant h.neighborhoods,
    h.facts 1 (by simpa [Pi.smul_apply, sbc5_v] using hδ.ne')⟩
  all_goals
    norm_num [Fin.forall_fin_succ, sbc5Family_r]
    and_intros <;> nlinarith [mul_le_mul_of_nonneg_left hδhalf hε.le]

local notation "X" => traj Model.sbc sbc5_r sbc5_x0

private theorem base_orbit : ModeOrbit .sbc sbc5_r sbc5_x0 sbc5_lim sbc5_v sbc5Rate (fun _ => N) := by
  have base_r : R[1] = sbc5_r := by check_rows [sbc5Family_r, sbc5_r]
  have base_x : sbc5Family_x0 1 = sbc5_x0 := by check_rows [sbc5Family_x0, sbc5_x0, sbc5_lim, sbc5_v]
  simpa only [base_r, base_x, one_smul] using orbit (δ := 1) (by norm_num) le_rfl

theorem sbc5_closed_form (t : ℕ) : X t = profile sbc5_lim (sbc5Rate ^ t) sbc5_v := base_orbit.form t

theorem sbc5_neighbors (t : ℕ) : neighbors .sbc sbc5_r (X t) = N := base_orbit.neighborhoods t

theorem sbc5_digraph_constant (t : ℕ) :
    proximityDigraph .sbc sbc5_r (X t) = proximityDigraph .sbc sbc5_r sbc5_x0 :=
  digraph_constant sbc5_neighbors t

theorem sbc5_facts : Tendsto X atTop (𝓝 sbc5_lim) ∧ NeverStable X :=
  base_orbit.facts 1 (by simp [sbc5_v])

private theorem r_pos : ∀ i, 0 < sbc5_r i := by norm_num [Fin.forall_fin_succ, sbc5_r]

theorem not_conjecture23_sbc_five : ¬ Conjecture23ForAgents .sbc 5 := refute23 r_pos sbc5_facts.2

theorem not_theorem64iv_sbc_five : ¬ Theorem64ivForAgents .sbc 5 :=
  refute64 r_pos sbc5_digraph_constant sbc5_facts.2

theorem sbc5_fvct (t : ℕ) : fvct .sbc sbc5_r (X t) = sbc5_lim := base_orbit.frozenLimit t

theorem sbc5_perStepFactor (t : ℕ) (i : Fin 5) (hi : i ∈ ({1, 2, 3} : Finset (Fin 5))) :
    perStepFactor .sbc sbc5_r X i t = sbc5Rate :=
  base_orbit.factor t i (by
    fin_cases i <;> simp_all [sbc5_v])

end HK
