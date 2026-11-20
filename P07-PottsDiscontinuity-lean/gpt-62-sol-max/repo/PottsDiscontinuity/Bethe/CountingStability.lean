module

public import PottsDiscontinuity.Bethe.CountingQuadrature
public import PottsDiscontinuity.Bethe.Theorem23ContinuousEstimate

/-! Counting-function estimates within a fixed mesh window. -/

@[expose] public section

open Set MeasureTheory

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

private theorem mem_large {x : ℝ} (hx : x ∈ J) : x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi) := by
  grind

theorem exists_uniform_positive_counting_window {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) {d : ℝ} (hd : 0 < d) :
    ∃ m L : ℝ, 0 < m ∧ 0 < L ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      2 * (k + 1) ≤ N → DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d / N) →
      (∀ x ∈ J, m ≤ betheCountingDerivative Δ N (k + 1) p x) ∧
      (∀ x ∈ J, ∀ y ∈ J, |betheCountingDerivative Δ N (k + 1) p x -
        betheCountingDerivative Δ N (k + 1) p y| ≤ L * |x - y|) := by
  obtain ⟨L, hL, hLip⟩ := exists_uniform_countingDerivative_lipschitz hΔ₀
  let m := 1 / (2 * d)
  have hm : 0 < m := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * L * d ^ 2)
  have hN₀' : 0 < N₀ := by exact_mod_cast (show (0 : ℝ) < N₀ from lt_trans (by positivity) hN₀)
  refine ⟨m, L, hm, hL, N₀, hN₀', fun Δ hΔ N k hlarge p hp hs hBE hmesh => ?_⟩
  have hN : 0 < N := hN₀'.trans_le hlarge
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdc : L * (d / (N : ℝ)) ≤ m := by
    have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hlarge
    dsimp [m]
    rw [← mul_div_assoc, div_le_div_iff₀ hN' (by positivity : 0 < 2 * d)]
    nlinarith only [hN₀.le.trans hn]
  have hL' := hLip Δ hΔ N _ hN p hp hs
  refine ⟨fun x hx => ?_, fun x hx y hy => hL' x (mem_large hx) y (mem_large hy)⟩
  obtain ⟨j, hj⟩ := exists_rootPartition_cell hp hx
  have hstep : 1 / d ≤ rootStepDensity N (k + 1) p (by omega) x := by
    rw [rootStepDensity_on_cell hp (by omega) hs j hj]
    have hgap := rootPartition_gap_pos hp (by omega) j
    have hd' := (le_div_iff₀ hN').mp (hmesh j)
    exact (one_div_le_one_div_of_le (mul_pos hN' hgap) (by simpa [mul_comm] using hd')).trans
      (div_le_div_of_nonneg_right (one_le_rootGapMultiplicity hs j) (by positivity))
  have hcmp := step_counting_pointwise_comparison (hΔ.trans_lt hΔ₀) hp (by omega) hs hBE hL.le hL' hmesh hx
  have he : 1 / d = 2 * m := by ring
  linarith only [abs_le.mp hcmp |>.2, hdc, hstep, he]

private theorem countingDerivative_mass {Δ : ℝ} (hΔ : Δ < -1) {N n r : ℕ}
    {p : Fin n → ℝ} (hp : p ∈ S_n n) (hN : 0 < N) (hcount : N = 2 * (n + r)) :
    (∫ x in (-Real.pi)..Real.pi, betheCountingDerivative Δ N n p x) = 1 / 2 + (r : ℝ) / N := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_betheCountingFunction hΔ N n p x)
    ((continuous_betheCountingDerivative hΔ N n p).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
  rw [h, betheCountingFunction_neg hp, betheCountingFunction_pi hp hN]
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hc : (N : ℝ) = 2 * ((n : ℝ) + r) := by exact_mod_cast hcount
  field_simp
  linarith

/-- Uniform density estimate for Bethe solutions in the mesh window. The
    quadrature compares with the smooth derivative, whose mass is explicit. -/
theorem exists_uniform_density_bound_of_Bethe_mesh (r : ℕ) {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (d : ℝ) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ Δ ≤ Δ₀, ∀ (N k : ℕ), N₀ ≤ N →
      N = 2 * ((k + 1) + r) → ∀ (p : Fin (k + 1) → ℝ), p ∈ S_n (k + 1) →
      2 * (k + 1) ≤ N → DiscreteBetheEquation Δ N (k + 1) p →
      (∀ j : Fin (k + 2), rootPartitionPoint (k + 1) p (by omega) j.succ -
        rootPartitionPoint (k + 1) p (by omega) j.castSucc ≤ d / N) →
      densityNorm Δ (rootStepError Δ N p (by omega)) ≤ K / N := by
  obtain ⟨m, L, hm, hL, N₀, hN₀, hw⟩ := exists_uniform_positive_counting_window hΔ₀ hd
  obtain ⟨A, hA, hker⟩ := exists_uniform_d1Theta_bounds hΔ₀
  obtain ⟨δ, hδ, _, hδb⟩ := exists_uniform_double_Xi_lower hΔ₀
  obtain ⟨X, hX, hXb⟩ := exists_uniform_Xi_upper_bound hΔ₀
  obtain ⟨Y, hY, hcmp⟩ := exists_uniform_step_counting_comparison hΔ₀
  let E := (X * countingQuadBound m L A r + δ * r) / (2 * Real.pi)
  have hE : 0 < E := by dsimp [E, countingQuadBound]; positivity
  refine ⟨E / δ + Y * d, by positivity, N₀, hN₀,
    fun Δ hΔ N k hlarge hcount p hp hs hBE hmesh => ?_⟩
  have hN : 0 < N := hN₀.trans_le hlarge
  have hvalid := hΔ.trans_lt hΔ₀
  rcases hw Δ hΔ N k hlarge p hp hs hBE hmesh with ⟨hpos, hLip⟩
  let D := betheCountingDerivative Δ N (k + 1) p
  let S := densityNorm Δ (fun x => D x - rho Δ x)
  have hcD : Continuous D := continuous_betheCountingDerivative hvalid _ _ _
  have hbD := countingError_bddAbove hvalid N (k + 1) p
  have hmass := countingDerivative_mass hvalid hp hN hcount
  have hpoint (α : ℝ) (hα : α ∈ J) :
      |Xi (lamOf Δ) α * (D (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))| ≤ (1 - δ) * S + E / N := by
    let x := kMap (lamOf Δ) α
    let T := cBEop Δ D x / (2 * Real.pi)
    have hx : x ∈ J := kMap_mem_Icc (lamOf_pos hvalid) hα
    have hq := bethe_counting_quadrature_of_bounded_deriv hvalid hp (by omega) hcount hBE hm hA.le hL.le
      hpos hLip (g := d1Theta Δ x) (G := deriv (d1Theta Δ x))
      (fun y _ => (hasDerivAt_d1Theta_right_inv hvalid x y).differentiableAt.hasDerivAt)
      (fun y hy => ((hker Δ hΔ).1 x hx y hy).2) (fun y hy => ((hker Δ hΔ).1 x hx y hy).1)
    have hid : D x - T =
        ((∑ j, d1Theta Δ x (p j)) / (N : ℝ) -
          (∫ y in (-Real.pi)..Real.pi, d1Theta Δ x y * D y)) / (2 * Real.pi) := by
      dsimp only [T, cBEop]
      change (1 + (∑ j, d1Theta Δ x (p j)) / (N : ℝ)) / (2 * Real.pi) - _ = _
      ring
    have hdiff : |Xi (lamOf Δ) α * (D x - T)| ≤
        X * (countingQuadBound m L A r / N / (2 * Real.pi)) := by
      rw [hid, abs_mul, abs_div, abs_of_pos (Xi_pos (lamOf_pos hvalid) α),
        abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact mul_le_mul (hXb Δ hΔ α) (div_le_div_of_nonneg_right hq (by positivity)) (by positivity) hX.le
    have hct := counting_continuous_contraction hvalid hcD hmass hδ.le (hδb Δ hΔ) hbD hα
    change |Xi (lamOf Δ) α * (T - rho Δ x)| ≤ _ at hct
    rw [abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) / N)] at hct
    change |Xi (lamOf Δ) α * (D x - rho Δ x)| ≤ _
    rw [show Xi (lamOf Δ) α * (D x - rho Δ x) =
      Xi (lamOf Δ) α * (D x - T) + Xi (lamOf Δ) α * (T - rho Δ x) by ring]
    exact (abs_add_le ..).trans ((add_le_add hdiff hct).trans_eq (by ring))
  have hS : S ≤ (1 - δ) * S + E / N := by
    apply csSup_le
    · exact ⟨_, ⟨⟨0, ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩⟩, rfl⟩⟩
    · rintro _ ⟨α, rfl⟩
      exact hpoint α α.property
  have hSD : S ≤ (E / δ) / N := by
    rw [div_right_comm]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hS]
  have h := hcmp Δ hΔ N k p hp hs hBE d hd.le hmesh
  rw [add_div]
  exact h.trans (add_le_add hSD le_rfl)

end PottsDiscontinuity.Bethe
