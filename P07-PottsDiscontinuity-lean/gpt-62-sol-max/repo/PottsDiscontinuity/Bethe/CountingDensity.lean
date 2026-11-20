module

public import PottsDiscontinuity.Bethe.Theorem23Comparison
public import PottsDiscontinuity.Bethe.RatioDensityLimits

/-! Quantitative step-density convergence transfers to the smooth derivative. -/

@[expose] public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

theorem eventually_countingDerivative_approx {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ) (hp : ∀ i, p i ∈ S_n (n i))
    (hn : ∀ i, 0 < n i) (hcount : ∀ i, N i = 2 * (n i + r))
    (hBE : ∀ i, DiscreteBetheEquation Δ (N i) (n i) (p i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    {E L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ i, ∀ x ∈ Icc (-(3 * Real.pi)) (3 * Real.pi), ∀ y ∈ Icc (-(3 * Real.pi)) (3 * Real.pi),
      |betheCountingDerivative Δ (N i) (n i) (p i) x - betheCountingDerivative Δ (N i) (n i) (p i) y| ≤ L * |x - y|)
    (herror : ∀ᶠ i in l, ∀ x ∈ J, |rootStepDensity (N i) (n i) (p i) (hn i) x - rho Δ x| ≤ E / N i) :
    ∃ d A : ℝ, 0 ≤ d ∧ ∀ᶠ i in l,
      (∀ j : Fin (n i + 1), rootPartitionPoint (n i) (p i) (hn i) j.succ -
        rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤ d / N i) ∧
      ∀ x ∈ J, |betheCountingDerivative Δ (N i) (n i) (p i) x - rho Δ x| ≤ A / N i := by
  obtain ⟨m, hm, hlower⟩ := rho_uniform_lower_bound hΔ
  let d : ℝ := 2 * (2 * r + 1) / m
  refine ⟨d, L * d + E, by positivity, ?_⟩
  have hElim : Tendsto (fun i => E / (N i : ℝ)) l (𝓝 0) := tendsto_const_nhds.div_atTop hNlim
  filter_upwards [herror, hElim.eventually (gt_mem_nhds (show 0 < m / 2 by positivity))] with i hi he
  have hiN : 2 * n i ≤ N i := by have := hcount i; omega
  have hlow (x : ℝ) (hx : x ∈ J) : m / 2 ≤ rootStepDensity (N i) (n i) (p i) (hn i) x := by
    linarith [(abs_le.mp (hi x hx)).1, hlower Δ le_rfl x hx]
  have hmesh (j : Fin (n i + 1)) : rootPartitionPoint (n i) (p i) (hn i) j.succ -
      rootPartitionPoint (n i) (p i) (hn i) j.castSucc ≤ d / N i := by
    refine (rootPartition_gap_le_of_density_lower (hp i) (hn i) hiN hm hlow j).trans ?_
    unfold d
    rw [div_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (rootGapMultiplicity_le_offset hiN (hcount i) j)
      (by norm_num)) (by positivity)
  refine ⟨hmesh, fun x hx => ?_⟩
  have h := step_counting_pointwise_comparison hΔ (hp i) (hn i) hiN (hBE i) hL (hLip i) hmesh hx
  rw [abs_sub_comm] at h
  rw [add_div, mul_div_assoc]
  exact (abs_sub_le _ (rootStepDensity (N i) (n i) (p i) (hn i) x) _).trans (add_le_add h (hi x hx))

end PottsDiscontinuity.Bethe
