module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticTaylor

/-! # Moving continuous tests for empirical sums -/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem continuous_d1Theta_pair {Δ : ℝ} (hΔ : Δ < -1) :
    Continuous  fun z : ℝ × ℝ => d1Theta Δ z.1 z.2  := by
  
  
  rw [(by
         funext z
         simpa only [mul_one, mul_zero, add_zero] using (fderiv_theta_apply hΔ z.1 z.2 1 0).symm : (fun z  => d1Theta Δ z.1 z.2) =
      fun z => fderiv ℝ (fun w  => theta Δ w.1 w.2) z (1, 0))]
  exact ((contDiff_iff_contDiffAt.mpr  fun z => (analyticAt_theta_xy hΔ z.1 z.2).contDiffAt ).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_d2Theta_pair {Δ : ℝ} (hΔ : Δ < -1) :
    Continuous  fun z : ℝ × ℝ => d2Theta Δ z.1 z.2  := by
  
  
  rw [(by
         funext z
         simpa only [mul_one, mul_zero, zero_add] using (fderiv_theta_apply hΔ z.1 z.2 0 1).symm : (fun z  => d2Theta Δ z.1 z.2) =
      fun z => fderiv ℝ (fun w  => theta Δ w.1 w.2) z (0, 1))]
  exact ((contDiff_iff_contDiffAt.mpr  fun z => (analyticAt_theta_xy hΔ z.1 z.2).contDiffAt ).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem tendstoUniformlyOn_continuous_slice {ι : Type*} {l : Filter ι}
    (F : ℝ → ℝ → ℝ) (hF : Continuous  fun z : ℝ × ℝ => F z.1 z.2 )
    {a : ι → ℝ} {x : ℝ} (ha : Tendsto a l (𝓝 x))
    (hai : ∀ᶠ i in l, a i ∈ Icc (-Real.pi) Real.pi) (hx : x ∈ Icc (-Real.pi) Real.pi) :
    TendstoUniformlyOn (fun i y => F (a i) y) (F x) l (Icc (-Real.pi) Real.pi) := by
  
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hF.continuousOn) ε hε
  filter_upwards [hai, Metric.tendsto_nhds.mp ha δ hδ] with i hi hdi y hy
  apply hmod (x, y) ⟨hx, hy⟩ (a i, y) ⟨hi, hy⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm] using hdi

/-- Weak convergence remains valid for tests converging uniformly on the
support, even when the test functions themselves depend on the root count. -/
theorem empirical_sum_tendsto_of_uniformlyOn {ι : Type*} {l : Filter ι}
    (N n : ι → ℕ) (hN : ∀ i, 0 < N i) (hn : ∀ i, n i ≤ N i)
    (p : ∀ i, Fin (n i) → ℝ) (hp : ∀ i j, p i j ∈ Icc (-Real.pi) Real.pi)
    (g : ℝ → ℝ) (G : ι → ℝ → ℝ) {I : ℝ}
    (hbase : Tendsto (fun i => (∑ j, g (p i j)) / (N i : ℝ)) l (𝓝 I))
    (hG : TendstoUniformlyOn G g l (Icc (-Real.pi) Real.pi)) :
    Tendsto (fun i => (∑ j, G i (p i j)) / (N i : ℝ)) l (𝓝 I) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hbase (ε / 2) (by positivity),
    Metric.tendstoUniformlyOn_iff.mp hG (ε / 2) (by positivity)] with i hi hGi
  have hNp : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
  
  have hd : dist ((∑ j, G i (p i j)) /  N i ) ((∑ j, g (p i j)) /  N i ) ≤ ε / 2 := by
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hNp]
    exact (div_le_iff₀ hNp).mpr (by simpa only [mul_comm] using  by
                                                                   rw [← Finset.sum_sub_distrib]
                                                                   calc
                                                                     _ ≤ ∑ j, |G i (p i j) - g (p i j)| := Finset.abs_sum_le_sum_abs _ _
                                                                     _ ≤ ∑ _j : Fin (n i), ε / 2 := by
                                                                       apply Finset.sum_le_sum
                                                                       intro j _
                                                                       
                                                                       simpa only [Real.dist_eq, abs_sub_comm] using  (hGi (p i j) (hp i j)).le 
                                                                     _ =  n i  * (ε / 2) := by simp
                                                                     _ ≤  N i  * (ε / 2) :=
                                                                       mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hn i)) (by positivity) )
  exact (dist_triangle _ ((∑ j, g (p i j)) /  N i ) I).trans_lt (by linarith)

end PottsDiscontinuity.Bethe
