module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticBoundaryLimit
public import PottsDiscontinuity.Bethe.AsymptoticDiscreteExpansion
public import PottsDiscontinuity.Bethe.AsymptoticLimitEquation
public import PottsDiscontinuity.Bethe.AsymptoticProducts

/-! # Every uniform subsequential limit is the offset-equation solution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem tendsto_of_abs_sub_le {ι : Type*} {l : Filter ι} {u v E : ι → ℝ} {a : ℝ}
    (hv : Tendsto v l (𝓝 a)) (hE : Tendsto E l (𝓝 0))
    (hb : ∀ i, |u i - v i| ≤ E i) : Tendsto u l (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) (by positivity),
    hE.eventually (gt_mem_nhds (show  0  < ε / 2 by positivity))] with i hi hEi
  have hd := dist_triangle (u i) (v i) a
  
  simp only [Real.dist_eq] at hd hi ⊢
  linarith only [hd, hi,  hb i , hEi]

/-- The limit-equation step of Theorem 2.9. Its premises are the geometric
estimates and weak convergence proved separately from the source density
assumptions, together with a uniform subsequential limit. -/
theorem offset_uniform_limit_identification {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N : ℕ → ℕ) (h4 : ∀ i, 4 ∣ N i) (hr : ∀ i, r ≤ N i / 2)
    (hN : ∀ i, 0 < N i) (hn : ∀ i, 0 < N i / 2 - r)
    (p : ∀ i, Fin (N i / 2) → ℝ) (q : ∀ i, Fin (N i / 2 - r) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (hq : ∀ i, q i ∈ S_n (N i / 2 - r))
    (hpBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2) (p i))
    (hqBE : ∀ i, DiscreteBetheEquation Δ (N i) (N i / 2 - r) (q i))
    (hNlim : Tendsto (fun i => (N i : ℝ)) atTop atTop)
    (B R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i j, |offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j| ≤ B)
    (hnear : ∀ i j, |offsetLowerRoot (N i) r (hr i) (p i) j - q i j| ≤ R / N i ∧
      |offsetUpperRoot (N i) r (hr i) (p i) j - q i j| ≤ R / N i)
    (dP dQ : ℕ → ℝ) (hdP : Tendsto dP atTop (𝓝 0)) (hdQ : Tendsto dQ atTop (𝓝 0))
    (hdPnonneg : ∀ i, 0 ≤ dP i)
    (hmeshP : ∀ i, ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.succ -
        rootPartitionPoint (N i / 2) (p i) (by have := hn i; omega) j.castSucc ≤ dP i)
    (hmeshQ : ∀ i, ∀ j : Fin (N i / 2 - r + 1),
      rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.succ -
        rootPartitionPoint (N i / 2 - r) (q i) (hn i) j.castSucc ≤ dQ i)
    (hweak : ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun i => (∑ j, g (q i j)) / (N i : ℝ)) atTop
        (𝓝 (∫ y in (-Real.pi)..Real.pi, g y * rho Δ y)))
    {f : ℝ → ℝ} (hf : Continuous f)
    (hF : TendstoUniformlyOn (fun i x => offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i) x)
      f atTop (Icc (-Real.pi) Real.pi)) :
    ∀ x ∈ Icc (-Real.pi) Real.pi, rho Δ x * f x = (r : ℝ) * tauCont Δ x := by
  let F  := fun i => offsetFunction (N i) r (h4 i) (hr i) (p i) (q i) (hn i)
  change TendstoUniformlyOn F f atTop (Icc (-Real.pi) Real.pi) at hF
  have hqmem (i : ℕ) (j : Fin (N i / 2 - r)) : q i j ∈ Icc (-Real.pi) Real.pi :=
    ⟨((hq i).1 j).1.le, ((hq i).1 j).2.le⟩
  have hFroot (i : ℕ) (j : Fin (N i / 2 - r)) :
      F i (q i j) = offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) j :=
    by
      solve_by_elim [_root_.PottsDiscontinuity.Bethe.offsetFunction_at_root, _root_.And.left, _root_.And.right]
  
  have hinv : Tendsto (fun i => (N i : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNlim
  have hRlim : Tendsto (fun i => R /  N i ) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul R
  apply eq_mul_tauCont_of_scaled_cOE hΔ ((continuous_rho hΔ).mul hf)
  intro x hx
  choose j hj hdist using  fun i => offsetFunction_near_root (h4 i) (hr i) (hn i) (hq i) (hmeshQ i) hx 
  let a  := fun i => q i (j i)
  have ha : Tendsto a atTop (𝓝 x) :=
    tendsto_of_abs_sub_le tendsto_const_nhds hdQ  fun i => by simpa only [abs_sub_comm] using hdist i 
  have hamem (i : ℕ) : a i ∈ Icc (-Real.pi) Real.pi := hqmem i (j i)
  
  
  have hε : Tendsto (fun i => offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) (j i))
      atTop (𝓝 (f x)) := by
    convert hF.tendsto_at hx using 1
    funext i
    exact (hj i).symm
  let boundary  := fun i =>
    (offsetBoundarySum Δ (N i) r (hr i) (p i) (offsetLowerRoot (N i) r (hr i) (p i) (j i)) +
      offsetBoundarySum Δ (N i) r (hr i) (p i) (offsetUpperRoot (N i) r (hr i) (p i) (j i))) / 2
  have hBL := tendsto_offsetBoundarySum hΔ r N hr  fun i => by have := hn i; omega 
    p hp dP hdP hdPnonneg hmeshP (tendsto_of_abs_sub_le ha hRlim  fun i => (hnear i (j i)).1 )
  have hBU := tendsto_offsetBoundarySum hΔ r N hr  fun i => by have := hn i; omega 
    p hp dP hdP hdPnonneg hmeshP (tendsto_of_abs_sub_le ha hRlim  fun i => (hnear i (j i)).2 )
  have hboundary : Tendsto boundary atTop
      (𝓝 ( r  / 2 * (theta Δ x (-Real.pi) + theta Δ x Real.pi))) := by
    convert (hBL.add hBU).div_const 2 using 1; ring
  
  let S₂  := fun i =>
    (∑ k, d2Theta Δ (a i) (q i k) * offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) k) /  N i 
  have hg₁ : Continuous  (d1Theta Δ x)  :=
    (continuous_d1Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)
  have hg₂ : Continuous  fun y => d2Theta Δ x y * f y  :=
    ((continuous_d2Theta_pair hΔ).comp (continuous_const.prodMk continuous_id)).mul hf
  
  
  
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
     (continuous_d2Theta_pair hΔ).continuousOn 
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  
  
  
  
  have hprod := tendstoUniformlyOn_mul_of_bounds (tendstoUniformlyOn_continuous_slice (d2Theta Δ) (continuous_d2Theta_pair hΔ)
                                                    ha (Eventually.of_forall hamem) hx) hF
    (by aesop)
    (by aesop) (fun i y hy => LE.le.trans (hM₀ (a i, y) ⟨hamem i, hy⟩) (le_max_left M₀ 1))  fun y hy => LE.le.trans (hC₀ y hy) (le_max_left C₀ 1) 
  
  obtain ⟨K, hK, hTaylor⟩ := offset_bethe_taylor hΔ
  have herrlim : Tendsto (fun i => K * R ^ 2 /  N i ) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (K * R ^ 2)
  have hzero : Tendsto (fun i =>
      offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) (j i) - boundary i +
        (fun i => (∑ k, d1Theta Δ (a i) (q i k)) / (N i )) i * offsetDisplacement (N i) r (h4 i) (hr i) (p i) (q i) (j i) + S₂ i)
      atTop (𝓝 0) := by
    apply tendsto_of_abs_sub_le tendsto_const_nhds herrlim
    intro i
    simpa only [sub_zero] using hTaylor (N i) r (h4 i) (hr i) (hN i) (p i) (q i)
      (hp i) (hq i) (hpBE i) (hqBE i) R hR (hnear i) (j i)
  have hident := tendsto_nhds_unique (((hε.sub hboundary).add ((empirical_sum_tendsto_of_uniformlyOn N (fun i => N i / 2 - r) hN  fun i => by omega 
                                                                    q hqmem _ _ (hweak _ hg₁) (tendstoUniformlyOn_continuous_slice (d1Theta Δ) (continuous_d1Theta_pair hΔ)
                                                                                                 ha (Eventually.of_forall hamem) hx)).mul hε)).add (by
                                                                                   have ht := empirical_sum_tendsto_of_uniformlyOn N (fun i => N i / 2 - r) hN
                                                                                      fun i => by omega  q hqmem _ _ (hweak _ hg₂) hprod
                                                                                   convert ht using 1
                                                                                   funext i
                                                                                   dsimp only [S₂]
                                                                                   congr 1
                                                                                   apply Finset.sum_congr rfl
                                                                                   intro k _
                                                                                   rw [hFroot])) hzero
  have hcbe := rho_isCBESolution hΔ x hx
  unfold cBEop at hcbe
  
  have hInt :  ∫ y in (-Real.pi)..Real.pi, d2Theta Δ x y * (rho Δ y * f y)  =
      ∫ y in (-Real.pi)..Real.pi,  d2Theta Δ x y * f y  * rho Δ y := by
    apply intervalIntegral.integral_congr
    intro y _
    ring
  
  simp only [Pi.mul_apply]
  rw [hInt]
  nlinarith only [hident,  congrArg (fun z  => z * f x) hcbe ]

end PottsDiscontinuity.Bethe
