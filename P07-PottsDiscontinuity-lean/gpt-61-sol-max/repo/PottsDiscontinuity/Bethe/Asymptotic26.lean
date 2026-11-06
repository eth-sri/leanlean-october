module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticQuadrature

/-! # Theorem 2.6: convergence of the empirical integrals

The positive root count is written `k i + 1`; the count identity
`N i = 2 * (k i + 1 + r)` is precisely `n=N/2-r`.  The index filter is
arbitrary, so the statement applies in particular to `N ∈ 4ℕ` tending to
infinity. No discrete Bethe equation and no rate of density convergence are
assumed.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem integral_empiricalMeasure (N : ℕ) (hN : 0 < N) (n : ℕ)
    (p : Fin n → ℝ) (g : ℝ → ℝ) :
     ∫ x, g x ∂empiricalMeasure N hN n p  = (∑ j, g (p j)) / (N : ℝ) := by
  unfold empiricalMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp_all <;> grind
  · intro j _
    exact integrable_dirac (by simp)

/-- The test-function form of Theorem 2.6, for the actual empirical measures.
The finite error estimate treats the two boundary tails separately. -/
theorem theorem26_integrals {ι : Type*} {l : Filter ι} {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N k : ι → ℕ) (p : ∀ i, Fin (k i + 1) → ℝ)
    (hp : ∀ i, p i ∈ S_n (k i + 1)) (hs : ∀ i, 2 * (k i + 1) ≤ N i)
    (hcount : ∀ i, N i = 2 * (k i + 1 + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) l atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α *
        (rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i)
          (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ hΔ
      (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
      (hb i)) l (𝓝 0))
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun i => ∫ x, g x ∂empiricalMeasure (N i)
      (by have := hs i; omega) (k i + 1) (p i)) l
      (𝓝 (∫ x in (-Real.pi)..Real.pi, g x * rho Δ x)) := by
  
  
  let E  := fun i => densityNorm Δ hΔ
    (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
    (hb i) / (Real.sinh (lamOf Δ) / (Real.cosh (lamOf Δ) + 1))
  
  have hEnonneg (i : ι) : 0 ≤ E i :=
    div_nonneg (densityNorm_nonneg hΔ _ (hb i)) (density_weight_lower_pos hΔ).le
  
  obtain ⟨m, hm, hmesh⟩ := eventually_rootPartition_gap_le hΔ r N (fun i => k i + 1) p hp
     fun i => by omega  hs hcount hb hlim
  let d  := fun i => 2 * (2 * r + 1 ) / (m *  N i )
  have hinv : Tendsto (fun i => (N i : ℝ)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hNlim
  have hd : Tendsto d l (𝓝 0) := by
    
    simpa only [mul_zero, d, div_mul_eq_div_mul_one_div, one_div] using  hinv.const_mul (2 * (2 * r + 1 ) / m) 
  
  obtain ⟨G₀, hG₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuous_rho hΔ).continuousOn
  let G := max G₀ 1
  let M := max M₀ 1
  
  
  
  
  let B  := fun i => 2 * Real.pi * G * E i + 2 * G * M * d i + G * (N i : ℝ)⁻¹
  have hB : Tendsto B l (𝓝 0) := by
    have ht := (((tendsto_densityNorm_div hΔ
                      (fun i x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
                      hb hlim).const_mul (2 * Real.pi * G)).add (hd.const_mul (2 * G * M))).add
      (hinv.const_mul G)
    grind
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let w  := ε / (4 * Real.pi * M)
  have hwpos : 0 < w := by  positivity
  
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) w hwpos
  filter_upwards [hmesh, hd.eventually (gt_mem_nhds hδ),
    hB.eventually (gt_mem_nhds (show  0  < ε / 2 by positivity))] with i hmi hdi hBi
  rw [Real.dist_eq, integral_empiricalMeasure, abs_sub_comm]
  have hquad := root_quadrature_error (hp i) (hs i) hΔ hg (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le (lt_of_lt_of_le zero_lt_one (le_max_right _ _)).le (hEnonneg i)
    hwpos.le (fun x hx => LE.le.trans (hG₀ x hx) (le_max_left G₀ 1)) (fun x hx => LE.le.trans (hM₀ x hx) (le_max_left M₀ 1)) ((fun i x (hx : x ∈ Icc (-Real.pi) Real.pi) => abs_le_densityNorm_div hΔ
                                   (fun x => rootStepDensity (N i) (k i + 1) (p i) (hp i) (by omega) (hs i) x - rho Δ x)
                                   (hb i) hx) i) hmi
     fun x hx y hy hxy => by
      apply hmod x hx y hy
      
      exact hxy.trans hdi.le 
  
  have hidentity : 2 * Real.pi * (w * M + G * E i) + 2 * G * M * d i + G /  N i  =
      ε / 2 + B i := by
    grind
  
  linarith

end PottsDiscontinuity.Bethe
