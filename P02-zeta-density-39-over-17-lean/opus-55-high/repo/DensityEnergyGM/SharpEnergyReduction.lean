module
public import DensityEnergyGM.SharpGcdSummation
public import DiscreteAdditiveEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Finset GuthMaynard.NativeMoment GuthMaynard.Improvement
namespace Montgomery.RationalMoment

/-- The actual large-value energy reduction with the optimized profile.
All reproducing, sampling, moment and gcd bounds are proved inputs supplied
inside the proof; no analytic estimate remains among the premises. -/
theorem discrete_energy_sharp_profile_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T N : ℝ) (a : ℕ → ℂ) (W : Finset ℝ) (V : ℝ),
        T₀ ≤ T → 0 < N → T ≤ N ^ 2 → N ≤ T →
        (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
        0 < V → (∀ t ∈ W, V ≤ ‖boundedPolynomial N a t‖) →
        IsSeparated 1 W → InBaseInterval T W →
        (discreteAdditiveEnergy W : ℝ) * V ^ 2 ≤ C * T ^ ε *
          (N ^ 2 * Real.sqrt (W.card : ℝ) * Real.sqrt (discreteAdditiveEnergy W : ℝ) +
            N * sharpCubicProfile T W) := by
  obtain ⟨C₀, hC₀, hRepro⟩ := discrete_additive_energy_reproducing
  obtain ⟨C₁, hC₁, hSmall⟩ := small_gcd_cubic_energy
  pm_4083 C₂ T₀ hC₂ hT₀ hLarge large_gcd_cubic_sharp_native ε hε
  let C : ℝ := C₀ * C₁ + C₀ * C₂
  pm_4123
  pm_4084
  pm_4039
  pm_3977
  have hAbsSep : ∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u| := by
    pm_7381 hne
  let A := sourceRatioIndices N
  let P := A ×ˢ A
  let F : ℕ × ℕ → ℝ := fun p => ‖∑ t ∈ W, phase (pairRatio p) t‖ ^ 3
  let Psmall := P.filter (fun p => (pairGcd p : ℝ) < N ^ 2 / T)
  let Plarge := P.filter (fun p => N ^ 2 / T ≤ (pairGcd p : ℝ))
  let S : ℝ := N ^ 2 * Real.sqrt (W.card : ℝ) * Real.sqrt (discreteAdditiveEnergy W : ℝ)
  let B : ℝ := N * sharpCubicProfile T W
  pm_4027
  have hB : 0 ≤ B := mul_nonneg hN.le (sharpCubicProfile_nonneg hTpos.le W)
  have hGeom : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2 ∧
      N < p.1 ∧ (p.1 : ℝ) ≤ 2 * N ∧ N < p.2 ∧ (p.2 : ℝ) ≤ 2 * N := by
    pm_381 p hp hp1 hp2 Finset.mem_product.mp
    obtain ⟨hl1, hu1⟩ := (sourceRatioIndices_mem hN.le p.1).mp hp1
    obtain ⟨hl2, hu2⟩ := (sourceRatioIndices_mem hN.le p.2).mp hp2
    exact ⟨by exact_mod_cast hN.trans hl1, by exact_mod_cast hN.trans hl2,
      hl1, hu1, hl2, hu2⟩
  have hSmallBound : (∑ p ∈ Psmall, F p) ≤ C₁ * S := by
    have h := hSmall T 0 N (by linarith) hN Psmall (by
      pm_4040
      exact ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩) W
        (by intro t ht; simpa only [zero_add] using hBase t ht) hAbsSep
    pm_446 h.trans_eq S
  have hLargeBound : (∑ p ∈ Plarge, F p) ≤ C₂ * T ^ ε * B := by
    have h := hLarge T N Plarge W hT hN hTN hNT (by
      pm_4040
      exact ⟨h1, h2, hl1, hu1, hl2, hu2, hd⟩) hSep hBase
    pm_446 h.trans_eq B
  have hPartition : (∑ p ∈ P, F p) =
      (∑ p ∈ Psmall, F p) + ∑ p ∈ Plarge, F p := by
    simpa only [Psmall, Plarge, not_lt] using
      (Finset.sum_filter_add_sum_filter_not P (fun p => (pairGcd p : ℝ) < N ^ 2 / T) F).symm
  have hRepro' := hRepro N hN a W V ha hV.le hValues hAbsSep
  have hPair : (∑ n ∈ A, ∑ m ∈ A, ‖∑ t ∈ W, phase ((n : ℝ) / m) t‖ ^ 3) =
      ∑ p ∈ P, F p := by
    pm_316 P F Finset.sum_product pairRatio Rat.cast_div Rat.cast_natCast
  rw [hPair, hPartition] at hRepro'
  pm_8509 hC₁le C₁
  pm_8509 hC₂le C₂
  pm_7058 hCpow C
  have hCoeffSmall : C₀ * C₁ * S ≤ C * T ^ ε * S :=
    mul_le_mul_of_nonneg_right (hC₁le.trans hCpow) hS
  have hCoeffLarge : C₀ * C₂ * T ^ ε * B ≤ C * T ^ ε * B := by gcongr
  calc
    _ ≤ C₀ * (C₁ * S + C₂ * T ^ ε * B) :=
      hRepro'.trans (mul_le_mul_of_nonneg_left (add_le_add hSmallBound hLargeBound) hC₀.le)
    _ ≤ C * T ^ ε * (S + B) := by nlinarith
    _ = _ := rfl

end Montgomery.RationalMoment
