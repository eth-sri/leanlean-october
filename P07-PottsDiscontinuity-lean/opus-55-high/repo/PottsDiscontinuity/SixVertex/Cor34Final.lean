module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34FinalAnalytic
public import PottsDiscontinuity.SixVertex.Cor34FinalNormalization
public import PottsDiscontinuity.SixVertex.Cor34FinalWave

/-! # Corollary 3.4: identify the Theorem 2.3 family with the Perron root -/

public section

open Filter Topology Set Matrix
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- Corollary 3.4 for an analytic Theorem 2.3 family, for either eigenvalue branch `E` with
normalized form `En`. -/
theorem cor34_final_generic {N n : ℕ} {d₀ d₁ : ℝ} {p P : ℝ → Fin n → ℝ}
    (E : ℝ → (Fin n → ℝ) → ℂ) (En : ℝ → (Fin n → ℝ) → ℂ) (Z : Fin n → Prop)
    (hd₀₁ : d₀ < d₁) (hd₁ : d₁ < -1) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (hZ : ∀ d ≤ d₀, ∀ j, Z j ∨ p d j ≠ 0)
    (hBE : ∀ d ≤ d₀, Bethe.DiscreteBetheEquation d N n (p d))
    (hformula : ∀ d ≤ d₀, p d = P (1 / d))
    (hPanalytic : AnalyticAt ℝ P 0)
    (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hscale : ∀ ε, -1 < ε → ε < 0 → ∀ p, En ε p = ((-ε / 2 : ℝ) : ℂ) ^ n * E √(2 - 2 / ε) p)
    (hblock : ∀ c Δ, 2 < c → BetheAnsatz.anisotropy c = Δ → ∀ p ∈ Bethe.S_n n,
      Bethe.DiscreteBetheEquation Δ N n p →
      (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ BetheAnsatz.blockWave Δ p =
        E c p • BetheAnsatz.blockWave Δ p)
    (htend : Tendsto (fun ε => En ε (P ε)) (𝓝 0) (𝓝 (pfRoot (infinityBlock N n) : ℂ)))
    (han : ∀ d < d₁, (∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (Z j ∨ p d j ≠ 0)) →
      AnalyticAt ℝ (fun t => En (1 / t) (p t)) d) :
    ∀ d ≤ d₀, pfRoot (transferBlock N √(2 - 2 * d) n) = (E √(2 - 2 * d) (p d)).re := by
  obtain ⟨d₂, hd₀, hd₂₁, hreg⟩ := cor34_final_exists_regular_cutoff Z hd₀₁ hpAnalytic hp hZ
  have hd₂ := hd₂₁.trans hd₁
  have hinv2 (d : ℝ) : 2 / (1 / d) = 2 * d := by rw [div_div_eq_mul_div, div_one]
  have hInv : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have hEig : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      cor34_normalizedBlockWave (N := N) ε (P ε) ≠ 0 ∧
        (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ
            cor34_normalizedBlockWave ε (P ε) =
          En ε (P ε) • cor34_normalizedBlockWave ε (P ε) := by
    filter_upwards [cor34_final_eventually_normalizedBlockWave_ne_zero hPanalytic.continuousAt hP0
      hNpos hbound, hInv, self_mem_nhdsWithin] with ε hw hΔ hε
    have hεlo : -1 < ε := by have := mul_one_div_cancel hε.ne; nlinarith
    have hBEε := hBE _ hΔ
    have hS := hp _ hΔ
    rw [hformula _ hΔ, one_div_one_div] at hBEε hS
    have hc : 2 < √(2 - 2 / ε) := (Real.lt_sqrt (by norm_num)).2
      (by rw [show 2 / ε = 2 * (1 / ε) by ring]; linarith)
    have hAni : BetheAnsatz.anisotropy √(2 - 2 / ε) = 1 / ε := by
      grind [BetheAnsatz.anisotropy]
    have hmatrixR := cor34_final_normalizedTransferBlock_scale (N := N) (n := n) hε
    have hmatrixC :
        (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
          (((-ε / 2 : ℝ) : ℂ) ^ n) • (transferBlock N √(2 - 2 / ε) n).map (algebraMap ℝ ℂ) := by
      aesop
    refine ⟨hw, ?_⟩
    rw [hmatrixC, cor34_final_normalizedBlockWave_scale hε, hscale ε hεlo hε]
    exact cor34_final_scale_eigen_equation (hblock _ _ hc hAni _ hS hBEε)
  have hphys : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
      E √(2 - 2 / ε) (P ε) = pfRoot (transferBlock N √(2 - 2 / ε) n) := by
    filter_upwards [cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound htend hEig,
      self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))]
      with ε h hε hεlo
    exact cor34_unscale (by omega) hε h (hscale ε hεlo hε _)
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] (0 : ℝ)) := by
    simpa using tendsto_inv_atBot_nhdsLT_zero
  obtain ⟨b, hb⟩ := eventually_atBot.mp (hinv.eventually hphys)
  have key (d : ℝ) (hd : d < -1) :
      ((-2 * d : ℝ) : ℂ) ^ n * En (1 / d) (p d) = E √(2 - 2 * d) (p d) := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast (by linarith : d ≠ 0)
    rw [hscale _ ((lt_div_iff_of_neg (by linarith)).2 (by linarith)) (one_div_neg.2 (by linarith)),
      ← mul_assoc, ← mul_pow, hinv2, show ((-2 * d : ℝ) : ℂ) * ((-(1 / d) / 2 : ℝ) : ℂ) = 1 by
        push_cast; field_simp, one_pow, one_mul]
  have hiden := cor34_identity_theorem_extension
    (f := fun d => pfRoot (transferBlock N √(2 - 2 * d) n))
    (g := fun d => (((-2 * d : ℝ) : ℂ) ^ n * En (1 / d) (p d)).re)
    (fun d hd => cor34_analyticAt_pfRoot_transferBlock (by omega) (lt_trans hd hd₂))
    (fun d hd => (Complex.reCLM.analyticAt _).comp (((cor34_final_analyticAt_ofReal
      (by fun_prop : AnalyticAt ℝ (fun t : ℝ => -2 * t) d)).pow n).mul (han d (lt_trans hd hd₂₁) (hreg d hd))))
    isPreconnected_Iio isOpen_Iio nonempty_Iio
    (Iio_subset_Iio ((min_le_left d₀ b).trans hd₀.le)) (fun d hd => by
      have h := hb d (le_of_lt (lt_of_lt_of_le hd (min_le_right _ _)))
      rw [hinv2, ← hformula d (le_of_lt (lt_of_lt_of_le hd (min_le_left _ _)))] at h
      simp only
      rw [key d (by linarith [min_le_left d₀ b, hd.out]), h, Complex.ofReal_re])
  intro d hd
  have := hiden (show d < d₂ by linarith)
  simp only at this
  rw [this, key d (by linarith)]

end PottsDiscontinuity.SixVertex
