module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayFrequency
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass

/-! # Combined kinetic Fourier decay on bounded intervals

Frequency decay on the first half and killing decay on the second half give the
source rate `1 + |ξ|^(2/3)`. Constants are chosen before the interval position,
coefficients, query times, starting velocity, and frequency.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Real bounds for the two factors imply a real product bound for composition. -/
theorem interval_composition_real_bound {a c F G : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hhead : TV (intervalFourierKernel K σ r hσr ξ v) ≤ F)
    (htail : ∀ w : PDE.oneDimensionalAxisBox a c,
      TV (intervalFourierKernel K r τ hrτ ξ w) ≤ G) :
    TV (intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤ F * G := by
  have hfinite : ∀ s t hst w,
      totalVariationNorm (intervalFourierKernel K s t hst ξ w) ≠ ⊤ :=
    fun s t hst w => ne_of_lt
      ((intervalFourierKernel_totalVariation_le_one K s t hst ξ w).trans_lt
        ENNReal.one_lt_top)
  have hhead' : totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) ≤
      ENNReal.ofReal F := by
    rw [← ENNReal.ofReal_toReal (hfinite σ r hσr v)]
    exact ENNReal.ofReal_le_ofReal hhead
  have htail' : (⨆ w : PDE.oneDimensionalAxisBox a c,
      totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_toReal (hfinite r τ hrτ w)]
    exact ENNReal.ofReal_le_ofReal (htail w)
  have h := (intervalFourierKernel_totalVariation_composition K hJ hcomp hcov
    σ r τ hσr hrτ ξ v).trans (mul_le_mul' hhead' htail')
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hF,
    ENNReal.toReal_ofReal hG] using ht

/-- The case-I decay estimate, conditional only on Hörmander's theorem and Lieberman's Theorem 5.14.
-/
theorem interval_fourier_decay
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (E : IntervalEvolution lam Lam m Lb),
      E.length = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (v ξ : PDE.Vec 1)
      (hv : v ∈ movingDomain (E.domain) stationary σ)
      (ν : ComplexMeasure (PDE.Vec 1)),
      IsFourierProjection E.kernel (movingQuery σ τ hστ v 0 hv) ξ ν →
      TV ν ≤ C * Real.exp (-k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
  obtain ⟨C₁, k₁, hC₁, hk₁, hfreq⟩ := interval_frequency_decay
    lam Lam m Lb hlam hlamLam hm hmLb
  obtain ⟨C₂, k₂, hC₂, hk₂, hkill⟩ := interval_fourier_killing_decay
    lam Lam m Lb length hlam hlength
  let k := min k₁ k₂ / 2
  have hk : 0 < k := div_pos (lt_min hk₁ hk₂) (by norm_num)
  refine ⟨C₁ * C₂, k, mul_pos hC₁ hC₂, hk, ?_⟩
  intro E hlen σ τ hστ v ξ hv ν hν
  let w : E.domain :=
    ⟨v, by simpa only [movingDomain_stationary] using hv⟩
  have heq : ν = intervalFourierKernel E.kernel σ τ hστ ξ w := by
    apply VectorMeasure.ext
    intro A hA
    exact (hν A hA).trans ((intervalFourierKernel_spec E.kernel σ τ hστ ξ w A hA).symm)
  rw [heq]
  let r := (σ + τ) / 2
  have hσr : σ ≤ r := by dsimp [r]; linarith only [hστ]
  have hrτ : r ≤ τ := by dsimp [r]; linarith only [hστ]
  have hc := (E.clauses).2.2
  have hb := interval_composition_real_bound E.kernel E.measurableSet E.realizes.2.2.2 hc σ r τ hσr hrτ ξ w
    (mul_pos hC₁ (Real.exp_pos _)).le (mul_pos hC₂ (Real.exp_pos _)).le
    (hfreq E σ r hσr ξ w)
    (fun w' => hkill E hlen r τ hrτ ξ w')
  have hexp : -k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
      -k₂ * (τ - r) ≤ -k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
    have hN : 0 ≤ PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) := Real.rpow_nonneg
      (by unfold PDE.vecEuclideanNorm; exact Real.sqrt_nonneg _) _
    have htime : 0 ≤ τ - σ := sub_nonneg.mpr hστ
    have h1 := mul_le_mul_of_nonneg_right (min_le_left k₁ k₂)
      (mul_nonneg htime hN)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right k₁ k₂) htime
    dsimp only [r, k]
    nlinarith only [h1, h2]
  have hmul :
      (C₁ * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) *
        (C₂ * Real.exp (-k₂ * (τ - r))) =
      (C₁ * C₂) * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
        -k₂ * (τ - r)) := by rw [Real.exp_add]; ring
  rw [hmul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (mul_pos hC₁ hC₂).le)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
