module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayFrequency
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass

/-! # Combined kinetic Fourier decay on bounded intervals

Frequency decay on the first half and killing decay on the second half give the
source rate `1 + |ξ|^(2/3)`. Constants are chosen before the interval position,
coefficients, query times, starting velocity, and frequency.
-/

@[expose] public section
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
  have hfinite  :=
    fun s t hst w => ne_of_lt
      ((intervalFourierKernel_totalVariation_le_one K s t hst ξ w).trans_lt
        ENNReal.one_lt_top)
  have hhead' : totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) ≤
      ENNReal.ofReal F := by
    rw [← ENNReal.ofReal_toReal (hfinite σ r hσr v)]
    simp_all
  have htail' : (⨆ w : PDE.oneDimensionalAxisBox a c,
      totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤ ENNReal.ofReal G := by
    apply iSup_le
    intro w
    rw [← ENNReal.ofReal_toReal (hfinite r τ hrτ w)]
    aesop
  have h := (intervalFourierKernel_totalVariation_composition K hJ hcomp hcov
    σ r τ hσr hrτ ξ v).trans (mul_le_mul' hhead' htail')
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h
  simp_all

/-- The case-I decay estimate, conditional only on Hörmander's theorem and Lieberman's Theorem 5.14.
-/
theorem interval_fourier_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (v ξ : PDE.Vec 1)
      (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
      (ν : ComplexMeasure (PDE.Vec 1)),
      IsFourierProjection K (movingQuery σ τ hστ v 0 hv) ξ ν →
      TV ν ≤ C * Real.exp (-k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
  obtain ⟨C₁, k₁, hC₁, hk₁, hfreq⟩ := interval_frequency_decay
    hH hLE lam Lam m Lb hlam hlamLam hm hmLb
  obtain ⟨C₂, k₂, hC₂, hk₂, hkill⟩ := interval_fourier_killing_decay
    hH hLE lam Lam m Lb length hlam hlength
  let k := min k₁ k₂ / 2
  have hk : 0 < k := div_pos (lt_min hk₁ hk₂) (by norm_num)
  refine ⟨C₁ * C₂, k, mul_pos hC₁ hC₂, hk, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ τ hστ v ξ hv ν hν
  let w : PDE.oneDimensionalAxisBox a c :=
    ⟨v, by simpa using hv⟩
  have heq : ν = intervalFourierKernel K σ τ hστ ξ w := by
    apply VectorMeasure.ext
    intro E hE
    exact (hν E hE).trans ((intervalFourierKernel_spec K σ τ hστ ξ w E hE).symm)
  rw [heq]
  let r := (σ + τ) / 2
  have hσr : σ ≤ r := by grind
  have hrτ : r ≤ τ := by grind
  have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
  have hb := interval_composition_real_bound K hJ hr.2.2.2 hc σ r τ hσr hrτ ξ w
    (mul_pos hC₁ (Real.exp_pos _)).le (mul_pos hC₂ (Real.exp_pos _)).le
    (hfreq a c hac B b hs hJ S K hr σ r hσr ξ w)
    (fun w' => hkill a c hac B b hs hJ S K hr hlen r τ hrτ ξ w')
  have hexp : -k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
      -k₂ * (τ - r) ≤ -k * (τ - σ) *
        (1 + PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
    have hN : 0 ≤ PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) := Real.rpow_nonneg
      (Real.sqrt_nonneg _) _
    have htime : 0 ≤ τ - σ := sub_nonneg.mpr hστ
    have h1 := mul_le_mul_of_nonneg_right (min_le_left k₁ k₂)
      (mul_nonneg htime hN)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right k₁ k₂) htime
    grind
  have hmul :
      (C₁ * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) *
        (C₂ * Real.exp (-k₂ * (τ - r))) =
      (C₁ * C₂) * Real.exp (-k₁ * (r - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) +
        -k₂ * (τ - r)) := by rw [Real.exp_add]; ring
  rw [hmul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (mul_pos hC₁ hC₂).le)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
