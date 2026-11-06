module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourier
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabReconstruction

/-! # The interval slab density theorem

Occupation, killing and frequency decay are discharged by their proved interval
lemmas. The only hypotheses are the explicit analytic inputs.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- Uniform interval slab density with exponential killing. -/
theorem interval_slab_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length)
    (q : ℝ) (hq : 1 < q) (hq2 : q < 2) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.VectorField 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution _ stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ T : ℝ), 0 < T →
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        ENNReal.ofReal C * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
  obtain ⟨C, k, hk, hfourier⟩ := interval_slab_fourier hH hLE
    lam Lam m Lb length hlam hlamLam hm hmLb hlength
  refine ⟨(slabConstant 1 q C : ℝ) + 1, k * (q - 1),
    by positivity, mul_pos hk (by linarith), ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
  obtain ⟨g, hgm, hgE, hgb, f, _hfm, hf, hfb⟩ :=
    hfourier a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
  have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq2


  obtain ⟨G, hGm, hGE, hbd⟩ := killed_slab_reconstruction C k K σ μ Γ hΓ hq hq2 hT
    g hgm hgE (fun r h1 h2 => by

      simpa only [interval_slab_beta] using hgb r h1 (by norm_num [slabGamma0] at h2; exact h2)) f hf (by
      have he : slabBeta 1 (slabGamma 1 q) - 3 / 2 =
          3 / (2 * slabGamma 1 q) - 2 := by rw [interval_slab_beta]; ring
      simpa only [he] using
        (hfb (slabGamma 1 q) ((slab_gamma_one_lt  hq hqd).le) (by
            have := (slab_q_lt_gamma  hq hqd).2.le
            norm_num [slabGamma0] at this
            exact this)).2)
  refine ⟨G, hGm, hGE, hbd.trans ?_⟩
  apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
