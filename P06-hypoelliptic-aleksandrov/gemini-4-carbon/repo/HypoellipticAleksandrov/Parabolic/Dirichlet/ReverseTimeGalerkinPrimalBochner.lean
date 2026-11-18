module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

/-- A continuous spatial Sobolev curve satisfying the stated value and
gradient bounds has a reverse-time Bochner `L²(V)` representative with the
corresponding constant-one graph-norm energy bound. -/
theorem exists_reverseTimeL2V_of_continuousOn_energy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) {T lam B G : ℝ}
    (hT : 0 < T) (hlam : 0 < lam)
    (w : ℝ → H10HilbertGraph hΩ)
    (hw : ContinuousOn w (Set.Icc 0 T))
    (hvalue : ∀ t ∈ Set.Icc 0 T,
      ‖valueCLM hΩ (w t)‖ ^ 2 ≤ B)
    (hgradient : lam * ∫ t in Set.Ioc 0 T,
      ‖gradientCLM hΩ (w t)‖ ^ 2 ≤ G) :
    ∃ W : ReverseTimeL2V hΩ T,
      W =ᵐ[reverseTimeVolume T] w ∧
      ‖W‖ ^ 2 ≤ T * B + G / lam := by
  let W := reverseTimeL2OfContinuousOn T w hw
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  have hBnonneg : 0 ≤ B := by
    exact (sq_nonneg (‖valueCLM hΩ (w 0)‖)).trans
      (hvalue 0 ⟨le_rfl, le_of_lt hT⟩)
  have hgradientIntegralNonneg :
      0 ≤ ∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2 := by
    exact integral_nonneg fun _ => sq_nonneg _
  have hGnonneg : 0 ≤ G := by
    exact (mul_nonneg (le_of_lt hlam) hgradientIntegralNonneg).trans hgradient
  have hvalueLp :=
    memLp_two_reverseTime_of_continuousOn T _ ((valueCLM hΩ).continuous.comp_continuousOn hw)
  have hgradientLp :=
    memLp_two_reverseTime_of_continuousOn T _ ((gradientCLM hΩ).continuous.comp_continuousOn hw)
  have hvalueIntegrable :
      Integrable (fun t => ‖valueCLM hΩ (w t)‖ ^ 2) (reverseTimeVolume T) := by
    exact hvalueLp.integrable_norm_pow (by norm_num)
  have hgradientIntegrable :
      Integrable (fun t => ‖gradientCLM hΩ (w t)‖ ^ 2) (reverseTimeVolume T) := by
    exact hgradientLp.integrable_norm_pow (by norm_num)
  have hvalueBound :
      (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤ T * B := by
    calc
      (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤
          ∫ _ : ℝ, B ∂reverseTimeVolume T := by
        apply integral_mono_ae hvalueIntegrable (integrable_const B)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hvalue t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      _ = T * B := by
        rw [integral_const, smul_eq_mul, reverseTimeVolume_real_univ T hT]
  have hgradientIoc :
      (∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) =
        ∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2 := by
    exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
  have hgradientBound :
      (∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤ G / lam := by
    rw [hgradientIoc]
    apply (le_div_iff₀ hlam).mpr
    simpa only [mul_comm] using hgradient
  have hnorm :
      (∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T) = ‖W‖ ^ 2 := by
    simpa only [W, reverseTimeL2OfContinuousOn] using
      integral_norm_sq_eq_norm_sq_toLp w (memLp_two_reverseTime_of_continuousOn T w hw)
  refine ⟨W, coeFn_reverseTimeL2OfContinuousOn T w hw, ?_⟩
  calc
    ‖W‖ ^ 2 = ∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T := hnorm.symm
    _ = ∫ t, (‖valueCLM hΩ (w t)‖ ^ 2 + ‖gradientCLM hΩ (w t)‖ ^ 2)
        ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards with t
      exact norm_sq_h10HilbertGraph hΩ (w t)
    _ = (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) +
        ∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T :=
      integral_add hvalueIntegrable hgradientIntegrable
    _ ≤ T * B + G / lam := add_le_add hvalueBound hgradientBound



variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The canonical quotient-valued representative of the selected raw
reverse-time Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimal
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ReverseTimeL2V hΩ (r₁ - r₀) :=
  reverseTimeL2OfContinuousOn (r₁ - r₀)
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)

/-- The uniform value-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalValueBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  gronwallBound (‖initial‖ ^ 2)
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2)
    (r₁ - r₀)

/-- The uniform gradient-energy bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalGradientBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  ‖initial‖ ^ 2 +
    (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1) * (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) * (r₁ - r₀)

/-- The uniform squared `L²(V)` bound for every selected Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalNormSqBound
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  (r₁ - r₀) *
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
    reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial / lam

/-- The explicit uniform radius associated with the squared Bochner bound. -/
noncomputable def reverseTimeGalerkinPrimalRadius
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  Real.sqrt
    (reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)

/-- The canonical quotient representative agrees almost everywhere with its
selected raw Galerkin curve. -/
theorem ae_reverseTimeGalerkinPrimal_eq_raw
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial =ᵐ[
        reverseTimeVolume (r₁ - r₀)]
      reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := by
  exact coeFn_reverseTimeL2OfContinuousOn (r₁ - r₀)
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)

private theorem reverseTimeGalerkinPrimal_value_energy_le_bound
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM hΩ
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  have hK : 0 ≤ 2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1 := by
    nlinarith [reverseTimeGalerkinPrimalK_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos]
  calc
    ‖valueCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
        gronwallBound (‖initial‖ ^ 2)
          (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
          (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) t :=
      reverseTimeGalerkinPrimal_value_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t ht
    _ ≤ gronwallBound (‖initial‖ ^ 2)
          (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
          (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) (r₁ - r₀) :=
      gronwallBound_mono (sq_nonneg ‖initial‖) (sq_nonneg _ ) hK ht.2
    _ = reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := rfl

private theorem reverseTimeGalerkinPrimal_gradient_energy_le_bound
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    lam * ∫ τ in Set.Ioc 0 (r₁ - r₀),
      ‖gradientCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)‖ ^ 2 ≤
      reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  simpa only [reverseTimeGalerkinPrimalGradientBound,
    reverseTimeGalerkinPrimalValueBound] using
    (reverseTimeGalerkinPrimal_gradient_energy r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial (r₁ - r₀)
      ⟨sub_nonneg.mpr h₀₁.le, le_rfl⟩)

/-- The canonical reverse-time Galerkin class satisfies the explicit uniform
squared Bochner bound. -/
theorem norm_sq_reverseTimeGalerkinPrimal_le
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ^ 2 ≤
      reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  obtain ⟨W, hWraw, hWbound⟩ := exists_reverseTimeL2V_of_continuousOn_energy hΩ (sub_pos.mpr h₀₁) hlam
    (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (continuousOn_reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_value_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimal_gradient_energy_le_bound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
  have hW : W = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := by
    apply MeasureTheory.Lp.ext
    exact hWraw.trans
      (ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial).symm
  calc
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ^ 2 = ‖W‖ ^ 2 := by
      rw [hW]
    _ ≤ (r₁ - r₀) *
          reverseTimeGalerkinPrimalValueBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial +
        reverseTimeGalerkinPrimalGradientBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial / lam := hWbound
    _ = reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := rfl

private theorem reverseTimeGalerkinPrimalNormSqBound_nonneg
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    0 ≤ reverseTimeGalerkinPrimalNormSqBound r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  exact (sq_nonneg ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos 0 initial‖).trans
    (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial 0)

/-- The canonical reverse-time Galerkin class lies in its explicit uniform
Bochner radius. -/
theorem norm_reverseTimeGalerkinPrimal_le_radius
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N : ℕ) :
    ‖reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial‖ ≤
      reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  apply (Real.le_sqrt (norm_nonneg _)
    (reverseTimeGalerkinPrimalNormSqBound_nonneg r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)).mpr
  simpa using
    (norm_sq_reverseTimeGalerkinPrimal_le r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial N)

end HypoellipticAleksandrov.Parabolic.Dirichlet

