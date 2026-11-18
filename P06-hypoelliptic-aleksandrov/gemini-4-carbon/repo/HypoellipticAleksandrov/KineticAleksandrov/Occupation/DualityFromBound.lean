module

public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen
public import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Set SectionTwo HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory
section

open MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}

/-- Unit `L¹` and `Lʳ` bounds imply a uniform bound at every intervening exponent. -/
theorem memLp_intermediate_of_unit_bounds {r γ : ℝ} (hr : 1 < r)
    (hγ : 1 ≤ γ) (hγr : γ ≤ r) (h1 : MemLp g 1 μ)
    (hrLp : MemLp g (ENNReal.ofReal r) μ)
    (h1n : (eLpNorm g 1 μ).toReal ≤ 1)
    (hrn : (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ 1) :
    MemLp g (ENNReal.ofReal γ) μ ∧
      (eLpNorm g (ENNReal.ofReal γ) μ).toReal ≤ 2 := by
  have hγpos : 0 < γ := zero_lt_one.trans_le hγ
  have hrpos := zero_lt_one.trans hr
  have hgr : Integrable (fun x => ‖g x‖ ^ r) μ := by
    simpa only [ENNReal.toReal_ofReal hrpos.le] using
      (memLp_one_iff_integrable.1 (hrLp.norm_rpow
        (ne_of_gt (ENNReal.ofReal_pos.2 hrpos)) ENNReal.ofReal_ne_top))
  have hg1 := (memLp_one_iff_integrable.1 h1).norm
  have hpoint (x : α) : ‖g x‖ ^ γ ≤ ‖g x‖ + ‖g x‖ ^ r := by
    by_cases hx : ‖g x‖ ≤ 1
    · exact (Real.rpow_le_self_of_le_one (norm_nonneg _) hx hγ).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hγr).trans
        (le_add_of_nonneg_left (norm_nonneg _))
  have hgγ : Integrable (fun x => ‖g x‖ ^ γ) μ :=
    (hg1.add hgr).mono' ((Real.continuous_rpow_const hγpos.le).comp_aestronglyMeasurable h1.aestronglyMeasurable.norm) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hpoint x)
  have hγLp : MemLp g (ENNReal.ofReal γ) μ := by
    apply (integrable_norm_rpow_iff h1.aestronglyMeasurable
      (ne_of_gt (ENNReal.ofReal_pos.2 hγpos)) ENNReal.ofReal_ne_top).1
    simpa only [ENNReal.toReal_ofReal hγpos.le] using hgγ
  have hint : (∫ x, ‖g x‖ ^ γ ∂μ) ≤ 2 := by
    calc
      _ ≤ ∫ x, ‖g x‖ + ‖g x‖ ^ r ∂μ := integral_mono hgγ (hg1.add hgr) hpoint
      _ = (eLpNorm g 1 μ).toReal +
          (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r := by
        rw [integral_add hg1 hgr,
          ← PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hrpos hrLp]
        have heq := PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
          (p := 1) zero_lt_one (by simpa using h1)
        simpa using congrArg (fun a => a + (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r)
          heq.symm
      _ ≤ 2 := by
        have hb : (eLpNorm g (ENNReal.ofReal r) μ).toReal ^ r ≤ 1 := by
          simpa using Real.rpow_le_rpow ENNReal.toReal_nonneg hrn hrpos.le
        linarith
  refine ⟨hγLp, ?_⟩
  have htwo : (2 : ℝ) ≤ 2 ^ γ := Real.self_le_rpow_of_one_le (by norm_num) hγ
  have hn : (eLpNorm g (ENNReal.ofReal γ) μ).toReal ^ γ ≤ 2 ^ γ := by
    rw [(PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hγpos hγLp)]
    exact hint.trans htwo
  exact (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg (by norm_num) hγpos).mp hn

/-- Multiplication by a scalar scales the real `Lp` norm by its absolute value. -/
theorem toReal_eLpNorm_const_mul (c : ℝ) (f : α → ℝ) (p : ℝ≥0∞) (μ : Measure α) :
    (eLpNorm (fun x => c * f x) p μ).toReal = |c| * (eLpNorm f p μ).toReal := by
  change (eLpNorm (c • f) p μ).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]

/-- Two endpoint bounds of size `A` give an intermediate bound of size `2A`, even
when the reference measure has infinite mass. -/
theorem memLp_intermediate_of_bounds {r γ A : ℝ} (hr : 1 < r)
    (hγ : 1 ≤ γ) (hγr : γ ≤ r) (hA : 0 ≤ A) (h1 : MemLp g 1 μ)
    (hrLp : MemLp g (ENNReal.ofReal r) μ)
    (h1n : (eLpNorm g 1 μ).toReal ≤ A)
    (hrn : (eLpNorm g (ENNReal.ofReal r) μ).toReal ≤ A) :
    MemLp g (ENNReal.ofReal γ) μ ∧
      (eLpNorm g (ENNReal.ofReal γ) μ).toReal ≤ 2 * A := by
  rcases hA.eq_or_lt with hAz | hAp
  · have hzero : eLpNorm g 1 μ = 0 := by
      apply (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm
        (h1n.trans (by rw [← hAz])) ENNReal.toReal_nonneg) |>.resolve_right
        h1.eLpNorm_ne_top
    have hn : eLpNorm g (ENNReal.ofReal γ) μ = 0 := by
      rw [eLpNorm_congr_ae ((eLpNorm_eq_zero_iff one_ne_zero).mp hzero)]
      simp
    refine ⟨by rw [memLp_iff, hn]; exact ENNReal.zero_lt_top, ?_⟩
    rw [hn, ENNReal.toReal_zero, ← hAz, mul_zero]
  · let f : α → ℝ := fun x => A⁻¹ * g x
    have hf1 : MemLp f 1 μ := h1.const_mul _
    have hfr : MemLp f (ENNReal.ofReal r) μ := hrLp.const_mul _
    have hfn (p : ℝ≥0∞) (hn : (eLpNorm g p μ).toReal ≤ A) :
        (eLpNorm f p μ).toReal ≤ 1 := by
      rw [toReal_eLpNorm_const_mul, abs_of_pos (inv_pos.mpr hAp)]
      exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hAp.le)).trans_eq
        (inv_mul_cancel₀ hAp.ne')
    obtain ⟨hfγ, hfγn⟩ := memLp_intermediate_of_unit_bounds hr hγ hγr hf1 hfr
      (hfn 1 h1n) (hfn _ hrn)
    have heq : (fun x => A * f x) = g := by
      funext x
      simp [f, ← mul_assoc, mul_inv_cancel₀ hAp.ne']
    have hγLp : MemLp g (ENNReal.ofReal γ) μ := heq ▸ hfγ.const_mul A
    refine ⟨hγLp, ?_⟩
    rw [← heq, toReal_eLpNorm_const_mul, abs_of_pos hAp]
    exact (mul_le_mul_of_nonneg_left hfγn hAp.le).trans_eq (mul_comm A 2)

end


variable {d : ℕ}

/-- Unit elapsed-time Lebesgue measure is finite. -/
instance unitElapsedVolume_finite : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal (1 : ℝ))) := ⟨by
  rw [elapsedVolume_univ 1 zero_lt_one]
  exact ENNReal.ofReal_lt_top⟩

/-- Pull back the first marginal along the literal unit-time occupation queries. -/
def unitOccupationKernel (K : WholeKernel d) :
    ProbabilityTheory.Kernel (PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) (PDE.Vec d) :=
  K.firstMarginal.comap (fun q => wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0) (by
    apply Measurable.subtype_mk
    change Measurable (fun q : PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ)) =>
      (0, (q.2.1, (q.1, 0))))
    fun_prop)

/-- The pulled-back velocity kernel is finite. -/
instance unitOccupationKernel_finite (K : WholeKernel d) :
    ProbabilityTheory.IsFiniteKernel (unitOccupationKernel K) := by
  unfold unitOccupationKernel MovingFiberKernel.firstMarginal
  infer_instance


/-- The product-kernel measure has mass at most the initial mass. -/
theorem unitOccupationProduct_mass_le (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] :
    ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd
      (unitOccupationKernel K)) univ ≤ ρ univ  := by
  have unitOccupationKernel_mass_le (q : PDE.Vec d × ElapsedTime (ENNReal.ofReal 1)) :
      unitOccupationKernel K q univ ≤ 1 := by
    change K.firstMarginal (wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0) univ ≤ 1
    rw [K.firstMarginal_apply _ _ MeasurableSet.univ]
    simpa using K.mass_le_one (wholeSpaceQuery 0 q.2.1 q.2.2.1.le q.1 0)
  rw [Measure.compProd_apply MeasurableSet.univ]
  calc
    _ ≤ ∫⁻ q, 1 ∂ρ.prod (elapsedVolume (ENNReal.ofReal 1)) :=
      lintegral_mono fun q => by simpa using unitOccupationKernel_mass_le q
    _ = ρ univ := by
      rw [lintegral_const, one_mul, ← univ_prod_univ, Measure.prod_prod]
      have he : elapsedVolume (ENNReal.ofReal 1) univ = 1 := by
        rw [elapsedVolume_univ 1 zero_lt_one, ENNReal.ofReal_one]
      rw [he, mul_one]

/-- The unprojected product-kernel occupation measure is finite. -/
instance unitOccupationProduct_finite (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] :
    IsFiniteMeasure ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd
      (unitOccupationKernel K)) :=
  ⟨(unitOccupationProduct_mass_le K ρ).trans_lt (measure_lt_top ρ univ)⟩

/-- The unit-time occupation measure, with time and velocity in source order. -/
def unitOccupationMeasure (K : WholeKernel d) (ρ : Measure (PDE.Vec d)) :
    Measure (TimeVelocity d) :=
  ((ρ.prod (elapsedVolume (ENNReal.ofReal (1 : ℝ)))).compProd (unitOccupationKernel K)).map
    (fun q => (q.1.2.1, q.2))

/-- The projected occupation measure is finite for finite initial measures. -/
instance unitOccupationMeasure_finite (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] : IsFiniteMeasure (unitOccupationMeasure K ρ) := by
  unfold unitOccupationMeasure
  infer_instance

/-- Unit-time occupation mass is at most the initial mass. -/
theorem unitOccupationMeasure_mass_le (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] : unitOccupationMeasure K ρ univ ≤ ρ univ := by
  rw [unitOccupationMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
  exact unitOccupationProduct_mass_le K ρ

/-- Positive elapsed time puts the entire occupation measure in the open unit slab. -/
theorem unitOccupationMeasure_compl_slab (K : WholeKernel d) (ρ : Measure (PDE.Vec d)) :
    unitOccupationMeasure K ρ (Ioo (0 : ℝ) 1 ×ˢ univ)ᶜ = 0 := by
  rw [unitOccupationMeasure, Measure.map_apply (by fun_prop)
    ((measurableSet_Ioo.prod MeasurableSet.univ).compl)]
  have he : (fun q : (PDE.Vec d × ElapsedTime (ENNReal.ofReal 1)) × PDE.Vec d =>
      (q.1.2.1, q.2)) ⁻¹'
      (Ioo 0 1 ×ˢ univ)ᶜ = ∅ := by
    ext q
    simp
    exact ⟨q.1.2.2.1, ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp q.1.2.2.2)⟩
  rw [he, measure_empty]

/-- Projected occupation integration is the full iterated first-marginal characterization. -/
theorem integral_unitOccupationMeasure (K : WholeKernel d) (ρ : Measure (PDE.Vec d))
    [IsFiniteMeasure ρ] (φ : TimeVelocity d → ℝ) (hφ : Measurable φ)
    (hφb : ∃ M : ℝ, ∀ q, |φ q| ≤ M) :
    (∫ q, φ q ∂unitOccupationMeasure K ρ) =
      ∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal (1 : ℝ)),
        ∫ w, φ (τ.1, w) ∂K.firstMarginal
          (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
        ∂elapsedVolume (ENNReal.ofReal (1 : ℝ)) ∂ρ := by
  obtain ⟨M, hM⟩ := hφb
  let ψ : (PDE.Vec d × ElapsedTime (ENNReal.ofReal 1)) × PDE.Vec d → ℝ :=
    fun q => φ (q.1.2.1, q.2)
  have hψ : Measurable ψ := hφ.comp (by fun_prop)
  have hi : Integrable ψ ((ρ.prod (elapsedVolume (ENNReal.ofReal 1))).compProd
      (unitOccupationKernel K)) :=
    (integrable_const M).mono' hψ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa using hM _)
  rw [unitOccupationMeasure, integral_map (by fun_prop) hφ.aestronglyMeasurable]
  change (∫ q, ψ q ∂_) = _
  rw [Measure.integral_compProd hi]
  exact (integral_prod _ hi.integral_compProd).trans (by
    simp [ProbabilityTheory.Kernel.prodMkLeft_apply, unitOccupationKernel, ProbabilityTheory.Kernel.comap_apply, ψ])



variable {d : ℕ}

/-- Smooth-source occupation integration is integration of the zero-time potential. -/
theorem integral_unitOccupationMeasure_eq_potential (K : WholeKernel d)
    (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ] (F : TimeVelocity d → ℝ)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    (∫ q, F q ∂unitOccupationMeasure K ρ) =
      ∫ v, parabolicDuhamelPotential K MeasurableSet.univ 1 F (0, v) ∂ρ := by
  have hΩm : MeasurableSet (wholeSpace d) := MeasurableSet.univ
  have hFm := hFs.continuous.measurable
  obtain ⟨M, hM⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  rw [integral_unitOccupationMeasure K ρ F hFm ⟨M, fun q => by simpa using hM q⟩]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  change (∫ τ : ElapsedTime (ENNReal.ofReal 1),
    ∫ w, F (τ.1, w) ∂K.firstMarginal
      (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
    ∂elapsedVolume (ENNReal.ofReal 1)) =
    parabolicDuhamelPotential K hΩm 1 F (0, v)
  have hint (τ : ElapsedTime (ENNReal.ofReal 1)) :
      (∫ w, F (τ.1, w) ∂K.firstMarginal
        (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)) =
      parabolicDuhamelIntegrand K MeasurableSet.univ F (0, v) τ.1 := by
    rw [parabolicDuhamelIntegrand_of_valid K MeasurableSet.univ F (0, v) τ.1
      ⟨τ.2.1.le, by rw [movingDomain_wholeSpace]; exact mem_univ v⟩,
      parabolicSourceIntegral_eq_master K MeasurableSet.univ F 0 τ.1 τ.2.1.le
        ⟨v, by rw [movingDomain_wholeSpace]; exact mem_univ v⟩
        (hFm.comp (measurable_const.prodMk measurable_id))]
    unfold MovingFiberKernel.firstMarginal
    rw [ProbabilityTheory.Kernel.fst_apply,
      integral_map (f := fun w => F (τ.1, w)) measurable_fst.aemeasurable
      (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    simp [parabolicMasterIntegral, wholeSpaceQuery]
  rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
  have htime : Measurable (fun r => parabolicDuhamelIntegrand K
      MeasurableSet.univ F (0, v) r) := by
    exact (measurable_parabolicDuhamelIntegrand K MeasurableSet.univ
      continuous_const F hFm).comp (measurable_const.prodMk measurable_id)
  rw [integral_elapsed_eq 1 zero_lt_one _ htime]
  change (∫ r in Ioo 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r) =
    ∫ r in Ioc 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r
  exact (integral_Ioc_eq_integral_Ioo).symm






variable {d : ℕ}

/-- The exact whole-space bound implies the occupation-duality conclusion.
This derivation is conditional on the stated bound. -/
theorem occupation_duality_of_whole_space_bound
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (hWhole :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (F : TimeVelocity d → ℝ) (_hF0 : ∀ q, 0 ≤ F q)
        (_hFs : ContDiff ℝ (⊤ : ℕ∞) F) (_hFc : HasCompactSupport F)
        (_hFsupp : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ),
        let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
        let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
        (∀ (α : ℝ), 0 ≤ α → α < 1 → ∀ (vStar : PDE.Vec d) (R : ℝ),
          0 < R → R ^ 2 = max 1 (4 * d * Lam) →
          ∃ V : TimeVelocity d → ℝ,
            IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
              (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
              (fun _ => 0) (fun _ => 0) V ∧
            (∀ q ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
              W q ≤ V q + H *
                ((∑ i, (q.2 i - vStar i) ^ 2) + 2 * d * Lam * (1 - q.1)) / R ^ 2) ∧
            (2 * d * Lam * (1 - α)) / R ^ 2 ≤ 1 / 2) ∧
        H ≤ C * parabolicLpNorm d F
    ) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal   := by
  have parabolicLpNorm_eq_slab (F : TimeVelocity d → ℝ) (hF : tsupport F ⊆ Ioo 0 1 ×ˢ univ) :
      parabolicLpNorm d F =
      (eLpNorm F (ENNReal.ofReal
        ((((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1)))
        (volume.restrict (Ioo 0 1 ×ˢ univ))).toReal := by
    have occupation_endpoint_conjugate :
        (((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1) = (d : ℝ) + 1 := by
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    rw [occupation_endpoint_conjugate]
    have he : ENNReal.ofReal ((d : ℝ) + 1) = parabolicExponent d := by
      simp [parabolicExponent, ENNReal.ofReal_add, Nat.cast_nonneg]
    rw [he]
    unfold parabolicLpNorm parabolicELpNorm
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Ioo.prod MeasurableSet.univ), (indicator_eq_self.2 ((Function.support_subset_iff').2 fun q hq => image_eq_zero_of_notMem_tsupport (fun h => hq (hF h))))]
  have occupation_endpoint_gt_one :
      1 < ((d : ℝ) + 1) / d := by
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    exact (lt_div_iff₀ hdR).2 (by linarith)
  obtain ⟨C₀, hC₀, hWhole⟩ := hWhole
  refine ⟨fun _ => 2 * (C₀ + 1), fun _ _ _ => by positivity, ?_⟩
  intro B hB S K hreal hP ρ _
  let M := (ρ univ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have htest : ∀ F : TimeVelocity d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ → (∀ q, 0 ≤ F q) →
      (∫ q, F q ∂unitOccupationMeasure K ρ) ≤ (C₀ * M) *
        (eLpNorm F (ENNReal.ofReal
          ((((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1)))
          (volume.restrict (Ioo 0 1 ×ˢ univ))).toReal := by
    intro F hFs hFc hFsupp hF0
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
    have hb (v : PDE.Vec d) : W (0, v) ≤ C₀ * parabolicLpNorm d F :=
      (le_csSup hpot.2.1 ⟨(0, v), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩).trans ((hWhole B hB S K hreal hP F hF0 hFs hFc hFsupp).2)
    have hn (v : PDE.Vec d) : ‖W (0, v)‖ ≤ C₀ * parabolicLpNorm d F := by
      rw [Real.norm_of_nonneg (hpot.1 (0, v))]
      exact hb v
    rw [integral_unitOccupationMeasure_eq_potential K ρ F hFs hFc]
    have hle :=
      (le_abs_self _).trans (by simpa [measureReal_def] using (norm_integral_le_of_norm_le_const (μ := ρ) (Filter.Eventually.of_forall hn)))
    rw [parabolicLpNorm_eq_slab F hFsupp] at hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hle
  obtain ⟨_hac, g, hgm, hg0, hgi, hgr, hgrn, hgmass, hgpair⟩ :=
    exists_density_of_smooth_tests volume (unitOccupationMeasure K ρ)
      (isOpen_Ioo.prod isOpen_univ) (unitOccupationMeasure_compl_slab K ρ)
      (occupation_endpoint_gt_one) (mul_nonneg hC₀ hM) htest
  have h1 :=
    memLp_one_iff_integrable.2 hgi
  have hnormMass : (eLpNorm g 1 (volume.restrict (Ioo 0 1 ×ˢ univ))).toReal =
      (unitOccupationMeasure K ρ univ).toReal := by
    have he := PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
      (p := 1) zero_lt_one (by simpa using h1)
    simp only [ENNReal.ofReal_one, Real.rpow_one] at he
    have heq : (fun q => ‖g q‖) = g := by
      funext q
      exact Real.norm_of_nonneg (hg0 q)
    rw [heq, hgmass] at he
    exact he
  have h1n : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ M := by
    rw [hnormMass]
    exact ENNReal.toReal_mono (measure_ne_top ρ univ) (unitOccupationMeasure_mass_le K ρ)
  refine ⟨g, ⟨hgm, hg0, ?_⟩, ?_⟩
  · intro φ
    obtain ⟨A, _hA, hφA⟩ := φ.exists_bound
    exact (hgpair φ).trans (integral_unitOccupationMeasure K ρ φ φ.measurable ⟨A, hφA⟩)
  · intro γ hγ hγr
    have hA : 0 ≤ (C₀ + 1) * M := mul_nonneg (by positivity) hM
    have h1A : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤
        (C₀ + 1) * M := h1n.trans (by nlinarith)
    have hrA : (eLpNorm g (ENNReal.ofReal (((d : ℝ) + 1) / d))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ (C₀ + 1) * M :=
      hgrn.trans (by nlinarith)
    obtain ⟨hgγ, hgγn⟩ := memLp_intermediate_of_bounds (occupation_endpoint_gt_one)
      hγ hγr hA h1 hgr h1A hrA
    refine ⟨hgγ, ?_⟩
    change (eLpNorm g (ENNReal.ofReal γ)
      (volume.restrict (Ioo 0 1 ×ˢ univ))).toReal ≤ (2 * (C₀ + 1)) * M
    simpa only [mul_assoc] using hgγn

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

