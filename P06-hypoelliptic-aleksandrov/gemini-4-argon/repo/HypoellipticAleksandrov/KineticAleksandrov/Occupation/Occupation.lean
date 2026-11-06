module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityConsumer
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Duality
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityEvolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingBundle
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingCharacterization
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingKernel
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingTerminal
import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-! # Occupation assembly and the exact slab consumer -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo MeasureTheory Set
open scoped ENNReal
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder ProbabilityTheory
open Scaling ProbabilityTheory
variable {d : ℕ}

/- Forget the scaled representative after scaling the unit-time duality theorem. -/
theorem occupation
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ → ℝ,
      (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
      ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
        (S : WholeFamily d) (K : WholeKernel d)
        (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
        (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K)
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
        (σ₀ T : ℝ) (_hT : 0 < T),
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K σ₀ T ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
            occupationLpNorm T γ g ≤
              C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
  have hDuality := (occupation_duality hH hd lam Lam hlam hLam)
  obtain ⟨C, hC0, hscale⟩ :
      ∃ C : ℝ → ℝ,
            (∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d → 0 ≤ C γ) ∧
            ∀ (B : CoefficientField d) (_hB : IsSectionTwoCoefficient lam Lam B)
              (S : WholeFamily d) (K : WholeKernel d)
              (_hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
                MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
              (_hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
                MeasurableSet.univ (zIndependentCoefficient B) K)
              (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ]
              (σ₀ T : ℝ) (hT : 0 < T),
              let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.2 hT⟩
              let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
              let Ktilde := Scaling.KineticAffineScaling.pushKernel
                (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K
              let ρtilde := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
              ∃ (g gtilde : TimeVelocity d → ℝ),
                IsOccupationDensity K σ₀ T ρ g ∧
                IsOccupationDensity Ktilde 0 1 ρtilde gtilde ∧
                (∀ q, g q = T ^ (-(d : ℝ) / 2) *
                  gtilde (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) ∧
                ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
                  MemLp g (ENNReal.ofReal γ)
                    (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ∧
                  MemLp gtilde (ENNReal.ofReal γ)
                    (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
                  occupationLpNorm T γ g =
                    T ^ occupationBeta d γ * occupationLpNorm 1 γ gtilde ∧
                  occupationLpNorm T γ g ≤
                    C γ * (ρ univ).toReal * T ^ occupationBeta d γ := by
    obtain ⟨C, hC0, hunit⟩ := hDuality
    refine ⟨C, hC0, ?_⟩
    intro B hB S K hreal hP ρ _ σ₀ T hT
    dsimp only
    let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
    let Φ := Scaling.KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    let Kt := Scaling.KineticAffineScaling.pushKernel
      (Scaling.KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    let ρt := ρ.map (fun v => (Real.sqrt T)⁻¹ • v)
    have hBt := scaledCoefficient_sectionTwo lam Lam B hB σ₀ 0 r
    have hr := Scaling.realizes_ofRadius_wholeSpace σ₀ 0 0 r hreal
    have hPt : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r))
        (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace
          (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r)) K) := by
      intro _hBz
      obtain ⟨Q, -, h2, h3, h4, h5, h6, -, h8, h9, h10⟩ := hP (fun _ _ _ _ => rfl)
      let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
      let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
      refine ⟨occupation_pushParabolicFamily Φ Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro σ τ hστ y z
        apply (wholeSpacePositionEquiv d τ).measurableEmbedding.map_injective
        have ha := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt
          MeasurableSet.univ σ τ hστ (positionStateZero (wholeSpace d) (fun _ => 0) σ y)
        have hb := MovingFiberKernel.map_fiberFirstMarginal_eq_firstMarginal Kt
          MeasurableSet.univ σ τ hστ (evolutionStateOfPosition (wholeSpace d) (fun _ => 0) σ y z)
        have hi := occupation_scaled_firstMarginal_independent Φ K hP σ τ hστ y.1 0 z
        exact ha.trans (hi.trans hb.symm)
      · exact occupation_pushParabolicFamily_endpoint Φ Q h2
      · exact occupation_pushParabolicFamily_positive Φ Q h3
      · exact occupation_pushParabolicFamily_contraction Φ Q h4
      · exact occupation_pushParabolicFamily_composition Φ Q h5
      · intro σ τ hστ y f
        let eσ := occupation_positionEquiv Φ σ
        let eτ := occupation_positionEquiv Φ τ
        let f0 := occupation_borelComap eτ.symm eτ.symm.measurable f
        have heval := h6 (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) (eσ y) f0
        have hc := occupation_parabolicMarginal_conjugate Φ K hP σ τ hστ y
        have hi := congrArg (fun μ => ∫ x, f x ∂μ) hc
        have hm := eτ.symm.measurableEmbedding.integral_map (fun x => f x)
          (μ := parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time τ)
            (Φ.time_le_iff.mpr hστ) (eσ y))
        exact heval.trans (hi.trans hm).symm
      · exact occupation_parabolicMarginal_measurable Kt
      · intro σ
        have hc := occupation_parabolicKernel_conjugate Φ K hP σ σ le_rfl
        exact hc.trans ((congrArg (kernelConj (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ σ)) (h8 (Φ.time σ))).trans (kernelConj_id (occupation_positionEquiv Φ σ)))
      · intro σ s τ hσs hsτ
        have hc := occupation_parabolicKernel_conjugate Φ K hP σ τ (hσs.trans hsτ)
        have hcs := occupation_parabolicKernel_conjugate Φ K hP σ s hσs
        have hct := occupation_parabolicKernel_conjugate Φ K hP s τ hsτ
        exact hc.trans ((congrArg (kernelConj (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ τ)) (h9 (Φ.time σ) (Φ.time s) (Φ.time τ) (Φ.time_le_iff.mpr hσs) (Φ.time_le_iff.mpr hsτ))).trans ((kernelConj_comp (occupation_positionEquiv Φ σ) (occupation_positionEquiv Φ s) (occupation_positionEquiv Φ τ) (parabolicMarginalKernel K MeasurableSet.univ (Φ.time σ) (Φ.time s) (Φ.time_le_iff.mpr hσs)) (parabolicMarginalKernel K MeasurableSet.univ (Φ.time s) (Φ.time τ) (Φ.time_le_iff.mpr hsτ))).trans
          (congrArg₂ (fun A B => A ∘ₖ B) hct.symm hcs.symm)))
      · exact occupation_scalarTerminalClause_scale σ₀ r B Q h10
    obtain ⟨gt, hgt, hnorm⟩ := hunit (scaledCoefficient B σ₀ 0 r) hBt
      (Scaling.fiberOperator Kt MeasurableSet.univ) Kt hr hPt ρt
    let g := fun q => T ^ (-(d : ℝ) / 2) *
      gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)
    have hg := isOccupationDensity_scaled K σ₀ hT ρ gt hgt
    have hgeq : ∀ q, g q = T ^ (-(d : ℝ) / 2) *
        gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) := by
      intro q
      dsimp [g]
      congr 2
      apply Prod.ext
      · change 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1 = q.1 / T
        rw [inv_pow, Real.sq_sqrt hT.le]
        simp only [zero_add, inv_mul_eq_div]
      · simp only [parabolicAffine, zero_add]
    refine ⟨g, gt, hg, hgt, hgeq, ?_⟩
    intro γ hγ0 hγ1
    obtain ⟨hmem, hbd⟩ := hnorm γ hγ0 hγ1
    have hmemg : MemLp g (ENNReal.ofReal γ)
        (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) := by
      apply occupation_memLp_pullback 0 0 (inv_pos.mpr (Real.sqrt_pos.mpr hT))
      simpa only [occupation_inverseScaling_image_slab hT] using hmem
    have hnormeq : occupationLpNorm T γ g =
        T ^ occupationBeta d γ * occupationLpNorm 1 γ gt := by
      rw [show g = fun q => T ^ (-(d : ℝ) / 2) *
        gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2) from funext hgeq]
      have hγ := (zero_le_one.trans hγ0)
      have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
      have hsq := Real.sq_sqrt hT.le
      have hf : (fun q : TimeVelocity d =>
          T ^ (-(d : ℝ) / 2) * gt (q.1 / T, (Real.sqrt T)⁻¹ • q.2)) =
          fun q => T ^ (-(d : ℝ) / 2) *
            gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q) := by
        funext q
        congr 2
        apply Prod.ext
        · change q.1 / T = 0 + (Real.sqrt T)⁻¹ ^ 2 * q.1
          rw [inv_pow, hsq]
          simp only [zero_add, inv_mul_eq_div]
        · simp only [parabolicAffine, zero_add]
      unfold occupationLpNorm
      rw [hf, occupation_eLpNorm_pullback 0 0 (inv_pos.mpr hs),
        occupation_inverseScaling_image_slab hT, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ← ENNReal.toReal_rpow, Real.enorm_of_nonneg (Real.rpow_nonneg hT.le _),
        ENNReal.toReal_ofReal (Real.rpow_nonneg hT.le _),
        ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hs.le) _)),
        ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hγ,
        occupation_scaling_factor hT]
    have hmass : (ρt univ).toReal = (ρ univ).toReal := by
      have hm : Measurable (fun v : PDE.Vec d => (Real.sqrt T)⁻¹ • v) :=
        (continuous_const_smul (Real.sqrt T)⁻¹).measurable
      change (ρ.map (fun v => (Real.sqrt T)⁻¹ • v) univ).toReal = _
      rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ]
    refine ⟨hmemg, hmem, hnormeq, ?_⟩
    rw [hnormeq]
    rw [hmass] at hbd
    have hh := mul_le_mul_of_nonneg_left hbd
      (Real.rpow_nonneg hT.le (occupationBeta d γ))
    calc
      _ ≤ T ^ occupationBeta d γ * (C γ * (ρ univ).toReal) := hh
      _ = _ := by ring
  refine ⟨C, hC0, ?_⟩
  intro B hB S K hreal hP ρ _ σ₀ T hT
  obtain ⟨g, gt, hg, -, -, hb⟩ := hscale B hB S K hreal hP ρ σ₀ T hT
  refine ⟨g, hg, ?_⟩
  intro γ hγ0 hγ1
  exact ⟨(hb γ hγ0 hγ1).1, (hb γ hγ0 hγ1).2.2.2⟩

/- The occupation family, relative to the terminal evolution statement and Hörmander's theorem. -/
theorem parabolicOccupationFamily_holds (hEvol : TerminalEvolutionStatement)
    (hH : HormanderHypoellipticityStatement)
    (hd : 0 < d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    Green.ParabolicOccupationFamily d lam Lam := by
  obtain ⟨C, hC0, hocc⟩ := occupation hH hd lam Lam hlam hLam
  refine ⟨C, ?_⟩
  intro B hB S K hreal
  refine ⟨hC0, ?_⟩
  intro ρ _ σ₀ T hT
  have hP : HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K := by
    obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
    have hb := identityDrift_bounds d
    exact (evolution_clauses_of_realization hEvol d hd lam Lam 1 1 hB.1 hB.2.1
      one_pos le_rfl (wholeSpace d) (fun _ => 0) (zIndependentCoefficient B)
      (identityDrift d) (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d)
      hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2 S K hreal).2.2
  obtain ⟨g, hg, hb⟩ := hocc B hB S K hreal hP ρ σ₀ T hT
  refine ⟨g, (isOccupationDensity_iff_slabOccupationDensity K σ₀ T ρ g).mp hg, ?_⟩
  intro γ hγ0 hγ1
  exact hb γ hγ0 hγ1

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
