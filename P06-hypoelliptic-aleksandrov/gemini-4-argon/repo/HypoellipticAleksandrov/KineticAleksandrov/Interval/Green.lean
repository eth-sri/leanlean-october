module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenMass
import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenNorm
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Slab
import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockScaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayFrequency
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourier
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierAssembly
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionFibers
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionOccupation
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierGreen
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabReconstruction
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierGreen
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionMarginal
import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockInterior
import HypoellipticAleksandrov.KineticAleksandrov.Decay.CommonSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhase
import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.CorridorSelection
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
import HypoellipticAleksandrov.KineticAleksandrov.Decay.OppositePaths
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockRetentionLift
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Block
import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockInterior
import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Scaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayIteration
import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationDensity
import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationDomination
import HypoellipticAleksandrov.KineticAleksandrov.Interval.OccupationTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionCovariance
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation

/-! # The interval infinite-horizon Green theorem

Killed slab densities are glued and logarithmically averaged over all positive times.
Constants depend only on the structural parameters, interval length and exponent.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal
open scoped ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.Scaling HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Occupation

/- The interval Green theorem: uniform density norm and finite infinite-horizon mass. -/
theorem interval_green_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length)
    (q ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ : ℝ),
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ = (greenLebesgue 1).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ ∧
      Γ univ < ⊤ := by
  obtain ⟨C, k, hC, _hk, hnorm⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ : ℝ),
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ = (greenLebesgue 1).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ := by
    have hq' : q < 2 := by linarith
    have hq0 : 0 < q := by linarith
    have hδ : 0 < 3 - 2 * q := by linarith
    obtain ⟨A, k, _hA, hk, hslab⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ T : ℝ), 0 < T →
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        ENNReal.ofReal C * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
      obtain ⟨C, k, hk, hfourier⟩ : ∃ C : ℝ → ℝ≥0, ∃ k : ℝ, 0 < k ∧
        ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
        SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
        ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
          (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
          (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
        RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
          (zIndependentCoefficient B) b S K →
        c - a = length → ∀ (σ T : ℝ), 0 < T →
        ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
        ∃ g : SlabBase 1 → ℝ≥0∞, Measurable g ∧
          (slabMeasure 1 T Γ).fst = (slabBase 1 T).withDensity g ∧
          (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → eLpNorm g (ENNReal.ofReal γ) (slabBase 1 T) ≤
            (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2))) ∧
          ∃ f : PDE.Vec 1 → SlabBase 1 → ℂ, Measurable (Function.uncurry f) ∧
          (∀ ξ, Integrable (f ξ) (slabBase 1 T) ∧
            ∀ E : Set (SlabBase 1), MeasurableSet E → ∫ y in E, f ξ y ∂slabBase 1 T =
              ∫ p in {p : GreenCarrier 1 | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
                Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
          ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
            (∀ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
              (C γ : ℝ≥0∞) * μ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2) *
                Real.exp (-k * T * (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
            ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                ∫⁻ ξ, eLpNorm (f ξ) (ENNReal.ofReal γ) (slabBase 1 T) ≤
              (C γ : ℝ≥0∞) * μ univ *
                ENNReal.ofReal (T ^ (3 / (2 * γ) - 2) * Real.exp (-k * T)) := by
        obtain ⟨Co, hoc⟩ : ∃ C : ℝ → ℝ, ∀ (m Lb : ℝ), 0 < m → m ≤ Lb → ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1), SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b → ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary) (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary), RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ (zIndependentCoefficient B) b S K → OccupationBoundedBy (intervalExtension hJ K) C := by
          obtain ⟨C, hC, hocc⟩ : ∃ C : ℝ → ℝ, (∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → 0 ≤ C γ) ∧
            ∀ (m Lb : ℝ), 0 < m → m ≤ Lb →
            ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
            SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
            ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
              (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
              (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
            RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
              (zIndependentCoefficient B) b S K →
            ∀ (σ T : ℝ), 0 < T →
            ∀ (ρ : Measure (PDE.oneDimensionalAxisBox a c)) [IsFiniteMeasure ρ],
            ∃ g : TimeVelocity 1 → ℝ, Measurable g ∧ (∀ p, 0 ≤ g p) ∧
              (∀ φ : BoundedBorel (TimeVelocity 1),
                (∫ p, φ p * g p ∂volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) =
                ∫ v, ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
                  ∂P K hJ (scalarQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v.1
                    (by simpa only [movingDomain_stationary] using v.2))
                  ∂elapsedVolume (ENNReal.ofReal T) ∂ρ) ∧
              ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 →
                MemLp g (ENNReal.ofReal γ)
                  (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ∧
                eLpNorm g (ENNReal.ofReal γ)
                  (volume.restrict (Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c)) ≤
                  ENNReal.ofReal (C γ) * ρ univ * ENNReal.ofReal (T ^ (3 / (2 * γ) - 1 / 2)) := by
            obtain ⟨C, hC, hocc⟩ := occupation hH (d := 1) (by norm_num)
              lam Lam hlam hlamLam
            refine ⟨C, fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num; exact hγ2), ?_⟩
            intro m Lb _hm _hmLb a c hac B b hs hJ S K hr σ T hT ρ _
            have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
            have hsetting : SourceSetting lam Lam 1 1 (univ : Set (PDE.Vec 1)) B (identityDrift 1) :=
              ⟨hs.1, identityDrift_smooth 1, zero_lt_one, le_rfl, identityDrift_bounds 1,
                Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
            obtain ⟨Sw, Kw, hrw, _, hpw, _⟩ :=
              exists_unitBlock_evolution (exists_terminalEvolution_of_classical hLE hH)
                (by norm_num) lam Lam 1 1 univ B (identityDrift 1) hsetting
                (wholeSpace 1) (fun _ => 0) (wholeSpace_admissible 1) (zeroCurve_piecewiseC1 1)
            obtain ⟨gw, hgw, hgwLp⟩ := hocc B hs.1 Sw Kw hrw hpw (ρ.map Subtype.val) σ T hT
            have hgwi : Integrable gw (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) :=
              memLp_one_iff_integrable.1 (by simpa using (hgwLp 1 le_rfl (by norm_num)).1)
            have hgwSlab : Green.SlabOccupationDensity Kw σ T (ρ.map Subtype.val) gw :=
              (isOccupationDensity_iff_slabOccupationDensity Kw σ T (ρ.map Subtype.val) gw).mp hgw
            have hdom : intervalOccupationMeasure σ T K ρ ≤
                (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)).withDensity
                  (fun p => ENNReal.ofReal (gw p)) := by
              have hB := hs.1
              let R : Set (TimeVelocity 1) := Ioo 0 T ×ˢ univ
              have hR : MeasurableSet R := measurableSet_Ioo.prod MeasurableSet.univ
              have hs : (intervalOccupationMeasure σ T K ρ).restrict R =
                  intervalOccupationMeasure σ T K ρ :=
                Measure.restrict_eq_self_of_ae_mem (by
                  rw [ae_iff]; exact intervalOccupationMeasure_compl_slab σ T hT K ρ)
              have hsub : ∀ A : Set (TimeVelocity 1), MeasurableSet A → A ⊆ R →
                  intervalOccupationMeasure σ T K ρ A ≤
                    ∫⁻ p in A, ENNReal.ofReal (gw p) := by
                intro A hA hAR
                have hm : Measurable (fun v : PDE.Vec 1 =>
                    ∫⁻ t in Ioo 0 T, occupationKernel Kw σ t v {w | (t, w) ∈ A}) :=
                  ((measurable_occupationKernel_section Kw σ hA).comp measurable_swap).lintegral_prod_right'
                rw [occupation_set_identity Kw σ T hT (ρ.map Subtype.val) gw hgwSlab hgwi hA hAR,
                  lintegral_map hm measurable_subtype_coe]
                rw [intervalOccupationMeasure_apply σ T K ρ A hA]
                apply lintegral_mono
                intro v
                dsimp only
                rw [← lintegral_elapsed_finite T hT]
                apply lintegral_mono
                intro t
                have hst : σ < σ + t.1 := lt_add_of_pos_right _ t.2.1
                have hv : v.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ := by
                  simpa only [movingDomain_stationary] using v.2
                have ht := interval_parabolic_le_whole hac hst B hB hJ K hp Kw hpw v.1 hv
                have he := interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1) hst.le v.1 0 hv
                change K.firstMarginal (movingQuery σ (σ + t.1) hst.le v.1 0 hv) _ ≤ _
                rw [he]
                dsimp only
                rw [occupationKernel_of_nonneg Kw σ t.1 t.2.1.le]
                exact Measure.le_iff'.1 ht _
              apply Measure.le_iff.2
              intro A hA
              rw [← hs, Measure.restrict_apply hA, withDensity_apply _ hA]
              calc
                _ ≤ ∫⁻ p in A ∩ R, ENNReal.ofReal (gw p) :=
                  hsub _ (hA.inter hR) inter_subset_right
                _ = _ := by rw [Measure.restrict_restrict hA]
            let U : Set (TimeVelocity 1) := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
            have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
            have hνU : (intervalOccupationMeasure σ T K ρ).restrict U =
                intervalOccupationMeasure σ T K ρ :=
              Measure.restrict_eq_self_of_ae_mem (by
                rw [ae_iff]; exact intervalOccupationMeasure_compl_region σ T hT hJ K ρ)
            have hdomU : intervalOccupationMeasure σ T K ρ ≤
                (volume.restrict U).withDensity (fun p => ENNReal.ofReal (gw p)) := by
              have h := Measure.restrict_mono_measure hdom U
              rw [hνU, restrict_withDensity hU, Measure.restrict_restrict_of_subset
                (show U ⊆ Ioo (0 : ℝ) T ×ˢ univ from prod_mono Subset.rfl (subset_univ _))] at h
              exact h
            have := intervalOccupationMeasure_finite σ T hT K ρ
            obtain ⟨g, hgm, hg0, _hgi, hgle, hpair⟩ := exists_real_density_of_le_withDensity
              (volume.restrict U) (intervalOccupationMeasure σ T K ρ) gw hgw.1 hgw.2.1 hdomU
            refine ⟨g, hgm, hg0, ?_, ?_⟩
            · intro φ
              rw [hpair φ]
              obtain ⟨M, _, hM⟩ := φ.exists_bound
              rw [integral_intervalOccupationMeasure σ T hT K ρ φ φ.measurable ⟨M, hM⟩]
              apply integral_congr_ae
              refine Filter.Eventually.of_forall fun v => ?_
              apply integral_congr_ae
              refine Filter.Eventually.of_forall fun t => ?_
              dsimp only
              rw [interval_firstMarginal_eq_parabolic hJ K B hp σ (σ + t.1)
                (le_add_of_nonneg_right t.2.1.le) v.1 0]
            · intro γ hγ1 hγ2
              have hw := hgwLp γ hγ1 (by norm_num; exact hγ2)
              have hmeasure : volume.restrict U ≤ volume.restrict (Ioo (0 : ℝ) T ×ˢ univ) :=
                Measure.restrict_mono_set _ (prod_mono Subset.rfl (subset_univ _))
              have hgwU := hw.1.mono_measure hmeasure
              have hnorm : ∀ᵐ p ∂volume.restrict U, ‖g p‖ ≤ ‖gw p‖ := by
                filter_upwards [hgle] with p hp
                simpa only [Real.norm_of_nonneg (hg0 p), Real.norm_of_nonneg (hgw.2.1 p)] using hp
              have hgLp := hgwU.mono hgm.aestronglyMeasurable hnorm
              refine ⟨hgLp, ?_⟩
              have hle : eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) ≤
                  eLpNorm gw (ENNReal.ofReal γ) (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) :=
                (eLpNorm_mono_ae hgm.aestronglyMeasurable hnorm).trans
                  (eLpNorm_mono_measure gw hmeasure)
              have hbound : eLpNorm gw (ENNReal.ofReal γ)
                  (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ≤
                  ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2)) := by
                apply (ENNReal.toReal_le_toReal hw.1.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
                have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ (3 / (2 * γ) - 1 / 2) := by
                  exact mul_nonneg (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
                    ENNReal.toReal_nonneg) (Real.rpow_nonneg hT.le _)
                rw [ENNReal.toReal_ofReal hpos]
                have hm : (ρ.map Subtype.val) univ = ρ univ :=
                  Measure.map_apply measurable_subtype_coe MeasurableSet.univ |>.trans (by
                    rw [preimage_univ])
                simpa only [occupationLpNorm, occupationBeta, Nat.cast_one, hm,
                  show (1 : ℝ) + 2 = 3 from by norm_num] using hw.2
              apply hle.trans
              convert hbound using 1
              rw [ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 (by norm_num; exact hγ2))
                ENNReal.toReal_nonneg), ENNReal.ofReal_mul (hC γ hγ1 (by norm_num; exact hγ2)),
                ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
          refine ⟨C, ?_⟩
          intro m Lb hm hmLb a c hac B b hs hJ S K hr
          refine ⟨fun γ hγ1 hγ2 => hC γ hγ1 (by norm_num [slabGamma0] at hγ2; exact hγ2), ?_⟩
          intro ρ _ σ T hT
          let ρj : Measure (PDE.oneDimensionalAxisBox a c) := Measure.comap Subtype.val ρ
          have hρj : ρj univ ≤ ρ univ := by
            rw [(MeasurableEmbedding.subtype_coe hJ).comap_apply ρ univ]
            exact measure_mono (subset_univ _)
          have : IsFiniteMeasure ρj := ⟨hρj.trans_lt (measure_lt_top ρ univ)⟩
          obtain ⟨g, hgm, hg0, hchar, hb⟩ :=
            hocc m Lb hm hmLb a c hac B b hs hJ S K hr σ T hT ρj
          have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
          let U := Ioo 0 T ×ˢ PDE.oneDimensionalAxisBox a c
          let gw := U.indicator g
          have hU : MeasurableSet U := measurableSet_Ioo.prod hJ
          have hUR : U ⊆ Ioo (0 : ℝ) T ×ˢ univ := prod_mono Subset.rfl (subset_univ _)
          have hgw : Measurable gw := hgm.indicator hU
          have hgw0 : ∀ p, 0 ≤ gw p := fun p => by
            by_cases hp : p ∈ U
            · simpa only [gw, indicator_of_mem hp] using hg0 p
            · simp only [gw, indicator_of_notMem hp, le_refl]
          refine ⟨gw, ⟨hgw, hgw0, ?_⟩, ?_⟩
          · intro φ
            have hfun : (fun p => φ p * gw p) = U.indicator (fun p => φ p * g p) := by
              funext p
              by_cases hp : p ∈ U <;> simp [gw, hp]
            rw [hfun, integral_indicator hU, Measure.restrict_restrict_of_subset hUR, hchar φ]
            let F : PDE.Vec 1 → ℝ := fun v =>
              ∫ t : ElapsedTime (ENNReal.ofReal T), ∫ w, φ (t.1, w)
                ∂(intervalExtension hJ K).firstMarginal
                  (wholeSpaceQuery σ (σ + t.1) (le_add_of_nonneg_right t.2.1.le) v 0)
                ∂elapsedVolume (ENNReal.ofReal T)
            have hFzero : ∀ v, v ∉ PDE.oneDimensionalAxisBox a c → F v = 0 := by
              intro v hv
              dsimp only [F]
              simp_rw [intervalExtension_first_outside hJ K σ _ _ v hv]
              simp only [integral_zero_measure, integral_zero]
            change _ = ∫ v, F v ∂ρ
            rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFzero,
              ← integral_subtype_comap hJ F]
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun v => ?_
            dsimp only [F]
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun t => ?_
            dsimp only
            have _h_xinl_0 (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (K) (σ : ℝ) (τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) : (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v.1 0) = K.firstMarginal (movingQuery σ τ hστ v.1 0 (by simpa only [movingDomain_stationary] using v.2)) := by
              unfold MovingFiberKernel.firstMarginal
              rw [ProbabilityTheory.Kernel.fst_apply, ProbabilityTheory.Kernel.fst_apply]
              congr 1
              change intervalExtensionMaster hJ K (intervalQueryInclusion
                (movingQuery σ τ hστ v.1 0
                  (by simpa only [movingDomain_stationary] using v.2))) = _
              exact intervalExtensionMaster_inside hJ K _
            rw [_h_xinl_0,
              interval_firstMarginal_eq_parabolic hJ K B hp]
          · intro γ hγ1 hγ2
            have hγ2' : γ ≤ 2 := by norm_num [slabGamma0] at hγ2; exact hγ2
            obtain ⟨hgLp, hgBound⟩ := hb γ hγ1 hγ2'
            have hnorm : eLpNorm gw (ENNReal.ofReal γ)
                (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) =
                eLpNorm g (ENNReal.ofReal γ) (volume.restrict U) := by
              dsimp only [gw]
              rw [eLpNorm_indicator_eq_eLpNorm_restrict hU,
                Measure.restrict_restrict_of_subset hUR]
            have hgwLp : MemLp gw (ENNReal.ofReal γ)
                (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) := by
              change eLpNorm gw _ _ < ⊤
              rw [hnorm]
              exact hgLp.eLpNorm_lt_top
            refine ⟨hgwLp, ?_⟩
            have hbd : eLpNorm gw (ENNReal.ofReal γ)
                (volume.restrict (Ioo (0 : ℝ) T ×ˢ univ)) ≤
                ENNReal.ofReal (C γ * (ρ univ).toReal * T ^ slabBeta 1 γ) := by
              rw [hnorm]
              have hB := hgBound.trans (mul_le_mul'
                (mul_le_mul' le_rfl hρj) le_rfl)
              have hβ : slabBeta 1 γ = 3 / (2 * γ) - 1 / 2 := by
                norm_num [slabBeta]
              rw [hβ, ENNReal.ofReal_mul (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg),
                ENNReal.ofReal_mul (hC γ hγ1 hγ2'),
                ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
              exact hB
            have hpos : 0 ≤ C γ * (ρ univ).toReal * T ^ slabBeta 1 γ :=
              mul_nonneg (mul_nonneg (hC γ hγ1 hγ2') ENNReal.toReal_nonneg)
                (Real.rpow_nonneg hT.le _)
            simpa only [ENNReal.toReal_ofReal hpos] using
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
        obtain ⟨Cd, kd, hCd, hkd, hdec⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
        ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
        SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
        ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
          (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
          (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
        RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
          (zIndependentCoefficient B) b S K →
        c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1),
        totalVariationNorm (fourierKernel (intervalExtension hJ K) σ τ hστ ξ v) ≤
          ENNReal.ofReal (C * Real.exp (-k * (τ - σ) *
            (1 + PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) := by
          obtain ⟨C, k, hC, hk, hdec⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
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
            obtain ⟨C₁, k₁, hC₁, hk₁, hfreq⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
                ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
                SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
                ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
                (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
                (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
                RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
                  (zIndependentCoefficient B) b S K →
                ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
                (v : PDE.oneDimensionalAxisBox a c),
                TV (intervalFourierKernel K σ τ hστ ξ v) ≤
                  C * Real.exp (-k * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
              obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ : ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧ ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1), SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b → ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary) (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary), RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ (zIndependentCoefficient B) b S K → ∀ (ξ : PDE.Vec 1), ξ ≠ 0 → ∀ (σ : ℝ) (v : PDE.oneDimensionalAxisBox a c), ∀ (ht : σ ≤ σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))), TV (intervalFourierKernel K σ (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v) ≤ 1 - δ := by
                obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ : ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
                    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
                    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
                    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
                    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
                    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
                    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
                      (zIndependentCoefficient B) b S K →
                    ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
                    ∀ (σ : ℝ) (v : PDE.Vec 1)
                    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
                    (hL : σ ≤ σ + L) (ν : ComplexMeasure (PDE.Vec 1)),
                    IsFourierProjection K (movingQuery σ (σ + L) hL v 0 hv) ξ ν → TV ν ≤ 1 - δ := by
                  obtain ⟨δ₁, hδ₁, hδ₁one, hi⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
                      ∀ (a c : ℝ) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
                      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
                      ∀ (hD : MeasurableSet (PDE.oneDimensionalAxisBox a c))
                      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
                      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
                      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hD
                        (zIndependentCoefficient B) b S K →
                      IsDomainMonotoneEvolution (PDE.oneDimensionalAxisBox a c) stationary
                        (zIndependentCoefficient B) b K →
                      HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hD
                        (zIndependentCoefficient B) K →
                      ∀ (ξ : PDE.Vec 1), PDE.vecNormSq ξ = 1 →
                      ∀ (σ : ℝ) (v : PDE.Vec 1)
                      (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ),
                      PDE.euclideanBall v (blockOuter Lb) ⊆ PDE.oneDimensionalAxisBox a c →
                      ∀ (hL : σ ≤ σ + blockTime m Lb) (ν : ComplexMeasure (PDE.Vec 1)),
                      IsFourierProjection K (movingQuery σ (σ + blockTime m Lb) hL v 0 hv) ξ ν →
                      TV ν ≤ 1 - δ := by
                    let hEvol := exists_terminalEvolution_of_classical hLE hH
                    have hd : 1 ≤ (1 : ℕ) := by norm_num
                    have hLb : 0 < Lb := hm.trans_le hmLb
                    obtain ⟨Cstar, hC, hcorr⟩ := corridors_retained_dominated 1 hd lam Lam hlam hlamLam
                    obtain ⟨h, q0, hh, hq0, hcommon⟩ :=
                      continued_common_minorant_trimming 1 hd lam Lam hlam hlamLam
                    let δ0 := (3 / 4) * blockMass Cstar m Lb * h * q0
                    have hδ0 : 0 < δ0 := by
                      exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 4)
                        (Real.exp_pos _)) hh) hq0
                    let δ := min δ0 (1 / 2)
                    have hδ : 0 < δ := lt_min hδ0 (by norm_num)
                    have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
                    refine ⟨δ, hδ, hδ1, ?_⟩
                    intro a c B b hsetting hD S K hreal hmono hpar ξ hξ σ v hv hfit hL ν hν
                    let J := PDE.oneDimensionalAxisBox a c
                    let ρ := blockRho Lb
                    let η := blockEta m Lb
                    let s := σ + blockL0 m
                    let T := σ + blockTime m Lb
                    let Ω := PDE.euclideanBall v (4 * ρ)
                    have hρ : 0 < ρ := blockRho_pos hLb
                    have hη : 0 < η := blockEta_pos hm hLb
                    have hηρ : η < ρ := blockEta_lt_rho hLb
                    have hστ : σ ≤ s := le_add_of_nonneg_right (blockL0_pos hm).le
                    have hsT : s ≤ T := by
                      dsimp only [s, T, blockTime]
                      nlinarith only [sq_nonneg ρ]
                    have hsmallfit : Ω ⊆ J :=
                      (PDE.euclideanBall_mono (by positivity : 0 ≤ 4 * ρ)
                        (by dsimp [blockOuter]; linarith : 4 * ρ ≤ blockOuter Lb)).trans hfit
                    have hvJ : v ∈ J := by simpa only [movingDomain_stationary] using hv
                    obtain ⟨α, -, -, hpaths⟩ := exists_opposite_paths m Lb σ hm hmLb
                      J b hsetting.2.1 hsetting.2.2.2.2.1 ξ v hξ hfit
                    let γ1 : ℝ → PDE.Vec 1 := fun _ => v
                    let γ2 : ℝ → PDE.Vec 1 := fun r =>
                      v + (α * tent (blockL0 m) (max 0 (min (blockL0 m) (r - σ)))) • ξ
                    obtain ⟨hγ1, hγ2, hstart1, hstart2, hend1, hend2,
                      hspeed1, hspeed2, htube, hphase⟩ := hpaths
                    change γ1 σ = v at hstart1
                    change γ2 σ = v at hstart2
                    have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec 1) η) :=
                      Or.inr (Or.inl ⟨0, η, hη, rfl⟩)
                    have hΩadm : IsAdmissibleEvolutionDomain Ω :=
                      Or.inr (Or.inl ⟨v, 4 * ρ, mul_pos (by norm_num) hρ, rfl⟩)
                    obtain ⟨S1, K1, hreal1, -, hpar1, -⟩ :=
                      exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting _ γ1 hadm hγ1
                    obtain ⟨S2, K2, hreal2, -, hpar2, -⟩ :=
                      exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting _ γ2 hadm hγ2
                    obtain ⟨S0, K0, hreal0, hmono0, hpar0, -⟩ :=
                      exists_unitBlock_evolution hEvol hd lam Lam m Lb J B b hsetting Ω stationary
                        hΩadm (zeroCurve_piecewiseC1 1)
                    have hv1 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ1 σ := by
                      rw [mem_movingDomain_euclideanBall_iff, hstart1]
                      simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
                        zero_mul, Finset.sum_const_zero]
                      exact sq_pos_of_pos hη
                    have hv2 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ2 σ := by
                      rw [mem_movingDomain_euclideanBall_iff, hstart2]
                      simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
                        zero_mul, Finset.sum_const_zero]
                      exact sq_pos_of_pos hη
                    let q1 := movingQuery σ s hστ v 0 hv1
                    let q2 := movingQuery σ s hστ v 0 hv2
                    let qD := movingQuery σ s hστ v 0 hv
                    let qT := movingQuery σ T hL v 0 hv
                    obtain ⟨-, -, -, -, hsupp1, hsupp2, hmass1, hmass2, hdom⟩ :=
                      hcorr m Lb σ J B b hsetting S K hD hreal hmono γ1 γ2 v 0
                        hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2
                        (fun r => (htube r).1) (fun r => (htube r).2)
                        S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD rfl rfl rfl
                    let μ1 := K1.master q1
                    let μ2 := K2.master q2
                    have hfμ1 : IsFiniteMeasure μ1 := ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
                    have hfμ2 : IsFiniteMeasure μ2 := ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
                    let N1 := ENNReal.ofReal (blockMass Cstar m Lb / (2 * μ1.real univ)) • μ1
                    let N2 := ENNReal.ofReal (blockMass Cstar m Lb / (2 * μ2.real univ)) • μ2
                    have hfN1 : IsFiniteMeasure N1 := by
                      refine ⟨?_⟩
                      rw [Measure.smul_apply, smul_eq_mul]
                      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ1 univ)
                    have hfN2 : IsFiniteMeasure N2 := by
                      refine ⟨?_⟩
                      rw [Measure.smul_apply, smul_eq_mul]
                      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ2 univ)
                    have hN1supp : N1 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
                      rw [Measure.smul_apply, hsupp1, smul_zero]
                    have hN2supp : N2 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
                      rw [Measure.smul_apply, hsupp2, smul_zero]
                    let R1 := N1.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState 1)
                    let R2 := N2.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState 1)
                    have hη4ρ : η ≤ 4 * ρ := by linarith only [hηρ, hρ]
                    obtain ⟨hR1, hmR1, hsupport1⟩ := retained_ball_comap_properties v η (4 * ρ) s
                      hη.le hη4ρ N1 hN1supp
                    obtain ⟨hR2, hmR2, hsupport2⟩ := retained_ball_comap_properties v η (4 * ρ) s
                      hη.le hη4ρ N2 hN2supp
                    have hfR1 : IsFiniteMeasure R1 := inferInstance
                    have hfR2 : IsFiniteMeasure R2 := inferInstance
                    let E1 := continuedMeasure K0 hsT R1
                    let E2 := continuedMeasure K0 hsT R2
                    have hE1 : ∀ A, MeasurableSet A → E1 A =
                        ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1 :=
                      fun A hA => continuedMeasure_apply K0 hsT R1 hA
                    have hE2 : ∀ A, MeasurableSet A → E2 A =
                        ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2 :=
                      fun A hA => continuedMeasure_apply K0 hsT R2 hA
                    let M := K.master qT
                    have hfM : IsFiniteMeasure M := ⟨(K.mass_le_one qT).trans_lt ENNReal.one_lt_top⟩
                    have hcontinued : E1 + E2 ≤ M := by
                      apply continued_measures_dominated J Ω hD (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet
                        B b S K S0 K0 hreal hreal0 hmono hΩadm hsmallfit σ s T hστ hsT qD qT
                        ⟨rfl, rfl⟩ rfl R1 R2 _ E1 E2 hE1 hE2
                      rw [hR1, hR2]
                      exact hdom
                    have hs : s = T - 4 * ρ ^ 2 := by dsimp only [s, T, blockTime]; ring
                    have ha : 0 < blockMass Cstar m Lb / 2 := div_pos (Real.exp_pos _) (by norm_num)
                    have hvΩ : v ∈ movingDomain Ω stationary (T - ρ ^ 2) := by
                      rw [movingDomain_stationary]
                      change PDE.vecNormSq (v - v) < (4 * ρ) ^ 2
                      simpa only [sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
                        zero_mul, Finset.sum_const_zero] using sq_pos_of_pos (mul_pos (by norm_num) hρ)
                    let qlate := scalarQuery (T - ρ ^ 2) T (sub_le_self _ (sq_nonneg ρ)) v hvΩ
                    obtain ⟨-, -, hfloor, F1, F2, hF1, hF2, hFsum, hmap1, hmap2⟩ :=
                      hcommon m Lb J B b hsetting v ρ T hvJ hρ hsmallfit
                        S0 K0 hreal0 hpar0 hmono0 s (blockMass Cstar m Lb / 2) η hs hsT ha hη hηρ
                        R1 R2 hfR1 hfR2 (hmR1.trans hmass1) (hmR2.trans hmass2) hsupport1 hsupport2
                        E1 E2 M hfM hE1 hE2 hcontinued qlate rfl
                    let Θ := ENNReal.ofReal (blockMass Cstar m Lb / 2 * h) •
                      P K0 (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet qlate
                    have hfE1 : IsFiniteMeasure E1 := inferInstance
                    have hfE2 : IsFiniteMeasure E2 := inferInstance
                    have hfF1 : IsFiniteMeasure F1 := isFiniteMeasure_of_le _ hF1
                    have hfF2 : IsFiniteMeasure F2 := isFiniteMeasure_of_le _ hF2
                    obtain ⟨hΦ, -, -, hf1, hf2⟩ := block_continued_phase_error hd lam Lam m Lb Cstar σ
                      J B b hsetting hC ξ v 0 hξ hfit γ1 γ2 hγ1 hγ2 hstart1 hstart2 hend1 hend2
                      (fun r => (htube r).1) (fun r => (htube r).2) hphase
                      S1 K1 S2 K2 S0 K0 hreal1 hreal2 hreal0 hpar1 hpar2 hpar0 q1 q2 rfl rfl
                      R1 R2 hR1 hR2 hsT E1 E2 F1 F2 hE1 hE2 hF1 hF2
                    have hMone : M.real univ ≤ 1 := by
                      simpa only [measureReal_def, ENNReal.toReal_one] using
                        ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one qT)
                    have hmass : blockMass Cstar m Lb * h * q0 / 2 ≤ Θ.real univ := by
                      convert hfloor using 1
                      ring
                    have hphaseν : IsPhaseProjection (phaseCoordinate ξ (0 : PDE.Vec 1)) M ν := by
                      intro A hA
                      exact hν A hA
                    have hcancel := (block_interior_cancellation ξ 0 M F1 F2 Θ (blockMass Cstar m Lb)
                      h q0 _ _ hMone hFsum hmap1 hmap2 hmass hΦ hf1 hf2 ν hphaseν).2
                    exact hcancel.trans (sub_le_sub_left (min_le_left δ0 (1 / 2)) 1)
                  have ht : 0 < blockTime m Lb := by
                    unfold blockTime
                    have h := blockL0_pos hm
                    positivity
                  have hR : 0 < blockOuter Lb := by
                    unfold blockOuter
                    have h := blockRho_pos (hm.trans_le hmLb)
                    positivity
                  let δ₂ := 1 - intervalHeat lam (blockTime m Lb) (blockOuter Lb)
                  have hδ₂ : 0 < δ₂ := sub_pos.mpr (intervalErf_lt_one (by
                    exact div_nonneg hR.le (by positivity)))
                  let δ := min δ₁ (min δ₂ (1 / 2))
                  refine ⟨blockTime m Lb, δ, ht, lt_min hδ₁ (lt_min hδ₂ (by norm_num)),
                    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by norm_num)), ?_⟩
                  intro a c hac B b hs hJ S K hr ξ hξ σ v hv hL ν hν
                  obtain ⟨hmono, hpar, _hcov⟩ := interval_evolution_clauses hH hLE hac B b hs hJ S K hr
                  by_cases hfit : PDE.euclideanBall v (blockOuter Lb) ⊆ PDE.oneDimensionalAxisBox a c
                  · exact (hi a c B b hs hJ S K hr hmono hpar ξ hξ σ v hv hfit hL ν hν).trans
                      (sub_le_sub_left (min_le_left _ _) 1)
                  · have hb : min (v 0 - a) (c - v 0) ≤ blockOuter Lb := by
                      by_contra hn
                      exact hfit (interval_ball_subset_of_distance hR v (lt_of_not_ge hn))
                    have hbound : TV ν ≤ intervalHeat lam (blockTime m Lb) (blockOuter Lb) := by
                        have ht : 0 < blockTime m Lb := by
                          unfold blockTime
                          have h := blockL0_pos hs.2.2.1
                          positivity
                        have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
                        have hkill := interval_killing hH hLE hac B b hs hJ S K hr
                          σ (σ + blockTime m Lb) (lt_add_of_pos_right σ ht) v hv
                        have htv := interval_fourier_tv_le_mass hJ K B hp σ (σ + blockTime m Lb) hL
                          v 0 ξ hv ν hν
                        have hnorm : σ + blockTime m Lb - σ = blockTime m Lb := by ring
                        rw [hnorm] at hkill
                        exact htv.trans (hkill.trans (intervalHeat_mono_distance hs.1.1 ht hb))


                    have hδle : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
                    dsimp only [δ₂] at hδle
                    linarith
                refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
                intro a c hac B b hs hJ S K hr ξ hξ σ v ht
                obtain ⟨hrpos, hr2, hrunit⟩ := frequency_radius_identities hξ
                let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hrpos⟩
                let D := scaledDomain (PDE.oneDimensionalAxisBox a c) v.1 r
                let hmap := mapsDomain_interval a c σ v.1 0 b r
                let hDr := measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v.1 r)
                let K' := KineticAffineScaling.pushKernel hmap K
                let S' := fiberOperator K' hDr
                have hr' :
                    let hmap := mapsDomain_interval a c σ v.1 0 b r
                        let hJr := measurableSet_of_isAdmissibleEvolutionDomain
                          (scaled_interval_admissible hac v.1 r)
                        RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v.1 r)
                          stationary hJr (zIndependentCoefficient (scaledCoefficient B σ v.1 r))
                          (scaledDrift b v.1 r)
                          (fiberOperator (KineticAffineScaling.pushKernel hmap K) hJr)
                          (KineticAffineScaling.pushKernel hmap K) := by
                  let v₀ := v.1
                  have h := KineticAffineScaling.realizes_pushKernel
                    (mapsDomain_interval a c σ v₀ 0 b r)
                    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac)) continuous_const
                    (measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v₀ r)) hr
                  rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift] at h
                  exact h
                have hs' : SourceSetting lam Lam m Lb (scaledDomain (PDE.oneDimensionalAxisBox a c) v.1 r)
                    (scaledCoefficient B σ v.1 r) (scaledDrift b v.1 r) := by
                  let v₀ := v.1
                  rw [scaledDomain_interval]
                  exact sourceSetting_interval (scaled_interval_endpoints hac v₀ r) _ _
                    (scaledCoefficient_sectionTwo lam Lam B hs.1 σ v₀ r)
                    (scaledDrift_smooth b v₀ r hs.2.1) hs.2.2.1 hs.2.2.2.1
                    (scaledDrift_transportBounds b v₀ r hs.2.2.2.2.1)
                have hv' : (0 : PDE.Vec 1) ∈ movingDomain D stationary 0 := by
                  rw [movingDomain_stationary]
                  change v.1 + r.1 • (0 : PDE.Vec 1) ∈ PDE.oneDimensionalAxisBox a c
                  simpa only [smul_zero, add_zero] using v.2
                let q' := movingQuery 0 L hL.le (0 : PDE.Vec 1) 0 hv'
                let ν' := fourierProjection K' q' (r.1 ^ 3 • ξ)
                have hν' := fourierProjection_spec K' q' (r.1 ^ 3 • ξ)
                have hunit' := hunit ((a - v.1 0) / r.1) ((c - v.1 0) / r.1)
                  (scaled_interval_endpoints hac v.1 r) (scaledCoefficient B σ v.1 r) (scaledDrift b v.1 r)
                rw [← scaledDomain_interval a c v.1 r] at hunit'
                have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L)
                    (by simpa only [zero_add] using hL.le) 0 0 hv') (r.1 ^ 3 • ξ) ν' := by
                  simpa only [zero_add] using hν'
                have hbound := hunit' hs' hDr S' K' hr' (r.1 ^ 3 • ξ) hrunit
                  0 0 hv' (by simpa only [zero_add] using hL.le) ν' hνunit
                let ν := intervalFourierKernel K σ
                  (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v
                have hquery : KineticAffineScaling.queryMap hmap q' =
                    movingQuery σ (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht v.1 0
                      (by simpa only [movingDomain_stationary] using v.2) := by
                  apply Subtype.ext
                  change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
                    v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
                      (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) = _
                  change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
                    v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
                      (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) =
                    (σ, σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v.1, 0)
                  simp only [mul_zero, add_zero, smul_zero, zero_smul]
                  have hr2' := hr2
                  rw [hr2', mul_comm L]
                have hν : IsFourierProjection K (KineticAffineScaling.queryMap hmap q') ξ ν := by
                  rw [hquery]
                  exact intervalFourierKernel_spec K _ _ ht ξ v
                have htv := (realizes_ofRadius_interval_fourier_tv a c σ hac v.1 0 b r hr hr'
                  q' ξ ν ν' hν hν').2
                change (totalVariationNorm ν).toReal ≤ 1 - δ
                rw [htv]
                exact hbound
              have hq : 0 < 1 - δ := sub_pos.mpr hδ1
              obtain ⟨hC, hk⟩ := decay_constants hδ hδ1 hL
              refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, zero_lt_one.trans_le hC, hk, ?_⟩
              intro a c hac B b hs hJ S K hr σ τ hστ ξ v
              by_cases hξ : ξ = 0
              · subst ξ
                have htv := intervalFourierKernel_totalVariation_le_one K σ τ hστ 0 v
                have hr := ENNReal.toReal_mono ENNReal.one_ne_top htv
                simp only [ENNReal.toReal_one] at hr
                simpa only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
                  zero_mul, Finset.sum_const_zero, Real.sqrt_zero,
                  Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero,
                  Real.exp_zero, mul_one] using hr.trans hC
              · have hN := frequency_norm_pos hξ
                let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
                have hNp : 0 < N := Real.rpow_pos_of_pos hN _
                let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
                have hTdef : T = L / N := by
                  dsimp [T, N]
                  rw [Real.rpow_neg hN.le]
                  rfl
                have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
                have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
                have hb := interval_exponential_of_blocks K hJ hr.2.2.2 hc hT hq
                  (by linarith only [hδ] : 1 - δ ≤ 1) ξ
                  (fun s w => hsteps a c hac B b hs hJ S K hr ξ hξ s w
                    (le_add_of_nonneg_right hT.le)) σ τ hστ v
                have he : -(-Real.log (1 - δ) / T) * (τ - σ) =
                    -(-Real.log (1 - δ) / L) * (τ - σ) * N := by
                  rw [hTdef]
                  field_simp
                rw [he] at hb
                exact hb
            obtain ⟨C₂, k₂, hC₂, hk₂, hkill⟩ : ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1), SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b → ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary) (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary), RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ (zIndependentCoefficient B) b S K → c - a = length → ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c), TV (intervalFourierKernel K σ τ hστ ξ v) ≤ C * Real.exp (-k * (τ - σ)) := by
              obtain ⟨C, k, hC, hk, hmass⟩ := interval_mass_decay hH hLE
                lam Lam m Lb length hlam hlength
              refine ⟨C, k, hC, hk, ?_⟩
              intro a c hac B b hs hJ S K hr hlen σ τ hστ ξ v
              exact (interval_fourier_tv_le_mass hJ K B ((interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1) σ τ hστ v.1 0 ξ
                (by simpa only [movingDomain_stationary] using v.2) _
                (intervalFourierKernel_spec K σ τ hστ ξ v)).trans
                (hmass a c hac B b hs hJ S K hr hlen σ τ hστ v)
            let k := min k₁ k₂ / 2
            have hk : 0 < k := div_pos (lt_min hk₁ hk₂) (by norm_num)
            refine ⟨C₁ * C₂, k, mul_pos hC₁ hC₂, hk, ?_⟩
            intro a c hac B b hs hJ S K hr hlen σ τ hστ v ξ hv ν hν
            let w : PDE.oneDimensionalAxisBox a c :=
              ⟨v, by simpa only [movingDomain_stationary] using hv⟩
            have heq : ν = intervalFourierKernel K σ τ hστ ξ w := by
              apply VectorMeasure.ext
              intro E hE
              exact (hν E hE).trans ((intervalFourierKernel_spec K σ τ hστ ξ w E hE).symm)
            rw [heq]
            let r := (σ + τ) / 2
            have hσr : σ ≤ r := by dsimp [r]; linarith only [hστ]
            have hrτ : r ≤ τ := by dsimp [r]; linarith only [hστ]
            have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
            have hb := interval_composition_real_bound K hJ hr.2.2.2 hc σ r τ hσr hrτ ξ w
              (mul_pos hC₁ (Real.exp_pos _)).le (mul_pos hC₂ (Real.exp_pos _)).le
              (hfreq a c hac B b hs hJ S K hr σ r hσr ξ w)
              (fun w' => hkill a c hac B b hs hJ S K hr hlen r τ hrτ ξ w')
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
          refine ⟨C, k, hC, hk, ?_⟩
          intro a c hac B b hs hJ S K hr hlen σ τ hστ ξ v
          by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
          · rw [intervalExtension_fourier_inside hJ K σ τ hστ ξ ⟨v, hv⟩]
            have h := hdec a c hac B b hs hJ S K hr hlen σ τ hστ v ξ
              (by simpa only [movingDomain_stationary] using hv) _
              (intervalFourierKernel_spec K σ τ hστ ξ ⟨v, hv⟩)
            rw [← ENNReal.ofReal_toReal
              (show totalVariationNorm (intervalFourierKernel K σ τ hστ ξ ⟨v, hv⟩) ≠ ⊤ from
                ne_top_of_le_ne_top ENNReal.one_ne_top
                  (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ ⟨v, hv⟩))]
            exact ENNReal.ofReal_le_ofReal h
          · have _h_xinl_0 : fourierKernel (intervalExtension hJ K) σ τ hστ ξ v = 0 := by
                have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v 0) = 0 :=
                  intervalExtensionMaster_outside hJ K _ hv
                apply VectorMeasure.ext
                intro E hE
                rw [fourierKernel_spec _ _ _ _ _ _ E hE, he]
                simp only [Measure.restrict_zero, integral_zero_measure, zero_apply]

              /- The uniform interval killing and frequency decay also hold for the carrier adapter. -/
            rw [_h_xinl_0]
            simp only [totalVariationNorm, VectorMeasure.variation_zero, Measure.coe_zero, Pi.zero_apply,
              zero_le]
        refine ⟨slabConstant' 1 Co Cd kd, kd / 2, div_pos hkd (by norm_num), ?_⟩
        intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
        let Kw := intervalExtension hJ K
        let μw := μ.map (intervalStateInclusion σ)
        have hc := intervalExtension_covariance hJ K
          (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
        have hcomp : Kw.HasComposition MeasurableSet.univ := by
          have hcomp := hr.2.2.2
          intro σ r τ hσr hrτ
          apply ProbabilityTheory.Kernel.ext
          intro p
          apply Measure.ext
          intro A hA
          by_cases hp : p.1.1 ∈ PDE.oneDimensionalAxisBox a c
          · let pj : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
              ⟨p.1, by simpa only [evolutionStateSet, mem_prod, movingDomain_stationary,
                mem_univ, and_true] using hp⟩
            have he : intervalStateInclusion σ pj = p := Subtype.ext rfl
            rw [← he, intervalExtension_fiber_inside,
              Measure.map_apply (measurable_intervalStateInclusion τ) hA,
              hcomp σ r τ hσr hrτ,
              ProbabilityTheory.Kernel.comp_apply' _ _ _
                (hA.preimage (measurable_intervalStateInclusion τ)),
              ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
              intervalExtension_fiber_inside,
              lintegral_map
                (((intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable r τ
                  hrτ).measurable_coe hA)
                (measurable_intervalStateInclusion r)]
            apply lintegral_congr_ae
            refine Filter.Eventually.of_forall fun w => ?_
            dsimp only
            rw [intervalExtension_fiber_inside,
              Measure.map_apply (measurable_intervalStateInclusion τ) hA]
          · rw [intervalExtension_fiber_outside hJ K σ τ (hσr.trans hrτ) p hp,
              ProbabilityTheory.Kernel.comp_apply' _ _ _ hA,
              intervalExtension_fiber_outside hJ K σ r hσr p hp]
            simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero_measure]
        have hΓw : IsGreenMeasure (intervalExtension hJ K) σ ⊤ (μ.map (intervalStateInclusion σ)) Γ := by
          intro F hF
          let Kw := intervalExtension hJ K
          have : ProbabilityTheory.IsFiniteKernel (elapsedKernel Kw σ ⊤) := by
            unfold elapsedKernel
            infer_instance
          have hf : Measurable (fun q :
              (EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤) ×
                EvolutionAmbientState 1 => F (q.1.2, q.2)) := hF.comp (by fun_prop)
          have hi : Measurable (fun q :
              EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ × ElapsedTime ⊤ =>
              ∫⁻ w, F (q.2, w) ∂elapsedKernel Kw σ ⊤ q) :=
            hf.lintegral_kernel_prod_right'
          have hm : Measurable (fun p :
              EvolutionState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ =>
              ∫⁻ t : ElapsedTime ⊤, ∫⁻ w, F (t, w) ∂Kw.master (elapsedQuery σ p t)
                ∂elapsedVolume ⊤) := hi.lintegral_prod_right'
          rw [lintegral_map hm (measurable_intervalStateInclusion σ), hΓ F hF]
          apply lintegral_congr_ae
          refine Filter.Eventually.of_forall fun p => ?_
          dsimp only
          apply lintegral_congr_ae
          refine Filter.Eventually.of_forall fun t => ?_
          dsimp only
          change (∫⁻ w, F (t, w) ∂K.master (elapsedQuery σ p t)) =
            ∫⁻ w, F (t, w) ∂intervalExtensionMaster hJ K
              (intervalQueryInclusion (elapsedQuery σ p t))
          rw [intervalExtensionMaster_inside]
        obtain ⟨g, hgm, hgE, hgb, f, hfm, hfE, hfb⟩ := killed_slab_fourier_of_bounds
          (by norm_num) Kw hc hcomp Co (hoc m Lb hm hmLb a c hac B b hs hJ S K hr)
          Cd kd hCd hkd (hdec a c hac B b hs hJ S K hr hlen) σ μw Γ hΓw hT
        have hM : μw univ = μ univ := by
          dsimp only [μw]
          rw [Measure.map_apply (measurable_intervalStateInclusion σ) MeasurableSet.univ,
            preimage_univ]
        refine ⟨g, hgm, hgE, ?_, f, hfm, hfE, ?_⟩
        · intro γ hγ1 hγ2
          have h := hgb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
          simpa only [hM, interval_slab_beta] using h
        · intro γ hγ1 hγ2
          obtain ⟨hf, hfreq⟩ := hfb γ hγ1 (by norm_num [slabGamma0]; exact hγ2)
          constructor
          · intro ξ
            have h := hf ξ
            rw [hM, interval_slab_beta] at h
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
            simpa only [neg_mul, mul_assoc] using h
          · rw [hM, Nat.cast_one, interval_slab_height_exponent] at hfreq
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg hT.le _)]
            simpa only [pow_one, neg_mul, mul_assoc] using hfreq
      refine ⟨(slabConstant 1 q C : ℝ) + 1, k * (q - 1),
        by positivity, mul_pos hk (by linarith), ?_⟩
      intro a c hac B b hs hJ S K hr hlen σ T hT μ _ Γ hΓ
      obtain ⟨g, hgm, hgE, hgb, f, _hfm, hf, hfb⟩ :=
        hfourier a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
      have hqd : q < 1 + 1 / ((1 : ℕ) : ℝ) := by norm_num; exact hq'
      have hγ1 := (slab_gamma_one_lt (d := 1) hq hqd).le
      have hγ2 : slabGamma 1 q ≤ 2 := by
        have := (slab_q_lt_gamma (d := 1) hq hqd).2.le
        norm_num [slabGamma0] at this
        exact this
      obtain ⟨G, hGm, hGE, hbd⟩ := killed_slab_reconstruction C k K σ μ Γ hΓ hq hq' hT
        g hgm hgE (fun r h1 h2 => by
          have h2' : r ≤ 2 := by norm_num [slabGamma0] at h2; exact h2
          simpa only [interval_slab_beta] using hgb r h1 h2') f hf (by
          have he : slabBeta 1 (slabGamma 1 q) - 3 / 2 =
              3 / (2 * slabGamma 1 q) - 2 := by rw [interval_slab_beta]; ring
          simpa only [he] using
            (hfb (slabGamma 1 q) hγ1 hγ2).2)
      refine ⟨G, hGm, hGE, hbd.trans ?_⟩
      apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    let N := killedGreenConstant A (3 - 2 * q) k q
    have hN : N ≠ ⊤ := killedGreenConstant_ne_top hδ hk hq0
    refine ⟨N.toReal + 1, k, by positivity, hk, ?_⟩
    intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
    have hloc : ∀ T : ℝ, ∃ G : GreenCarrier 1 → ℝ≥0∞, 0 < T →
        Measurable G ∧
        Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
        ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
          ENNReal.ofReal A * μ univ ^ q *
            ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
      intro T
      by_cases hT : 0 < T
      · obtain ⟨G, hG⟩ := hslab a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
        exact ⟨G, fun _ => hG⟩
      · exact ⟨0, fun h => absurd h hT⟩
    choose Gl hGl using hloc
    obtain ⟨G, hGm, hGE, hGae⟩ := exists_global_density K σ μ Γ hΓ Gl
      (fun T hT => (hGl T hT).1) (fun T hT => (hGl T hT).2.1)
    refine ⟨G, hGm, hGE, ?_⟩
    have hbd := killed_green_norm_bound G hGm A (3 - 2 * q) k q (μ univ) hq0 (by
      intro T hT
      calc ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1
          = ∫⁻ p in slabSet T, Gl T p ^ q ∂greenLebesgue 1 := by
            refine lintegral_congr_ae ?_
            filter_upwards [hGae T hT] with p hp
            rw [hp]
        _ ≤ _ := (hGl T hT).2.2)
    apply hbd.trans
    apply mul_le_mul' ?_ le_rfl
    calc N = ENNReal.ofReal N.toReal := (ENNReal.ofReal_toReal hN).symm
      _ ≤ ENNReal.ofReal (N.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨_Cm, _hCm, hmass⟩ := interval_green_finite_mass hH hLE
    lam Lam m Lb length hlam hlength
  refine ⟨C, hC, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  obtain ⟨G, hGm, hGE, hGn⟩ := hnorm a c hac B b hs hJ S K hr hlen σ μ Γ hΓ
  exact ⟨G, hGm, hGE, hGn, (hmass a c hac B b hs hJ S K hr hlen σ μ Γ hΓ).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval
