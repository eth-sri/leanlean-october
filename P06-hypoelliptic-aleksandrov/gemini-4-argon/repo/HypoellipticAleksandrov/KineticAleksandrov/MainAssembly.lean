module

public import HypoellipticAleksandrov.Statements.HormanderHypoellipticity
public import HypoellipticAleksandrov.Statements.LiebermanDirichlet
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedFinal
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.FinalA
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.LocalisedAutonomous
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier
import HypoellipticAleksandrov.KineticAleksandrov.Holder.TimeVelocityCorollary
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusionConsumers
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedAssembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.LocalStatement
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.TimeVelocityCorollaryGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Borel
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedSource
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimate
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateSource
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibility
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousAdmissibilitySource
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousHolder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BorelTransfer
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TheoremAutonomous
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationBasics
import HypoellipticAleksandrov.KineticAleksandrov.Holder.PairGeometry
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Unconditional proofs of the main statements

The two classical inputs are discharged from the theorems in `Statements`, and the seven final
statements are proved from the existing internal theorems with no extra hypotheses.
-/

@[expose] public section
noncomputable section
-- The statement types are verbatim copies of the statements in `Statements`, which name binders
-- that occur only inside nested types.
set_option linter.unusedVariables false
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder LocalA
open HypoellipticAleksandrov.Parabolic
open scoped ENNReal MatrixOrder ProbabilityTheory
open TheoremA
open SectionTwo Green Parabolic
open scoped NNReal
open Evolution HypoellipticAleksandrov.KineticAleksandrov.Autonomous HypoellipticAleksandrov.KineticAleksandrov.Holder

abbrev hH : HormanderHypoellipticityStatement :=
  exists_smooth_aeRepresentative_of_hormander

abbrev hLE : LiebermanEllipsoidDirichletStatement :=
  exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman

abbrev hBel :=
  below_four_density_of_frontier autonomousRemainingFrontier_holds hH hLE

private abbrev hSmoothEst (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 2 * (d : ℝ) + 1 < p) :=
  let hEv := exists_terminalEvolution_of_classical hLE hH
  let hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
  smooth_estimate_of_slabFourierBounds hd lam Lam p hlam hLam hp hH
    (Green.slabFourierBounds_of_occupation_decay hd lam Lam
      (Occupation.parabolicOccupationFamily_holds
        (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam)
      (Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter
        (Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam)))
    fun B hB =>
      let ⟨S, K, hreal, _, _, _⟩ :=
        SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam B hB
      ⟨S, K, hreal⟩

theorem kinetic_aleksandrov_timeVelocity_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsmooth⟩ := hSmoothEst d hd lam Lam p hlam hLam hp
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 ≤ p := by linarith
  have hfull : ∀ A : CoefficientField d,
      IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ u f : KineticPoint d → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
            (eLpNorm (borelSource false u f) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
    intro A hAs hsym hlo hhi P₀ R hR u f hc hr hf hLp hsub P hP
    refine (hsmooth A hAs hsym (Filter.Eventually.of_forall fun z => hlo z.1 z.2)
      (Filter.Eventually.of_forall fun z => hhi z.1 z.2) P₀ R hR u f hc hr hf hLp hsub P hP).trans ?_
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg hR.le _))
    simpa only [borelSource, Bool.false_eq_true, ite_false] using
      localized_positive_source_norm_le volume (isOpen_backwardCylinder P₀ R hR)
        u f hr.continuousOn (ENNReal.ofReal p) hLp
  refine ⟨C, hC, fun P₀ R hR A hBorel hsym hlo hhi f u hf hc hr hsub hLp P hP => ?_⟩
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hae := source_indicator_ae_eq hQ f
  have hbound := kinetic_abp_smooth_to_borel lam Lam hlam hLam p hp1
    (2 - (4 * (d : ℝ) + 2) / p) C false hfull A hBorel hsym hlo hhi
    P₀ R hR u f₀ hc hr (measurable_source_indicator hQ f hf)
    (hLp.ae_eq (by filter_upwards [hae] with Q hEq; dsimp [f₀]; rw [hEq]))
    (by filter_upwards [hsub, hae] with Q h1 h2; dsimp [f₀]; rwa [h2]) P hP
  simpa only [f₀, borelSource, Bool.false_eq_true, ite_false,
    eLpNorm_positive_source_indicator hQ f] using hbound

theorem kinetic_aleksandrov_timeVelocity_localised_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hsmooth⟩ := hSmoothEst d hd lam Lam p hlam hLam hp
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 ≤ p := by linarith
  have hfull : ∀ A : CoefficientField d,
      IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ u f : KineticPoint d → ℝ,
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
            (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
              (volume.restrict (backwardCylinder P₀ R))).toReal := by
    intro A hAs hsym hlo hhi P₀ R hR u f hc hr hf hLp hsub P hP
    simpa only [borelSource, ite_true] using
      hsmooth A hAs hsym (Filter.Eventually.of_forall fun z => hlo z.1 z.2)
        (Filter.Eventually.of_forall fun z => hhi z.1 z.2) P₀ R hR u f hc hr hf hLp hsub P hP
  refine ⟨C, hC, fun P₀ R hR A hBorel hsym hlo hhi f u hf hc hr hsub hLp P hP => ?_⟩
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hae := source_indicator_ae_eq hQ f
  have hbound := kinetic_abp_smooth_to_borel lam Lam hlam hLam p hp1
    (2 - (4 * (d : ℝ) + 2) / p) C true hfull A hBorel hsym hlo hhi
    P₀ R hR u f₀ hc hr (measurable_source_indicator hQ f hf)
    (hLp.ae_eq (by filter_upwards [hae] with Q hEq; dsimp [f₀]; rw [hEq]))
    (by filter_upwards [hsub, hae] with Q h1 h2; dsimp [f₀]; rwa [h2]) P hP
  simpa only [f₀, borelSource, ite_true,
    eLpNorm_localized_source_indicator hQ f u] using hbound

/- Companion paper, Corollary 9.9, with no extra hypotheses. -/
theorem kinetic_holder_timeVelocity_proof
    (d ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  have hlocal := (localTimeVelocityRegularity_of_smooth smoothLocalRegularityStatement_holds)
  obtain ⟨Cm, D, alpha, _hCm, hD, ha, ha1, hreg⟩ :=
    hlocal hH hLE d hd lam Lam hlam hLam
  let C := max D ((4 : ℝ) ^ alpha)
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  refine ⟨alpha, C, ha, ha1.le, ?_⟩
  intro A hmeas hsym hlo hhi Omega _hOmega u _hbounded hu heq K _hKO hK R0 hR0 hQ
  let E := holderNeighbourhood R0 K
  obtain ⟨hclosed, hcompact⟩ := holder_neighbourhood_compact K hK R0 hR0
  have hEO : closure E ⊆ Omega := by
    rw [hclosed]
    intro Z hZ
    simp only [mem_iUnion] at hZ
    obtain ⟨P, hP, hZ⟩ := hZ
    exact hQ P hP hZ
  have hcont : ContinuousOn u (closure E) := hu.continuousOn.mono hEO
  have habc : BddAbove (u '' closure E) := hcompact.bddAbove_image hcont
  have hbbc : BddBelow (u '' closure E) := hcompact.bddBelow_image hcont
  have hab : BddAbove (u '' E) := habc.mono (image_mono subset_closure)
  have hbb : BddBelow (u '' E) := hbbc.mono (image_mono subset_closure)
  have hcenter (P : KineticPoint d) (hP : P ∈ K) : P ∈ closure E := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨P, mem_iUnion.mpr ⟨hP,
      Covering.top_mem_closure_cylinder P (by positivity : 0 < 2 * R0)
        (PDE.center_mem_euclideanBall _ (by positivity))⟩⟩
  have hpair (P : KineticPoint d) (hP : P ∈ K) (Q : KineticPoint d) (hQK : Q ∈ K)
      (ht : P.time ≤ Q.time) :
      |u P - u Q| ≤ C * oscillationOn u E * (quasiDistance P Q / R0) ^ alpha := by
    have hne : E.Nonempty := by
      obtain ⟨Z, hZ⟩ := backwardCylinder_nonempty Q (by positivity : 0 < 2 * R0)
      exact ⟨Z, mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQK, hZ⟩⟩⟩
    have hosc := oscillationOn_nonneg hne hab hbb
    have hosccl := oscillationOn_closure hne hcompact hcont
    have hdelta := quasiDistance_nonneg P Q
    by_cases hz : quasiDistance P Q = 0
    · have he := (quasiDistance_eq_zero_iff P Q).mp hz
      rw [congrArg u he, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le hosc)
        (Real.rpow_nonneg (div_nonneg hdelta hR0.le) _)
    have hdpos : 0 < quasiDistance P Q := lt_of_le_of_ne hdelta (Ne.symm hz)
    by_cases hnear : quasiDistance P Q < R0 / 4
    · have hhalf : 0 < R0 / 2 := by positivity
      have hdhalf : quasiDistance P Q ≤ R0 / 2 := by linarith only [hnear, hR0]
      obtain ⟨hpcl, hqcl⟩ := pair_mem_closed_later_cylinder P Q ht hdpos
      have hsubhalf := closure_mono (backwardCylinder_radius_mono Q hdpos hdhalf)
      have hsub : backwardCylinder Q R0 ⊆ backwardCylinder Q (2 * R0) :=
        backwardCylinder_radius_mono Q hR0 (by linarith only [hR0])
      have hsmallO : closure (backwardCylinder Q R0) ⊆ Omega :=
        (closure_mono hsub).trans (hQ Q hQK)
      have hsmall : backwardCylinder Q R0 ⊆ Omega := subset_closure.trans hsmallO
      have huSmall : Parabolic.IsKineticC112On u (backwardCylinder Q R0) := by
        refine ⟨hu.1.mono hsmall, ?_, ?_, ?_, hu.2.2.2.2.1.mono hsmall,
          hu.2.2.2.2.2.1.mono hsmall, hu.2.2.2.2.2.2.1.mono hsmall,
          hu.2.2.2.2.2.2.2.mono hsmall⟩
        · exact fun Z hZ => hu.2.1 Z (hsmall hZ)
        · exact fun Z hZ => hu.2.2.1 Z (hsmall hZ)
        · exact fun Z hZ => hu.2.2.2.1 Z (hsmall hZ)
      have huc := hu.continuousOn.mono hsmallO
      have hestimate := (hreg A hmeas hsym hlo hhi Q R0 hR0 u huc huSmall
        (ae_restrict_of_ae_restrict_of_subset hsmall heq)).2.2
      have hhalfsub : closure (backwardCylinder Q (R0 / 2)) ⊆
          closure (backwardCylinder Q R0) :=
        closure_mono (backwardCylinder_radius_mono Q hhalf (by linarith only [hR0]))
      have hbound := local_estimate_on_closure Q ha.le u (huc.mono hhalfsub)
        hestimate (hsubhalf hpcl) (hsubhalf hqcl)
      have hbigE : backwardCylinder Q R0 ⊆ E := fun Z hZ =>
        mem_iUnion.mpr ⟨Q, mem_iUnion.mpr ⟨hQK, hsub hZ⟩⟩
      have hsmallosc := oscillationOn_nonneg (backwardCylinder_nonempty Q hR0)
        (hab.mono (image_mono hbigE)) (hbb.mono (image_mono hbigE))
      have hoscmono := oscillationOn_mono (backwardCylinder_nonempty Q hR0) hbigE hab hbb
      have hincnonneg : 0 ≤ kineticIncrement Q P Q := by
        exact add_nonneg
          (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
            (PDE.vecEuclideanNorm_nonneg _))
          (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
      have _h_xinl_2 : kineticIncrement Q P Q ≤ quasiDistance P Q := by
        unfold kineticIncrement quasiDistance
        rw [← Real.sqrt_eq_rpow]
        have hr := Real.rpow_le_rpow
          (PDE.vecEuclideanNorm_nonneg
            (P.position - Q.position - (P.time - Q.time) • Q.velocity))
          (le_max_right
            (PDE.vecEuclideanNorm (Q.position - P.position - (Q.time - P.time) • P.velocity))
            (PDE.vecEuclideanNorm (P.position - Q.position - (P.time - Q.time) • Q.velocity)))
          (by norm_num : (0 : ℝ) ≤ 1 / 3)
        exact add_le_add_right hr _
      have hpower := Real.rpow_le_rpow (div_nonneg hincnonneg hR0.le)
        (div_le_div_of_nonneg_right _h_xinl_2 hR0.le)
        ha.le
      exact hbound.trans ((mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_left D _) hoscmono hsmallosc hC.le)
        (Real.rpow_nonneg (div_nonneg hincnonneg hR0.le) _)).trans
        (mul_le_mul_of_nonneg_left hpower (mul_nonneg hC.le hosc)))
    · have hbase := abs_sub_le_oscillationOn habc hbbc (hcenter P hP) (hcenter Q hQK)
      rw [hosccl] at hbase
      have hratio : 1 / 4 ≤ quasiDistance P Q / R0 := by
        apply (le_div_iff₀ hR0).mpr
        have hh := le_of_not_gt hnear
        linarith only [hh]
      have hpower := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hratio ha.le
      have hfour : (4 : ℝ) ^ alpha * (1 / 4 : ℝ) ^ alpha = 1 := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by norm_num)]
        norm_num
      have hcoeff : 1 ≤ C * (quasiDistance P Q / R0) ^ alpha := by
        rw [← hfour]
        exact mul_le_mul (le_max_right D _) hpower (Real.rpow_nonneg (by norm_num) _)
          hC.le
      have hb := mul_le_mul_of_nonneg_right hcoeff hosc
      rw [one_mul] at hb
      exact hbase.trans (hb.trans_eq (by ring))
  intro P hP Q hQK
  rcases le_total P.time Q.time with ht | ht
  · exact hpair P hP Q hQK ht
  · have hb := hpair Q hQK P hP ht
    simpa only [abs_sub_comm, quasiDistance_symm Q P] using hb

theorem kinetic_aleksandrov_autonomous_proof
    (lam Lam p ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hborel⟩ := autonomous_borel_of_below_four_density hBel hH hLE lam Lam hlam hLam p hp
  refine ⟨C, hC.le, fun P₀ R hR a ha hb f u hf hcont hreg hsub hLp P hP => ?_⟩
  have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
  let f₀ := (backwardCylinder P₀ R).indicator f
  have hae := source_indicator_ae_eq hQ f
  simpa only [f₀, eLpNorm_positive_source_indicator hQ f] using
    hborel a ha hb P₀ R hR u f₀ hcont hreg (measurable_source_indicator hQ f hf)
      (hLp.ae_eq (by filter_upwards [hae] with Q hEq; dsimp [f₀]; rw [hEq]))
      (by filter_upwards [hsub, hae] with Q h1 h2; dsimp [f₀]; rwa [h2]) P hP

abbrev kinetic_aleksandrov_autonomous_localised_proof :=
  kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density hBel hH hLE

theorem kinetic_holder_autonomous_proof
    (lam Lam ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  obtain ⟨C_A, hadm⟩ : ∃ C_A : ℝ,
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ Omega : Set (KineticPoint 1), IsOpen Omega →
      ∀ u : KineticPoint 1 → ℝ,
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
        IsAdmissibleSolution
          (fun _ x v => fun _ _ => a (x 0) (v 0)) Omega 6 C_A u := by
    have hp : 1 + bellmanAdjointExponent (Lam / lam)
        ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < 6 := by
      have hc := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
        (by simpa only [one_mul] using hLam)⟩).2
      change 1 + bellmanAdjointExponent _ _ < 4 at hc
      linarith only [hc]
    obtain ⟨C_A, _hC, hestimate⟩ :=
      kinetic_aleksandrov_autonomous_localised_relative_of_below_four_density
        hBel hH hLE lam Lam 6 hlam hLam hp
    refine ⟨C_A, ?_⟩
    intro a ha hb Omega _hOmega u _hbounded hu heq
    have hsup (w : Point → ℝ) (hw : IsKineticC112On w Omega)
        (heqw : ∀ᵐ P ∂volume.restrict Omega, autonomousScalarOperator a w P = 0) :
        IsAdmissibleSupersolution (autonomousCoefficient a) Omega 6 C_A w := by
      refine ⟨hw.continuousOn, ?_⟩
      intro P₀ R hR hQ psi hpsi
      obtain ⟨U, _hU, hUQ, hps⟩ := smoothNear_regular hpsi
      have hQQ := subset_closure.trans hQ
      have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
      have hwr := comparison_regular_mono hw hQQ
      have hneg := comparison_regular_const_mul hwr (-1)
      have hdiff : IsKineticC112On (fun P => psi P - w P) (backwardCylinder P₀ R) := by
        simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
      have hop : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          autonomousScalarOperator a (fun Q => psi Q - w Q) P ≤
            autonomousScalarOperator a psi P := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
          ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet] with P he hP
        have hadd := autonomous_operator_add hpr hneg a hP
        have hmul := autonomous_operator_const_mul hwr (-1) a hP
        simp only [neg_one_mul, ← sub_eq_add_neg] at hadd hmul
        rw [hadd, hmul, he]
        simp only [neg_zero, add_zero, le_refl]
      obtain ⟨hmeas, hLp⟩ := autonomous_test_source hlam ha hb P₀ R hR hpsi
      have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := by
        ext P
        exact sub_pos
      have hbnd := hestimate P₀ R hR a ha hb (autonomousScalarOperator a psi)
        (fun P => psi P - w P) hmeas
        (hpsi.continuousOn.sub (hw.continuousOn.mono hQ)) hdiff hop hLp
      have hbnd' : ∀ P ∈ closure (backwardCylinder P₀ R), psi P - w P ≤
          sSup ((fun P => max (psi P - w P) 0) '' kineticBoundary P₀ R) +
            C_A * R ^ (2 - (4 * (1 : ℝ) + 2) / 6) *
              (eLpNorm (localizedSource (autonomousCoefficient a) psi w) (ENNReal.ofReal 6)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
        simpa only [hn, localizedSource, backwardOperator_autonomous,
          show 4 * (1 : ℝ) + 2 = 6 by norm_num] using hbnd
      apply csSup_le
      · exact (backwardCylinder_nonempty P₀ hR).closure.image _
      · rintro y ⟨P, hP, rfl⟩
        simpa only [Nat.cast_one] using hbnd' P hP
    refine ⟨hsup u hu heq, ?_⟩
    have hneg : IsKineticC112On (fun P => -u P) Omega := by
      simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
    apply hsup (fun P => -u P) hneg
    filter_upwards [heq, ae_restrict_mem _hOmega.measurableSet] with P he hP
    have hm := autonomous_operator_const_mul hu (-1) a hP
    simpa only [neg_one_mul, he, neg_zero] using hm
  obtain ⟨alpha, C, ha, ha1, hholder⟩ := kinetic_holder_of_aleksandrov_aux
    1 (by norm_num) lam Lam 6 C_A hlam hLam (by norm_num)
  refine ⟨alpha, C, ha, ha1, ?_⟩
  intro a hmeas hb Omega hOmega u hbounded hu heq
  have hlo : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      lam • (1 : PDE.Mat 1) ≤
        fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).1)
  have hhi : ∀ᵐ P ∂(volume : Measure (KineticPoint 1)),
      fullKineticCoefficientAt (Autonomous.autonomousCoefficient a) P ≤
        Lam • (1 : PDE.Mat 1) :=
    Filter.Eventually.of_forall (fun P => (Autonomous.autonomous_lift_elliptic hb P).2)
  have _h_xinl_0 : Measurable (fullKineticCoefficientAt (autonomousCoefficient a)) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact hmeas.comp (((continuous_apply 0).comp continuous_position).measurable.prodMk
      (((continuous_apply 0).comp continuous_velocity).measurable))
  exact hholder (Autonomous.autonomousCoefficient a)
    _h_xinl_0 (Autonomous.autonomous_lift_symm a)
    hlo hhi Omega hOmega u hbounded (hadm a hmeas hb Omega hOmega u hbounded hu heq)

end HypoellipticAleksandrov.KineticAleksandrov
