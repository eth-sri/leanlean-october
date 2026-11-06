module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityFromBound
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceBound
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTests
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DensityFromTestsInterpolation
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityPotential
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.PotentialWhole
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.DualityMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelGreen
import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovBound
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceAbsorption
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceLocalization
import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorEstimate
import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorReduction
import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.LocalizedAdmissibility
import HypoellipticAleksandrov.Parabolic.ABP
import HypoellipticAleksandrov.Parabolic.ScalingMeasure
import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PDEFoundation.Ambient.EuclideanNorm
import PDEFoundation.Geometry.Affine
import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# The unit-time occupation duality

The whole-space source estimate is consumed at its complete form. The smooth-test
density theorem proves absolute continuity internally; one density works at every exponent.
The only analytic inputs are the explicit hypotheses of Hörmander's hypoellipticity theorem
and classical Dirichlet solvability (Lieberman, Theorem 5.14).
-/

@[expose] public section
noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set SectionTwo
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal
open scoped ProbabilityTheory
open Filter Parabolic HypoellipticAleksandrov.KineticAleksandrov.LsuFree PDE
open scoped Matrix.Norms.Elementwise Topology MatrixOrder Pointwise

variable {d : ℕ}

/- Unit-time occupation density with uniform constants and the full exponent range. -/
theorem occupation_duality
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
        (ρ : Measure (PDE.Vec d)) [IsFiniteMeasure ρ],
        ∃ g : TimeVelocity d → ℝ, IsOccupationDensity K 0 1 ρ g ∧
          ∀ γ, 1 ≤ γ → γ ≤ ((d : ℝ) + 1) / d →
            MemLp g (ENNReal.ofReal γ)
              (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) ∧
            occupationLpNorm 1 γ g ≤ C γ * (ρ univ).toReal := by
  have hWhole :
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
              H ≤ C * parabolicLpNorm d F := by
    obtain ⟨C, hC0, hbound⟩ : ∃ C : ℝ, 0 ≤ C ∧
        ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
          (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
          (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
          (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
          (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
          (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
          (_ : R ^ 2 = max 1 (4 * d * Lam))
          (V : TimeVelocity d → ℝ)
          (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
            (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
          ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
            0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) * parabolicLpNorm d F := by
      obtain ⟨C, hC0, hbound⟩ : ∃ C : ℝ, 0 ≤ C ∧
          ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
            (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
            (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
            (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
            (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
            (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
            (_ : R ^ 2 = max 1 (4 * d * Lam))
            (V : TimeVelocity d → ℝ)
            (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
              (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
            ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
              0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
                parabolicLpNormOn d F
                  (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
          obtain ⟨C, hC0, hK⟩ : ∃ C : ℝ, 0 ≤ C ∧
          ∀ (t₀ : ℝ) (v₀ : PDE.Vec d) (h : ℝ), 0 < h → h ≤ 1 →
          ∀ (a : TimeVelocity d → PDE.Mat d) (f u : TimeVelocity d → ℝ),
            ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
            (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
            (∀ z ∈ krylovClosedCylinder t₀ h v₀,
              lam • (1 : PDE.Mat d) ≤ a z ∧ a z ≤ Lam • (1 : PDE.Mat d)) →
            MemLp f (parabolicExponent d) (volume.restrict (krylovCylinder t₀ h v₀)) →
            IsScalarC12On u (krylovCylinder t₀ h v₀) →
            ContinuousOn u (krylovClosedCylinder t₀ h v₀) →
            (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
              scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
                ≤ f z) →
            (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
            ∀ z ∈ krylovCylinder t₀ h v₀,
              u z ≤ C * parabolicLpNormOn d f (krylovCylinder t₀ h v₀) := by
            obtain ⟨C, hC, hABP⟩ := parabolic_abp_unit_of_lower_ellipticity d hd lam hlam
            refine ⟨C, hC.le, ?_⟩
            intro t₀ v₀ h hh hh1 a f u ha _hsym hell hf hu huc hsub hb z hz
            let Z : TimeVelocity d := (z.1 - (t₀ - h), z.2 - v₀)
            have hZ : Z ∈ closedParabolicCylinder h (0 : PDE.Vec d) := by
              refine ⟨⟨by dsimp [Z]; linarith [hz.1.1],
                by dsimp [Z]; linarith [hz.1.2]⟩, ?_⟩
              change PDE.euclideanSqDist (z.2 - v₀) 0 ≤ 1 ^ 2
              have hv :=
                (show PDE.euclideanSqDist z.2 v₀ < 1 ^ 2 from hz.2).le
              simpa only [PDE.euclideanSqDist, Pi.sub_apply, sub_zero] using hv
            have hmap : KrylovEstimate.innerMap t₀ h v₀ 1 Z = z := by
              apply Prod.ext
              · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_pow,
                  sub_self, zero_mul, zero_div, add_zero, one_mul]
                ring
              · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_smul]
                exact add_sub_cancel _ _
            apply le_of_forall_pos_le_add
            intro ε hε
            let δ := ε / (C + 1)
            have hδ : 0 < δ := div_pos hε (by linarith)
            obtain ⟨A, F, w, hA, hF, hw, hlo, hsw, hbw, hclose, hnorm⟩ :=
              exists_smooth_subsolution_close_direct d hd lam hlam t₀ h v₀ hh a f u
                ha (fun y hy => (hell y hy).1) hf hu huc hsub hb hδ
            have hestimate := hABP hh hh1 0 A F w hA hF hw hlo hsw hbw Z hZ
            have hvalue := hclose Z hZ
            rw [hmap] at hvalue
            have hupper := (neg_le_abs (w Z - u z)).trans hvalue
            have hsource := mul_le_mul_of_nonneg_left hnorm hC.le
            have herror : δ * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
            nlinarith
          refine ⟨C, hC0, ?_⟩
          intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV
          obtain ⟨hInterior, hValue, hcoef, hsy, hbd, hpos, hle, hmem, hpde, -, hzero, hnorm, hnonneg⟩ :=
            localizedKrylov_admissible_direct hd hlam hLam hsymm hsmooth hlow hup hF0 hFs hFc hFsupp
              hα0 hα1 hR hRsq hV
          set Qk := krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) with hQk
          set QV := scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) with hQV
          set M : ℝ := C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            parabolicLpNormOn d F QV with hM

          have hqk := hK (localHeight α R) (0 : PDE.Vec d) (localHeight α R) hpos hle
            (localizedCoefficient R vStar B) (localizedSource R vStar F) (localizedScaled R vStar V)
            hcoef hsy hbd hmem hInterior hValue
            (ae_restrict_of_forall_mem (isOpen_krylovCylinder _ _ _).measurableSet
              (fun z hz => (hpde z hz).le))
            (fun z hz => (hzero z hz).le)
          have hopen : ∀ w ∈ QV, V w ≤ M := by
            intro w hw
            obtain ⟨z, hz, rfl⟩ : ∃ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        reflectScale R vStar z = w := by
              refine ⟨reflectScaleInv R vStar w, ?_, reflectScale_reflectScaleInv hR w⟩
              rw [mem_krylovCylinder_iff_reflectScale hR (vStar := vStar) (α := α),
                reflectScale_reflectScaleInv hR]
              exact hw
            have h1 := hqk z hz
            rw [hnorm] at h1
            change V (reflectScale R vStar z) ≤ _ at h1
            simpa only [hM, mul_assoc] using h1

          have hclosure : closure QV = scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) := by
            rw [hQV, scalarParabolicOpenCylinder, closure_prod_eq, closure_Ioo hα1.ne]
            rfl
          intro z hz
          refine ⟨hnonneg z hz, ?_⟩
          have hQK :=
            subset_closure.trans hclosure.le
          have hzc : z ∈ closure QV := by rw [hclosure]; exact hz
          exact ContinuousWithinAt.closure_le hzc ((hV.1 z hz).mono hQK) continuousWithinAt_const hopen



      refine ⟨C, hC0, ?_⟩
      intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV z hz
      obtain ⟨h0, h1⟩ := hbound B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR
        hRsq V hV z hz
      refine ⟨h0, h1.trans ?_⟩
      exact mul_le_mul_of_nonneg_left
        (parabolicLpNormOn_le_parabolicLpNorm_direct hFs.continuous hFc _)
        (mul_nonneg hC0 (Real.rpow_nonneg hR.le _))
    let R := Real.sqrt (max 1 (4 * (d : ℝ) * Lam))
    have hm : 0 < max 1 (4 * (d : ℝ) * Lam) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hR : 0 < R := Real.sqrt_pos.mpr hm
    have hRsq := Real.sq_sqrt hm.le
    let M := C * R ^ ((d : ℝ) / ((d : ℝ) + 1))
    have hM : 0 ≤ M := mul_nonneg hC0 (Real.rpow_nonneg hR.le _)
    refine ⟨2 * M, by positivity, ?_⟩
    intro B hB S K _hreal hP F hF0 hFs hFc hFsupp
    dsimp only
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    let H := sSup (W '' (Icc (0 : ℝ) 1 ×ˢ univ))
    have hloc := wholeSpace_localization_direct hH hd hB K hP F hF0 hFs hFc hFsupp
    refine ⟨?_, ?_⟩
    · intro α hα0 hα1 vStar R' hR' hRsq'
      simpa only [occupationQuadratic] using hloc α hα0 hα1 vStar R' hR' hRsq'
    · have hnorm : 0 ≤ parabolicLpNorm d F := ENNReal.toReal_nonneg
      have hpoint : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ univ,
          W q ≤ M * parabolicLpNorm d F + H / 2 := by
        intro q hq
        by_cases ht : q.1 = 1
        · have hzero : W q = 0 := by
            exact parabolicDuhamelPotential_eq_zero_of_terminal_le K MeasurableSet.univ
              1 F q ht.ge
          have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
          have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
            (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
          rw [hzero]
          positivity
        · have htlt : q.1 < 1 := lt_of_le_of_ne hq.1.2 ht
          obtain ⟨V, hV, hcmp, hhalf⟩ := hloc q.1 hq.1.1 htlt q.2 R hR hRsq
          have hqball : q.2 ∈ closure (PDE.euclideanBall q.2 R) := by
            apply subset_closure
            change PDE.euclideanSqDist q.2 q.2 < R ^ 2
            simpa [PDE.euclideanSqDist, PDE.vecNormSq_eq_sum_sq] using sq_pos_of_pos hR
          have hqc : q ∈ scalarParabolicClosedCylinder q.1 1
              (PDE.euclideanBall q.2 R) := ⟨⟨le_rfl, hq.1.2⟩, hqball⟩
          have hc := hcmp q hqc
          have hv := (hbound B hB.2.2.2.1 (sectionTwoCoefficient_smooth hB)
            hB.2.2.2.2.1 hB.2.2.2.2.2 F hF0 hFs hFc hFsupp q.1 hq.1.1 htlt
            q.2 R hR hRsq V hV q hqc).2
          have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
          have hH0 : 0 ≤ H := (hpot.1 (0, 0)).trans
            (le_csSup hpot.2.1 ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩)
          have hh := mul_le_mul_of_nonneg_left hhalf hH0
          simp only [occupationQuadratic, sub_self, zero_pow (by norm_num : 2 ≠ 0),
            Finset.sum_const_zero, zero_add] at hc
          rw [mul_div_assoc] at hc
          dsimp [M] at hv ⊢
          linarith
      have hsup := wholeSpace_absorb
        (show (Icc (0 : ℝ) 1 ×ˢ (univ : Set (PDE.Vec d))).Nonempty from
          ⟨(0, 0), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩⟩) hpoint
      change H ≤ (2 * M) * parabolicLpNorm d F
      nlinarith [hsup]

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
          (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal := by
    intro F hFs hFc hFsupp hF0
    let W := parabolicDuhamelPotential K MeasurableSet.univ 1 F
    have hwhole := (hWhole B hB S K hreal hP F hF0 hFs hFc hFsupp).2
    have hpot := occupation_potential hH hB K hP F hF0 hFs hFc hFsupp
    have hb (v : PDE.Vec d) : W (0, v) ≤ C₀ * parabolicLpNorm d F :=
      (le_csSup hpot.2.1 ⟨(0, v), ⟨⟨le_rfl, zero_le_one⟩, mem_univ _⟩, rfl⟩).trans hwhole
    have hn (v : PDE.Vec d) : ‖W (0, v)‖ ≤ C₀ * parabolicLpNorm d F := by
      rw [Real.norm_of_nonneg (hpot.1 (0, v))]
      exact hb v
    have _h_xinl_0 : (∫ q, F q ∂unitOccupationMeasure K ρ) =
      ∫ v, parabolicDuhamelPotential K MeasurableSet.univ 1 F (0, v) ∂ρ := by
      have hΩm : MeasurableSet (wholeSpace d) := MeasurableSet.univ
      have hFm := hFs.continuous.measurable
      obtain ⟨M, hM⟩ := hFs.continuous.bounded_above_of_compact_support hFc
      rw [integral_unitOccupationMeasure K ρ F hFm ⟨M, fun q => by simpa using hM q⟩]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun v => ?_
      change (∫ τ : ElapsedTime (ENNReal.ofReal (1 : ℝ)),
        ∫ w, F (τ.1, w) ∂K.firstMarginal
          (wholeSpaceQuery 0 (0 + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
        ∂elapsedVolume (ENNReal.ofReal (1 : ℝ))) =
        parabolicDuhamelPotential K hΩm 1 F (0, v)
      have hint (τ : ElapsedTime (ENNReal.ofReal (1 : ℝ))) :
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
        simp only [parabolicMasterIntegral, wholeSpaceQuery, zero_add]
      rw [integral_congr_ae (Filter.Eventually.of_forall hint)]
      have htime : Measurable (fun r => parabolicDuhamelIntegrand K
          MeasurableSet.univ F (0, v) r) := by
        exact (measurable_parabolicDuhamelIntegrand K MeasurableSet.univ
          continuous_const F hFm).comp (measurable_const.prodMk measurable_id)
      rw [integral_elapsed_eq 1 zero_lt_one _ htime]
      change (∫ r in Ioo 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r) =
        ∫ r in Ioc 0 1, parabolicDuhamelIntegrand K hΩm F (0, v) r
      exact (integral_Ioc_eq_integral_Ioo).symm
    rw [_h_xinl_0]
    have hi := norm_integral_le_of_norm_le_const (μ := ρ)
      (Filter.Eventually.of_forall hn)
    have hle : (∫ v, W (0, v) ∂ρ) ≤ (C₀ * parabolicLpNorm d F) * M :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, measureReal_def] using hi)
    have _h_xinl_0 : parabolicLpNorm d F =
      (eLpNorm F (ENNReal.ofReal
        ((((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1)))
        (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal := by
      have _h_inl_14 : (((d : ℝ) + 1) / d) / ((((d : ℝ) + 1) / d) - 1) = (d : ℝ) + 1 := by
          have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
          field_simp
          ring


      rw [_h_inl_14]
      have he : ENNReal.ofReal ((d : ℝ) + 1) = parabolicExponent d := by
        simp [parabolicExponent, ENNReal.ofReal_add, Nat.cast_nonneg]
      rw [he]
      have hind :=
        indicator_eq_self.2 ((Function.support_subset_iff').2 fun q hq =>
          image_eq_zero_of_notMem_tsupport (fun h => hq (hFsupp h)))
      unfold parabolicLpNorm parabolicELpNorm
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_Ioo.prod MeasurableSet.univ), hind]
    rw [_h_xinl_0] at hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hle
  have _h_xinl_0 : unitOccupationMeasure K ρ (Ioo (0 : ℝ) 1 ×ˢ univ)ᶜ = 0 := by
    rw [unitOccupationMeasure, Measure.map_apply (by fun_prop)
      ((measurableSet_Ioo.prod MeasurableSet.univ).compl)]
    have he : (fun q : (PDE.Vec d × ElapsedTime (ENNReal.ofReal (1 : ℝ))) × PDE.Vec d =>
        (q.1.2.1, q.2)) ⁻¹'
        (Ioo (0 : ℝ) 1 ×ˢ univ)ᶜ = ∅ := by
      ext q
      simp only [mem_preimage, mem_compl_iff, mem_prod, mem_Ioo, mem_univ, and_true,
        mem_empty_iff_false, iff_false, not_not]
      exact ⟨q.1.2.2.1, ((ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mp q.1.2.2.2)⟩
    rw [he, measure_empty]
  obtain ⟨_hac, g, hgm, hg0, hgi, hgr, hgrn, hgmass, hgpair⟩ :=
    exists_density_of_smooth_tests volume (unitOccupationMeasure K ρ)
      (isOpen_Ioo.prod isOpen_univ) _h_xinl_0
      (occupation_endpoint_gt_one hd) (mul_nonneg hC₀ hM) htest
  have h1 : MemLp g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ)) :=
    memLp_one_iff_integrable.2 hgi
  have hnormMass : (eLpNorm g 1 (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal =
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
    have _h_xinl_0 : unitOccupationMeasure K ρ univ ≤ ρ univ := by
      rw [unitOccupationMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ]
      exact unitOccupationProduct_mass_le K ρ
    exact ENNReal.toReal_mono (measure_ne_top ρ univ) _h_xinl_0
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
    obtain ⟨hgγ, hgγn⟩ := memLp_intermediate_of_bounds (occupation_endpoint_gt_one hd)
      hγ hγr hA h1 hgr h1A hrA
    refine ⟨hgγ, ?_⟩
    change (eLpNorm g (ENNReal.ofReal γ)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ univ))).toReal ≤ (2 * (C₀ + 1)) * M
    simpa only [mul_assoc] using hgγn

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
