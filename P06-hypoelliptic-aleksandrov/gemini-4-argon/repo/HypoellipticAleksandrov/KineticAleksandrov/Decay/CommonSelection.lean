module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Minorant
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Trimming
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
import Mathlib.MeasureTheory.Measure.Real
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantChain
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantMass
import Mathlib.Tactic.Positivity
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantMassComparison
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
import HypoellipticAleksandrov.Parabolic.LocalClassical
import HypoellipticAleksandrov.Statements.ParabolicHarnack

/-! # Integrating the source minorant and selecting common marginals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder
open scoped ENNReal Topology

private theorem marginal_query_eq {d D γ} (hD : MeasurableSet D) (B : CoefficientField d)
    (K : MovingFiberKernel D γ)
    (hpar : HasParabolicMarginalBundle D γ hD (zIndependentCoefficient B) K)
    (s T : ℝ) (hsT : s ≤ T) (p : EvolutionState D γ s) :
    P K hD (scalarQuery s T hsT p.1.1 p.2.1) =
      (K.master (evolutionQueryOfState D γ s T hsT p)).map Prod.fst := by
  obtain ⟨Q, hfirst, _⟩ := hpar (fun _ _ _ _ => rfl)
  change Measure.map Subtype.val
    (parabolicMarginalKernel K hD s T hsT ⟨p.1.1, p.2.1⟩) = _
  rw [hfirst s T hsT ⟨p.1.1, p.2.1⟩ p.1.2,
    K.map_fiberFirstMarginal_eq_firstMarginal hD s T hsT]
  rfl

private theorem integrated_minorant {d D γ} (K : MovingFiberKernel D γ) {s T } (hsT : s ≤ T)
    (R : Measure (EvolutionState D γ s)) [IsFiniteMeasure R]
    (a h ) (ha : 0 < a) (hmass : R.real univ = a)
    (ν : Measure (PDE.Vec d))
    (hminor : ∀ᵐ p ∂R, ENNReal.ofReal h • ν ≤
      (K.master (evolutionQueryOfState D γ s T hsT p)).map Prod.fst) :
    ENNReal.ofReal (a * h) • ν ≤ (continuedMeasure K hsT R).map Prod.fst := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_fst hA, continuedMeasure_apply K hsT R (measurable_fst hA)]
  have hmass' : R univ = ENNReal.ofReal a := by
    rw [← hmass]
    exact (ofReal_measureReal (measure_ne_top _ _)).symm
  calc
    ENNReal.ofReal (a * h) * ν A =
        ∫⁻ _p, ENNReal.ofReal h * ν A ∂R := by
      rw [lintegral_const, hmass', ENNReal.ofReal_mul ha.le]
      ring
    _ ≤ _ := lintegral_mono_ae (by
      filter_upwards [hminor] with p hp
      have he := hp A
      simpa only [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_fst hA] using he)

/- Integrating the source terminal minorant supplies two dominated portions
with exactly the same first marginal and the uniform source mass floor. -/
theorem continued_common_minorant_trimming (d ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ h q0 : ℝ, 0 < h ∧ 0 < q0 ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (v0 : PDE.Vec d) (ρ T : ℝ), v0 ∈ D → 0 < ρ →
        PDE.euclideanBall v0 (4 * ρ) ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * ρ)) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (zIndependentCoefficient B) b K →
      ∀ (s a η : ℝ), s = T - 4 * ρ ^ 2 →
      ∀ (hsT : s ≤ T), 0 < a → 0 < η → η < ρ →
      ∀ (R1 R2 : Measure (EvolutionState (PDE.euclideanBall v0 (4 * ρ)) stationary s)),
        IsFiniteMeasure R1 → IsFiniteMeasure R2 →
        R1.real univ = a → R2.real univ = a →
        (∀ᵐ p ∂R1, p.1.1 ∈ PDE.euclideanBall v0 η) →
        (∀ᵐ p ∂R2, p.1.1 ∈ PDE.euclideanBall v0 η) →
      ∀ (E1 E2 M : Measure (EvolutionAmbientState d)), IsFiniteMeasure M →
        (∀ A, MeasurableSet A → E1 A =
          ∫⁻ p, K.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1) →
        (∀ A, MeasurableSet A → E2 A =
          ∫⁻ p, K.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2) →
        E1 + E2 ≤ M →
      ∀ (qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qlate.1 = (T - ρ ^ 2, T, v0) →
        let Θ := ENNReal.ofReal (a * h) •
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
        Θ ≤ E1.map Prod.fst ∧ Θ ≤ E2.map Prod.fst ∧ a * h * q0 ≤ Θ.real univ ∧
        ∃ F1 F2 : Measure (EvolutionAmbientState d),
          F1 ≤ E1 ∧ F2 ≤ E2 ∧ F1 + F2 ≤ M ∧
          F1.map Prod.fst = Θ ∧ F2.map Prod.fst = Θ := by
  obtain ⟨h, q0, hh, hq0, hminor⟩ : ∃ h q0 : ℝ, 0 < h ∧ 0 < q0 ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (v0 : PDE.Vec d) (ρ T : ℝ), v0 ∈ D → 0 < ρ →
        PDE.euclideanBall v0 (4 * ρ) ⊆ D →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * ρ)) stationary)
        (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
        RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
          (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
          (zIndependentCoefficient B) K →
        IsDomainMonotoneEvolution (PDE.euclideanBall v0 (4 * ρ)) stationary
          (zIndependentCoefficient B) b K →
      ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qearly.1 = (T - 4 * ρ ^ 2, T, qearly.1.2.2) →
        qlate.1 = (T - ρ ^ 2, T, v0) →
        qearly.1.2.2 ∈ PDE.euclideanBall v0 ρ →
        ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qearly ∧
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
            (PDE.euclideanBall v0 (4 * ρ)) := by
    obtain ⟨h, hh, hcomp⟩ : ∃ h : ℝ, 0 < h ∧
        ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
        ∀ (v0 : PDE.Vec d) (ρ T : ℝ), 0 < ρ →
        ∀ (K : MovingFiberKernel (PDE.euclideanBall v0 (4 * ρ)) stationary),
          HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * ρ)) stationary
            (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
            (zIndependentCoefficient B) K →
        ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
          qearly.1 = (T - 4 * ρ ^ 2, T, qearly.1.2.2) →
          qlate.1 = (T - ρ ^ 2, T, v0) →
          qearly.1.2.2 ∈ PDE.euclideanBall v0 ρ →
          ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate ≤
            P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qearly := by
        obtain ⟨hf, hfpos, hfH⟩ : ∃ hfrak : ℝ, 0 < hfrak ∧
      ∀ (B : CoefficientField d) (u : TimeVelocity d → ℝ),
        IsContinuousCoefficientOn B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4, (coefficientAt B p).IsSymm) →
        HasLowerEllipticityOn lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        HasUpperEllipticityOn Lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsScalarC12On u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsNonnegativeOn u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4,
          scalarTimeDerivative u p =
            matrixContraction (coefficientAt B p) (scalarSpatialHessian u p)) →
        ∀ v ∈ PDE.euclideanBall 0 1, hfrak ^ 6 * u (1, 0) ≤ u (4, v) := by
          obtain ⟨hf, hfpos, hfH⟩ := parabolic_harnack_unit_cylinder d hd lam hlam Lam hlamLam
          refine ⟨hf, hfpos, ?_⟩
          intro B u hcont hsymm hlow hup hC12 hnn heq v hv
          have hv' : PDE.vecEuclideanNorm v < 1 := by
            have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
              (by norm_num : (0 : ℝ) < 1)).1 hv
            simpa only [sub_zero] using this

          have step : ∀ (t0 : ℝ) (c p p' : PDE.Vec d), 0 < t0 → c ∈ PDE.euclideanBall 0 1 →
              p - c ∈ PDE.euclideanBall 0 (1 / 2) → p' - c ∈ PDE.euclideanBall 0 (1 / 2) →
              ∀ t t' : ℝ, t = t0 + 3 / 8 → t' = t0 + 7 / 8 → hf * u (t, p) ≤ u (t', p') := by
            intro t0 c p p' ht0 hc hp hp' t t' ht ht'
            have hc' : PDE.vecEuclideanNorm c < 1 := by
              have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
                (by norm_num : (0 : ℝ) < 1)).1 hc
              simpa only [sub_zero] using this
            have hmaps : MapsTo (scalarAffine t0 1 c 1)
                (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1)
                (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 4) := by
              rintro ⟨s, w⟩ ⟨⟨hs0, hs1⟩, hw⟩
              refine ⟨?_, ?_⟩
              · change 0 < t0 + 1 * s
                linarith
              · have hw' : PDE.vecEuclideanNorm w < 1 := by
                  have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
                    (by norm_num : (0 : ℝ) < 1)).1 hw
                  simpa only [sub_zero] using this
                rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 4), sub_zero]
                change PDE.vecEuclideanNorm (c + (1 : ℝ) • w) < 4
                rw [one_smul]
                linarith [PDE.vecEuclideanNorm_add_le c w]
            have hu12 := isScalarC12On_comp_scalarAffine hC12 hmaps
            have hP0 : ((3 / 8 : ℝ), p - c) ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
                PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) :=
              ⟨⟨by norm_num, by norm_num⟩, hp⟩
            have hP1 : ((7 / 8 : ℝ), p' - c) ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
                PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) :=
              ⟨⟨by norm_num, by norm_num⟩, hp'⟩
            have key := hfH (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w))
              (fun z => u (scalarAffine t0 1 c 1 z))
              (hcont.comp (contDiff_scalarAffine t0 1 c 1).continuous.continuousOn hmaps)
              (fun z hz => hsymm _ (hmaps hz))
              (fun z hz => hlow _ (hmaps hz)) (fun z hz => hup _ (hmaps hz)) hu12
              (fun z hz => hnn _ (hmaps hz))
              (by
                intro z hz
                have h1 := hC12.timeSlice_differentiableAt (hmaps hz)
                have h2 := hC12.spatialSlice_contDiffAt (hmaps hz)
                rw [scalarTimeDerivative_comp_scalarAffine h1,
                  scalarSpatialHessian_comp_scalarAffine h2,
                  show coefficientAt (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w)) z =
                    coefficientAt B (scalarAffine t0 1 c 1 z) from rfl,
                  one_pow, one_smul, one_mul]
                exact heq _ (hmaps hz))
              _ hP0 _ hP1
            have e0 : scalarAffine t0 1 c 1 ((3 / 8 : ℝ), p - c) = (t, p) := by
              simp only [scalarAffine, one_mul, one_smul, ht, add_sub_cancel]
            have e1 : scalarAffine t0 1 c 1 ((7 / 8 : ℝ), p' - c) = (t', p') := by
              simp only [scalarAffine, one_mul, one_smul, ht', add_sub_cancel]
            simpa only [e0, e1] using key

          have chain : ∀ j : ℕ, j ≤ 6 →
              hf ^ j * u (1, 0) ≤ u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) := by
            intro j
            induction j with
            | zero => intro _; simp
            | succ j ih =>
              intro hj
              have ih' := ih (by omega)
              have hjR : (j : ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
              have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
              have hnv0 := PDE.vecEuclideanNorm_nonneg v
              have hc : (((2 * j + 1) / 12 : ℝ)) • v ∈ PDE.euclideanBall (0 : PDE.Vec d) 1 := by
                rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1), sub_zero,
                  PDE.vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
                nlinarith
              have hp : ((j : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v ∈
                  PDE.euclideanBall (0 : PDE.Vec d) (1 / 2) := by
                have : ((j : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v = (-(1 / 12 : ℝ)) • v := by
                  module
                rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1 / 2),
                  sub_zero, PDE.vecEuclideanNorm_smul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
                nlinarith
              have hp' : (((j + 1 : ℕ) : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v ∈
                  PDE.euclideanBall (0 : PDE.Vec d) (1 / 2) := by
                have : (((j + 1 : ℕ) : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v =
                    ((1 / 12 : ℝ)) • v := by
                  push_cast
                  module
                rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1 / 2),
                  sub_zero, PDE.vecEuclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
                nlinarith
              have hstep := step (5 / 8 + (j : ℝ) / 2) (((2 * j + 1) / 12 : ℝ) • v)
                (((j : ℝ) / 6) • v) ((((j + 1 : ℕ) : ℝ) / 6) • v) (by positivity) hc hp hp'
                (1 + (j : ℝ) / 2) (1 + ((j + 1 : ℕ) : ℝ) / 2) (by ring) (by push_cast; ring)
              calc hf ^ (j + 1) * u (1, 0) = hf * (hf ^ j * u (1, 0)) := by ring
                _ ≤ hf * u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) :=
                  mul_le_mul_of_nonneg_left ih' hfpos.le
                _ ≤ u (1 + ((j + 1 : ℕ) : ℝ) / 2, (((j + 1 : ℕ) : ℝ) / 6) • v) := hstep
          have h6 := chain 6 le_rfl
          norm_num at h6
          convert h6 using 2
        refine ⟨hf ^ 6, pow_pos hfpos 6, ?_⟩
        intro B hB v0 ρ T hρ K hpar qearly qlate hqe hql hv
        have hΩo := PDE.isOpen_euclideanBall v0 (4 * ρ)
        rcases qearly with ⟨⟨σ, τ, y⟩, hστ, hy⟩
        rcases qlate with ⟨⟨σ', τ', y'⟩, hστ', hy'⟩
        dsimp only at hqe hql hv
        simp only [Prod.mk.injEq, and_true] at hqe hql
        obtain ⟨hσ, hτ⟩ := hqe
        obtain ⟨hσ', hτ', hy0⟩ := hql
        subst y'
        subst hσ hσ'
        have hT1 : T = τ := hτ.symm
        have hT2 : T = τ' := hτ'.symm
        subst hT1 hT2
        have hfin : IsFiniteMeasure (ENNReal.ofReal (hf ^ 6) •
            P K hΩo.measurableSet ⟨(T - ρ ^ 2, T, v0), hστ', hy'⟩) := by
          refine ⟨?_⟩
          rw [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
        refine measure_le_of_smooth_integral_le hΩo ?_ ?_
        · rw [Measure.smul_apply, P_compl_eq_zero_stationary, smul_zero]
        · intro φ hφ hφc hφsupp h01
          obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩo.measurableSet B K hpar
            φ hφ hφc hφsupp T
          let φ' : PDE.Vec d → ℝ := fun w => φ (parabolicAffine v0 ρ w)
          have hφ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
          have hc' : HasCompactSupport φ' := hφc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
          have hV0 : ParabolicProbe.IsClassicalScalarTerminalSolution
              (PDE.euclideanBall v0 (4 * ρ)) stationary (zIndependentCoefficient B)
              (T + ρ ^ 2 * 0) (smoothTestBorel φ hφ.continuous hφc) V := by
            simpa only [mul_zero, add_zero] using hV
          let B' := normalizedParabolicCoefficient B T ρ v0
          let W : TimeVelocity d → ℝ := fun p => V (minorantAffine T ρ v0 p)
          have hW := isClassicalScalarTerminalSolution_comp_minorantAffine hΩo B T v0 hρ
            (parabolicAffine_preimage_ball v0 hρ).symm 0
            (smoothTestBorel φ hφ.continuous hφc) (smoothTestBorel φ' hφ'.continuous hc')
            (fun _ => rfl) hV0
          have hB' := normalizedParabolicCoefficient_sectionTwo lam Lam B hB T v0 ρ hρ
          have hcontB := continuous_coefficientAt_of_smooth hB'.2.2.1
          let w : PDE.Vec d := ρ⁻¹ • (y - v0)
          have hwpoint : parabolicAffine v0 ρ w = y := by
            simp [w, parabolicAffine, smul_smul, ne_of_gt hρ]
          have hw : w ∈ PDE.euclideanBall 0 1 := by
            change PDE.vecNormSq (w - 0) < 1 ^ 2
            simp only [sub_zero, one_pow]
            have heq : PDE.vecNormSq (y - v0) = ρ ^ 2 * PDE.vecNormSq w := by
              rw [← hwpoint]
              change PDE.euclideanSqDist (v0 + ρ • w) v0 = _
              rw [add_comm, PDE.euclideanSqDist_affine_center]
              simp only [PDE.euclideanSqDist, sub_zero]
            change PDE.vecNormSq (y - v0) < ρ ^ 2 at hv
            nlinarith [sq_pos_of_pos hρ]
          have hnonneg : IsNonnegativeOn (fun p => W (timeReversal 0 p))
              (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) := by
            intro p hp
            have hpball : parabolicAffine v0 ρ p.2 ∈ PDE.euclideanBall v0 (4 * ρ) := by
              rw [← parabolicAffine_preimage_ball v0 hρ] at hp
              exact hp.2
            have ht : T + ρ ^ 2 * (-p.1) ≤ T := by
              have hprod := mul_nonneg (sq_nonneg ρ) (show 0 ≤ p.1 from hp.1.le)
              nlinarith only [hprod]
            have heval := hVeval _ ht (parabolicAffine v0 ρ p.2)
              (by simpa only [movingDomain_stationary] using hpball)
            have he : timeReversal 0 p = (-p.1, p.2) := by
              simpa only [zero_sub] using timeReversal_apply 0 p.1 p.2
            change 0 ≤ W (timeReversal 0 p)
            rw [he]
            change 0 ≤ V (T + ρ ^ 2 * (-p.1), parabolicAffine v0 ρ p.2)
            rw [heval]
            exact integral_nonneg fun x => (h01 x).1
          have key := hfH (fun θ v => B' (0 + -1 * θ) (0 + (1 : ℝ) • v))
            (fun p => W (timeReversal 0 p))
            (hcontB.continuousOn.comp (contDiff_scalarAffine 0 (-1) 0 1).continuous.continuousOn
              (fun p _ => mem_univ _))
            (fun p _ => hB'.2.2.2.1 _ _)
            (fun p _ => hB'.2.2.2.2.1 _ _) (fun p _ => hB'.2.2.2.2.2 _ _)
            (timeReversed_isScalarC12On (PDE.isOpen_euclideanBall 0 4) hW)
            hnonneg (timeReversed_equation (PDE.isOpen_euclideanBall 0 4) hW) w hw
          have e1 : minorantAffine T ρ v0 (timeReversal 0 (1, 0)) =
              (T - ρ ^ 2, v0) := by
            simp [minorantAffine, scalarAffine, timeReversal, sub_eq_add_neg]
          have e4 : minorantAffine T ρ v0 (timeReversal 0 (4, w)) =
              (T - 4 * ρ ^ 2, y) := by
            rw [timeReversal_apply]
            simp only [zero_sub]
            change (T + ρ ^ 2 * (-4), parabolicAffine v0 ρ w) = _
            rw [hwpoint]
            congr 1
            ring
          change hf ^ 6 * V (minorantAffine T ρ v0 (timeReversal 0 (1, 0))) ≤
            V (minorantAffine T ρ v0 (timeReversal 0 (4, w))) at key
          rw [e1, e4] at key
          have hlate := hVeval (T - ρ ^ 2) hστ' v0 hy'
          have hearly := hVeval (T - 4 * ρ ^ 2) hστ y hy
          rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hfpos 6).le, smul_eq_mul]
          change hf ^ 6 * ∫ x, φ x ∂(P K hΩo.measurableSet
              (scalarQuery (T - ρ ^ 2) T hστ' v0 hy')) ≤
            ∫ x, φ x ∂(P K hΩo.measurableSet (scalarQuery (T - 4 * ρ ^ 2) T hστ y hy))
          rw [← hlate, ← hearly]
          exact key

      /- The source common terminal minorant for the same supplied marginal kernel. -/
    obtain ⟨C, q, _hC, _hq, hqpos, hmass⟩ : ∃ Cstar q0 : ℝ, 0 < Cstar ∧ q0 = Real.exp (-Cstar / 9) ∧ 0 < q0 ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (v0 : PDE.Vec d) (ρ T R : ℝ), 0 < ρ → R = 4 * ρ →
      ∀ (K : MovingFiberKernel (PDE.euclideanBall v0 R) stationary),
        HasParabolicMarginalBundle (PDE.euclideanBall v0 R) stationary
          (PDE.isOpen_euclideanBall v0 R).measurableSet
          (zIndependentCoefficient B) K →
      ∀ (qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 R) stationary),
        qlate.1 = (T - ρ ^ 2, T, v0) →
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall v0 R).measurableSet qlate
            (PDE.euclideanBall v0 R) := by
      obtain ⟨N, hN, _hchoice, hc⟩ := exists_retention_barrier_order d hd lam Lam hlam hlamLam
      let Cstar : ℝ := 2 * N * d * Lam
      have hLam := hlam.trans_le hlamLam
      have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
      have hC : 0 < Cstar := by dsimp [Cstar]; positivity
      refine ⟨Cstar, Real.exp (-Cstar / 9), hC, rfl, Real.exp_pos _, ?_⟩
      intro B hB v0 ρ T R hρ hR K hpar qlate hql
      subst R
      have hΩ := PDE.isOpen_euclideanBall v0 (4 * ρ)
      have hcompact := PDE.isCompact_euclideanClosedBall v0 (by positivity : 0 ≤ 3 * ρ)
      have hsub : PDE.euclideanClosedBall v0 (3 * ρ) ⊆ PDE.euclideanBall v0 (4 * ρ) :=
        PDE.euclideanClosedBall_subset_euclideanBall (by positivity) (by linarith)
      obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ :=
        exists_smooth_cutoff hcompact hΩ hsub
      obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩ.measurableSet B K hpar
        φ hφ hφc hφsupp T
      let φ' : PDE.Vec d → ℝ := fun y => φ (parabolicAffine v0 ρ y)
      have hφ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
      have hc' : HasCompactSupport φ' := hφc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
      have hV0 : ParabolicProbe.IsClassicalScalarTerminalSolution
          (PDE.euclideanBall v0 (4 * ρ)) stationary (zIndependentCoefficient B)
          (T + ρ ^ 2 * 0) (smoothTestBorel φ hφ.continuous hφc) V := by
        simpa only [mul_zero, add_zero] using hV
      have hW := isClassicalScalarTerminalSolution_comp_minorantAffine hΩ B T v0 hρ
        (parabolicAffine_preimage_ball v0 hρ).symm 0
        (smoothTestBorel φ hφ.continuous hφc) (smoothTestBorel φ' hφ'.continuous hc')
        (fun _ => rfl) hV0
      have hdom : ∀ y : PDE.Vec d, barrier N 3 y ≤
          smoothTestBorel φ' hφ'.continuous hc' y := by
        intro y
        change barrier N 3 y ≤ φ (parabolicAffine v0 ρ y)
        by_cases hy : y ∈ PDE.euclideanBall 0 3
        · have hyc : parabolicAffine v0 ρ y ∈ PDE.euclideanClosedBall v0 (3 * ρ) := by
            change PDE.euclideanSqDist (v0 + ρ • y) v0 ≤ (3 * ρ) ^ 2
            rw [add_comm, PDE.euclideanSqDist_affine_center]
            change PDE.vecNormSq (y - 0) < 3 ^ 2 at hy
            rw [sub_zero] at hy
            simp only [PDE.euclideanSqDist, sub_zero]
            nlinarith [sq_pos_of_pos hρ]
          rw [hφone _ hyc]
          exact ((retention_polynomial_barrier (d := d) hN 3 (by norm_num)).2.1 y).2
        · rw [((retention_polynomial_barrier hN 3 (by norm_num)).2.2.2.2 y hy).1]
          exact (hφbound _).1
      have hfloor := minorant_scalar_barrier_floor hN lam Lam hlam hlamLam hc
        (normalizedParabolicCoefficient B T ρ v0)
        (normalizedParabolicCoefficient_sectionTwo lam Lam B hB T v0 ρ hρ)
        _ _ hW hdom
      have hpoint : minorantAffine T ρ v0 (-1, 0) = (T - ρ ^ 2, v0) := by
        simp [minorantAffine, scalarAffine, sub_eq_add_neg]
      change Real.exp (-Cstar / 9) ≤ V (minorantAffine T ρ v0 (-1, 0)) at hfloor
      rw [hpoint] at hfloor
      have hv0 : v0 ∈ movingDomain (PDE.euclideanBall v0 (4 * ρ)) stationary (T - ρ ^ 2) := by
        rw [movingDomain_stationary]
        change PDE.vecNormSq (v0 - v0) < (4 * ρ) ^ 2
        simp only [sub_self]
        simpa [PDE.vecNormSq, PDE.vecDot] using
          sq_pos_of_pos (show 0 < 4 * ρ by positivity)
      have heval := hVeval (T - ρ ^ 2) (by nlinarith [sq_nonneg ρ]) v0 hv0
      have hq : scalarQuery (T - ρ ^ 2) T (by nlinarith [sq_nonneg ρ]) v0 hv0 = qlate :=
        Subtype.ext hql.symm
      rw [hq] at heval
      rw [heval] at hfloor
      have hint := integral_le_measure (μ := P K hΩ.measurableSet qlate)
        (s := univ) (f := φ) (fun y _ => (hφbound y).2)
        (fun y hy => (hy (mem_univ y)).elim)
      have hmass : P K hΩ.measurableSet qlate univ =
          P K hΩ.measurableSet qlate (PDE.euclideanBall v0 (4 * ρ)) := by
        rw [← measure_add_measure_compl hΩ.measurableSet,
          P_compl_eq_zero_stationary, add_zero]
      exact (ENNReal.ofReal_le_ofReal hfloor).trans (hint.trans_eq hmass)
    refine ⟨h, q, hh, hqpos, ?_⟩
    intro m Lb D B b hset v0 ρ T hv0 hρ hsub S K hreal hpar hmono
      qearly qlate hqe hql hv
    have _ := And.intro hv0 (And.intro hsub (And.intro hreal hmono))
    exact ⟨hcomp B hset.1 v0 ρ T hρ K hpar qearly qlate hqe hql hv,
      hmass B hset.1 v0 ρ T (4 * ρ) hρ rfl K hpar qlate hql⟩
  refine ⟨h, q0, hh, hq0, ?_⟩
  intro m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar hmono
    s a η hs hsT ha hη hηρ R1 R2 hf1 hf2 hmass1 hmass2 hsupport1 hsupport2
    E1 E2 M hfM hE1 hE2 hdom qlate hql
  let ν := P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
  let Θ := ENNReal.ofReal (a * h) • ν
  have hpoint (R : Measure (EvolutionState (PDE.euclideanBall v0 (4 * ρ)) stationary s))
      (hsupport : ∀ᵐ p ∂R, p.1.1 ∈ PDE.euclideanBall v0 η) :
      ∀ᵐ p ∂R, ENNReal.ofReal h • ν ≤
        (K.master (evolutionQueryOfState _ stationary s T hsT p)).map Prod.fst := by
    filter_upwards [hsupport] with p hp
    have hpρ :=
      PDE.euclideanBall_mono hη.le hηρ.le hp
    have hh' := (hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar
      hmono (scalarQuery s T hsT p.1.1 p.2.1) qlate
      (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).1
    rw [marginal_query_eq (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
      B K hpar s T hsT p] at hh'
    exact hh'
  have heq1 := eq_continuedMeasure_of_apply K hsT R1 hE1
  have heq2 := eq_continuedMeasure_of_apply K hsT R2 hE2
  have hmin1 : Θ ≤ E1.map Prod.fst := by
    rw [heq1]
    exact integrated_minorant K hsT R1 a h ha hmass1 ν (hpoint R1 hsupport1)
  have hmin2 : Θ ≤ E2.map Prod.fst := by
    rw [heq2]
    exact integrated_minorant K hsT R2 a h ha hmass2 ν (hpoint R2 hsupport2)
  have hfE1 : IsFiniteMeasure E1 := heq1.symm ▸ inferInstance
  have hfE2 : IsFiniteMeasure E2 := heq2.symm ▸ inferInstance
  have hνmass : q0 ≤ ν.real univ := by
    let p : EvolutionPosition (PDE.euclideanBall v0 (4 * ρ)) stationary s :=
      ⟨v0, by
        rw [movingDomain_stationary]
        simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_self,
          PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
          using sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hρ)⟩
    have hpρ : v0 ∈ PDE.euclideanBall v0 ρ := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_self,
        PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
        using sq_pos_of_pos hρ
    have he := (hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar
      hmono (scalarQuery s T hsT v0 p.2) qlate
      (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).2
    have hfν : IsFiniteMeasure ν := inferInstance
    simpa only [ENNReal.toReal_ofReal hq0.le, measureReal_def] using (ENNReal.toReal_mono (measure_ne_top ν univ) (he.trans (measure_mono (subset_univ _))))
  have hfloor : a * h * q0 ≤ Θ.real univ := by
    rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (mul_pos ha hh).le]
    exact mul_le_mul_of_nonneg_left hνmass (mul_pos ha hh).le
  obtain ⟨g1, hg1, hgle1, hΘ1, hmap1, hF1⟩ := exists_trimming_of_le_map_fst E1 Θ hmin1
  obtain ⟨g2, hg2, hgle2, hΘ2, hmap2, hF2⟩ := exists_trimming_of_le_map_fst E2 Θ hmin2
  exact ⟨hmin1, hmin2, hfloor, E1.withDensity (g1 ∘ Prod.fst),
    E2.withDensity (g2 ∘ Prod.fst), hF1, hF2, (add_le_add hF1 hF2).trans hdom,
    hmap1, hmap2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
