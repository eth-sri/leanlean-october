module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsHomogeneous
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusionConsumers
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FourierDecay
import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlock
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsSource
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceInterior
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorWeak
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorsCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerError
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Borel homogeneous correctors on compact interior collars

The approximating coefficients, evolutions, sources and solutions are constructed
internally. Their smoothness and convergence follow from the weak and Green calculus.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA Filter
open scoped Topology ENNReal Matrix.Norms.Elementwise
open Evolution Green

/- Compact-interior Borel solutions have actual smooth homogeneous correctors. -/
theorem exists_borel_homogeneous_correctors
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d } (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A ) (hA : IsBorelCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticityAE lam A)
    (hhi : HasUpperEllipticityAE Lam A)
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (U : KineticPoint d → ℝ) (hu : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (he : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
      forwardKineticOperator (ofTimeVelocityCoefficient A) U P = 0)
    (K₀ : Set (KineticPoint d)) (hK : IsCompact K₀)
    (hKU : K₀ ⊆ forwardCylinder Z₀ R hR) :
    ∃ (A_j : ℕ → CoefficientField d) (U_j : ℕ → KineticPoint d → ℝ)
      (O : Set (KineticPoint d)),
      IsOpen O ∧ K₀ ⊆ O ∧ closure O ⊆ forwardCylinder Z₀ R hR ∧
      (∀ j, IsSectionTwoCoefficient lam Lam (A_j j)) ∧
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞)
        (U_j j ∘ (KineticPoint.equivProd d).symm) ((KineticPoint.equivProd d) '' O)) ∧
      (∀ j, ∀ P ∈ O,
        forwardKineticOperator (ofTimeVelocityCoefficient (A_j j)) (U_j j) P = 0) ∧
      TendstoUniformlyOn U_j U atTop K₀ := by
  let D := forwardCylinder Z₀ R hR
  have hD : IsOpen D := isOpen_forwardCylinder Z₀ R hR
  obtain ⟨O, χ, hO, hKO, hOD, _, hχs, hχc, hχD, hχb, hχone⟩ :=
    exists_borelCorrector_cutoff hD hK hKU
  have hχ : Continuous χ := boundary_probe_continuous χ hχs
  obtain ⟨B, hB, hconv⟩ := borel_coefficient_approximation lam Lam hlam hLam A hA hs hlo hhi
  have hCoeff j : IsSectionTwoCoefficient lam Lam (B j) :=
    ⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent (hB j).1,
      (hB j).2.1, (hB j).2.2.1, (hB j).2.2.2⟩
  have hEv := exists_terminalEvolution_of_classical hLE hH
  have hwhole := SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam
  choose S K hreal _ _ _ using (fun j => hwhole (B j) (hCoeff j))
  let T := Z₀.time + R ^ 2
  let J := fun j => borelCorrectedFunction (K j) T χ (B j) U
  have hDt : ∀ P ∈ D, P.time < T := fun P hP => hP.2.1
  have hOD' := subset_closure.trans hOD
  have hJ j := borelCorrectedFunction_smooth_homogeneous hH (B j) (hCoeff j) (hB j).1
    (S j) (K j) (hreal j) T D O hD hO hOD' hDt U hu χ hχ hχc hχD
    (fun P hP => hχone P (subset_closure hP))
  let p := 2 * (d : ℝ) + 2
  have hp : 2 * (d : ℝ) + 1 < p := by dsimp [p]; linarith
  have hp0 : 0 < p := by dsimp [p]; positivity
  obtain ⟨hmem, hnorm⟩ : (∀ j, MemLp (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume) ∧
    Tendsto (fun j => (eLpNorm (borelCorrectorSource χ (B j) U)
      (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
    let K := tsupport χ
    have hK : IsCompact K := hχc
    have hhm :=
      hu.continuousOn_kineticVelocityHessian.mono hχD
    obtain ⟨_, hErr, hErr0⟩ := borel_inner_error hlam hLam A hA hlo hhi
      B hB hconv K hK (kineticVelocityHessian U) hhm hp0
    have hEq j : K.indicator (borelCorrectorSource χ (B j) U) =
        borelCorrectorSource χ (B j) U := by
      apply indicator_eq_self.mpr
      intro P hP
      exact subset_tsupport χ (by
        intro hz
        apply hP
        simp only [borelCorrectorSource, hz, zero_mul])
    have hnorm j : eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume =
        eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) (volume.restrict K) := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet, hEq j]
    have hb j : ∀ᵐ P ∂volume.restrict K,
        ‖borelCorrectorSource χ (B j) U P‖ ≤ ‖borelCoefficientError (B j) A
          (kineticVelocityHessian U) P‖ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hχD he] with P hP
      have hop : forwardKineticOperator (ofTimeVelocityCoefficient (B j)) U P -
        forwardKineticOperator (ofTimeVelocityCoefficient A) U P =
        matrixContraction ((B j) P.time P.velocity - A P.time P.velocity)
          (kineticVelocityHessian U P) := by
        let B := (B j)
        simp only [forwardKineticOperator_apply, ofTimeVelocityCoefficient, matrixContraction,
          Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [hP, sub_zero] at hop
      simp only [borelCorrectorSource, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hχb P).1, hop, borelCoefficientError, abs_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχb P).2
    have hmem j : MemLp (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p)
        (volume.restrict K) := by
      have hc := (borelCorrectorSource_continuous_compact hD χ hχ hχc hχD
        (B j) (hB j).1 U hu).1
      exact (hErr j).of_le hc.measurable.aestronglyMeasurable.restrict (hb j)
    have hbound j : (eLpNorm (borelCorrectorSource χ (B j) U)
        (ENNReal.ofReal p) volume).toReal ≤
        (eLpNorm (borelCoefficientError (B j) A (kineticVelocityHessian U))
          (ENNReal.ofReal p) (volume.restrict K)).toReal := by
      rw [hnorm j]
      exact ENNReal.toReal_mono (hErr j).eLpNorm_ne_top
        (eLpNorm_mono_ae (hmem j).aestronglyMeasurable (hb j))
    refine ⟨fun j => ?_, ?_⟩
    · have hm := (memLp_indicator_iff_restrict hK.measurableSet).mpr (hmem j)
      rwa [hEq j] at hm
    · exact squeeze_zero (fun j => ENNReal.toReal_nonneg) hbound hErr0
  obtain ⟨C, _, hbound⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R),
      ∀ (F : KineticPoint d → ℝ), Continuous F → HasCompactSupport F →
        tsupport F ⊆ forwardCylinder Z₀ R hR →
        MemLp F (ENNReal.ofReal p) volume →
      ∀ P ∈ forwardCylinder Z₀ R hR,
        |borelCorrectorPotential K (Z₀.time + R ^ 2) F P| ≤
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
            (eLpNorm F (ENNReal.ofReal p) volume).toReal := by
    have hEv := exists_terminalEvolution_of_classical hLE hH
    have hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
    have hOcc := Occupation.parabolicOccupationFamily_holds
      (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam
    have hBlock := Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam
    have hDecay := Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter hBlock
    obtain ⟨C, hC, hgreen⟩ := green_density_bound_of_slabFourierBounds hd lam Lam p
      hlam hLam hp (Green.slabFourierBounds_of_occupation_decay hd lam Lam hOcc hDecay)
    have hp1 : 1 < p := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    let q := p / (p - 1)
    have hq : 1 < q := by
      dsimp only [q]
      rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
      linarith
    have hqp : q.HolderConjugate p := (Real.HolderConjugate.conjExponent hp1).symm
    refine ⟨C, hC, ?_⟩
    intro B hB S K hreal Z₀ R hR F hF hFc hFs hFLp P hP
    let Q := forwardCylinder Z₀ R hR
    let Γ := cylinderGreenMeasure K Z₀ R hR P
    let a := 2 - (4 * (d : ℝ) + 2) / p
    have ht := hP.2.1
    let GP := greenMeasure K P.time (ENNReal.ofReal (remainingTime Z₀ P R))
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    have hGP := greenMeasure_spec K P.time _
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    let A := kineticReflectedCoefficient B
    have hBs : IsSmoothCoefficient B := by
      apply contDiff_pi.mpr
      intro i
      apply contDiff_pi.mpr
      intro j
      exact (hB.2.2.1 i j).comp
        (contDiff_fst.prodMk (contDiff_snd.prodMk
          (contDiff_const (c := (0 : PDE.Vec d)))))
    have hAs := isSmoothCoefficient_kineticReflectedCoefficient B hBs
    have hAreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
        MeasurableSet.univ (zIndependentCoefficient (kineticReflectedCoefficient A))
        (identityDrift d) S K := by
      have hBB : kineticReflectedCoefficient A = B := by
        funext t v
        simp only [A, kineticReflectedCoefficient, neg_neg]
      rw [hBB]
      exact hreal
    have hgreenB := hgreen (kineticReflection Z₀) R hR A hAs
      (isSymmetricCoefficient_kineticReflectedCoefficient B hB.2.2.2.1)
      (fun t v => hB.2.2.2.2.1 (-t) v) (fun t v => hB.2.2.2.2.2 (-t) v)
      S K hAreal
    rw [kineticReflection_involutive Z₀] at hgreenB
    obtain ⟨G, hG, hden, hn, hscale⟩ := hgreenB P hP GP hGP
    have hnorm := hn.trans (ENNReal.ofReal_le_ofReal hscale)
    have hden' : Γ = (volume.restrict Q).withDensity G := by
      dsimp only [Γ, cylinderGreenMeasure]
      rw [dite_eq_left ht]
      exact hden
    obtain ⟨g, hgm, hgn, hgd, hgb, hgLp⟩ := real_density_of_eLpNorm_bound
      (volume.restrict Q) Γ G hG hden' q (C * R ^ a) (lt_trans zero_lt_one hq)
      (mul_nonneg hC (Real.rpow_nonneg hR.le _)) hnorm
    have habs : MemLp (fun Q => |F Q|) (ENNReal.ofReal p) (volume.restrict Q) := by
      simpa only [Real.norm_eq_abs] using hFLp.norm.restrict Q
    have hpair := abp_potential_holder (volume.restrict Q) Γ g (fun Q => |F Q|) hqp
      hgm hgn (Eventually.of_forall fun Q => abs_nonneg (F Q)) hgd hgLp habs hgb
    have hsabs : tsupport (fun Q => |F Q|) ⊆ forwardCylinder Z₀ R hR := by
      apply Subset.trans _ hFs
      apply closure_mono
      intro P hP
      exact abs_ne_zero.mp hP
    have heq := integral_cylinderGreenMeasure K Z₀ R hR (fun Q => |F Q|)
      (fun Q => abs_nonneg _) hF.abs hFc.abs hsabs P ht
    obtain ⟨M, hM⟩ := hFc.exists_bound_of_continuous hF
    have hM0 : 0 ≤ max M 0 := le_max_right _ _
    have hFb : ∀ Q, |F Q| ≤ max M 0 := fun Q => (hM Q).trans (le_max_left _ _)
    have hfirst : |borelCorrectorPotential K (Z₀.time + R ^ 2) F P| ≤
      borelCorrectorPotential K (Z₀.time + R ^ 2) (fun Q => |F Q|) P := by
      let T := (Z₀.time + R ^ 2)
      have hF := hF.measurable
      let M := (max M 0)
      let g := F ∘ sectionTwoPoint
      have hgm : Measurable g := hF.comp (continuous_sectionTwoPoint d).measurable
      have hgb : ∀ Q, |g Q| ≤ M := fun Q => hFb _
      have hi := integrableOn_duhamelIntegrand_bounded K MeasurableSet.univ continuous_const
        g hgm M hM0 hgb (sectionTwoPoint P) T
      have hia := integrableOn_duhamelIntegrand_bounded K MeasurableSet.univ continuous_const
        (fun Q => |g Q|) (by simpa only [Real.norm_eq_abs] using hgm.norm) M hM0
        (fun Q => by rw [abs_abs]; exact hgb Q) (sectionTwoPoint P) T
      have hb : ∀ r, |duhamelIntegrand K g (sectionTwoPoint P) r| ≤
          duhamelIntegrand K (fun Q => |g Q|) (sectionTwoPoint P) r := by
        intro r
        unfold duhamelIntegrand
        split
        · unfold duhamelSourceIntegral
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun w : EvolutionAmbientState d => g ⟨r, w.1, w.2⟩)
        · simp only [abs_zero, le_refl]
      change |∫ r in Ioc P.time T, duhamelIntegrand K g (sectionTwoPoint P) r| ≤ _
      have hn : |∫ r in Ioc P.time T, duhamelIntegrand K g (sectionTwoPoint P) r| ≤
          ∫ r in Ioc P.time T, |duhamelIntegrand K g (sectionTwoPoint P) r| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun r => duhamelIntegrand K g (sectionTwoPoint P) r)
      exact hn.trans (integral_mono
        (by simpa only [Real.norm_eq_abs, sectionTwoPoint] using hi.norm)
        (by simpa only [IntegrableOn, sectionTwoPoint, g, Function.comp_def] using hia) hb)
    have hlast : (eLpNorm (fun Q => |F Q|) (ENNReal.ofReal p)
        (volume.restrict Q)).toReal ≤ (eLpNorm F (ENNReal.ofReal p) volume).toReal := by
      rw [show (fun Q => |F Q|) = (fun Q => ‖F Q‖) from funext fun Q =>
        (Real.norm_eq_abs _).symm, eLpNorm_norm F hFLp.aestronglyMeasurable.restrict]
      exact ENNReal.toReal_mono hFLp.eLpNorm_ne_top (eLpNorm_mono_measure F Measure.restrict_le_self)
    exact hfirst.trans (by
      change borelCorrectorPotential K (Z₀.time + R ^ 2) (fun Q => |F Q|) P ≤ _
      change duhamelPotential K _ _ _ ≤ _
      rw [← heq]
      exact hpair.trans (mul_le_mul_of_nonneg_left hlast
        (mul_nonneg hC (Real.rpow_nonneg hR.le _))))
  let e := fun j => C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
    (eLpNorm (borelCorrectorSource χ (B j) U) (ENNReal.ofReal p) volume).toReal
  have he0 : Tendsto e atTop (𝓝 0) := by
    simpa only [mul_zero] using hnorm.const_mul (C * R ^ (2 - (4 * (d : ℝ) + 2) / p))
  refine ⟨B, J, O, hO, hKO, hOD, hCoeff, fun j => (hJ j).1, fun j => (hJ j).2, ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp he0).2 ε hε] with j hj
  intro P hP
  have hFc := borelCorrectorSource_continuous_compact hD χ hχ hχc hχD (B j) (hB j).1 U hu
  have hFs : tsupport (borelCorrectorSource χ (B j) U) ⊆ D :=
    tsupport_mul_subset_left.trans hχD
  have hb := hbound (B j) (hCoeff j) (S j) (K j) (hreal j) Z₀ R hR
    (borelCorrectorSource χ (B j) U) hFc.1 hFc.2 hFs (hmem j) P (hKU hP)
  have hd : dist (U P) (J j P) =
      |borelCorrectorPotential (K j) T (borelCorrectorSource χ (B j) U) P| := by
    rw [Real.dist_eq]
    dsimp only [J, borelCorrectedFunction]
    rw [show U P - (U P + borelCorrectorPotential (K j) T
      (borelCorrectorSource χ (B j) U) P) =
      -borelCorrectorPotential (K j) T (borelCorrectorSource χ (B j) U) P by ring, abs_neg]
  rw [hd]
  exact hb.trans_lt hj

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
