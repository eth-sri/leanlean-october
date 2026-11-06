module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrierSmooth
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BallEvolution
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrier
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTraces
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Finite-measure passage for bounded source barriers

Smooth source bounds control the total mass of the literal source-action measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution
open scoped ENNReal
open HypoellipticAleksandrov Parabolic Matrix
open scoped Topology MatrixOrder

/- Uniform bounds on smooth compact tests control the mass of a finite measure supported in U. -/
theorem boundedSource_measure_mass_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    {U } (hU : IsOpen U) (hμ : μ Uᶜ = 0) (C : ℝ) (hC : 0 ≤ C)
    (ht : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ C) :
    μ.real univ ≤ C := by
  have hbound : μ U ≤ ENNReal.ofReal C := by
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
    obtain ⟨φ, hφ, hφc, hφU, hφb, hφone⟩ := exists_smooth_cutoff hK hU hKU
    have htest := ht φ hφ hφc hφU hφb
    have hKi : Integrable (K.indicator (1 : E → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hK.measurableSet
    have hφi : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hKreal : μ.real K ≤ C := by
      rw [← integral_indicator_one hK.measurableSet]
      refine (integral_mono hKi hφi (fun x => ?_)).trans htest
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, Pi.one_apply, hφone x hx, le_refl]
      · simpa only [indicator_of_notMem hx] using (hφb x).1
    have hKbound : μ K ≤ ENNReal.ofReal C := by
      apply (ENNReal.toReal_le_toReal (measure_ne_top μ K) ENNReal.ofReal_ne_top).mp
      simpa only [Measure.real, ENNReal.toReal_ofReal hC] using hKreal
    exact hrK.trans_le hKbound
  have heq : μ U = μ univ := by
    simpa only [hμ, add_zero] using (measure_add_measure_compl hU.measurableSet (μ := μ))
  rw [heq] at hbound
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/- The source-action measure from one starting point has quadratically controlled mass. -/
theorem abs_duhamelPotential_le_boundedSourceQuadratic
    (hH : HormanderHypoellipticityStatement) {d } (hd : 0 < d)
    {c : PDE.Vec d} {R : ℝ} (hR : 0 < R) {lam Lam m Lb }
    (hlam : 0 < lam) (hm : 0 < m)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (hb : IsSmoothDrift b)
    (hbounds : HasTransportBounds m Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall c R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) (fun _ => 0)
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Measurable g) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ q, |g q| ≤ M) (T : ℝ) (p : KineticPoint d)
    (hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T) :
    |duhamelPotential K T g p| ≤ boundedSourceQuadratic c R lam p * M := by
  let μ := boundedSourceActionMeasure K (Measure.dirac p) p.time T
  have hΩm := (PDE.isOpen_euclideanBall c R).measurableSet
  have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec d)) := continuous_const
  have hi := integral_boundedSourceActionMeasure K hΩm hγ (Measure.dirac p) p.time T
    g hg M hM hgb
  change (∫ q, g ⟨q.1, q.2.1, q.2.2⟩ ∂μ) =
    ∫ q, (∫ r in Ioo p.time T, duhamelIntegrand K g q r) ∂Measure.dirac p at hi
  rw [integral_dirac, ← duhamelPotential_eq_integral_window K g p le_rfl] at hi
  have hnorm := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun q => g ⟨q.1, q.2.1, q.2.2⟩) (C := M)
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hgb _)
  rw [Real.norm_eq_abs, hi] at hnorm
  have hmass : (boundedSourceActionMeasure K (Measure.dirac p) p.time T).real univ ≤
      boundedSourceQuadratic c R lam p := by
      let μ := boundedSourceActionMeasure K (Measure.dirac p) p.time T
      have hΩm := (PDE.isOpen_euclideanBall c R).measurableSet
      have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec d)) := continuous_const
      have hU := isOpen_boundedSourcePast (PDE.isOpen_euclideanBall c R) hγ T
      have hμ := boundedSourceActionMeasure_compl_past K hΩm hγ (Measure.dirac p) p.time T
      have hQn : 0 ≤ boundedSourceQuadratic c R lam p := by
        apply boundedSourceQuadratic_nonneg hlam c R
        simpa only [boundedSource_stationary_domain] using hp.2
      apply boundedSource_measure_mass_le μ hU hμ _ hQn
      intro φ hφ hφc hφU hφb
      let g := φ ∘ KineticPoint.equivProd d
      have hg : Continuous g := hφ.continuous.comp (KineticPoint.homeomorphProd d).continuous
      have hgc : HasCompactSupport g := hφc.comp_homeomorph (KineticPoint.homeomorphProd d)
      have hgs := hφ
      have hgn : ∀ q, 0 ≤ g q := fun q => (hφb _).1
      have hgb : ∀ q, g q ≤ 1 := fun q => (hφb _).2
      have hga : ∀ q, |g q| ≤ 1 := fun q => by rw [abs_of_nonneg (hgn q)]; exact hgb q
      have hgU : tsupport g ⊆
          evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T := by
        rw [boundedSourceTest_support]
        intro q hq
        exact hφU hq
      have hi := integral_boundedSourceActionMeasure K hΩm hγ (Measure.dirac p) p.time T
        g hg.measurable 1 zero_le_one hga
      change (∫ q, φ q ∂μ) =
        ∫ q, (∫ r in Ioo p.time T, duhamelIntegrand K g q r) ∂Measure.dirac p at hi
      rw [integral_dirac, ← duhamelPotential_eq_integral_window K g p le_rfl] at hi
      rw [hi]
      have hΩ := LocalA.localBall_admissible c hR
      have hΩm := (PDE.isOpen_euclideanBall c R).measurableSet
      have hγ : Continuous (fun _ : ℝ => (0 : PDE.Vec d)) := continuous_const
      let W := duhamelPotential K T g
      let Q := boundedSourceQuadratic c R lam
      have hWc := continuousOn_duhamelPotential hΩ hΩm hγ B b S K hreal
        g hgn hg hgc hgs T hgU
      have hWs := duhamelPotential_contDiffOn hH hΩ hΩm hγ B b S K hreal
        hB hBs hb g hgn hg hgc hgs T hgU hlam hm hell hbounds.2
      have hWe := duhamelPotential_source_equation hH hΩ hΩm hγ B b S K hreal
        hB hBs hb g hgn hg hgc hgs T hgU hlam hm hell hbounds.2
      have hU := (isOpen_duhamelCylinder (PDE.isOpen_euclideanBall c R) hγ T).preimage
        (evolutionHomeomorph d).continuous
      have hreg : ∀ q ∈ evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T,
          IsSliceRegularAt W q := by
        intro q hq
        apply boundedSource_sliceRegular_of_smooth
        have hqm : (evolutionHomeomorph d).symm q ∈
            evolutionHomeomorph d ⁻¹'
              evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T := by
          simpa using hq
        exact hWs.contDiffAt (hU.mem_nhds hqm)
      have hslab : movingClosedSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T ⊆
          evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T :=
        fun q hq => ⟨hq.2.1, hq.2.2⟩
      have hactive : movingActiveSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T ⊆
          evolutionPastOpenCylinder (PDE.euclideanBall c R) (fun _ => 0) T :=
        fun q hq => ⟨hq.2.1, hq.2.2⟩
      have hQn : ∀ q ∈ movingClosedSlab (PDE.euclideanBall c R) (fun _ => 0) p.time T,
          0 ≤ Q q := by
        intro q hq
        apply boundedSourceQuadratic_nonneg hlam c R
        simpa only [boundedSource_stationary_domain] using hq.2.2
      have hmax := growth_comparison (PDE.isOpen_euclideanBall c R) hγ hlam hell hbounds.1
        (le_refl 0) zero_le_one (a := p.time) (T := T) (u := fun q => W q - Q q)
        ?_ ?_ ?_ ?_ ?_ ?_ p ⟨le_rfl, hp.1, hp.2⟩
      · exact sub_nonpos.mp hmax
      · refine ⟨T - p.time, fun q hq => ?_⟩
        have hw := (duhamelPotential_nonneg_le K T g hgn 1 zero_le_one hgb q hq.2.1).2
        dsimp only [W, Q]
        have hqn := hQn q hq
        dsimp only [Q] at hqn
        linarith only [hw, hqn, hq.1]
      · exact (hWc.mono hslab).sub (continuous_boundedSourceQuadratic c R lam).continuousOn
      · intro q hq
        exact (hreg q (hactive hq)).sub (isSliceRegularAt_boundedSourceQuadratic c R lam q)
      · intro q hq
        rw [viscousTransportedOperator_sub (hreg q (hactive hq))
          (isSliceRegularAt_boundedSourceQuadratic c R lam q)]
        have hw : viscousTransportedOperator B b 0 W q = -g q := by
          rw [viscousTransportedOperator_zero]
          exact hWe q (hactive hq)
        have hqv : viscousTransportedOperator B b 0 (boundedSourceQuadratic c R lam) q ≤ -1 := by
            have _h_xinl_0 (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (c : PDE.Vec d) (R : ℝ) (lam p) : viscousTransportedOperator B b 0 (boundedSourceQuadratic c R lam) p = -(2 * (B p.time p.position p.velocity).trace) / (2 * (d : ℝ) * lam) := by
              let Ψ : ℝ → ℝ := fun s => (R ^ 2 - s) / (2 * (d : ℝ) * lam)
              have hΨ : ContDiff ℝ 2 Ψ := (contDiff_const.sub contDiff_id).div_const _
              have hd : ∀ s, deriv Ψ s = -(1 / (2 * (d : ℝ) * lam)) := by
                intro s
                simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div] using
                  (((hasDerivAt_const s (R ^ 2)).sub (hasDerivAt_id s)).div_const
                    (2 * (d : ℝ) * lam)).deriv
              have hdd : ∀ s, deriv (deriv Ψ) s = 0 := by
                intro s
                rw [show deriv Ψ = fun _ => -(1 / (2 * (d : ℝ) * lam)) from funext hd]
                exact deriv_const _ _
              have hdiff : matrixContraction (B p.time p.position p.velocity)
                  (diffusedHessian (boundedSourceQuadratic c R lam) p) =
                  -(2 * (B p.time p.position p.velocity).trace) / (2 * (d : ℝ) * lam) := by
                rw [diffusedHessian_eq_sliceHessian]
                change matrixContraction _ (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - c))) _) = _
                rw [matrixContraction_sliceHessian_comp_vecNormSq_sub hΨ.contDiffAt, hd, hdd]
                ring
              have ht : kineticTimeDerivative (boundedSourceQuadratic c R lam) p = 0 := by
                change deriv (fun _ : ℝ =>
                  (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.time = 0
                exact deriv_const _ _
              have hv : kineticVelocityGradient (boundedSourceQuadratic c R lam) p = 0 := by
                ext i
                change fderiv ℝ (fun _ : PDE.Vec d =>
                  (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam))
                    p.velocity (PDE.basisVec i) = 0
                rw [fderiv_const_apply]
                rfl
              rw [viscousTransportedOperator_apply, transportedForwardOperator_apply,
                fullKineticCoefficientAt_apply, ht, hdiff, hv]
              simp only [PDE.vecDot, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero, zero_add, add_zero, zero_mul]
            rw [_h_xinl_0]
            have htr := trace_ge_of_smul_one_le (hell q.time q.position q.velocity).1
            have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
            apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hdR) hlam)).2
            nlinarith only [htr]

          /- Smoothness in transported coordinates implies slice regularity of the literal potential. -/
        change 0 ≤ viscousTransportedOperator B b 0 W q -
          viscousTransportedOperator B b 0 Q q
        rw [hw]
        exact sub_nonneg.mpr (hqv.trans (neg_le_neg (hgb q)))
      · intro q hq ht
        have hw := duhamelPotential_eq_zero_of_terminal_le K T g q ht.ge
        change W q - Q q ≤ 0
        dsimp only [W]
        rw [hw, zero_sub]
        exact neg_nonpos.mpr (hQn q hq)
      · intro q hq hfront
        have hnot : q.position ∉ movingDomain (PDE.euclideanBall c R) (fun _ => 0) q.time :=
          ((isOpen_movingDomain_of_isAdmissibleEvolutionDomain (fun _ => 0) hΩ q.time
            ).frontier_eq ▸ hfront).2
        have hw := duhamelPotential_eq_zero_of_not_mem K T g q hnot
        change W q - Q q ≤ 0
        dsimp only [W]
        rw [hw, zero_sub]
        exact neg_nonpos.mpr (hQn q hq)

    /- Signed bounded Borel potentials inherit the uniform quadratic barrier. -/
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hmass hM).trans_eq (mul_comm _ _))

/- The two independent barriers give the source-needed minimum with exact normalization. -/
theorem abs_duhamelPotential_le_time_min_quadratic
    (hH : HormanderHypoellipticityStatement) {d } (hd : 0 < d)
    {c R} (hR : 0 < R) {lam Lam m Lb }
    (hlam : 0 < lam) (hm : 0 < m)
    (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (hb : IsSmoothDrift b)
    (hbounds : HasTransportBounds m Lb b)
    (S : TerminalOperatorFamily (PDE.euclideanBall c R) (fun _ => 0))
    (K : MovingFiberKernel (PDE.euclideanBall c R) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall c R) (fun _ => 0)
      (PDE.isOpen_euclideanBall c R).measurableSet B b S K)
    (g : KineticPoint d → ℝ) (hg : Measurable g) (M ) (hM : 0 ≤ M)
    (hgb : ∀ q, |g q| ≤ M) (T : ℝ) (p : KineticPoint d)
    (hp : p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c R) (fun _ => 0) T) :
    |duhamelPotential K T g p| ≤
      min (T - p.time) (boundedSourceQuadratic c R lam p) * M := by
  rw [min_mul_of_nonneg _ _ hM]
  exact le_min (abs_duhamelPotential_le K g M hM hgb p T hp.1)
    (abs_duhamelPotential_le_boundedSourceQuadratic hH hd hR hlam hm B hB hBs hell
      b hb hbounds S K hreal g hg M hM hgb T p hp)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
