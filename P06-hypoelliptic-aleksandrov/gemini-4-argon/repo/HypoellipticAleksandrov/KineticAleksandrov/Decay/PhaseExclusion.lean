module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseInfinity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

/-!
# Cutoffs of the strictly forbidden phase

A compactly supported terminal test has a positive phase margin. A smooth
increasing cutoff of the phase then dominates the test and vanishes at phase zero.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set Filter MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/- A compact test supported in a positive phase region has a uniform positive margin. -/
theorem phaseCutoff_isSliceRegularAt {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ σ τ ρ} (hγ : ContinuousOn γ (Icc σ τ))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    IsSliceRegularAt (fun q => χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ q)) p := by
  have hr := phaseBarrier_isSliceRegularAt sgn ξ z0 hb (ρ := ρ) hγ p ht
  exact ⟨(hχ.differentiable (by norm_num)).differentiableAt.comp p.time hr.time,
    hχ.contDiffAt.comp p.position hr.position, hχ.contDiffAt.comp p.velocity hr.velocity⟩

/- The transported operator obeys the scalar chain rule on an affine phase barrier. -/
theorem lop_phaseCutoff {d : ℕ} (B : CoefficientField d) (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ σ τ ρ} (hγ : ContinuousOn γ (Icc σ τ))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    lop B b (fun q => χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ q)) p =
      deriv χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ p) *
        lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p := by
  let κ := phaseBarrier sgn ξ z0 b γ σ Lb ρ
  have hr := phaseBarrier_isSliceRegularAt sgn ξ z0 hb (ρ := ρ) hγ p ht
  have hd := (hχ.differentiable (by norm_num)).differentiableAt.hasDerivAt
    (x := κ p)
  have htime : kineticTimeDerivative (fun q => χ (κ q)) p =
      deriv χ (κ p) * kineticTimeDerivative κ p := by
    exact (hd.comp p.time hr.time.hasDerivAt).deriv
  have hgrad : kineticVelocityGradient (fun q => χ (κ q)) p =
      deriv χ (κ p) • kineticVelocityGradient κ p := by
    have hv := hd.comp_hasFDerivAt p.velocity
      (hr.velocity.differentiableAt (by norm_num)).hasFDerivAt
    ext i
    change fderiv ℝ (χ ∘ fun z : PDE.Vec d =>
      phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨p.time, p.position, z⟩)
        p.velocity (PDE.basisVec i) = _
    rw [hv.fderiv]
    rfl
  have hh : diffusedHessian (fun q => χ (κ q)) p = 0 := by
    have hz : (fun y : PDE.Vec d => kineticPositionGradient
        (fun q => χ (κ q)) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
      funext y i
      change fderiv ℝ (fun _ : PDE.Vec d => χ (κ p)) y (PDE.basisVec i) = 0
      rw [fderiv_const_apply]
      rfl
    ext i j
    simp only [diffusedHessian]
    rw [hz, fderiv_const_apply]
    rfl
  unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
  rw [htime, hgrad, hh, phase_diffused_hessian]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  have hs : (∑ i, b p.position i * (deriv χ (κ p) * kineticVelocityGradient κ p i)) =
      ∑ i, deriv χ (κ p) * (b p.position i * kineticVelocityGradient κ p i) := by
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, ← Finset.mul_sum]
  dsimp only [κ]
  ring

/- A classical terminal solution with a forbidden-phase test is nonpositive initially. -/
theorem classical_phase_test_nonpos {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d)
    (σ τ Lb ρ : ℝ) (hστ : σ < τ) (hρ : 0 < ρ)
    (ξ z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hb : HasEuclideanLipschitzDrift Lb b) (hγ : Continuous γ)
    (hB : ∀ t v, (B t v).PosSemidef)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ) γ τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) -
        Lb * ρ * (τ - σ)})
    (u : KineticPoint d → ℝ)
    (hu : IsClassicalTerminalSolution (PDE.euclideanBall 0 ρ) γ
      (zIndependentCoefficient B) b τ φ u)
    (v : PDE.Vec d) (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ) :
    u ⟨σ, v, z0⟩ ≤ 0 := by
  let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
  let κ := phaseBarrier sgn ξ z0 b γ σ Lb ρ
  let q : EvolutionAmbientState d → ℝ := fun x =>
    sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) - Lb * ρ * (τ - σ)
  have hq : Continuous q := by
    dsimp only [q, phaseCoordinate]
    unfold PDE.vecDot
    simp only [Pi.sub_apply]
    fun_prop
  obtain ⟨χ, hχ, hmχ, hχ0, hχbounds, hdom⟩ : ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ Monotone χ ∧
      χ 0 = 0 ∧ (∀ r, 0 ≤ χ r ∧ χ r ≤ 1) ∧ (∀ x, φ x ≤ χ (q x)) := by
    have hφ := hφ.2.1
    obtain ⟨δ, hδ, hm⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport φ, δ ≤ q x := by
        by_cases he : (tsupport φ).Nonempty
        · obtain ⟨x, hx, hmin⟩ := hφ.exists_isMinOn he hq.continuousOn
          exact ⟨q x, hs hx, fun y hy => hmin hy⟩
        · exact ⟨1, zero_lt_one, fun x hx => False.elim (he ⟨x, hx⟩)⟩


    refine ⟨fun r => Real.smoothTransition (r / δ), ?_, ?_, ?_, ?_, ?_⟩
    · exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
    · intro r s hrs
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hrs hδ.le)
    · simp only [zero_div, Real.smoothTransition.zero]
    · intro r
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    · intro x
      change φ x ≤ Real.smoothTransition (q x / δ)
      by_cases hx : x ∈ tsupport φ
      · rw [Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (hm x hx))]
        exact (hbound x).2
      · rw [image_eq_zero_of_notMem_tsupport hx]
        exact Real.smoothTransition.nonneg _
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let F : KineticPoint d → ℝ := fun p => χ (κ p)
  have hFnonneg : ∀ p, 0 ≤ F p := fun p => (hχbounds (κ p)).1
  have hFc : ContinuousOn F (maximumClosedTube Ω γ σ τ) :=
    hχ.continuous.comp_continuousOn
      ((phaseBarrier_continuousOn sgn ξ z0 hb (ρ := ρ) hστ.le hγ.continuousOn).mono
        (fun p hp => hp.1))
  have hFr : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt F p :=
    fun p hp => phaseCutoff_isSliceRegularAt sgn ξ z0 hb hγ.continuousOn hχ2 p hp.1
  have hFlop : ∀ p ∈ maximumOpenTube Ω γ σ τ, lop B b F p ≤ 0 := by
    intro p hp
    rw [lop_phaseCutoff B sgn ξ z0 hb hγ.continuousOn hχ2 p hp.1]
    apply mul_nonpos_of_nonneg_of_nonpos hmχ.deriv_nonneg
    apply (phase_barrier_drift B b γ σ τ Lb ρ hρ ξ z0 hξ hb hγ.continuousOn
      sgn hsgn p hp.1 ?_).2
    have hv' := mem_movingDomain_iff.mp hp.2
    simpa only [Ω, PDE.euclideanBall, PDE.euclideanSqDist, Set.mem_ofPred_eq, sub_zero] using hv'
  obtain ⟨M, hM, hbM, -⟩ :=
    phase_infinity_barrier B b σ τ ρ hρ γ hγ.continuousOn
      (continuous_of_euclidean_lipschitz hb) z0
  obtain ⟨C, -, hC⟩ := hu.1
  have hclosed : maximumClosedTube Ω γ σ τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.2, hp.2⟩
  have hopen : maximumOpenTube Ω γ σ τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.2, hp.2⟩
  have huv := (isClassicalViscousTerminalSolution_zero_iff Ω γ
    (zIndependentCoefficient B) b τ φ u).mpr hu
  have hur : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt u p :=
    fun p hp => huv.isSliceRegularAt (PDE.isOpen_euclideanBall 0 ρ) hγ (hopen hp)
  have huinitial : ∀ η : ℝ, 0 < η →
      u ⟨σ, v, z0⟩ ≤ η * Real.exp ((M + 1) * (τ - σ)) := by
    intro η hη
    let H := infinityBarrier η M τ z0
    let w : KineticPoint d → ℝ := fun p => u p - F p - H p
    have hHr := infinityBarrier_isSliceRegularAt η M τ z0
    have hwcontrol : IsUniformlyNegAtInfinityOn w (maximumClosedTube Ω γ σ τ) := by
      intro A
      obtain ⟨R, hR, hh⟩ := infinityBarrier_uniform_growth hη hM z0 (C - A)
      refine ⟨R, hR, ?_⟩
      intro p hp hz
      have huC := (le_abs_self (u p)).trans (hC p (hclosed hp))
      have hH := hh p hp.1.2 hz
      have hF := hFnonneg p
      dsimp [w, H]
      linarith
    have hwr : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt w p :=
      fun p hp => ((hur p hp).sub (hFr p hp)).sub (hHr p)
    have hwsub : ∀ p ∈ maximumOpenTube Ω γ σ τ,
        0 ≤ transportedForwardOperator (zIndependentCoefficient B) b w p := by
      intro p hp
      have hr := hur p hp
      have hfr := hFr p hp
      have hhr := hHr p
      have heq := hu.2.2.2.1 p (hopen hp)
      have hf := hFlop p hp
      have hh := lop_infinityBarrier_le B b (τ := τ) hη.le hM z0 p
        (hbM p ⟨⟨hp.1.1.le, hp.1.2.le⟩, subset_closure hp.2⟩)
      have hHpos : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      have he : transportedForwardOperator (zIndependentCoefficient B) b w p =
          transportedForwardOperator (zIndependentCoefficient B) b u p -
            lop B b F p - lop B b H p := by
        have h1 := viscousTransportedOperator_sub (B := zIndependentCoefficient B)
          (b := b) (ε := 0) (hr.sub hfr) hhr
        have h2 := viscousTransportedOperator_sub (B := zIndependentCoefficient B)
          (b := b) (ε := 0) hr hfr
        simpa only [viscousTransportedOperator_zero, h2, w, lop,
          transportedForwardOperatorOfTimeDiffusedCoefficient] using h1
      rw [he, heq]
      linarith
    have hterminal : ∀ p ∈ maximumClosedTube Ω γ σ τ, p.time = τ → w p ≤ 0 := by
      intro p hp ht
      have hut := hu.2.2.2.2.1 p ⟨ht, ht ▸ hp.2⟩
      have hdom' := hdom (p.position, p.velocity)
      have hF : F p = χ (q (p.position, p.velocity)) := by
        dsimp [F, κ, q, phaseBarrier, phaseCoordinate]
        rw [ht]
      have hH : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      dsimp [w]
      rw [hut, hF]
      linarith
    have hlateral : ∀ p ∈ maximumClosedTube Ω γ σ τ,
        p.position ∈ frontier (movingDomain Ω γ p.time) → w p ≤ 0 := by
      intro p hp hf
      have hul := hu.2.2.2.2.2 p ⟨hp.1.2, hf⟩
      have hF := hFnonneg p
      have hH : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      dsimp [w]
      rw [hul]
      linarith
    have _h_xinl_0 : Continuous (infinityBarrier η M τ z0) := by
      have hv : Continuous (fun p : KineticPoint d => p.velocity - z0) :=
        continuous_velocity.sub continuous_const
      exact (continuous_const.mul (continuous_const.add (PDE.continuous_vecNormSq.comp hv))).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_time)))
    have hw := nonpos_on_maximumClosedTube hστ (PDE.isOpen_euclideanBall 0 ρ)
      (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨0, ρ, hρ, rfl⟩))
      hγ.continuousOn
      (((hu.2.1.mono hclosed).sub hFc).sub _h_xinl_0.continuousOn)
      (Or.inr hwcontrol)
      (fun p hp => ⟨(hwr p hp).time, (hwr p hp).position,
        (hwr p hp).velocity.differentiableAt (by norm_num)⟩)
      (fun p _ => hB p.time p.position) hwsub hterminal hlateral
      ⟨σ, v, z0⟩ ⟨⟨le_rfl, hστ.le⟩, subset_closure hv⟩
    have hstart : F ⟨σ, v, z0⟩ = 0 := by
      dsimp [F, κ, phaseBarrier, phaseCenter]
      simpa only [sub_self, PDE.vecDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, intervalIntegral.integral_same, sub_zero] using hχ0
    dsimp [w, H] at hw
    rw [hstart] at hw
    simpa only [infinityBarrier, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, mul_one, sub_zero, sub_nonpos] using hw
  by_contra hn
  have hpos := lt_of_not_ge hn
  let E := Real.exp ((M + 1) * (τ - σ))
  have he : 0 < E := Real.exp_pos _
  have hh := huinitial (u ⟨σ, v, z0⟩ / (2 * E)) (div_pos hpos (by positivity))
  have hcancel : u ⟨σ, v, z0⟩ / (2 * E) * E = u ⟨σ, v, z0⟩ / 2 := by
    field_simp
  rw [hcancel] at hh
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Decay
