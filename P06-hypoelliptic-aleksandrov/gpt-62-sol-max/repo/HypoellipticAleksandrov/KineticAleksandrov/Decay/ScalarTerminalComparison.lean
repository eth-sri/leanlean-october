module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.Parabolic.Derivatives

/-! # Scalar classical comparison on a stationary ball or interval -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ} (B : CoefficientField d)

theorem transportedForwardOperator_scalar_lift
    (b : PDE.Vec d → PDE.Vec d) (V : TimeVelocity d → ℝ) (p : KineticPoint d) :
    transportedForwardOperator (zIndependentCoefficient B) b
      (fun q => V (q.time, q.position)) p = scalarParabolicOperator B 0 V
        (p.time, p.position) := by
  unfold transportedForwardOperator scalarParabolicOperator kineticTimeDerivative
    diffusedHessian scalarTimeDerivative scalarSpatialHessian kineticVelocityGradient
    scalarSpatialGradient kineticPositionGradient
  simp [PDE.classicalGradient, PDE.vecDot]

theorem scalarParabolicOperator_sub_zeroDrift
    (U V : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (hUt : DifferentiableAt ℝ (fun t => U (t, p.2)) p.1)
    (hVt : DifferentiableAt ℝ (fun t => V (t, p.2)) p.1)
    (hUy : ContDiffAt ℝ 2 (fun y => U (p.1, y)) p.2)
    (hVy : ContDiffAt ℝ 2 (fun y => V (p.1, y)) p.2) :
    scalarParabolicOperator B 0 (fun q => U q - V q) p =
      scalarParabolicOperator B 0 U p - scalarParabolicOperator B 0 V p := by
  have htime := deriv_fun_sub hUt hVt
  have hhess : scalarSpatialHessian (fun q => U q - V q) p =
      scalarSpatialHessian U p - scalarSpatialHessian V p := by
    change sliceHessian _ _ = sliceHessian _ _ - sliceHessian _ _
    ext i j
    simp only [Matrix.sub_apply, sliceHessian_apply_eq_sndFDeriv (hUy.sub hVy),
      sliceHessian_apply_eq_sndFDeriv hUy, sliceHessian_apply_eq_sndFDeriv hVy,
      fderiv_fderiv_fun_sub hUy hVy, ContinuousLinearMap.sub_apply]
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [htime, hhess]
  simp only [matrixContraction, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  ring

end

/-- The same maximum-principle argument compares a signed sub- or supersolution
with the terminal solution. -/
theorem scalar_terminal_signed_comparison {d : ℕ} {J : Set (PDE.Vec d)} {σ τ : ℝ}
    (hJ : (∃ c R, 0 < R ∧ J = PDE.euclideanBall c R) ∨
      (∃ hd : d = 1, ∃ a c, a < c ∧ hd ▸ J = PDE.oneDimensionalAxisBox a c))
    (hστ : σ < τ) (B : CoefficientField d) (hB : ∀ t v, (B t v).PosSemidef)
    (F : BoundedBorel (PDE.Vec d)) {V U : TimeVelocity d → ℝ}
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution J stationary
      (zIndependentCoefficient B) τ F V)
    (hUc : ContinuousOn U (scalarParabolicClosedCylinder σ τ J))
    (hUj : ∀ p ∈ scalarParabolicOpenCylinder σ τ J, ContDiffAt ℝ 2 U p)
    (s : ℝ) (hUs : ∀ p ∈ scalarParabolicOpenCylinder σ τ J,
      0 ≤ s * scalarParabolicOperator B 0 U p)
    (hterm : ∀ v ∈ closure J, s * (U (τ, v) - F v) ≤ 0)
    (hlat : ∀ p ∈ scalarParabolicLateralFace σ τ J, s * U p ≤ 0) :
    ∀ v ∈ closure J, s * (U (σ, v) - V (σ, v)) ≤ 0 := by
  let w : KineticPoint d → ℝ := fun p => U (p.time, p.position) - V (p.time, p.position)
  let W : KineticPoint d → ℝ := fun p => s * w p
  let r : Fin 2 → ℝ := ![σ, τ]
  have hr : StrictMono r := (Fin.strictMono_iff_lt_succ).mpr (by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hστ)
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder J stationary τ) := by
    have he : ParabolicProbe.scalarPastOpenCylinder J stationary τ = Iio τ ×ˢ J := by
      ext p
      simp only [ParabolicProbe.scalarPastOpenCylinder, mem_ofPred_eq,
        movingDomain_stationary, mem_prod, mem_Iio]
    rw [he]
    exact isOpen_Iio.prod (isOpen_of_isAdmissibleEvolutionDomain (Or.inr hJ))
  have hVc : ContinuousOn V (ParabolicProbe.scalarPastClosedCylinder J stationary τ) := hV.2.1
  have hVj : ∀ p ∈ scalarParabolicOpenCylinder σ τ J, ContDiffAt ℝ 2 V p := by
    intro p hp
    have hm : p ∈ ParabolicProbe.scalarPastOpenCylinder J stationary τ :=
      ⟨hp.1.2, by simpa only [movingDomain_stationary] using hp.2⟩
    exact ((hV.2.2.1 p hm).contDiffAt (hopen.mem_nhds hm)).of_le (by norm_num)
  have hJet {f : TimeVelocity d → ℝ} {p : KineticPoint d}
      (hf : ContDiffAt ℝ 2 f (p.time, p.position)) :
      IsSliceRegularAt (fun q => f (q.time, q.position)) p :=
    ⟨(hf.differentiableAt (by norm_num)).comp p.time (by fun_prop),
      hf.comp p.position (contDiffAt_const.prodMk contDiffAt_id),
      contDiffAt_const (c := f (p.time, p.position))⟩
  have hm (i : Fin 1) (p : KineticPoint d)
      (hp : p ∈ maximumOpenTube J stationary (r i.castSucc) (r i.succ)) :
      (p.time, p.position) ∈ scalarParabolicOpenCylinder σ τ J := by
    rw [Fin.eq_zero i] at hp
    exact ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩
  have hmax : ∀ p ∈ maximumClosedTube J stationary σ τ, W p ≤ 0 := by
    apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B)
      (γ := stationary) (drift := fun _ => 0) hJ 0 r hr continuous_const.continuousOn
    · have hc := (continuous_time.prodMk continuous_position :
          Continuous (fun p : KineticPoint d => (p.time, p.position))).continuousOn
          (s := maximumClosedTube J stationary σ τ)
      exact continuousOn_const.mul ((hUc.comp hc (fun p hp => ⟨hp.1, by
        simpa only [movingDomain_stationary] using hp.2⟩)).sub
        (hVc.comp hc (fun p hp => ⟨hp.1.2, hp.2⟩)))
    · exact Or.inl (fun _ _ _ => rfl)
    · intro i p hp
      have h := ((hJet (hUj _ (hm i p hp))).sub (hJet (hVj _ (hm i p hp)))).const_mul s
      exact ⟨h.time, h.position, h.velocity.differentiableAt (by norm_num)⟩
    · exact fun _ p _ => hB p.time p.position
    · intro i p hp
      have h := hm i p hp
      have hu := hJet (hUj _ h)
      have hv := hJet (hVj _ h)
      have hmul := viscousTransportedOperator_const_mul
        (B := zIndependentCoefficient B) (b := fun _ => 0) (ε := 0) s (hu.sub hv)
      simp only [viscousTransportedOperator_apply, zero_mul, add_zero] at hmul
      change 0 ≤ transportedForwardOperator (zIndependentCoefficient B) (fun _ => 0) W p
      rw [show W = _ from rfl, hmul,
        transportedForwardOperator_scalar_lift B (fun _ => 0) (fun q => U q - V q) p,
        scalarParabolicOperator_sub_zeroDrift B U V (p.time, p.position)
          hu.time hv.time hu.position hv.position]
      have hs := hV.2.2.2.1 (p.time, p.position) ⟨h.1.2, hp.2⟩
      change scalarParabolicOperator B 0 V (p.time, p.position) = 0 at hs
      simpa only [hs, sub_zero] using hUs _ h
    · intro p hp hpt
      have hpJ : p.position ∈ closure J := by simpa only [movingDomain_stationary] using hp.2
      have ht := hV.2.2.2.2.1 (p.time, p.position) ⟨hpt, by
        simpa only [movingDomain_stationary] using hpJ⟩
      change s * (U (p.time, p.position) - V (p.time, p.position)) ≤ 0
      rw [ht, show p.time = τ from hpt]
      exact hterm _ hpJ
    · intro p hp hfront
      have ht := hV.2.2.2.2.2 (p.time, p.position) ⟨hp.1.2, hfront⟩
      change s * (U (p.time, p.position) - V (p.time, p.position)) ≤ 0
      simpa only [ht, sub_zero] using hlat (p.time, p.position) ⟨hp.1, by
        simpa only [movingDomain_stationary] using hfront⟩
  exact fun v hv => hmax ⟨σ, v, 0⟩ ⟨⟨le_rfl, hστ.le⟩, by
    simpa only [movingDomain_stationary] using hv⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay
