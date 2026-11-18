module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionLimit
public import HypoellipticAleksandrov.Parabolic.KineticClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder


private theorem gradient_translate {d : ℕ} {f : PDE.Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (c x : PDE.Vec d) :
    PDE.classicalGradient (fun y => f (y - c)) x = PDE.classicalGradient f (x - c) := by
  have h := (hf.differentiable (by norm_num) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  change HasFDerivAt (fun y => f (y - c))
    ((fderiv ℝ f (x - c)).comp (ContinuousLinearMap.id ℝ (PDE.Vec d))) x at h
  ext i
  simp [PDE.classicalGradient_apply, h.fderiv]

private theorem hessian_translate {d : ℕ} {f : PDE.Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (c x : PDE.Vec d) :
    Hess (fun y => f (y - c)) x = Hess f (x - c) := by
  have hg : ContDiff ℝ 1 (PDE.classicalGradient f) := by
    apply contDiff_pi.mpr
    intro i
    exact (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
  have heq : (fun y => PDE.classicalGradient (fun w => f (w - c)) y) =
      (fun y => PDE.classicalGradient f (y - c)) := by
    funext y
    exact gradient_translate hf c y
  have h := (hg.differentiable (by norm_num) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  change HasFDerivAt (fun y => PDE.classicalGradient f (y - c))
    ((fderiv ℝ (PDE.classicalGradient f) (x - c)).comp
      (ContinuousLinearMap.id ℝ (PDE.Vec d))) x at h
  ext i j
  change (fderiv ℝ (fun y => PDE.classicalGradient (fun w => f (w - c)) y) x
    (PDE.basisVec i)) j = _
  rw [heq]
  change (fderiv ℝ (fun y => PDE.classicalGradient f (y - c)) x
    (PDE.basisVec i)) j =
    (fderiv ℝ (PDE.classicalGradient f) (x - c) (PDE.basisVec i)) j
  rw [h.fderiv]
  rfl

private def movingBarrier {d : ℕ} (N : ℕ) (s rate τ : ℝ)
    (γ : ℝ → PDE.Vec d) (p : TimeVelocity d) : ℝ :=
  Real.exp (-rate * (τ - p.1)) * barrier N s (p.2 - γ p.1)

private theorem movingBarrier_time_derivative {d N : ℕ} (hN : 3 ≤ N)
    (s rate τ t : ℝ) (γ : ℝ → PDE.Vec d) (y : PDE.Vec d)
    (hγ : DifferentiableAt ℝ γ t) :
    HasDerivAt (fun r => movingBarrier N s rate τ γ (r, y))
      (Real.exp (-rate * (τ - t)) *
        (rate * barrier N s (y - γ t) -
          PDE.vecDot (deriv γ t) (PDE.classicalGradient (barrier N s) (y - γ t)))) t := by
  have hcomp := ((retention_barrier_contDiff (d := d) hN s).differentiable (by norm_num) (y - γ t)).hasFDerivAt.comp_hasDerivAt t (hγ.hasDerivAt.const_sub y)
  have h := ((((hasDerivAt_id t).const_sub τ).const_mul (-rate)).exp).mul hcomp
  refine h.congr_deriv ?_
  simp only [id_eq, Function.comp_apply]
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  unfold PDE.vecDot
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hc : (∑ i, PDE.classicalGradient (barrier N s) (y - γ t) i * deriv γ t i) =
      ∑ i, deriv γ t i * PDE.classicalGradient (barrier N s) (y - γ t) i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring



private theorem movingBarrier_subsolution {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H τ : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B) (γ : ℝ → PDE.Vec d)
    (p : TimeVelocity d) (hγ : DifferentiableAt ℝ γ p.1)
    (hspd : PDE.vecEuclideanNorm (deriv γ p.1) ≤ H) :
    0 ≤ scalarParabolicOperator B 0
      (movingBarrier N s (barrierRate d N lam Lam s H) τ γ) p  := by
  have movingBarrier_hessian {d : ℕ} (s rate τ : ℝ) (γ : ℝ → PDE.Vec d) (p : TimeVelocity d) :
      scalarSpatialHessian (movingBarrier N s rate τ γ) p =
      Real.exp (-rate * (τ - p.1)) • Hess (barrier N s) (p.2 - γ p.1) := by
    have hf : ContDiff ℝ 2 (fun y => barrier N s (y - γ p.1)) :=
      (retention_barrier_contDiff hN s).comp (contDiff_id.sub contDiff_const)
    change sliceHessian (fun y => Real.exp (-rate * (τ - p.1)) *
      barrier N s (y - γ p.1)) p.2 = _
    rw [sliceHessian_const_mul _ hf.contDiffAt]
    change _ • Hess (fun y => barrier N s (y - γ p.1)) p.2 = _
    rw [hessian_translate (retention_barrier_contDiff hN s)]
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [(movingBarrier_time_derivative hN s (barrierRate d N lam Lam s H) τ p.1 γ p.2 hγ).deriv, movingBarrier_hessian, matrixContraction_smul_right]
  simp only [Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  have he : 0 ≤ Real.exp (-barrierRate d N lam Lam s H * (τ - p.1)) := (Real.exp_pos _).le
  convert mul_nonneg he (sub_nonneg.mpr (retention_barrier_drift_inequality hN lam Lam s H hs hlam hlamLam hc (B p.1 p.2) (hB.2.2.2.1 p.1 p.2) (hB.2.2.2.2.1 p.1 p.2) (hB.2.2.2.2.2 p.1 p.2) (deriv γ p.1) (p.2 - γ p.1) hspd)) using 1
  unfold PDE.vecDot
  ring


private theorem lifted_operator {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (V : TimeVelocity d → ℝ) (p : KineticPoint d) :
    transportedForwardOperator (zIndependentCoefficient B) b
      (fun q => V (q.time, q.position)) p = scalarParabolicOperator B 0 V
        (p.time, p.position) := by
  unfold transportedForwardOperator scalarParabolicOperator kineticTimeDerivative
    diffusedHessian scalarTimeDerivative scalarSpatialHessian kineticVelocityGradient
    scalarSpatialGradient kineticPositionGradient
  simp [PDE.classicalGradient, PDE.vecDot]

private theorem scalar_difference_operator {d : ℕ} (B : CoefficientField d)
    (U V : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (hUt : DifferentiableAt ℝ (fun t => U (t, p.2)) p.1)
    (hVt : DifferentiableAt ℝ (fun t => V (t, p.2)) p.1)
    (hUy : ContDiffAt ℝ 2 (fun y => U (p.1, y)) p.2)
    (hVy : ContDiffAt ℝ 2 (fun y => V (p.1, y)) p.2) :
    scalarParabolicOperator B 0 (fun q => U q - V q) p =
      scalarParabolicOperator B 0 U p - scalarParabolicOperator B 0 V p := by
  have hhess : scalarSpatialHessian (fun q => U q - V q) p =
      scalarSpatialHessian U p - scalarSpatialHessian V p := by
    have heq : (fun y => U (p.1, y) - V (p.1, y)) =
        (fun y => U (p.1, y) + (-1) * V (p.1, y)) := by
      funext y
      ring
    change sliceHessian (fun y => U (p.1, y) - V (p.1, y)) p.2 = _
    rw [heq, (sliceHessian_add hUy ((contDiffAt_const (c := (-1 : ℝ))).mul hVy)), (sliceHessian_const_mul (-1) hVy)]
    simp
    rfl
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [(deriv_fun_sub hUt hVt), hhess]
  simp [matrixContraction, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, PDE.vecDot]
  ring

private theorem lifted_difference_subsolution {d : ℕ} (B : CoefficientField d)
    (U V : TimeVelocity d → ℝ) (p : KineticPoint d)
    (hUt : DifferentiableAt ℝ (fun t => U (t, p.position)) p.time)
    (hVt : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time)
    (hUy : ContDiffAt ℝ 2 (fun y => U (p.time, y)) p.position)
    (hVy : ContDiffAt ℝ 2 (fun y => V (p.time, y)) p.position)
    (hU : 0 ≤ scalarParabolicOperator B 0 U (p.time, p.position))
    (hV : scalarParabolicOperator B 0 V (p.time, p.position) = 0) :
    0 ≤ transportedForwardOperator (zIndependentCoefficient B) (fun _ => 0)
      (fun q => U (q.time, q.position) - V (q.time, q.position)) p := by
  rw [(lifted_operator B (fun _ => 0) (fun x => U x - V x) p), (scalar_difference_operator B U V (p.time, p.position) hUt hVt hUy hVy), hV, sub_zero]
  exact hU

private theorem comparison_at_center {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H ρ : ℝ) (hs : 0 < s) (hsρ : s < ρ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hc : 0 < barrierC d N lam Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (γ : ℝ → PDE.Vec d) (hγ : Continuous γ)
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hspd : HasCurveSpeedOn H γ (r 0) (r (Fin.last (n + 1))))
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 ρ) γ
      (zIndependentCoefficient B) (r (Fin.last (n + 1))) F V)
    (hF : ∀ y, barrier N s (y - γ (r (Fin.last (n + 1)))) ≤ F y) :
    Real.exp (-barrierRate d N lam Lam s H * (r (Fin.last (n + 1)) - r 0)) ≤
      V (r 0, γ (r 0)) := by
  let τ := r (Fin.last (n + 1))
  let rate := barrierRate d N lam Lam s H
  let U := movingBarrier N s rate τ γ
  let W : KineticPoint d → ℝ := fun p => U (p.time, p.position) - V (p.time, p.position)
  have hρ : 0 < ρ := hs.trans hsρ
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ) := by
    have heq : ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ =
        {p : TimeVelocity d | p.1 < τ ∧ PDE.vecNormSq (p.2 - γ p.1) < ρ ^ 2} := by
      ext p
      simp [ParabolicProbe.scalarPastOpenCylinder, mem_movingDomain_euclideanBall_iff]
    rw [heq]
    exact (isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp
        (continuous_snd.sub (hγ.comp continuous_fst))) continuous_const)
  have hVjet : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      ContDiffAt ℝ 2 V (p.time, p.position) := by
    intro i p hp
    have hpt := hp.1.2.trans_le (hr.monotone (Fin.le_last _))
    have hmem : (p.time, p.position) ∈
        ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ := ⟨hpt, hp.2⟩
    exact ((hV.2.2.1 _ hmem).contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  have hγd : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ γ p.time := by
    intro i p hp
    exact ((hγpieces i p.time ⟨hp.1.1.le, hp.1.2.le⟩).contDiffAt
      (Icc_mem_nhds hp.1.1 hp.1.2)).differentiableAt (by norm_num)
  have hUjet : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => U (t, p.position)) p.time ∧
      ContDiffAt ℝ 2 (fun y => U (p.time, y)) p.position := by
    intro i p hp
    refine ⟨(movingBarrier_time_derivative hN s rate τ p.time γ p.position
      (hγd i p hp)).differentiableAt, ?_⟩
    change ContDiffAt ℝ 2 (fun y => Real.exp (-rate * (τ - p.time)) *
      barrier N s (y - γ p.time)) p.position
    exact (contDiffAt_const).mul
      ((retention_barrier_contDiff hN s).contDiffAt.comp p.position
        (contDiffAt_id.sub (contDiffAt_const)))
  have hmax : ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ (r 0) τ, W p ≤ 0 := by
    apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B)
      (drift := fun _ => 0) (Or.inl ⟨0, ρ, hρ, rfl⟩) n r hr hγ.continuousOn
    · have hUc : Continuous (fun p : KineticPoint d => U (p.time, p.position)) := by
        dsimp [U, movingBarrier]
        apply Continuous.mul
        · exact (continuous_const.mul (continuous_const.sub continuous_time)).rexp
        · exact (retention_barrier_contDiff hN s).continuous.comp
            (continuous_position.sub (hγ.comp continuous_time))
      exact hUc.continuousOn.sub (hV.2.1.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun p hp => ⟨hp.1.2, hp.2⟩))
    · exact Or.inl (fun p _ z => rfl)
    · intro i p hp
      have hj := hVjet i p hp
      have ht : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time :=
        (hj.differentiableAt (by norm_num)).comp p.time (by fun_prop)
      have hy :=
        hj.comp p.position (contDiffAt_const.prodMk contDiffAt_id)
      exact ⟨(hUjet i p hp).1.sub ht, (hUjet i p hp).2.sub hy,
        differentiableAt_const (U (p.time, p.position) - V (p.time, p.position))⟩
    · intro i p hp
      exact (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 p.time p.position)).posSemidef
    · intro i p hp
      have hj := hVjet i p hp
      have ht : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time :=
        (hj.differentiableAt (by norm_num)).comp p.time (by fun_prop)
      have hspd' := hspd p.time
        ⟨(hr.monotone (Fin.zero_le _)).trans_lt hp.1.1,
          hp.1.2.trans_le (hr.monotone (Fin.le_last _))⟩ (hγd i p hp)
      have hsub := movingBarrier_subsolution hN lam Lam s H τ hs hlam hlamLam hc
        B hB γ (p.time, p.position) (hγd i p hp) hspd'
      have hsol := hV.2.2.2.1 (p.time, p.position)
        ⟨hp.1.2.trans_le (hr.monotone (Fin.le_last _)), hp.2⟩
      change scalarParabolicOperator B 0 V (p.time, p.position) = 0 at hsol
      change 0 ≤ scalarParabolicOperator B 0 U (p.time, p.position) at hsub
      exact lifted_difference_subsolution B U V p (hUjet i p hp).1 ht
        (hUjet i p hp).2 (hj.comp p.position (contDiffAt_const.prodMk contDiffAt_id)) hsub hsol

    · intro p hp hpt
      have ht : V (p.time, p.position) = F p.position := hV.2.2.2.2.1 _
        ⟨hpt, by simpa only [hpt] using hp.2⟩
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      rw [ht]
      dsimp [U, movingBarrier]
      simp only [hpt, τ, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact sub_nonpos.mpr (hF p.position)
    · intro p hp hlat
      have hv0 : V (p.time, p.position) = 0 := hV.2.2.2.2.2 _ ⟨hp.1.2, hlat⟩
      have hsq := vecNormSq_eq_of_mem_frontier_movingDomain hlat
      simp at hsq
      have hout : p.position - γ p.time ∉ PDE.euclideanBall 0 s := by
        change ¬ PDE.vecNormSq (p.position - γ p.time - 0) < s ^ 2
        rw [sub_zero, hsq]
        nlinarith
      have hψ := (retention_polynomial_barrier hN s hs).2.2.2.2 _ hout
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      simp [U, movingBarrier, hψ.1, hv0, le_refl]
  have hmem : (⟨r 0, γ (r 0), 0⟩ : KineticPoint d) ∈
      maximumClosedTube (PDE.euclideanBall 0 ρ) γ (r 0) τ := by
    refine ⟨⟨le_rfl, hr.monotone (Fin.zero_le _)⟩, subset_closure ?_⟩
    rw [mem_movingDomain_euclideanBall_iff]
    simp
    simpa [PDE.vecNormSq, PDE.vecDot] using sq_pos_of_pos hρ
  have h := hmax _ hmem
  have hψ0 := (retention_polynomial_barrier (d := d) hN s hs).2.2.1
  dsimp [W, U, movingBarrier] at h
  rw [sub_self, hψ0, mul_one] at h
  exact sub_nonpos.mp h


private theorem master_mass_eq_marginal_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ)
    (hfirst : (parabolicMarginalKernel K hΩ σ τ hστ) ⟨v, hv⟩ =
      (K.fiberFirstMarginal hΩ σ τ hστ) (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)) :
    (parabolicMarginalKernel K hΩ σ τ hστ ⟨v, hv⟩) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hΩ σ τ hστ
    (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)
  rw [← hfirst] at hmap
  have hq : evolutionQueryOfState Ω γ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z) = movingQuery σ τ hστ v z hv := rfl
  rw [hq] at hmap
  have h := congrArg (fun μ : Measure (PDE.Vec d) => μ univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa only [preimage_univ] using h

private theorem prelimit_of_partition {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H ρ : ℝ) (hs : 0 < s) (hsρ : s < ρ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hc : 0 < barrierC d N lam Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (γ : ℝ → PDE.Vec d) (hγ : Continuous γ)
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hspd : HasCurveSpeedOn H γ (r 0) (r (Fin.last (n + 1))))
    (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ)
    (hpar : HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) γ
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K)
    (z : PDE.Vec d)
    (hv : γ (r 0) ∈ movingDomain (PDE.euclideanBall 0 ρ) γ (r 0)) :
    ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam s H *
      (r (Fin.last (n + 1)) - r 0))) ≤
      K.master (movingQuery (r 0) (r (Fin.last (n + 1)))
        (hr.monotone (Fin.zero_le _)) (γ (r 0)) z hv) univ := by
  let τ := r (Fin.last (n + 1))
  have hρ : 0 < ρ := hs.trans hsρ
  have hsub : PDE.euclideanClosedBall (γ τ) s ⊆
      movingDomain (PDE.euclideanBall 0 ρ) γ τ := by
    intro y hy
    rw [mem_movingDomain_euclideanBall_iff]
    simpa [PDE.euclideanBall, PDE.euclideanSqDist] using (PDE.euclideanClosedBall_subset_euclideanBall hs.le hsρ hy)
  obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ := exists_smooth_cutoff (PDE.isCompact_euclideanClosedBall (γ τ) hs.le) (isOpen_movingDomain (PDE.isOpen_euclideanBall 0 ρ) (γ := γ) τ) hsub
  let F : BoundedBorel (PDE.Vec d) :=
    ⟨φ, hφ.continuous.measurable, ⟨1, zero_le_one, fun y => by
      rw [abs_of_nonneg (hφbound y).1]
      exact (hφbound y).2⟩⟩
  obtain ⟨Q, hfirst, _hQid, _hQpos, _hQsub, _hQcomp, hrepr,
    _hmeas, _hend, _hcomp, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  obtain ⟨V, hV, hVeval, _hunique⟩ := hsolve τ F ⟨hφ, hφc, hφsupp⟩
  have hdom : ∀ y, barrier N s (y - γ τ) ≤ F y := by
    intro y
    by_cases hy : y - γ τ ∈ PDE.euclideanBall 0 s
    · have hc : y ∈ PDE.euclideanClosedBall (γ τ) s := by
        change PDE.vecNormSq (y - γ τ) ≤ s ^ 2
        change PDE.vecNormSq (y - γ τ - 0) < s ^ 2 at hy
        simpa using hy.le
      change barrier N s (y - γ τ) ≤ φ y
      rw [hφone y hc]
      exact ((retention_polynomial_barrier (d := d) hN s hs).2.1 _).2
    · rw [(retention_polynomial_barrier hN s hs).2.2.2.2 _ hy |>.1]
      exact (hφbound y).1
  have hcenter := comparison_at_center hN lam Lam s H ρ hs hsρ hlam hlamLam hc
    B hB γ hγ n r hr hγpieces hspd F V hV hdom
  have heval := hVeval (r 0) (hr.monotone (Fin.zero_le _)) ⟨γ (r 0), hv⟩
  rw [hrepr] at heval
  rw [heval] at hcenter
  apply (ENNReal.ofReal_le_ofReal hcenter).trans
  have hint := integral_le_measure (μ := parabolicMarginalKernel K
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (r 0) τ
        (hr.monotone (Fin.zero_le _)) ⟨γ (r 0), hv⟩)
    (s := univ) (f := fun y => (terminalPositionDatum F) y)
    (fun y _ => (hφbound y.1).2) (fun y hy => (hy (mem_univ y)).elim)
  rw [master_mass_eq_marginal_mass (PDE.isOpen_euclideanBall 0 ρ).measurableSet
    K (r 0) τ (hr.monotone (Fin.zero_le _)) (γ (r 0)) z hv
      (hfirst _ _ _ _ z)] at hint
  exact hint


private theorem endpoint_master_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (B : CoefficientField d)
    (K : MovingFiberKernel Ω γ)
    (hpar : HasParabolicMarginalBundle Ω γ hΩ (zIndependentCoefficient B) K)
    (σ : ℝ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ) :
    K.master (movingQuery σ σ le_rfl v z hv) univ = 1 := by
  obtain ⟨_Q, hfirst, _hQid, _hQpos, _hQsub, _hQcomp, _hrepr,
    _hmeas, hend, _hcomp, _hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  rw [← master_mass_eq_marginal_mass hΩ K σ σ le_rfl v z hv
    (hfirst σ σ le_rfl ⟨v, hv⟩ z), hend σ]
  simp







/-- The source moving-ball retention estimate for the supplied joint evolution. -/
theorem moving_ball_retention_of_curve (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        IsContinuousPiecewiseC1 γ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ)
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) γ
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ),
        ENNReal.ofReal (Real.exp (-C * (ρ⁻¹ ^ 2 + H ^ 2) * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv)
            (PDE.euclideanBall (γ τ) ρ ×ˢ univ)   := by
  have master_mass_on_terminal_domain {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) :
      K.master q (evolutionStateSet Ω γ q.val.2.1) = K.master q univ := by
    have h := congrArg (fun μ : Measure (EvolutionAmbientState d) => μ univ)
      (K.terminal_support q)
    rw [Measure.restrict_apply MeasurableSet.univ] at h
    simpa only [univ_inter] using h
  have moving_ball_retention_at_radius_of_curve :
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        IsContinuousPiecewiseC1 γ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ)
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) γ
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ),
      ∀ (N : ℕ), 3 ≤ N → 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam →
        ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam ρ H * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv) univ := by
    have moving_ball_retention_prelimit_of_curve :
        ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
          (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
        ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
          IsContinuousPiecewiseC1 γ → HasCurveSpeedOn H γ σ τ →
          (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
        ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ)
          (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ),
          RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
            (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
          HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) γ
            (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
        ∀ z, ∀ (hστ : σ ≤ τ)
          (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ),
        ∀ (N : ℕ), 3 ≤ N → 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam →
        ∀ (s : ℝ), 0 < s → s < ρ →
          ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ≤
            K.master (movingQuery σ τ hστ (γ σ) z hv) univ := by
      have barrierC_pos_of_choice {d : ℕ} {N : ℕ} (hN : 3 ≤ N) (hchoice : 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam) :
          0 < barrierC d N lam Lam := by
        have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
        unfold barrierC
        nlinarith [(mul_pos hNp (sub_pos.mpr hchoice : 0 < 2 * (N - 1 : ℕ) * lam - (d : ℝ) * Lam))]
      have _hd := hd
      intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
        z hστ' hv N hN hchoice s hs hsρ
      by_cases heq : σ = τ
      · subst τ
        rw [endpoint_master_mass (PDE.isOpen_euclideanBall 0 ρ).measurableSet
          B K hpar σ (γ σ) z hv]
        simp
      · have hστlt : σ < τ := lt_of_le_of_ne hστ heq
        obtain ⟨n, r, hr, hr0, hrlast, hpieces⟩ := hpc.2 σ τ hστlt
        have hspd' : HasCurveSpeedOn H γ (r 0) (r (Fin.last (n + 1))) := by
          simpa only [hr0, hrlast] using hspd
        have hv' : γ (r 0) ∈ movingDomain (PDE.euclideanBall 0 ρ) γ (r 0) := by
          simpa only [hr0] using hv
        simpa only [hr0, hrlast] using (prelimit_of_partition hN lam Lam s H ρ hs hsρ hlam hlamLam (barrierC_pos_of_choice hN hchoice) B hsetting.1 γ hpc.1 n r hr hpieces hspd' K hpar z hv')
    intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
      z hστ' hv N hN hchoice
    have hcont : ContinuousAt
        (fun s => Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ρ := by
      unfold barrierRate
      fun_prop (disch := positivity)
    apply le_of_tendsto (ENNReal.tendsto_ofReal (hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] ρ ≤ 𝓝 ρ)))
    have hpos : ∀ᶠ s in 𝓝[<] ρ, 0 < s :=
      (lt_mem_nhds hρ).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs hsρ
    exact (moving_ball_retention_prelimit_of_curve m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv N hN hchoice) s hs hsρ
  obtain ⟨N, hN, hchoice, hc⟩ := exists_retention_barrier_order d hd lam Lam hlam hlamLam
  let C : ℝ := 2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam
  have hLam := hlam.trans_le hlamLam
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv
  have hexp : Real.exp (-C * (ρ⁻¹ ^ 2 + H ^ 2) * (τ - σ)) ≤
      Real.exp (-barrierRate d N lam Lam ρ H * (τ - σ)) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right (retention_rate_uniform hN lam Lam ρ H hlam hlamLam hρ hc) (sub_nonneg.mpr hστ)
    convert neg_le_neg ht using 1 <;> ring
  have hmass := master_mass_on_terminal_domain K (movingQuery σ τ hστ' (γ σ) z hv)
  have hdomain : movingDomain (PDE.euclideanBall 0 ρ) γ τ =
      PDE.euclideanBall (γ τ) ρ := by
    ext v
    rw [mem_movingDomain_euclideanBall_iff]
    simp [PDE.euclideanBall, PDE.euclideanSqDist]
  change K.master (movingQuery σ τ hστ' (γ σ) z hv)
    (movingDomain (PDE.euclideanBall 0 ρ) γ τ ×ˢ univ) = _ at hmass
  rw [hdomain] at hmass
  rw [hmass]
  exact (ENNReal.ofReal_le_ofReal hexp).trans (moving_ball_retention_at_radius_of_curve m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv N hN hchoice)




/-- The retained source corridors normalize to half the uniform mass floor and
are jointly dominated by the supplied full-domain evolution. -/
theorem corridors_retained_dominated (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ (m Lb σ : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (SD : TerminalOperatorFamily D stationary) (KD : MovingFiberKernel D stationary)
        (hD : MeasurableSet D),
        RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b SD KD →
        IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b KD →
      ∀ (γ1 γ2 : ℝ → PDE.Vec d) (v0 z0 : PDE.Vec d),
        IsContinuousPiecewiseC1 γ1 → IsContinuousPiecewiseC1 γ2 →
        γ1 σ = v0 → γ2 σ = v0 → γ1 (σ + blockL0 m) = v0 → γ2 (σ + blockL0 m) = v0 →
        HasCurveSpeedOn (1 / 2) γ1 σ (σ + blockL0 m) →
        HasCurveSpeedOn (1 / 2) γ2 σ (σ + blockL0 m) →
        (∀ r, PDE.euclideanBall (γ1 r) (blockEta m Lb) ⊆ D) →
        (∀ r, PDE.euclideanBall (γ2 r) (blockEta m Lb) ⊆ D) →
      ∀ (S1 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (K1 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (S2 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
        (K2 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ2),
        RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ1
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) b S1 K1 →
        RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ2
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) b S2 K2 →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ1
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) K1 →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ2
          (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
          (zIndependentCoefficient B) K2 →
      ∀ (q1 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
        (q2 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
        (qD : EvolutionQuery D stationary),
        q1.1 = (σ, σ + blockL0 m, v0, z0) →
        q2.1 = (σ, σ + blockL0 m, v0, z0) → qD.1 = (σ, σ + blockL0 m, v0, z0) →
        let μ1 := K1.master q1
        let μ2 := K2.master q2
        let m0 := blockMass Cstar m Lb
        let R1 := ENNReal.ofReal (m0 / (2 * μ1.real univ)) • μ1
        let R2 := ENNReal.ofReal (m0 / (2 * μ2.real univ)) • μ2
        m0 ≤ μ1.real univ ∧ μ1.real univ ≤ 1 ∧
        m0 ≤ μ2.real univ ∧ μ2.real univ ≤ 1 ∧
        μ1 ((PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ) = 0 ∧
        μ2 ((PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ) = 0 ∧
        R1.real univ = m0 / 2 ∧ R2.real univ = m0 / 2 ∧ R1 + R2 ≤ KD.master qD  := by
  have normalized_half_mass (μ : Measure (EvolutionAmbientState d)) [IsFiniteMeasure μ] (a : ℝ) (ha : 0 < a) (hμ : a ≤ μ.real univ) :
      (ENNReal.ofReal (a / (2 * μ.real univ)) • μ).real univ = a / 2 ∧
    ENNReal.ofReal (a / (2 * μ.real univ)) • μ ≤ ENNReal.ofReal (1 / 2) • μ := by
    have hp := ha.trans_le hμ
    have hc : 0 ≤ a / (2 * μ.real univ) := by positivity
    constructor
    · rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hc]
      field_simp
    · have hcoef : ENNReal.ofReal (a / (2 * μ.real univ)) ≤
          ENNReal.ofReal (1 / 2) := by
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_iff₀ (by positivity : 0 < 2 * μ.real univ)).mpr
        linarith only [hμ]
      intro A
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_left hcoef _
  obtain ⟨Cstar, hCstar, hret⟩ := moving_ball_retention_of_curve d hd lam Lam hlam hlamLam
  refine ⟨Cstar, hCstar, ?_⟩
  intro m Lb σ D B b hsetting SD KD hD hrealD hmono γ1 γ2 v0 z0
    hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2 hfit1 hfit2
    S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD hq1 hq2 hqD
  have hm := hsetting.2.2.1
  have hLb : 0 < Lb := hm.trans_le hsetting.2.2.2.1
  have hη := blockEta_pos hm hLb
  have htime : σ ≤ σ + blockL0 m := le_add_of_nonneg_right (blockL0_pos hm).le
  have hball (γ : ℝ → PDE.Vec d) (hs : γ σ = v0) :
      v0 ∈ movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ σ := by
    rw [mem_movingDomain_euclideanBall_iff, hs]
    simp only [add_zero, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    exact sq_pos_of_pos hη
  have hq1' : q1 = movingQuery σ (σ + blockL0 m) htime v0 z0 (hball γ1 hstart1) :=
    Subtype.ext hq1
  have hq2' : q2 = movingQuery σ (σ + blockL0 m) htime v0 z0 (hball γ2 hstart2) :=
    Subtype.ext hq2
  have hfloor1 : blockMass Cstar m Lb ≤ (K1.master q1).real univ := by
    have hmass : ENNReal.ofReal (Real.exp (-Cstar *
        ((blockEta m Lb)⁻¹ ^ 2 + (1 / 2) ^ 2) * (σ + blockL0 m - σ))) ≤
        K1.master q1 (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ) := by
      simpa only [hq1', hstart1, hend1] using (hret m Lb D B b hsetting σ (σ + blockL0 m) (1 / 2) (blockEta m Lb) γ1 htime hη hγ1 hspeed1 (fun r _ => hfit1 r) S1 K1 hreal1 hpar1 z0 htime (by simpa only [hstart1] using hball γ1 hstart1))
    have h := hmass.trans (measure_mono (subset_univ _))
    have hf : IsFiniteMeasure (K1.master q1) :=
      ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) h
    simpa only [measureReal_def, blockMass, add_sub_cancel_left, one_div, div_pow,
      one_pow, show 2 ^ 2 = 4 by norm_num,
      show (2 : ℝ)⁻¹ ^ 2 = 4⁻¹ by norm_num,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have hfloor2 : blockMass Cstar m Lb ≤ (K2.master q2).real univ := by
    have hmass : ENNReal.ofReal (Real.exp (-Cstar *
        ((blockEta m Lb)⁻¹ ^ 2 + (1 / 2) ^ 2) * (σ + blockL0 m - σ))) ≤
        K2.master q2 (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ) := by
      simpa only [hq2', hstart2, hend2] using (hret m Lb D B b hsetting σ (σ + blockL0 m) (1 / 2) (blockEta m Lb) γ2 htime hη hγ2 hspeed2 (fun r _ => hfit2 r) S2 K2 hreal2 hpar2 z0 htime (by simpa only [hstart2] using hball γ2 hstart2))
    have hf : IsFiniteMeasure (K2.master q2) :=
      ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hmass.trans (measure_mono (subset_univ _)))
    simpa only [measureReal_def, blockMass, add_sub_cancel_left, one_div, div_pow,
      one_pow, show 2 ^ 2 = 4 by norm_num,
      show (2 : ℝ)⁻¹ ^ 2 = 4⁻¹ by norm_num,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have hsub (γ : ℝ → PDE.Vec d)
      (hfit : ∀ r, PDE.euclideanBall (γ r) (blockEta m Lb) ⊆ D) :
      ∀ r, movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ r ⊆
        movingDomain D stationary r := by
    intro r v hv
    rw [mem_movingDomain_euclideanBall_iff] at hv
    apply (mem_movingDomain_iff).mpr
    simpa only [stationary, sub_zero] using hfit r (by
      simpa only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist,
        mem_ofPred_eq] using hv)
  have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec d)
      (blockEta m Lb)) := Or.inr (Or.inl ⟨0, blockEta m Lb, hη, rfl⟩)
  have hdom1 := domainMonotone_of_realizes (zIndependentCoefficient B) b KD hmono
    _ γ1 hadm hγ1 (hsub γ1 hfit1) S1 K1 hreal1 q1
  have hdom2 := domainMonotone_of_realizes (zIndependentCoefficient B) b KD hmono
    _ γ2 hadm hγ2 (hsub γ2 hfit2) S2 K2 hreal2 q2
  have hlarge1 : largeQueryOfSmall (hsub γ1 hfit1) q1 = qD :=
    Subtype.ext (hq1.trans hqD.symm)
  have hlarge2 : largeQueryOfSmall (hsub γ2 hfit2) q2 = qD :=
    Subtype.ext (hq2.trans hqD.symm)
  rw [hlarge1] at hdom1
  rw [hlarge2] at hdom2
  have hf1 : IsFiniteMeasure (K1.master q1) :=
    ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
  have hf2 : IsFiniteMeasure (K2.master q2) :=
    ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
  have hnorm1 := normalized_half_mass (K1.master q1) (blockMass Cstar m Lb)
    (Real.exp_pos _) hfloor1
  have hnorm2 := normalized_half_mass (K2.master q2) (blockMass Cstar m Lb)
    (Real.exp_pos _) hfloor2
  have hsupp (γ : ℝ → PDE.Vec d) (K : MovingFiberKernel
      (PDE.euclideanBall 0 (blockEta m Lb)) γ) (q : EvolutionQuery
      (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hq : q.1 = (σ, σ + blockL0 m, v0, z0)) (hend : γ (σ + blockL0 m) = v0) :
      K.master q (PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ)ᶜ = 0 := by
    have he : evolutionStateSet (PDE.euclideanBall 0 (blockEta m Lb)) γ q.1.2.1 =
        PDE.euclideanBall v0 (blockEta m Lb) ×ˢ univ := by
      simp only [evolutionStateSet, hq]
      congr 1
      ext v
      rw [mem_movingDomain_euclideanBall_iff, hend]
      simp only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq]
    have hr := K.terminal_support q
    rw [he] at hr
    rw [← hr, Measure.restrict_apply
      ((PDE.isOpen_euclideanBall v0 (blockEta m Lb)).measurableSet.prod
        MeasurableSet.univ).compl, compl_inter_self, measure_empty]
  refine ⟨hfloor1, ?_, hfloor2, ?_, hsupp γ1 K1 q1 hq1 hend1,
    hsupp γ2 K2 q2 hq2 hend2, hnorm1.1, hnorm2.1, ?_⟩
  · simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K1.mass_le_one q1)
  · simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K2.mass_le_one q2)
  · calc
      _ ≤ ENNReal.ofReal (1 / 2) • KD.master qD +
          ENNReal.ofReal (1 / 2) • KD.master qD :=
        add_le_add (hnorm1.2.trans (fun A => by
          simpa only [Measure.smul_apply, smul_eq_mul] using
            mul_le_mul_right (hdom1 A) (ENNReal.ofReal (1 / 2))))
          (hnorm2.2.trans (fun A => by
          simpa only [Measure.smul_apply, smul_eq_mul] using
            mul_le_mul_right (hdom2 A) (ENNReal.ofReal (1 / 2))))
      _ = KD.master qD := by
        rw [← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

end HypoellipticAleksandrov.KineticAleksandrov.Decay

