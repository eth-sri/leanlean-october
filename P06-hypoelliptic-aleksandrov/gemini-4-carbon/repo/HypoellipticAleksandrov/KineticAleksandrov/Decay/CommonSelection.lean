module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantChain
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
import Mathlib.MeasureTheory.Measure.Real

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder ENNReal


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





/-- The first marginal of `E.withDensity (g ∘ Prod.fst)` is the first marginal of `E`
reweighted by `g`. -/
theorem map_fst_withDensity_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E : Measure (α × β)) (g : α → ℝ≥0∞) (hg : Measurable g) :
    (E.withDensity (g ∘ Prod.fst)).map Prod.fst = (E.map Prod.fst).withDensity g := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA, Measure.restrict_map measurable_fst hA,
    lintegral_map hg measurable_fst]
  rfl

/-- One trimming step: a measure below the first marginal of a finite measure `E` is the
first marginal of a trimmed `F ≤ E`. -/
theorem exists_trimming_of_le_map_fst {d : ℕ}
    (E : Measure (EvolutionAmbientState d)) [IsFiniteMeasure E]
    (Θ : Measure (PDE.Vec d)) (hΘ : Θ ≤ E.map Prod.fst) :
    ∃ g : PDE.Vec d → ℝ≥0∞, Measurable g ∧ (∀ᵐ w ∂E.map Prod.fst, g w ≤ 1) ∧
      Θ = (E.map Prod.fst).withDensity g ∧
      (E.withDensity (g ∘ Prod.fst)).map Prod.fst = Θ ∧
      E.withDensity (g ∘ Prod.fst) ≤ E := by
  have : IsFiniteMeasure Θ := isFiniteMeasure_of_le _ hΘ
  have hle : ∀ᵐ w ∂E.map Prod.fst, Θ.rnDeriv (E.map Prod.fst) w ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hΘ] with w hw using hw
  have hΘeq : Θ = (E.map Prod.fst).withDensity (Θ.rnDeriv (E.map Prod.fst)) :=
    (Measure.withDensity_rnDeriv_eq _ _ (Measure.absolutelyContinuous_of_le hΘ)).symm
  have hmeas : Measurable (Θ.rnDeriv (E.map Prod.fst)) := Measure.measurable_rnDeriv _ _
  refine ⟨Θ.rnDeriv (E.map Prod.fst), hmeas, hle, hΘeq, ?_, ?_⟩
  · rw [map_fst_withDensity_comp_fst E _ hmeas]
    exact hΘeq.symm
  · have hae : ∀ᵐ x ∂E, (Θ.rnDeriv (E.map Prod.fst) ∘ Prod.fst) x ≤ 1 :=
      ae_of_ae_map measurable_fst.aemeasurable hle
    calc E.withDensity (Θ.rnDeriv (E.map Prod.fst) ∘ Prod.fst)
        ≤ E.withDensity (fun _ => 1) := withDensity_mono hae
      _ = E := withDensity_one


private theorem marginal_query_eq {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (B : CoefficientField d)
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

private theorem integrated_minorant {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel D γ) {s T : ℝ} (hsT : s ≤ T)
    (R : Measure (EvolutionState D γ s)) [IsFiniteMeasure R]
    (a h : ℝ) (ha : 0 < a) (hmass : R.real univ = a)
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
      simpa [Measure.smul_apply, Measure.map_apply measurable_fst hA] using (hp A))

/-- Integrating the source terminal minorant supplies two dominated portions
with exactly the same first marginal and the uniform source mass floor. -/
theorem continued_common_minorant_trimming (d : ℕ) (hd : 1 ≤ d)
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
          F1.map Prod.fst = Θ ∧ F2.map Prod.fst = Θ   := by
  have minorant_scalar_barrier_floor {d : ℕ} {N : ℕ} (hN : 3 ≤ N) (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B) (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ) (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 4)
      stationary (zIndependentCoefficient B) 0 F V) (hF : ∀ y, barrier N 3 y ≤ F y) :
      Real.exp (-(2 * N * d * Lam) / 9) ≤ V (-1, 0) := by
    let r : Fin (0 + 2) → ℝ := ![-1, 0]
    have hr : StrictMono r := by
      intro i j hij
      have hijv : i.val < j.val := hij
      have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
      have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
      subst i j
      norm_num [r]
    have hpieces : ∀ i : Fin (0 + 1), ContDiffOn ℝ 1
        (stationary : ℝ → PDE.Vec d) (Icc (r i.castSucc) (r i.succ)) :=
      fun _ => contDiffOn_const
    have hspd : HasCurveSpeedOn 0 (stationary : ℝ → PDE.Vec d) (r 0)
        (r (Fin.last (0 + 1))) := by
      intro t _ _
      change PDE.vecEuclideanNorm (deriv (fun _ => 0) t) ≤ 0
      rw [deriv_const]
      simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
    have h := comparison_at_center hN lam Lam 3 0 4 (by norm_num) (by norm_num)
      hlam hlamLam hc B hB stationary continuous_const 0 r hr hpieces hspd F V hV
      (by simpa [stationary] using hF)
    change Real.exp (-barrierRate d N lam Lam 3 0 * (0 - (-1))) ≤ V (-1, 0) at h
    norm_num [barrierRate, neg_div] at h ⊢
    exact h
  have common_terminal_minorant :
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
      ∀ (qearly qlate : ParabolicEvolutionQuery (PDE.euclideanBall v0 (4 * ρ)) stationary),
        qearly.1 = (T - 4 * ρ ^ 2, T, qearly.1.2.2) →
        qlate.1 = (T - ρ ^ 2, T, v0) →
        qearly.1.2.2 ∈ PDE.euclideanBall v0 ρ →
        ENNReal.ofReal h • P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qearly ∧
        ENNReal.ofReal q0 ≤
          P K (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet qlate
            (PDE.euclideanBall v0 (4 * ρ)) := by
    have scaled_minorant_comparison :
        ∃ h : ℝ, 0 < h ∧
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
      obtain ⟨hf, hfpos, hfH⟩ := normalized_six_step_harnack d hd lam Lam hlam hlamLam
      refine ⟨hf ^ 6, pow_pos hfpos 6, ?_⟩
      intro B hB v0 ρ T hρ K hpar qearly qlate hqe hql hv
      have hΩo := PDE.isOpen_euclideanBall v0 (4 * ρ)
      rcases qearly with ⟨⟨σ, τ, y⟩, hστ, hy⟩
      rcases qlate with ⟨⟨σ', τ', y'⟩, hστ', hy'⟩
      dsimp only at hqe hql hv
      simp [Prod.mk.injEq] at hqe hql
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
        have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
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
            (Ioi 0 ×ˢ PDE.euclideanBall 0 4) := by
          intro p hp
          have hpball : parabolicAffine v0 ρ p.2 ∈ PDE.euclideanBall v0 (4 * ρ) := by
            rw [← parabolicAffine_preimage_ball v0 hρ] at hp
            exact hp.2
          have ht : T + ρ ^ 2 * (-p.1) ≤ T := by
            nlinarith only [(mul_nonneg (sq_nonneg ρ) (show 0 ≤ p.1 from hp.1.le))]
          have heval := hVeval _ ht (parabolicAffine v0 ρ p.2)
            (by simpa only [movingDomain_stationary] using hpball)
          have he : timeReversal 0 p = (-p.1, p.2) := by
            simpa only [zero_sub] using timeReversal_apply 0 p.1 p.2
          change 0 ≤ W (timeReversal 0 p)
          rw [he]
          change 0 ≤ V (T + ρ ^ 2 * (-p.1), parabolicAffine v0 ρ p.2)
          rw [heval]
          exact integral_nonneg fun x => (h01 x).1
        have key := hfH (fun θ v => B' (0 + -1 * θ) (0 + 1 • v))
          (fun p => W (timeReversal 0 p))
          ((continuous_coefficientAt_of_smooth hB'.2.2.1).continuousOn.comp (contDiff_scalarAffine 0 (-1) 0 1).continuous.continuousOn
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
        rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_pos hfpos 6).le, smul_eq_mul]
        change hf ^ 6 * ∫ x, φ x ∂(P K hΩo.measurableSet
            (scalarQuery (T - ρ ^ 2) T hστ' v0 hy')) ≤
          ∫ x, φ x ∂(P K hΩo.measurableSet (scalarQuery (T - 4 * ρ ^ 2) T hστ y hy))
        rw [← (hVeval (T - ρ ^ 2) hστ' v0 hy'), ← (hVeval (T - 4 * ρ ^ 2) hστ y hy)]
        exact key
    have minorant_mass_floor :
        ∃ Cstar q0 : ℝ, 0 < Cstar ∧ q0 = Real.exp (-Cstar / 9) ∧ 0 < q0 ∧
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
      have hLam : 0 < Lam := hlam.trans_le hlamLam
      have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
      have hC : 0 < Cstar := by dsimp [Cstar]; positivity
      refine ⟨Cstar, Real.exp (-Cstar / 9), hC, rfl, Real.exp_pos _, ?_⟩
      intro B hB v0 ρ T R hρ hR K hpar qlate hql
      subst R
      have hΩ := PDE.isOpen_euclideanBall v0 (4 * ρ)
      have hsub : PDE.euclideanClosedBall v0 (3 * ρ) ⊆ PDE.euclideanBall v0 (4 * ρ) :=
        PDE.euclideanClosedBall_subset_euclideanBall (by positivity) (by linarith)
      obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ :=
        exists_smooth_cutoff (PDE.isCompact_euclideanClosedBall v0 (by positivity : 0 ≤ 3 * ρ)) hΩ hsub
      obtain ⟨V, hV, -, hVeval⟩ := exists_scalar_probe hΩ.measurableSet B K hpar
        φ hφ hφc hφsupp T
      let φ' : PDE.Vec d → ℝ := fun y => φ (parabolicAffine v0 ρ y)
      have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ' := hφ.comp (contDiff_parabolicAffine v0 ρ)
      have hc' : HasCompactSupport φ' := hφc.comp_homeomorph (parabolicAffineHomeo v0 hρ)
      have hV0 : ParabolicProbe.IsClassicalScalarTerminalSolution
          (PDE.euclideanBall v0 (4 * ρ)) stationary (zIndependentCoefficient B)
          (T + ρ ^ 2 * 0) (smoothTestBorel φ hφ.continuous hφc) V := by
        simpa only [mul_zero, add_zero] using hV
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
      have hfloor := minorant_scalar_barrier_floor hN hc
        (normalizedParabolicCoefficient B T ρ v0)
        (normalizedParabolicCoefficient_sectionTwo lam Lam B hB T v0 ρ hρ)
        _ _ (isClassicalScalarTerminalSolution_comp_minorantAffine hΩ B T v0 hρ (parabolicAffine_preimage_ball v0 hρ).symm 0 (smoothTestBorel φ hφ.continuous hφc) (smoothTestBorel φ' hφ'.continuous hc') (fun _ => rfl) hV0) hdom
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
      have hmass : P K hΩ.measurableSet qlate univ =
          P K hΩ.measurableSet qlate (PDE.euclideanBall v0 (4 * ρ)) := by
        rw [← measure_add_measure_compl hΩ.measurableSet,
          P_compl_eq_zero_stationary, add_zero]
      exact (ENNReal.ofReal_le_ofReal hfloor).trans ((integral_le_measure (μ := P K hΩ.measurableSet qlate) (s := univ) (f := φ) (fun y _ => (hφbound y).2) (fun y hy => (hy (mem_univ y)).elim)).trans_eq hmass)
    obtain ⟨h, hh, hcomp⟩ := scaled_minorant_comparison
    obtain ⟨C, q, _hC, _hq, hqpos, hmass⟩ := minorant_mass_floor
    refine ⟨h, q, hh, hqpos, ?_⟩
    intro m Lb D B b hset v0 ρ T hv0 hρ hsub S K hreal hpar hmono
      qearly qlate hqe hql hv
    have _ := And.intro hv0 (And.intro hsub (And.intro hreal hmono))
    exact ⟨hcomp B hset.1 v0 ρ T hρ K hpar qearly qlate hqe hql hv,
      hmass B hset.1 v0 ρ T (4 * ρ) hρ rfl K hpar qlate hql⟩
  obtain ⟨h, q0, hh, hq0, hminor⟩ := common_terminal_minorant
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
    have hpρ : p.1.1 ∈ PDE.euclideanBall v0 ρ :=
      PDE.euclideanBall_mono hη.le hηρ.le hp
    have hh' := (hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar
      hmono (scalarQuery s T hsT p.1.1 p.2.1) qlate
      (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).1
    rw [marginal_query_eq (PDE.isOpen_euclideanBall v0 (4 * ρ)).measurableSet
      B K hpar s T hsT p] at hh'
    exact hh'
  have heq1 : E1 = continuedMeasure K hsT R1 := eq_continuedMeasure_of_apply K hsT R1 hE1
  have heq2 : E2 = continuedMeasure K hsT R2 := eq_continuedMeasure_of_apply K hsT R2 hE2
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
    have hfν : IsFiniteMeasure ν := inferInstance
    have h' := ENNReal.toReal_mono (measure_ne_top ν univ)
      (((hminor m Lb D B b hsetting v0 ρ T hv0 hρ hsub S K hreal hpar hmono (scalarQuery s T hsT v0 p.2) qlate (by simp only [scalarQuery]; exact Prod.ext hs (Prod.ext rfl rfl)) hql hpρ).2).trans (measure_mono (subset_univ _)))
    simpa only [ENNReal.toReal_ofReal hq0.le, measureReal_def] using h'
  have hfloor : a * h * q0 ≤ Θ.real univ := by
    rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (mul_pos ha hh).le]
    exact mul_le_mul_of_nonneg_left hνmass (mul_pos ha hh).le
  obtain ⟨g1, hg1, hgle1, hΘ1, hmap1, hF1⟩ := exists_trimming_of_le_map_fst E1 Θ hmin1
  obtain ⟨g2, hg2, hgle2, hΘ2, hmap2, hF2⟩ := exists_trimming_of_le_map_fst E2 Θ hmin2
  exact ⟨hmin1, hmin2, hfloor, E1.withDensity (g1 ∘ Prod.fst),
    E2.withDensity (g2 ∘ Prod.fst), hF1, hF2, (add_le_add hF1 hF2).trans hdom,
    hmap1, hmap2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay

