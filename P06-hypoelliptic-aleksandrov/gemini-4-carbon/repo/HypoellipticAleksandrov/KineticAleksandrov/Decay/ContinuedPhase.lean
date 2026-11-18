module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import Mathlib.MeasureTheory.Measure.Module

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.SectionTwo Set Filter MeasureTheory
open scoped Topology NNReal

/-- An explicit Euclidean Lipschitz bound implies continuity in the native topology. -/
theorem continuous_of_euclidean_lipschitz {d : ℕ} {Lb : ℝ}
    {b : PDE.Vec d → PDE.Vec d} (hb : HasEuclideanLipschitzDrift Lb b) :
    Continuous b := by
  let K : ℝ≥0 := ⟨|Lb| * Real.sqrt d, mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro x y
  simp only [dist_eq_norm]
  calc
    ‖b x - b y‖ ≤ PDE.vecEuclideanNorm (b x - b y) := PDE.norm_le_vecEuclideanNorm _
    _ ≤ Lb * PDE.vecEuclideanNorm (x - y) := hb x y
    _ ≤ |Lb| * PDE.vecEuclideanNorm (x - y) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (PDE.vecEuclideanNorm_nonneg _)
    _ ≤ |Lb| * (Real.sqrt d * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _)
        (abs_nonneg _)
    _ = (K : ℝ) * ‖x - y‖ := by change _ = (|Lb| * Real.sqrt d) * ‖x - y‖; ring

/-- The phase center has the source integrand as its derivative at interior times. -/
theorem phaseCenter_hasDerivAt {d : ℕ} (ξ : PDE.Vec d)
    {Lb : ℝ} {b : PDE.Vec d → PDE.Vec d} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ t : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    (ht : t ∈ Ioo σ τ) :
    HasDerivAt (phaseCenter ξ b γ σ) (PDE.vecDot ξ (b (γ t))) t := by
  have hc : Continuous (fun y => PDE.vecDot ξ (b y)) := by
    unfold PDE.vecDot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp (continuous_of_euclidean_lipschitz hb))
  have hf := hc.comp_continuousOn hγ
  have hi : IntervalIntegrable (fun r => PDE.vecDot ξ (b (γ r))) MeasureTheory.volume σ t :=
    (hf.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht) (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- The transported gradient of the signed phase is its signed unit direction. -/
theorem phase_velocity_gradient {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d) (σ Lb ρ : ℝ)
    (p : KineticPoint d) :
    kineticVelocityGradient (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p = sgn • ξ := by
  let L :=
    ∑ i, (sgn * ξ i) • (ContinuousLinearMap.proj i : PDE.Vec d →L[ℝ] ℝ)
  have h : HasFDerivAt
      (fun z => phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨p.time, p.position, z⟩)
      L p.velocity := by
    have hd : HasFDerivAt (fun z => PDE.vecDot ξ (z - z0))
        (∑ i, ξ i • (ContinuousLinearMap.proj i : PDE.Vec d →L[ℝ] ℝ)) p.velocity := by
      unfold PDE.vecDot
      exact HasFDerivAt.fun_sum fun i _ =>
        ((hasFDerivAt_apply i p.velocity).sub_const (z0 i)).const_mul (ξ i)
    convert ((hd.sub_const (phaseCenter ξ b γ σ p.time)).const_mul sgn).sub_const
      (Lb * ρ * (p.time - σ)) using 1
    · rfl
    · simp [L, Finset.smul_sum, smul_smul]
  ext i
  change fderiv ℝ _ p.velocity (PDE.basisVec i) = _
  rw [h.fderiv]
  simp [L, PDE.basisVec_apply]

/-- The signed phase is independent of the diffused coordinate. -/
theorem phase_diffused_hessian {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d) (σ Lb ρ : ℝ)
    (p : KineticPoint d) :
    diffusedHessian (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p = 0 := by
  have hg : (fun y => kineticPositionGradient
      (phaseBarrier sgn ξ z0 b γ σ Lb ρ) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
    funext y i
    change fderiv ℝ (fun _ =>
      sgn * (PDE.vecDot ξ (p.velocity - z0) - phaseCenter ξ b γ σ p.time) -
      Lb * ρ * (p.time - σ)) y (PDE.basisVec i) = 0
    rw [fderiv_const_apply]
    rfl
  ext i j
  simp
  rw [hg, fderiv_const_apply]
  rfl


/-- The phase barrier is slice regular; no derivative of the moving center is needed. -/
theorem phaseBarrier_isSliceRegularAt {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    IsSliceRegularAt (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p  := by
  have phaseBarrier_hasDerivAt {d : ℕ} (ξ z0 : PDE.Vec d) {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b) {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ)) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
      HasDerivAt (fun t => phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨t, p.position, p.velocity⟩)
      (sgn * (0 - PDE.vecDot ξ (b (γ p.time))) - Lb * ρ) p.time := by
    unfold phaseBarrier
    convert
      (((hasDerivAt_const p.time (PDE.vecDot ξ (p.velocity - z0))).sub
        (phaseCenter_hasDerivAt ξ hb hγ ht)).const_mul sgn).sub
          (((hasDerivAt_id p.time).sub_const σ).const_mul (Lb * ρ)) using 1 <;>
      first | rfl | simp
  refine ⟨(phaseBarrier_hasDerivAt ξ z0 hb hγ p ht).differentiableAt, ?_, ?_⟩
  · change ContDiffAt ℝ 2 (fun _ =>
      sgn * (PDE.vecDot ξ (p.velocity - z0) - phaseCenter ξ b γ σ p.time) -
      Lb * ρ * (p.time - σ)) p.position
    exact contDiffAt_const
  · dsimp only [phaseBarrier]
    unfold PDE.vecDot
    simp
    fun_prop



/-- The signed affine phase barrier has nonpositive transported operator in the tube. -/
theorem phase_barrier_drift {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d)
    (σ τ Lb ρ : ℝ) (hρ : 0 < ρ) (ξ z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hb : HasEuclideanLipschitzDrift Lb b) (hγ : ContinuousOn γ (Icc σ τ))
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ)
    (hv : p.position ∈ PDE.euclideanBall (γ p.time) ρ) :
    lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      sgn * PDE.vecDot ξ (b p.position - b (γ p.time)) - Lb * ρ ∧
    lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p ≤ 0 := by
  have htime : kineticTimeDerivative (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      -sgn * PDE.vecDot ξ (b (γ p.time)) - Lb * ρ := by
    have h := (((hasDerivAt_const p.time (PDE.vecDot ξ (p.velocity - z0))).sub
      (phaseCenter_hasDerivAt ξ hb hγ ht)).const_mul sgn).sub
      (((hasDerivAt_id p.time).sub_const σ).const_mul (Lb * ρ))
    change deriv _ p.time = _
    change deriv (fun t => sgn * (PDE.vecDot ξ (p.velocity - z0) -
      phaseCenter ξ b γ σ t) - Lb * ρ * (t - σ)) p.time = _
    have he := h.deriv
    change deriv (fun t => sgn * (PDE.vecDot ξ (p.velocity - z0) -
      phaseCenter ξ b γ σ t) - Lb * ρ * (t - σ)) p.time = _ at he
    rw [he]
    ring
  have heq : lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      sgn * PDE.vecDot ξ (b p.position - b (γ p.time)) - Lb * ρ := by
    unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
    rw [htime, phase_diffused_hessian, phase_velocity_gradient]
    simp
    have hd : PDE.vecDot (b p.position) (sgn • ξ) =
        sgn * PDE.vecDot ξ (b p.position) := by
      unfold PDE.vecDot
      simp [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hd]
    have hs : PDE.vecDot ξ (b p.position - b (γ p.time)) =
        PDE.vecDot ξ (b p.position) - PDE.vecDot ξ (b (γ p.time)) := by
      simp [PDE.vecDot, mul_sub, Finset.sum_sub_distrib]
    rw [hs]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hnorm : PDE.vecEuclideanNorm ξ = 1 := by
    simp [PDE.vecEuclideanNorm, hξ]
  have hLb : 0 ≤ Lb := by
    have hh := hb ξ 0
    have hn : PDE.vecEuclideanNorm (ξ - 0) = 1 := by simpa using hnorm
    rw [hn, mul_one] at hh
    exact (PDE.vecEuclideanNorm_nonneg _).trans hh
  have hdot : |PDE.vecDot ξ (b p.position - b (γ p.time))| ≤ Lb * ρ := by
    calc
      _ ≤ PDE.vecEuclideanNorm ξ * PDE.vecEuclideanNorm
          (b p.position - b (γ p.time)) := PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ = PDE.vecEuclideanNorm (b p.position - b (γ p.time)) := by rw [hnorm, one_mul]
      _ ≤ Lb * PDE.vecEuclideanNorm (p.position - γ p.time) := hb _ _
      _ ≤ Lb * ρ := mul_le_mul_of_nonneg_left
        ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hv).le hLb
  rcases hsgn with rfl | rfl
  · nlinarith [le_abs_self (PDE.vecDot ξ (b p.position - b (γ p.time)))]
  · nlinarith [neg_le_abs (PDE.vecDot ξ (b p.position - b (γ p.time)))]


/-- The quadratic infinity penalty is continuous in all source coordinates. -/
theorem infinityBarrier_continuous {d : ℕ} (η M τ : ℝ) (z0 : PDE.Vec d) :
    Continuous (infinityBarrier η M τ z0) := by
  have hv : Continuous (fun p : KineticPoint d => p.velocity - z0) :=
    continuous_velocity.sub continuous_const
  exact (continuous_const.mul (continuous_const.add (PDE.continuous_vecNormSq.comp hv))).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_time)))

/-- The quadratic infinity penalty is slice regular everywhere. -/
theorem infinityBarrier_isSliceRegularAt {d : ℕ} (η M τ : ℝ) (z0 : PDE.Vec d)
    (p : KineticPoint d) : IsSliceRegularAt (infinityBarrier η M τ z0) p := by
  apply IsSliceRegularAt.of_contDiffAt
  unfold rawLift infinityBarrier PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The operator on the quadratic transported-variable penalty. -/
theorem lop_infinityBarrier {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (η M τ : ℝ) (z0 : PDE.Vec d) (p : KineticPoint d) :
    lop B b (infinityBarrier η M τ z0) p =
      η * Real.exp ((M + 1) * (τ - p.time)) *
        (-(M + 1) * (1 + PDE.vecNormSq (p.velocity - z0)) +
          2 * PDE.vecDot (b p.position) (p.velocity - z0)) := by
  have ht : kineticTimeDerivative (infinityBarrier η M τ z0) p =
      η * (1 + PDE.vecNormSq (p.velocity - z0)) *
        (Real.exp ((M + 1) * (τ - p.time)) * (-(M + 1))) := by
    have he := (((((hasDerivAt_id p.time).const_sub τ).const_mul (M + 1)).exp).const_mul (η * (1 + PDE.vecNormSq (p.velocity - z0)))).deriv
    change kineticTimeDerivative (infinityBarrier η M τ z0) p = _ at he
    simpa using he
  have hg : kineticVelocityGradient (infinityBarrier η M τ z0) p =
      fun i => 2 * (η * Real.exp ((M + 1) * (τ - p.time))) * (p.velocity i - z0 i) := by
    have hf : (fun z => infinityBarrier η M τ z0 ⟨p.time, p.position, z⟩) =
        fun z => (fun s => η * Real.exp ((M + 1) * (τ - p.time)) * (1 + s))
          (PDE.vecNormSq (z - z0)) := by
      funext z
      unfold infinityBarrier
      ring
    unfold kineticVelocityGradient
    rw [hf, classicalGradient_comp_vecNormSq_sub
      ((contDiffAt_affine_weight _ _ _).differentiableAt (by norm_num)), deriv_affine_weight]
  have hh : diffusedHessian (infinityBarrier η M τ z0) p = 0 := by
    have hzero : (fun y => kineticPositionGradient
        (infinityBarrier η M τ z0) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
      funext y i
      change fderiv ℝ (fun _ => η *
        (1 + PDE.vecNormSq (p.velocity - z0)) *
        Real.exp ((M + 1) * (τ - p.time))) y (PDE.basisVec i) = 0
      rw [fderiv_const_apply]
      rfl
    ext i j
    simp
    rw [hzero, fderiv_const_apply]
    rfl
  unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
  rw [ht, hg, hh]
  simp
  have hd : PDE.vecDot (b p.position)
      (fun i => 2 * (η * Real.exp ((M + 1) * (τ - p.time))) * (p.velocity i - z0 i)) =
      2 * (η * Real.exp ((M + 1) * (τ - p.time))) *
        PDE.vecDot (b p.position) (p.velocity - z0) := by
    simp [PDE.vecDot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  ring

/-- A local drift bound makes the quadratic infinity penalty a strict supersolution. -/
theorem lop_infinityBarrier_le {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) {η M τ : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M)
    (z0 : PDE.Vec d) (p : KineticPoint d) (hb : PDE.vecEuclideanNorm (b p.position) ≤ M) :
    lop B b (infinityBarrier η M τ z0) p ≤ -infinityBarrier η M τ z0 p := by
  have hcs := PDE.abs_vecDot_le_vecEuclideanNorm_mul (b p.position) (p.velocity - z0)
  have hsq := PDE.vecEuclideanNorm_sq (p.velocity - z0)
  have hdot : 2 * PDE.vecDot (b p.position) (p.velocity - z0) ≤
      M * (1 + PDE.vecNormSq (p.velocity - z0)) := by
    have hb' := mul_le_mul_of_nonneg_right hb (PDE.vecEuclideanNorm_nonneg (p.velocity - z0))
    have hm' := mul_nonneg hM (sq_nonneg (PDE.vecEuclideanNorm (p.velocity - z0) - 1))
    nlinarith [le_abs_self (PDE.vecDot (b p.position) (p.velocity - z0))]
  rw [lop_infinityBarrier]
  unfold infinityBarrier
  have hh := mul_le_mul_of_nonneg_left hdot
    (mul_nonneg hη (Real.exp_pos ((M + 1) * (τ - p.time))).le)
  nlinarith

/-- The quadratic penalty dominates every level uniformly at transported infinity. -/
theorem infinityBarrier_uniform_growth {d : ℕ} {η M τ : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (z0 : PDE.Vec d) (A : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p : KineticPoint d, p.time ≤ τ →
      R ≤ PDE.vecEuclideanNorm p.velocity → A ≤ infinityBarrier η M τ z0 p := by
  let Q := max (A / η) 0 + 1
  refine ⟨PDE.vecEuclideanNorm z0 + Q, ?_, ?_⟩
  · dsimp [Q]
    exact add_nonneg (PDE.vecEuclideanNorm_nonneg _)
      (by linarith [le_max_right (A / η) 0])
  · intro p ht hp
    have htriangle := PDE.vecEuclideanNorm_add_le (p.velocity - z0) z0
    rw [sub_add_cancel] at htriangle
    have hQ : 1 ≤ Q := by dsimp [Q]; linarith [le_max_right (A / η) 0]
    have hq : Q ≤ PDE.vecEuclideanNorm (p.velocity - z0) := by linarith
    have hsq := PDE.vecEuclideanNorm_sq (p.velocity - z0)
    have hbase : A ≤ η * (1 + PDE.vecNormSq (p.velocity - z0)) := by
      have hA : A / η ≤ Q := by dsimp [Q]; linarith [le_max_left (A / η) 0]
      have hAs : A ≤ η * Q := by
        simpa only [mul_comm] using (div_le_iff₀ hη).mp hA
      exact hAs.trans (mul_le_mul_of_nonneg_left (show Q ≤ 1 + PDE.vecNormSq (p.velocity - z0) by nlinarith) hη.le)
    have he : 1 ≤ Real.exp ((M + 1) * (τ - p.time)) :=
      Real.one_le_exp (mul_nonneg (by linarith) (sub_nonneg.mpr ht))
    unfold infinityBarrier
    exact hbase.trans (le_mul_of_one_le_right
      (mul_nonneg hη.le (by linarith [PDE.vecNormSq_nonneg (p.velocity - z0)])) he)

/-- A finite local drift bound supplies the source supersolution and uniform growth. -/
theorem phase_infinity_barrier {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (σ τ ρ : ℝ) (hρ : 0 < ρ)
    (γ : ℝ → PDE.Vec d) (hγ : ContinuousOn γ (Icc σ τ))
    (hb : Continuous b) (z0 : PDE.Vec d) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
        PDE.vecEuclideanNorm (b p.position) ≤ M) ∧
      ∀ η : ℝ, 0 < η →
        (∀ p ∈ maximumOpenTube (PDE.euclideanBall 0 ρ) γ σ τ,
          lop B b (infinityBarrier η M τ z0) p ≤ -infinityBarrier η M τ z0 p) ∧
        (∀ A : ℝ, ∃ R : ℝ, 0 ≤ R ∧
          ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
            R ≤ PDE.vecEuclideanNorm p.velocity → A ≤ infinityBarrier η M τ z0 p) := by
  have hf : Continuous
      (fun p : KineticPoint d => PDE.vecEuclideanNorm (b p.position)) :=
    PDE.continuous_vecEuclideanNorm.comp
      (hb.comp (KineticPoint.homeomorphProd d).continuous.snd.fst)
  obtain ⟨C, hC⟩ := (isCompact_maximumClosedTube_truncated (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨0, ρ, hρ, rfl⟩)) hγ (show 0 ≤ 0 from le_rfl)).exists_bound_of_continuousOn hf.continuousOn
  have hbnd : ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
      PDE.vecEuclideanNorm (b p.position) ≤ max C 0 := by
    intro p hp
    have hh := hC ⟨p.time, p.position, 0⟩
      (show (⟨p.time, p.position, 0⟩ : KineticPoint d) ∈
          {p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ |
            p.velocity ∈ PDE.euclideanClosedBall 0 0} from
        ⟨hp, by simp [PDE.euclideanClosedBall, PDE.euclideanSqDist,
          PDE.vecNormSq, PDE.vecDot]⟩)
    have ha : ‖PDE.vecEuclideanNorm (b p.position)‖ =
        PDE.vecEuclideanNorm (b p.position) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _)]
    rw [ha] at hh
    exact hh.trans (le_max_left C 0)
  refine ⟨max C 0, le_max_right C 0, hbnd, fun η hη => ⟨?_, ?_⟩⟩
  · intro p hp
    apply lop_infinityBarrier_le B b hη.le (le_max_right C 0) z0 p
    exact hbnd p ⟨⟨hp.1.1.le, hp.1.2.le⟩, subset_closure hp.2⟩
  · intro A
    obtain ⟨R, hR, hh⟩ := infinityBarrier_uniform_growth hη (le_max_right C 0) z0 A
    exact ⟨R, hR, fun p hp => hh p hp.1.2⟩



/-- A smooth monotone phase cutoff dominates every `[0,1]` test in the forbidden set. -/
theorem exists_phase_cutoff {E : Type*} [TopologicalSpace E]
    {φ q : E → ℝ} (hφ : HasCompactSupport φ) (hq : Continuous q)
    (hs : tsupport φ ⊆ {x | 0 < q x}) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ Monotone χ ∧
      χ 0 = 0 ∧ (∀ r, 0 ≤ χ r ∧ χ r ≤ 1) ∧ (∀ x, φ x ≤ χ (q x))  := by
  have exists_positive_phase_margin [TopologicalSpace E] {φ q : E → ℝ} (hφ : HasCompactSupport φ) (hq : Continuous q) (hs : tsupport φ ⊆ {x | 0 < q x}) :
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport φ, δ ≤ q x := by
    by_cases he : (tsupport φ).Nonempty
    · obtain ⟨x, hx, hmin⟩ := hφ.exists_isMinOn he hq.continuousOn
      exact ⟨q x, hs hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (he ⟨x, hx⟩)⟩
  obtain ⟨δ, hδ, hm⟩ := exists_positive_phase_margin hφ hq hs
  refine ⟨fun r => Real.smoothTransition (r / δ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
  · intro r s hrs
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hrs hδ.le)
  · simp [Real.smoothTransition.zero]
  · intro r
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x
    change φ x ≤ Real.smoothTransition (q x / δ)
    by_cases hx : x ∈ tsupport φ
    · rw [Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (hm x hx))]
      exact (hbound x).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact Real.smoothTransition.nonneg _


/-- The transported operator obeys the scalar chain rule on an affine phase barrier. -/
theorem lop_phaseCutoff {d : ℕ} (B : CoefficientField d) (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
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
    change fderiv ℝ (χ ∘ fun z =>
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
  simp [matrixContraction, Matrix.zero_apply]
  simp [PDE.vecDot]
  have hs : (∑ i, b p.position i * (deriv χ (κ p) * kineticVelocityGradient κ p i)) =
      ∑ i, deriv χ (κ p) * (b p.position i * kineticVelocityGradient κ p i) := by
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, ← Finset.mul_sum]
  dsimp only [κ]
  ring

/-- A classical terminal solution with a forbidden-phase test is nonpositive initially. -/
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
    u ⟨σ, v, z0⟩ ≤ 0   := by
  have phaseCutoff_isSliceRegularAt {d : ℕ} (ξ z0 : PDE.Vec d) {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b) {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ)) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
      IsSliceRegularAt (fun q => χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ q)) p := by
    have hr := phaseBarrier_isSliceRegularAt sgn ξ z0 hb (ρ := ρ) hγ p ht
    exact ⟨(hχ.differentiable (by norm_num)).differentiableAt.comp p.time hr.time,
      hχ.contDiffAt.comp p.position hr.position, hχ.contDiffAt.comp p.velocity hr.velocity⟩
  have phaseBarrier_continuousOn (ξ z0 : PDE.Vec d) {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b) {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hστ : σ ≤ τ) (hγ : ContinuousOn γ (Icc σ τ)) :
      ContinuousOn (phaseBarrier sgn ξ z0 b γ σ Lb ρ) {p | p.time ∈ Icc σ τ} := by
    have phaseCenter_continuousOn (ξ : PDE.Vec d) {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b) {γ : ℝ → PDE.Vec d} {σ τ : ℝ} (hστ : σ ≤ τ) (hγ : ContinuousOn γ (Icc σ τ)) :
        ContinuousOn (phaseCenter ξ b γ σ) (Icc σ τ) := by
      have hc : Continuous (fun y : PDE.Vec d => PDE.vecDot ξ (b y)) := by
        unfold PDE.vecDot
        exact continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_of_euclidean_lipschitz hb))
      have hi : IntervalIntegrable (fun r => PDE.vecDot ξ (b (γ r)))
          MeasureTheory.volume σ τ := (hc.comp_continuousOn hγ).intervalIntegrable_of_Icc hστ
      unfold phaseCenter
      simpa only [uIcc_of_le hστ] using
        intervalIntegral.continuousOn_primitive_interval' hi Set.left_mem_uIcc
    have hc : Continuous (fun p : KineticPoint d => PDE.vecDot ξ (p.velocity - z0)) := by
      unfold PDE.vecDot
      exact continuous_finsetSum _ fun i _ => continuous_const.mul
        (((continuous_apply i).comp continuous_velocity).sub continuous_const)
    exact ((hc.continuousOn.sub ((phaseCenter_continuousOn ξ hb hστ hγ).comp
      continuous_time.continuousOn (fun _ hp => hp))).const_mul sgn).sub
      ((continuous_time.continuousOn.sub continuousOn_const).const_mul (Lb * ρ))
  let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
  let κ := phaseBarrier sgn ξ z0 b γ σ Lb ρ
  let q : EvolutionAmbientState d → ℝ := fun x =>
    sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) - Lb * ρ * (τ - σ)
  have hq : Continuous q := by
    dsimp only [q, phaseCoordinate]
    unfold PDE.vecDot
    simp
    fun_prop
  obtain ⟨χ, hχ, hmχ, hχ0, hχbounds, hdom⟩ := exists_phase_cutoff hφ.2.1 hq hs hbound
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let F : KineticPoint d → ℝ := fun p => χ (κ p)
  have hFnonneg : ∀ p, 0 ≤ F p := fun p => (hχbounds (κ p)).1
  have hFc : ContinuousOn F (maximumClosedTube Ω γ σ τ) :=
    hχ.continuous.comp_continuousOn
      ((phaseBarrier_continuousOn ξ z0 hb (ρ := ρ) hστ.le hγ.continuousOn).mono
        (fun p hp => hp.1))
  have hFr : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt F p :=
    fun p hp => phaseCutoff_isSliceRegularAt ξ z0 hb hγ.continuousOn hχ2 p hp.1
  have hFlop : ∀ p ∈ maximumOpenTube Ω γ σ τ, lop B b F p ≤ 0 := by
    intro p hp
    rw [lop_phaseCutoff B sgn ξ z0 hb hγ.continuousOn hχ2 p hp.1]
    apply mul_nonpos_of_nonneg_of_nonpos hmχ.deriv_nonneg
    apply (phase_barrier_drift B b γ σ τ Lb ρ hρ ξ z0 hξ hb hγ.continuousOn
      sgn hsgn p hp.1 ?_).2
    have hv' := mem_movingDomain_iff.mp hp.2
    simpa [Ω, PDE.euclideanBall, PDE.euclideanSqDist] using hv'
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
    have hw := nonpos_on_maximumClosedTube hστ (PDE.isOpen_euclideanBall 0 ρ)
      (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨0, ρ, hρ, rfl⟩))
      hγ.continuousOn
      (((hu.2.1.mono hclosed).sub hFc).sub (infinityBarrier_continuous η M τ z0).continuousOn)
      (Or.inr hwcontrol)
      (fun p hp => ⟨(hwr p hp).time, (hwr p hp).position,
        (hwr p hp).velocity.differentiableAt (by norm_num)⟩)
      (fun p _ => hB p.time p.position) hwsub hterminal hlateral
      ⟨σ, v, z0⟩ ⟨⟨le_rfl, hστ.le⟩, subset_closure hv⟩
    have hstart : F ⟨σ, v, z0⟩ = 0 := by
      dsimp [F, κ, phaseBarrier, phaseCenter]
      simpa [PDE.vecDot, intervalIntegral.integral_same] using hχ0
    dsimp [w, H] at hw
    rw [hstart] at hw
    simpa [infinityBarrier, PDE.vecNormSq, PDE.vecDot, sub_nonpos] using hw
  by_contra hn
  have hpos := lt_of_not_ge hn
  let E := Real.exp ((M + 1) * (τ - σ))
  have he : 0 < E := Real.exp_pos _
  have hh := huinitial (u ⟨σ, v, z0⟩ / (2 * E)) (div_pos hpos (by positivity))
  have hcancel : u ⟨σ, v, z0⟩ / (2 * E) * E = u ⟨σ, v, z0⟩ / 2 := by
    field_simp
  rw [hcancel] at hh
  linarith




/-- Changing the transported base point splits the phase coordinate additively. -/
theorem phaseCoordinate_split {d : ℕ} (ξ z0 : PDE.Vec d)
    (x y : EvolutionAmbientState d) :
    phaseCoordinate ξ z0 x = phaseCoordinate ξ z0 y + phaseCoordinate ξ y.2 x := by
  unfold phaseCoordinate PDE.vecDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

/-- Source and conditional continuation phase errors add under kernel integration. -/
theorem continuation_phase_support {d : ℕ} {α : Type*} [MeasurableSpace α]
    (sourceState : α → EvolutionAmbientState d) (hsource : Measurable sourceState)
    (ξ z0 : PDE.Vec d) (a c e1 e2 : ℝ)
    (R : Measure α) [IsFiniteMeasure R]
    (κ : ProbabilityTheory.Kernel α (EvolutionAmbientState d))
    (hR : ∀ᵐ p ∂R, |phaseCoordinate ξ z0 (sourceState p) - a| ≤ e1)
    (hκ : ∀ᵐ p ∂R, ∀ᵐ x ∂κ p, |phaseCoordinate ξ (sourceState p).2 x - c| ≤ e2)
    (E : Measure (EvolutionAmbientState d))
    (hE : ∀ A, MeasurableSet A → E A = ∫⁻ p, κ p A ∂R) :
    ∀ᵐ x ∂E, |phaseCoordinate ξ z0 x - (a + c)| ≤ e1 + e2 := by
  have hmeas : MeasurableSet {x : EvolutionAmbientState d |
      ¬ |phaseCoordinate ξ z0 x - (a + c)| ≤ e1 + e2} := by
    have hq : Continuous (fun x : EvolutionAmbientState d =>
        |phaseCoordinate ξ z0 x - (a + c)|) := by
      unfold phaseCoordinate PDE.vecDot
      fun_prop
    exact (isClosed_le hq continuous_const).measurableSet.compl
  apply ae_iff.mpr
  rw [hE _ hmeas]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hR, hκ] with p hp hk
  apply ae_iff.mp
  filter_upwards [hk] with x hx
  have he : phaseCoordinate ξ z0 x - (a + c) =
      (phaseCoordinate ξ z0 (sourceState p) - a) +
      (phaseCoordinate ξ (sourceState p).2 x - c) := by
    rw [phaseCoordinate_split ξ z0 x (sourceState p)]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hp hx)


/-- The two actual corridor phases remain in quarter-width strips after continuation. -/
theorem block_continued_phase_error {d : ℕ} (hd : 1 ≤ d)
    (lam Lam m Lb Cstar σ : ℝ) (D : Set (PDE.Vec d))
    (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (hsetting : SourceSetting lam Lam m Lb D B b) (hC : 0 < Cstar)
    (ξ v0 z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hfit : PDE.euclideanBall v0 (blockOuter Lb) ⊆ D)
    (γ1 γ2 : ℝ → PDE.Vec d)
    (hγ1 : IsContinuousPiecewiseC1 γ1) (hγ2 : IsContinuousPiecewiseC1 γ2)
    (hstart1 : γ1 σ = v0) (hstart2 : γ2 σ = v0)
    (hend1 : γ1 (σ + blockL0 m) = v0) (hend2 : γ2 (σ + blockL0 m) = v0)
    (htube1 : ∀ r, PDE.euclideanBall (γ1 r) (blockEta m Lb) ⊆ D)
    (htube2 : ∀ r, PDE.euclideanBall (γ2 r) (blockEta m Lb) ⊆ D)
    (hphase : phaseCenter ξ b γ2 σ (σ + blockL0 m) -
      phaseCenter ξ b γ1 σ (σ + blockL0 m) = Real.pi)
    (S1 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (K1 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (S2 : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (K2 : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (S0 : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary)
    (K0 : MovingFiberKernel (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary)
    (hreal1 : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ1
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) b S1 K1)
    (hreal2 : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ2
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) b S2 K2)
    (hreal0 : RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * blockRho Lb)).measurableSet
      (zIndependentCoefficient B) b S0 K0)
    (hpar1 : HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ1
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) K1)
    (hpar2 : HasParabolicMarginalBundle (PDE.euclideanBall 0 (blockEta m Lb)) γ2
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
      (zIndependentCoefficient B) K2)
    (hpar0 : HasParabolicMarginalBundle (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * blockRho Lb)).measurableSet
      (zIndependentCoefficient B) K0)
    (q1 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ1)
    (q2 : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ2)
    (hq1 : q1.1 = (σ, σ + blockL0 m, v0, z0))
    (hq2 : q2.1 = (σ, σ + blockL0 m, v0, z0))
    (R1 R2 : Measure (EvolutionState
      (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary (σ + blockL0 m)))
    [IsFiniteMeasure R1] [IsFiniteMeasure R2]
    (hR1 : Measure.map Subtype.val R1 =
      ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K1.master q1).real univ)) • K1.master q1)
    (hR2 : Measure.map Subtype.val R2 =
      ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K2.master q2).real univ)) • K2.master q2)
    (hsT : σ + blockL0 m ≤ σ + blockTime m Lb)
    (E1 E2 F1 F2 : Measure (EvolutionAmbientState d))
    (hE1 : ∀ A, MeasurableSet A → E1 A =
      ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
        hsT p.1.1 p.1.2 p.2.1) A ∂R1)
    (hE2 : ∀ A, MeasurableSet A → E2 A =
      ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
        hsT p.1.1 p.1.2 p.2.1) A ∂R2)
    (hF1 : F1 ≤ E1) (hF2 : F2 ≤ E2) :
    let Φ1 := phaseCenter ξ b γ1 σ (σ + blockL0 m) +
      4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0)
    let Φ2 := phaseCenter ξ b γ2 σ (σ + blockL0 m) +
      4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0)
    Φ2 - Φ1 = Real.pi ∧
    (∀ᵐ x ∂E1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4) ∧
    (∀ᵐ x ∂E2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4) ∧
    (∀ᵐ x ∂F1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4) ∧
    (∀ᵐ x ∂F2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4)    := by
  have ae_phase_strip_of_forbidden_tests {μ : Measure (EvolutionAmbientState d)} [IsFiniteMeasure μ] {D : Set (EvolutionAmbientState d)} (hD : IsOpen D) (hμ : μ Dᶜ = 0) {q : EvolutionAmbientState d → ℝ} (hq : Continuous q) (c : ℝ) (htest : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ∀ φ : EvolutionAmbientState d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ {x | 0 < sgn * q x - c} ∩ D →
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
      ∀ᵐ x ∂μ, |q x| ≤ c := by
    have hzero : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 → μ {x | 0 < sgn * q x - c} = 0 := by
      intro sgn hs
      apply measure_eq_zero_of_smooth_integral_eq_zero_of_support
        (isOpen_lt continuous_const ((continuous_const.mul hq).sub continuous_const)) hD hμ
      exact htest sgn hs
    apply ae_iff.mpr
    apply measure_mono_null (fun x hx => ?_)
      (measure_union_null (hzero 1 (Or.inl rfl)) (hzero (-1) (Or.inr rfl)))
    change ¬ |q x| ≤ c at hx
    change 0 < 1 * q x - c ∨ 0 < -1 * q x - c
    by_cases hp : 0 ≤ q x
    · rw [abs_of_nonneg hp] at hx
      left
      linarith
    · rw [abs_of_neg (lt_of_not_ge hp)] at hx
      right
      linarith
  have stationary_phase_localization (lam : ℝ) (Lam : ℝ) (m : ℝ) (Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b) (σ τ ρ : ℝ) (c : PDE.Vec d) (hρ : 0 < ρ) (S : TerminalOperatorFamily (PDE.euclideanBall c ρ) stationary) (K : MovingFiberKernel (PDE.euclideanBall c ρ) stationary) (hreal : RealizesTerminalEvolution (PDE.euclideanBall c ρ) stationary
      (PDE.isOpen_euclideanBall c ρ).measurableSet (zIndependentCoefficient B) b S K) (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ) (hv : v ∈ movingDomain (PDE.euclideanBall c ρ) stationary σ) :
      ∀ᵐ x ∂K.master (movingQuery σ τ hστ v z0 hv),
      |phaseCoordinate ξ z0 x - phaseCenter ξ b (fun _ => c) σ τ| ≤ Lb * ρ * (τ - σ) := by
    have stationary_phase_test_zero (σ τ ρ : ℝ) (c : PDE.Vec d) (hρ : 0 < ρ) (S : TerminalOperatorFamily (PDE.euclideanBall c ρ) stationary) (K : MovingFiberKernel (PDE.euclideanBall c ρ) stationary) (hreal : RealizesTerminalEvolution (PDE.euclideanBall c ρ) stationary
        (PDE.isOpen_euclideanBall c ρ).measurableSet (zIndependentCoefficient B) b S K) (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ) (hv : v ∈ movingDomain (PDE.euclideanBall c ρ) stationary σ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (φ : BoundedBorel (EvolutionAmbientState d)) (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
        stationary τ φ) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
        {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b (fun _ => c) σ τ) -
          Lb * ρ * (τ - σ)}) :
        ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by
      let Ω := PDE.euclideanBall c ρ
      let γc : ℝ → PDE.Vec d := stationary
      let p : EvolutionState Ω γc σ := ⟨(v, z0), hv, mem_univ _⟩
      have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
          ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall c ρ).measurableSet σ τ hστ p :=
        integral_master_eq_fiber K (PDE.isOpen_euclideanBall c ρ).measurableSet
          σ τ hστ p φ φ.measurable
      by_cases ht : σ = τ
      · subst τ
        rw [hi, hreal.2.2.1 σ]
        simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac]
        change φ (v, z0) = 0
        by_contra hn
        have hs' := hs (subset_tsupport (φ : EvolutionAmbientState d → ℝ)
          (show (v, z0) ∈ Function.support (φ : EvolutionAmbientState d → ℝ) from hn))
        simp [phaseCoordinate, phaseCenter, PDE.vecDot, intervalIntegral.integral_same, lt_self_iff_false]
          at hs'
      · have ht' : σ < τ := lt_of_le_of_ne hστ ht
        obtain ⟨u, hu, hup, -⟩ := hreal.1 τ φ hφ
        have hB : ∀ t v, (B t v).PosSemidef := by
          intro t v
          have hbounds := (sectionTwoCoefficient_fullBounds lam Lam B hsetting.1).2.2
          exact posSemidef_of_hasEverywhereLoewnerBounds hsetting.1.1.le hbounds t v 0
        have hmove : ∀ t, movingDomain (PDE.euclideanBall 0 ρ) (fun _ => c) t =
            movingDomain (PDE.euclideanBall c ρ) stationary t := by
          intro t
          rw [movingDomain_stationary]
          ext w
          rw [mem_movingDomain_euclideanBall_iff]
          simp [PDE.euclideanBall, PDE.euclideanSqDist]
        have hφ' : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
            (fun _ => c) τ φ := by
          simpa only [IsSmoothCompactTerminalDatum, evolutionStateSet, hmove] using hφ
        have hu' : IsClassicalTerminalSolution (PDE.euclideanBall 0 ρ) (fun _ => c)
            (zIndependentCoefficient B) b τ φ u := by
          simpa only [IsClassicalTerminalSolution, evolutionPastClosedCylinder,
            evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
            evolutionLateralFrontier, hmove] using hu
        have hv' : v ∈ movingDomain (PDE.euclideanBall 0 ρ) (fun _ => c) σ := by
          rw [hmove]
          exact hv
        have hnonpos := classical_phase_test_nonpos B b (fun _ => c) σ τ Lb ρ ht' hρ ξ z0 hξ
          hsetting.2.2.2.2.1.1 continuous_const hB sgn hsgn
          φ hφ' hbound hs u hu' v hv' 
        have huintegral : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
            u ⟨σ, v, z0⟩ := by
          rw [hi]
          exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm
        apply le_antisymm
        · exact huintegral.trans_le hnonpos
        · exact integral_nonneg (fun x => (hbound x).1)
    let μ := K.master (movingQuery σ τ hστ v z0 hv)
    have hfinite : IsFiniteMeasure μ := ⟨(K.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
    let U := evolutionStateSet (PDE.euclideanBall c ρ) stationary τ
    have hU : IsOpen U := (isOpen_movingDomain (PDE.isOpen_euclideanBall c ρ) τ).prod
      isOpen_univ
    have hμ : μ Uᶜ = 0 := by
      have hr : μ.restrict U = μ := K.terminal_support _
      calc
        μ Uᶜ = (μ.restrict U) Uᶜ := by rw [hr]
        _ = μ (Uᶜ ∩ U) := Measure.restrict_apply hU.measurableSet.compl
        _ = 0 := by simp only [compl_inter_self, measure_empty]
    have hq : Continuous (fun x : EvolutionAmbientState d =>
        phaseCoordinate ξ z0 x - phaseCenter ξ b (fun _ => c) σ τ) := by
      unfold phaseCoordinate PDE.vecDot
      simp
      fun_prop
    apply ae_phase_strip_of_forbidden_tests hU hμ hq (Lb * ρ * (τ - σ))
    intro sgn hsgn φ hφ hc hs hbound
    let φB := smoothTestDatum φ hφ hbound
    have hdatum : IsSmoothCompactTerminalDatum (PDE.euclideanBall c ρ)
        stationary τ φB := ⟨hφ, hc, fun x hx => (hs hx).2⟩
    exact stationary_phase_test_zero σ τ ρ c hρ S K hreal
      ξ z0 v hξ hστ hv sgn hsgn φB hdatum hbound (fun x hx => (hs hx).1)
  have phase_localization_of_continuous_curve (lam : ℝ) (Lam : ℝ) (m : ℝ) (Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b) (σ τ ρ : ℝ) (γ : ℝ → PDE.Vec d) (hρ : 0 < ρ) (hγ : Continuous γ) (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ) (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ) (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K) (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ) (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ) :
      ∀ᵐ x ∂K.master (movingQuery σ τ hστ v z0 hv),
      |phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ| ≤ Lb * ρ * (τ - σ) := by
    have phase_test_zero_of_continuous_curve (σ τ ρ : ℝ) (γ : ℝ → PDE.Vec d) (hρ : 0 < ρ) (hγ : Continuous γ) (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) γ) (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ) (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) γ
        (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K) (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1) (hστ : σ ≤ τ) (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) (φ : BoundedBorel (EvolutionAmbientState d)) (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
        γ τ φ) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
        {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) -
          Lb * ρ * (τ - σ)}) :
        ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by
      let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
      let γc := γ
      let p : EvolutionState Ω γc σ := ⟨(v, z0), hv, mem_univ _⟩
      have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
          ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall 0 ρ).measurableSet σ τ hστ p :=
        integral_master_eq_fiber K (PDE.isOpen_euclideanBall 0 ρ).measurableSet
          σ τ hστ p φ φ.measurable
      by_cases ht : σ = τ
      · subst τ
        rw [hi, hreal.2.2.1 σ]
        simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac]
        change φ (v, z0) = 0
        by_contra hn
        have hs' := hs (subset_tsupport (φ : EvolutionAmbientState d → ℝ)
          (show (v, z0) ∈ Function.support (φ : EvolutionAmbientState d → ℝ) from hn))
        simp [phaseCoordinate, phaseCenter, PDE.vecDot, intervalIntegral.integral_same, lt_self_iff_false]
          at hs'
      · have ht' : σ < τ := lt_of_le_of_ne hστ ht
        obtain ⟨u, hu, hup, -⟩ := hreal.1 τ φ hφ
        have hB : ∀ t v, (B t v).PosSemidef := by
          intro t v
          have hbounds := (sectionTwoCoefficient_fullBounds lam Lam B hsetting.1).2.2
          exact posSemidef_of_hasEverywhereLoewnerBounds hsetting.1.1.le hbounds t v 0
        have hnonpos := classical_phase_test_nonpos B b γc σ τ Lb ρ ht' hρ ξ z0 hξ
          hsetting.2.2.2.2.1.1 hγ hB sgn hsgn
          φ hφ hbound hs u hu v hv
        have huintegral : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
            u ⟨σ, v, z0⟩ := by
          rw [hi]
          exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm
        apply le_antisymm
        · exact huintegral.trans_le hnonpos
        · exact integral_nonneg (fun x => (hbound x).1)
    let μ := K.master (movingQuery σ τ hστ v z0 hv)
    have hfinite : IsFiniteMeasure μ := ⟨(K.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
    let U := evolutionStateSet (PDE.euclideanBall 0 ρ) γ τ
    have hU : IsOpen U := (isOpen_movingDomain (PDE.isOpen_euclideanBall 0 ρ) τ).prod
      isOpen_univ
    have hμ : μ Uᶜ = 0 := by
      have hr : μ.restrict U = μ := K.terminal_support _
      calc
        μ Uᶜ = (μ.restrict U) Uᶜ := by rw [hr]
        _ = μ (Uᶜ ∩ U) := Measure.restrict_apply hU.measurableSet.compl
        _ = 0 := by simp only [compl_inter_self, measure_empty]
    have hq : Continuous (fun x : EvolutionAmbientState d =>
        phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) := by
      unfold phaseCoordinate PDE.vecDot
      simp
      fun_prop
    apply ae_phase_strip_of_forbidden_tests hU hμ hq (Lb * ρ * (τ - σ))
    intro sgn hsgn φ hφ hc hs hbound
    let φB := smoothTestDatum φ hφ hbound
    have hdatum : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
        γ τ φB := ⟨hφ, hc, fun x hx => (hs hx).2⟩
    exact phase_test_zero_of_continuous_curve σ τ ρ γ hρ hγ S K hreal
      ξ z0 v hξ hστ hv sgn hsgn φB hdatum hbound (fun x hx => (hs hx).1)
  have hm : 0 < m := hsetting.2.2.1
  have hLb : 0 < Lb := hm.trans_le hsetting.2.2.2.1
  have hρ := blockRho_pos hLb
  have hη := blockEta_pos hm hLb
  have hστ : σ ≤ σ + blockL0 m := le_add_of_nonneg_right (blockL0_pos hm).le
  have hsmall := add_le_add (Lb_mul_blockEta_mul_blockL0_le hm hLb)
    (sixteen_Lb_mul_blockRho_pow_three_le hLb)
  have hbound (γ : ℝ → PDE.Vec d) (hγ : IsContinuousPiecewiseC1 γ)
      (S : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (K : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ
        (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet
        (zIndependentCoefficient B) b S K)
      (q : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ)
      (hq : q.1 = (σ, σ + blockL0 m, v0, z0))
      (R : Measure (EvolutionState (PDE.euclideanBall v0 (4 * blockRho Lb))
        stationary (σ + blockL0 m))) [IsFiniteMeasure R]
      (hR : R.map Subtype.val =
        ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K.master q).real univ)) • K.master q)
      (E : Measure (EvolutionAmbientState d))
      (hE : ∀ A, MeasurableSet A → E A =
        ∫⁻ p, K0.master (movingQuery (σ + blockL0 m) (σ + blockTime m Lb)
          hsT p.1.1 p.1.2 p.2.1) A ∂R) :
      ∀ᵐ x ∂E, |phaseCoordinate ξ z0 x -
        (phaseCenter ξ b γ σ (σ + blockL0 m) +
          4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤ 1 / 4 := by
    have hv : v0 ∈ movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ σ := by
      have h := q.2.2.1
      simpa only [hq] using h
    have hq' : q = movingQuery σ (σ + blockL0 m) hστ v0 z0 hv := Subtype.ext hq
    have hphase := phase_localization_of_continuous_curve lam Lam m Lb D B b
      hsetting σ (σ + blockL0 m) (blockEta m Lb) γ hη hγ.1 S K hreal ξ z0 v0 hξ hστ hv
    rw [← hq'] at hphase
    have hRphase : ∀ᵐ p ∂R, |phaseCoordinate ξ z0 p.1 -
        phaseCenter ξ b γ σ (σ + blockL0 m)| ≤ Lb * blockEta m Lb * blockL0 m := by
      have h := Measure.ae_smul_measure hphase
        (ENNReal.ofReal (blockMass Cstar m Lb / (2 * (K.master q).real univ)))
      rw [← hR] at h
      have h' := ae_of_ae_map measurable_subtype_coe.aemeasurable h
      simpa only [add_sub_cancel_left] using h'
    have hKphase : ∀ᵐ p ∂R, ∀ᵐ x ∂continuationKernel K0 hsT p,
        |phaseCoordinate ξ p.1.2 x -
          (4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤
            16 * Lb * blockRho Lb ^ 3 := by
      apply Filter.Eventually.of_forall
      intro p
      have hp := stationary_phase_localization lam Lam m Lb D B b hsetting
        (σ + blockL0 m) (σ + blockTime m Lb) (4 * blockRho Lb) v0
        (mul_pos (by norm_num) hρ) S0 K0 hreal0 ξ p.1.2 p.1.1 hξ hsT p.2.1
      have hc : phaseCenter ξ b (fun _ => v0) (σ + blockL0 m)
          (σ + blockTime m Lb) = 4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0) := by
        unfold phaseCenter blockTime
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      rw [hc] at hp
      have he : Lb * (4 * blockRho Lb) *
          (σ + blockTime m Lb - (σ + blockL0 m)) = 16 * Lb * blockRho Lb ^ 3 := by
        unfold blockTime
        ring
      simpa only [he, continuationKernel_apply, evolutionQueryOfState_eq, movingQuery] using hp
    have h := continuation_phase_support Subtype.val measurable_subtype_coe ξ z0
      (phaseCenter ξ b γ σ (σ + blockL0 m))
      (4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))
      (Lb * blockEta m Lb * blockL0 m) (16 * Lb * blockRho Lb ^ 3)
      R (continuationKernel K0 hsT) hRphase hKphase E hE
    exact h.mono (fun x hx => hx.trans (by linarith only [hsmall]))
  have he1 := hbound γ1 hγ1 S1 K1 hreal1 q1 hq1 R1 hR1 E1 hE1
  have he2 := hbound γ2 hγ2 S2 K2 hreal2 q2 hq2 R2 hR2 E2 hE2
  refine ⟨?_, he1, he2, ?_, ?_⟩
  · linarith only [hphase]
  · exact he1.filter_mono (ae_mono hF1)
  · exact he2.filter_mono (ae_mono hF2)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

