module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MovingBarrierComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.Parabolic.KineticClassical
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Retention for the original globally piecewise-C1 curve

The supplied families and kernels remain indexed by the original curve. Only
the finite interval enters the barrier comparison and the final mass bound.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

theorem master_mass_eq_marginal_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
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
  have hC := PDE.isCompact_euclideanClosedBall (γ τ) hs.le
  have hopen := isOpen_movingDomain (PDE.isOpen_euclideanBall 0 ρ) (γ := γ) τ
  have hsub : PDE.euclideanClosedBall (γ τ) s ⊆
      movingDomain (PDE.euclideanBall 0 ρ) γ τ := by
    intro y hy
    have hball := PDE.euclideanClosedBall_subset_euclideanBall hs.le hsρ hy
    rw [mem_movingDomain_euclideanBall_iff]
    simpa only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist,
      Set.mem_ofPred_eq] using hball
  obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ := exists_smooth_cutoff hC hopen hsub
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
        simpa only [sub_zero] using hy.le
      change barrier N s (y - γ τ) ≤ φ y
      rw [hφone y hc]
      exact ((retention_polynomial_barrier (d := d) hN s hs).2.1 _).2
    · rw [(retention_polynomial_barrier hN s hs).2.2.2.2 _ hy |>.1]
      exact (hφbound y).1
  have hcenter := movingBarrier_comparison_at_center hN lam Lam s H ρ hs hsρ hlam hlamLam hc
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

private theorem barrierC_pos_of_choice {d N : ℕ} (hN : 3 ≤ N) (lam Lam : ℝ)
    (hchoice : 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam) :
    0 < barrierC d N lam Lam := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp := mul_pos hNp
    (sub_pos.mpr hchoice : 0 < 2 * (N - 1 : ℕ) * lam - (d : ℝ) * Lam)
  unfold barrierC
  nlinarith [hp]

section
variable (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
include hd hlam hlamLam

/-- The source prelimit retention bound for the original supplied curve. -/
theorem moving_ball_retention_prelimit_of_curve :
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
    have hbound := prelimit_of_partition hN lam Lam s H ρ hs hsρ hlam hlamLam
      (barrierC_pos_of_choice hN lam Lam hchoice) B hsetting.1 γ hpc.1 n r hr
      hpieces hspd' K hpar z hv'
    simpa only [hr0, hrlast] using hbound

/-- Passing the interior radius to the tube radius gives the exact source limiting rate. -/
theorem moving_ball_retention_at_radius_of_curve :
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
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
    z hστ' hv N hN hchoice
  have hpre := moving_ball_retention_prelimit_of_curve d hd lam Lam hlam hlamLam
    m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
    z hστ' hv N hN hchoice
  have hcont : ContinuousAt
      (fun s => Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ρ := by
    unfold barrierRate
    fun_prop (disch := positivity)
  have hlim := ENNReal.tendsto_ofReal (hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] ρ ≤ 𝓝 ρ))
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ s in 𝓝[<] ρ, 0 < s :=
    (lt_mem_nhds hρ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs hsρ
  exact hpre s hs hsρ

end

private theorem master_mass_on_terminal_domain {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ) :
    K.master q (evolutionStateSet Ω γ q.val.2.1) = K.master q univ := by
  have h := congrArg (fun μ : Measure (EvolutionAmbientState d) => μ univ)
    (K.terminal_support q)
  rw [Measure.restrict_apply MeasurableSet.univ] at h
  simpa only [univ_inter] using h

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
            (PDE.euclideanBall (γ τ) ρ ×ˢ univ) := by
  obtain ⟨N, hN, hchoice, hc⟩ := exists_retention_barrier_order d hd lam Lam hlam hlamLam
  let C : ℝ := 2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam
  have hLam : 0 < Lam := hlam.trans_le hlamLam
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv
  have hlimit := moving_ball_retention_at_radius_of_curve d hd lam Lam hlam hlamLam
    m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar z hστ' hv
    N hN hchoice
  have hrate := retention_rate_uniform hN lam Lam ρ H hlam hlamLam hρ hc
  have hexp : Real.exp (-C * (ρ⁻¹ ^ 2 + H ^ 2) * (τ - σ)) ≤
      Real.exp (-barrierRate d N lam Lam ρ H * (τ - σ)) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hrate (sub_nonneg.mpr hστ)
    convert neg_le_neg ht using 1 <;> ring
  have hmass := master_mass_on_terminal_domain K (movingQuery σ τ hστ' (γ σ) z hv)
  have hdomain : movingDomain (PDE.euclideanBall 0 ρ) γ τ =
      PDE.euclideanBall (γ τ) ρ := by
    ext v
    rw [mem_movingDomain_euclideanBall_iff]
    simp only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq]
  change K.master (movingQuery σ τ hστ' (γ σ) z hv)
    (movingDomain (PDE.euclideanBall 0 ρ) γ τ ×ˢ univ) = _ at hmass
  rw [hdomain] at hmass
  rw [hmass]
  exact (ENNReal.ofReal_le_ofReal hexp).trans hlimit

end HypoellipticAleksandrov.KineticAleksandrov.Decay
