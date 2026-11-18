module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Filter SectionTwo TheoremA Evolution Set MeasureTheory
open scoped Topology

/-- Exact derivative of a scalar cutoff depending only on transported position. -/
theorem reconstruction_position_cutoff_fderiv (chi : ℝ → ℝ)
    (hchi : Differentiable ℝ chi) (x w : EvolutionVec 1) :
    fderiv ℝ (fun y => chi (transportedCoord 1 y 0)) x w =
      deriv chi (transportedCoord 1 x 0) * transportedCoord 1 w 0 := by
  let c :=
    (ContinuousLinearMap.proj (φ := fun _ => ℝ) 0).comp (transportedCoord 1)
  have hh := congrArg (fun L => L w) ((hchi (c x)).hasDerivAt.comp_hasFDerivAt x c.hasFDerivAt).fderiv
  simpa using! hh

/-- Only the transport derivative contributes to a pure position cutoff product. -/
theorem reconstruction_position_cutoff_operator
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (f : EvolutionVec 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : EvolutionVec 1) :
    transportedOperator B b (fun y => chi (transportedCoord 1 y 0) * f y) x =
      chi (transportedCoord 1 x 0) * transportedOperator B b f x +
        b (diffusedCoord 1 x) 0 * deriv chi (transportedCoord 1 x 0) * f x := by
  let c : EvolutionVec 1 → ℝ := fun y => chi (transportedCoord 1 y 0)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    hchi.comp ((contDiff_apply ℝ ℝ 0).comp (transportedCoord 1).contDiff)
  have hcd := hc.differentiable (by simp)
  have hfd := hf.differentiable (by simp)
  have hcv (y : EvolutionVec 1) : fderiv ℝ c y (basisV 0) = 0 := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisV, transportedCoord_packPoint, Pi.zero_apply, mul_zero]
  have hct : fderiv ℝ c x basisT = 0 := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisT, transportedCoord_packPoint, Pi.zero_apply, mul_zero]
  have hcz : fderiv ℝ c x (basisZ 0) = deriv chi (transportedCoord 1 x 0) := by
    rw [reconstruction_position_cutoff_fderiv _ (hchi.differentiable (by simp))]
    simp only [basisZ, transportedCoord_packPoint, Pi.single_eq_same, mul_one]
  have hv : (fun y => fderiv ℝ (fun z => c z * f z) y (basisV 0)) =
      fun y => c y * fderiv ℝ f y (basisV 0) := by
    funext y
    rw [fderiv_fun_mul (hcd y) (hfd y)]
    simp [add_apply, smul_apply, hcv]
  have hfv : Differentiable ℝ (fun y => fderiv ℝ f y (basisV 0)) :=
    ((hf.contDiff_fderiv_apply (m := (⊤ : ℕ∞)) (by simp)).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  simp only [transportedOperator, Fin.sum_univ_one]
  rw [hv, fderiv_fun_mul (hcd x) (hfd x), fderiv_fun_mul (hcd x) (hfv x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hcv, hct, hcz, mul_zero, add_zero]
  ring



/-- Smoothness in packed coordinates supplies physical continuity. -/
theorem reconstruction_smooth_physical_continuous (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph)) :
    Continuous phi := by
  have hh := hphi.continuous.comp reconstructionPhysicalHomeomorph.symm.continuous
  have heq : (phi ∘ reconstructionPhysicalHomeomorph) ∘
      reconstructionPhysicalHomeomorph.symm = phi := by
    funext p
    exact congrArg phi (reconstructionPhysicalHomeomorph.apply_symm_apply p)
  rwa [heq] at hh

/-- The same endpoint bound needs only the physical time and position slice at the point. -/
theorem reconstruction_closed_velocity_slice_bound
    (H : Interval) (phi : Point → ℝ) (hc : Continuous phi) (M : ℝ)
    (p : Point) (hp : p.velocity 0 ∈ Icc H.lo H.hi)
    (hb : ∀ v ∈ H.carrier, |phi ⟨p.time, p.position, fun _ => v⟩| ≤ M) :
    |phi p| ≤ M := by
  let f : ℝ → ℝ := fun v => |phi ⟨p.time, p.position, fun _ => v⟩|
  have hf : Continuous f :=
    (hc.comp ((KineticPoint.homeomorphProd 1).symm.continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk
        (continuous_pi fun _ => continuous_id))))).abs
  have hcl : p.velocity 0 ∈ closure (Ioo H.lo H.hi) := by
    rw [closure_Ioo H.ordered.ne]
    exact hp
  have he : (fun _ => p.velocity 0) = p.velocity := by
    ext i
    rw [Fin.eq_zero i]
  simpa only [f, he] using (le_on_closure hb hf.continuousOn continuousOn_const hcl)


/-- The actual identity holds for every globally smooth test bounded, together with its
operator, on the open velocity strip. No derivative of the coefficient enters the bound. -/
theorem strip_identity_bounded_smooth_future_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hb : ∃ M : ℝ, ∀ p, e.1.time ≤ p.time → p.time ≤ T →
      p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e  := by
  have exists_reconstruction_position_probe (a : ℝ) (bx : ContDiffBump (0 : ℝ)) :
      ∃ F : exitProbeSubmodule,
      (∀ p, a ≤ p.time → p.time ≤ T → p.velocity 0 ∈ Icc H.lo H.hi →
        exitProbePhysical F p = bx (p.position 0) * phi p) ∧
      ∀ p, a ≤ p.time → p.time ≤ T → p.velocity 0 ∈ Icc H.lo H.hi →
        forwardScalarOperator A.a (exitProbePhysical F) p =
          bx (p.position 0) * forwardScalarOperator A.a phi p +
            p.velocity 0 * deriv bx (p.position 0) * phi p := open Metric in by
    have reconstruction_physical_operator_packed (p : Point) :
        forwardScalarOperator A.a phi p =
        transportedOperator (evolutionCoefficient A.a) (identityDrift 1)
          (phi ∘ reconstructionPhysicalHomeomorph) (reconstructionPhysicalHomeomorph.symm p) := by
      let x := reconstructionPhysicalHomeomorph.symm p
      have heq : (phi ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1 =
          phi ∘ reconstructionPhysicalHomeomorph := rfl
      have hs : ContDiffAt ℝ 2 ((phi ∘ sectionTwoPoint) ∘ evolutionHomeomorph 1) x := by
        rw [heq]
        exact (hphi.of_le (by simp)).contDiffAt
      have hop := transportedOperator_comp (B := evolutionCoefficient A.a) (b := identityDrift 1) hs
      rw [heq, reconstruction_scalar_operator_swap] at hop
      have hx : sectionTwoPoint (evolutionHomeomorph 1 x) = p :=
        reconstructionPhysicalHomeomorph.apply_symm_apply p
      rw [hx] at hop
      exact hop.symm
    let Rt := max |a| |T| + 1
    let Rv := max |H.lo| |H.hi| + 1
    have hRt : 0 < Rt := by dsimp [Rt]; positivity
    have hRv : 0 < Rv := by dsimp [Rv]; positivity
    let bt := reconstructionPositionBump Rt hRt
    let bv := reconstructionPositionBump Rv hRv
    let f := phi ∘ reconstructionPhysicalHomeomorph
    let g : EvolutionVec 1 → ℝ := fun x =>
      bt (timeCoord 1 x) * bv (diffusedCoord 1 x 0) * bx (transportedCoord 1 x 0) * f x
    let F : exitProbeSubmodule := ⟨g, (((bt.contDiff.comp (timeCoord 1).contDiff).mul (bv.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp (diffusedCoord 1).contDiff))).mul (bx.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp (transportedCoord 1).contDiff)) |>.mul hphi), reconstruction_product_cutoff_compact bt bv bx f⟩
    have hloc (p : Point) (ha : a ≤ p.time) (hT : p.time ≤ T)
        (hv : p.velocity 0 ∈ Icc H.lo H.hi) :
        g =ᶠ[𝓝 (reconstructionPhysicalHomeomorph.symm p)]
          (fun x => bx (transportedCoord 1 x 0) * f x) := by
      have ht : |p.time| < Rt := by
        have hh := abs_le.mpr
          ⟨(neg_abs_le a).trans ha |>.trans' (neg_le_neg (le_max_left _ _)),
            hT.trans ((le_abs_self T).trans (le_max_right _ _))⟩
        linarith
      have hv' : |p.velocity 0| < Rv := by
        have hh := abs_le.mpr
          ⟨(neg_abs_le H.lo).trans hv.1 |>.trans' (neg_le_neg (le_max_left _ _)),
            hv.2.trans ((le_abs_self H.hi).trans (le_max_right _ _))⟩
        linarith
      have ht1 := bt.eventuallyEq_one_of_mem_ball
        (show timeCoord 1 (reconstructionPhysicalHomeomorph.symm p) ∈ ball 0 bt.rIn by
          rw [mem_ball, Real.dist_eq, sub_zero]
          exact ht)
      have hv1 := bv.eventuallyEq_one_of_mem_ball
        (show diffusedCoord 1 (reconstructionPhysicalHomeomorph.symm p) 0 ∈ ball 0 bv.rIn by
          rw [mem_ball, Real.dist_eq, sub_zero]
          exact hv')
      filter_upwards [(ht1.comp_tendsto (timeCoord 1).continuous.continuousAt), (hv1.comp_tendsto (((continuous_apply 0).comp (diffusedCoord 1).continuous).continuousAt))] with x hx hy
      simp only [Function.comp_apply, Pi.one_apply] at hx hy
      dsimp only [g]
      rw [hx, hy]
      simp
    refine ⟨F, ?_, ?_⟩
    · intro p ha hT hv
      have hh := (hloc p ha hT hv).eq_of_nhds
      change g (reconstructionPhysicalHomeomorph.symm p) = _
      rw [hh]
      simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply]
      rfl
    · intro p ha hT hv
      rw [exitProbePhysical_operator]
      change transportedOperator _ _ g _ = _
      rw [reconstruction_transportedOperator_congr _ _ (hloc p ha hT hv),
        reconstruction_position_cutoff_operator _ _ bx bx.contDiff f hphi]
      rw [← reconstruction_physical_operator_packed p]
      simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply, identityDrift]
      rfl
  obtain ⟨M, hM⟩ := hb
  let bx (n : ℕ) := reconstructionPositionBump ((n : ℝ) + 1) (by positivity)
  choose F hF hK using fun n => exists_reconstruction_position_probe e.1.time
    (bx n)
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let Γ := stripGreenOfKernel H E.2 T e
  have hΩ := stripExitOfRealization_ae_closed_future hH hlam hLam A H E hE T e
  have hΓ : ∀ᵐ p ∂Γ, e.1.time ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e,
      reconstruction_green_ae_time_gt H E.2 T e] with p hp ht
    exact ⟨ht.le, hp.1.le, hp.2.1.le, hp.2.2.le⟩
  have hval (n : ℕ) : (fun p => exitProbePhysical (F n) p) =ᵐ[Ω]
      fun p => bx n (p.position 0) * phi p := by
    filter_upwards [hΩ] with p hp
    exact hF n p hp.1 hp.2.1 hp.2.2
  have hsrc (n : ℕ) : (fun p => forwardScalarOperator A.a (exitProbePhysical (F n)) p) =ᵐ[Γ]
      fun p => bx n (p.position 0) * forwardScalarOperator A.a phi p +
        p.velocity 0 * deriv (bx n) (p.position 0) * phi p := by
    filter_upwards [hΓ] with p hp
    exact hK n p hp.1 hp.2.1 hp.2.2
  have hvlim : Tendsto (fun n => ∫ p, exitProbePhysical (F n) p ∂Ω) atTop
      (𝓝 (∫ p, phi p ∂Ω)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
    · intro n
      exact (exitProbePhysical_continuous_compact (F n)).1.measurable.aestronglyMeasurable
    · exact integrable_const M
    · intro n
      filter_upwards [hval n, hΩ] with p hp hs
      rw [Real.norm_eq_abs, hp, abs_mul, abs_of_nonneg (bx n).nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) (bx n).le_one).trans
        (reconstruction_closed_velocity_slice_bound H phi (reconstruction_smooth_physical_continuous phi hphi) M p hs.2.2
          (fun v hv => (hM ⟨p.time, p.position, fun _ => v⟩ hs.1 hs.2.1 hv).1))
    · filter_upwards [hΩ] with p hp
      have hq := (reconstructionPositionBump_tendsto (p.position 0)).mul_const (phi p)
      simp only [one_mul] at hq
      exact hq.congr (fun n => (hF n p hp.1 hp.2.1 hp.2.2).symm)
  obtain ⟨D, hDn, hD⟩ := reconstructionUnitBump_properties.2.2.2
  let V := max |H.lo| |H.hi|
  have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
  have hvbd (p : Point) (hp : p.velocity 0 ∈ Icc H.lo H.hi) : |p.velocity 0| ≤ V := by
    apply abs_le.mpr
    constructor
    · exact ((neg_le_neg (le_max_left |H.lo| |H.hi|)).trans
        (neg_abs_le H.lo)).trans hp.1
    · exact hp.2.trans ((le_abs_self H.hi).trans (le_max_right _ _))
  have hsmeas (n : ℕ) : AEStronglyMeasurable
      (forwardScalarOperator A.a (exitProbePhysical (F n))) Γ :=
    (exitProbeOperatorDatum A (F n)).measurable.aestronglyMeasurable
  have hslim : Tendsto
      (fun n => ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ) atTop
      (𝓝 (∫ p, forwardScalarOperator A.a phi p ∂Γ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M + V * D * M)
    · exact hsmeas
    · exact integrable_const _
    · intro n
      filter_upwards [hsrc n, stripGreenOfKernel_ae_mem_stripPast H E.2 T e, hΓ]
        with p hp hs ht
      have hv := hvbd p ⟨hs.2.1.le, hs.2.2.le⟩
      have hd : |deriv (bx n) (p.position 0)| ≤ D :=
        (reconstructionPositionBump_deriv_bound _ (by positivity) D hD _).trans (by
          apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) n])
      have hh := hM p ht.1 ht.2.1 hs.2
      rw [Real.norm_eq_abs, hp]
      calc
        _ ≤ |bx n (p.position 0) * forwardScalarOperator A.a phi p| +
            |p.velocity 0 * deriv (bx n) (p.position 0) * phi p| := abs_add_le _ _
        _ ≤ M + V * D * M := by
          simp only [abs_mul, abs_of_nonneg (bx n).nonneg]
          apply add_le_add
          · exact (mul_le_of_le_one_left (abs_nonneg _) (bx n).le_one).trans hh.2
          · exact mul_le_mul
              (mul_le_mul hv hd (abs_nonneg _) hV) hh.1 (abs_nonneg _)
              (mul_nonneg hV hDn)
    · filter_upwards [hΓ] with p hp
      have hq := ((reconstructionPositionBump_tendsto (p.position 0)).mul_const
        (forwardScalarOperator A.a phi p)).add
        (((reconstructionPositionBump_deriv_tendsto (p.position 0)).const_mul
          (p.velocity 0)).mul_const (phi p))
      simp only [one_mul, mul_zero, zero_mul, add_zero] at hq
      exact hq.congr (fun n => (hK n p hp.1 hp.2.1 hp.2.2).symm)
  have hpole : Tendsto (fun n => exitProbePhysical (F n) e.1) atTop (𝓝 (phi e.1)) := by
    have hv : e.1.velocity 0 ∈ Icc H.lo H.hi := ⟨e.2.2.1.le, e.2.2.2.le⟩
    have hh := (reconstructionPositionBump_tendsto (e.1.position 0)).mul_const (phi e.1)
    simp only [one_mul] at hh
    exact hh.congr (fun n => (hF n e.1 le_rfl ((WithTop.coe_lt_coe.mp e.2.1).le) hv).symm)
  have hi (n : ℕ) : exitProbePhysical (F n) e.1 =
      (∫ p, exitProbePhysical (F n) p ∂Ω) -
        ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ := by
    have hh := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e (F n)
    change (∫ p, exitProbePhysical (F n) p ∂Ω) =
      exitProbePhysical (F n) e.1 +
        ∫ p, forwardScalarOperator A.a (exitProbePhysical (F n)) p ∂Γ at hh
    linarith
  exact tendsto_nhds_unique hpole ((hvlim.sub hslim).congr (fun n => (hi n).symm))

/-- The bounded smooth identity under the source's time-uniform open-velocity bounds. -/
theorem strip_identity_bounded_smooth_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (hb : ∃ M : ℝ, ∀ p, p.velocity 0 ∈ H.carrier →
      |phi p| ≤ M ∧ |forwardScalarOperator A.a phi p| ≤ M) :
    phi e.1 = (∫ p, phi p ∂stripExitOfRealization hH hlam hLam A H E hE T e) -
      ∫ p, forwardScalarOperator A.a phi p ∂stripGreenOfKernel H E.2 T e := by
  apply strip_identity_bounded_smooth_future_of_realization hH hlam hLam A H E hE T e phi hphi
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, fun p _ _ hp => hM p hp⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

