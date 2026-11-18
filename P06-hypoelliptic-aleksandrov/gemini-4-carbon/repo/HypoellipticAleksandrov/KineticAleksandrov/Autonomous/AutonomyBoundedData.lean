module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.Parabolic Filter Evolution
open scoped Topology MatrixOrder

/-- Multiply a bounded datum by the actual compact cutoff in both physical coordinates. -/
def boundedConservationDatum (F : BoundedBorel (EvolutionAmbientState 1)) (N : ℕ) :
    BoundedBorel (EvolutionAmbientState 1) := by
  refine ⟨fun x => F x * conservationDatum N x,
    F.measurable.mul (conservationDatum N).measurable, ?_⟩
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  refine ⟨C, hC0, ?_⟩
  intro x
  rw [abs_mul, abs_of_nonneg (conservationDatum_bounds N x).1]
  exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N x).2
    (abs_nonneg _)).trans (by simpa using hC x)








/-- Every bounded smooth datum has a classical solution represented by the supplied kernel. -/
theorem fullspace_bounded_smooth_solution
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState 1))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ u : KineticPoint 1 → ℝ,
      IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
        (evolutionCoefficient A.a) (identityDrift 1) τ F u ∧
      ∀ q : EvolutionQuery autonomousWholeDomain (fun _ => 0), q.1.2.1 = τ →
        u ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ = ∫ x, F x ∂E.2.master q    := by
  have exists_bounded_fullspace_classical_limit (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState 1)) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C) (u : ℕ → KineticPoint 1 → ℝ) (hu : ∀ N, IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) τ (boundedConservationDatum F N) (u N)) (hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, |u N p| ≤
      C) :
      ∃ V : KineticPoint 1 → ℝ,
      (∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, Tendsto (fun N => u
        N p) atTop (𝓝 (V p))) ∧
      IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a)
        (identityDrift 1) τ F V := by
    have boundedConservationDatum_sub {N : ℕ} {M : ℕ} (hNM : N ≤ M) (x : EvolutionAmbientState 1) :
        |boundedConservationDatum F M x - boundedConservationDatum F N x| ≤
        (2 * C) / ((N : ℝ) + 1) ^ 2 *
          (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
      have boundedConservationDatum_error (N : ℕ) :
          |F x - boundedConservationDatum F N x| ≤ C / ((N : ℝ) + 1) ^ 2 *
          (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
        change |F x - F x * conservationDatum N x| ≤ _
        rw [← mul_one_sub, abs_mul, abs_of_nonneg
          (sub_nonneg.mpr (conservationDatum_bounds N x).2)]
        convert (mul_le_mul (hC x) (conservationDatum_deficit N x) (sub_nonneg.mpr (conservationDatum_bounds N x).2) hC0) using 1
        simp
        ring
      have hN := boundedConservationDatum_error N
      have hM := boundedConservationDatum_error M
      have hden : ((N : ℝ) + 1) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by
        have hn : (N : ℝ) ≤ M := by exact_mod_cast hNM
        nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) M]
      have hR : 0 ≤ 1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2 := by
        linarith [PDE.vecNormSq_nonneg x.1, PDE.vecNormSq_nonneg x.2]
      have hle := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hC0 (by positivity : 0 < ((N : ℝ) + 1) ^ 2) hden) hR
      have ht := abs_sub_le (boundedConservationDatum F M x) (F x)
        (boundedConservationDatum F N x)
      rw [abs_sub_comm (boundedConservationDatum F M x) (F x)] at ht
      have he : (2 * C) / ((N : ℝ) + 1) ^ 2 = 2 * (C / ((N : ℝ) + 1) ^ 2) := by ring
      rw [he]
      linarith
    let : SecondCountableTopology (KineticPoint 1) :=
      (KineticPoint.homeomorphProd 1).isEmbedding.secondCountableTopology
    have hΩo := isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible
    let S := evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ
    let U := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) τ
    have hU : IsOpen U := isOpen_evolutionPastOpenCylinder hΩo continuous_const τ
    have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
    obtain ⟨Ct, _hCt0, hCt⟩ := classical_sub_le_growthBarrier hΩo continuous_const hlam
      (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
    -- tail bound
    have hTail : ∀ N M : ℕ, N ≤ M → ∀ p ∈ S,
        |u M p - u N p| ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
      intro N M hNM p hp
      have hc : 0 ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 := by positivity
      have h1 := hCt τ (boundedConservationDatum F M) (boundedConservationDatum F N) (u M) (u N) _
        hc (hu M) (hu N)
        (fun x _ => (le_abs_self _).trans (boundedConservationDatum_sub hNM x)) p hp
      have h2 := hCt τ (boundedConservationDatum F N) (boundedConservationDatum F M) (u N) (u M) _
        hc (hu N) (hu M)
        (fun x _ => by
          exact (le_abs_self _).trans (by
            rw [abs_sub_comm]
            exact boundedConservationDatum_sub hNM x)) p hp
      rw [abs_le]
      constructor <;> linarith
    have hlimex : ∀ p ∈ S, ∃ v, Tendsto (fun N => u N p) atTop (𝓝 v) := fun p hp =>
      cauchySeq_tendsto_of_complete (cauchySeq_of_quadratic_tail
 (fun N M hNM => by
          have := hTail N M hNM p hp
          rwa [div_mul_eq_mul_div] at this))
    let V : KineticPoint 1 → ℝ := fun p => limUnder atTop (fun N => u N p)
    have hV : ∀ p ∈ S, Tendsto (fun N => u N p) atTop (𝓝 (V p)) := fun p hp =>
      tendsto_nhds_limUnder (hlimex p hp)
    -- the limit is bounded and satisfies the tail bound
    have hVbd : ∀ p ∈ S, |V p| ≤ C := fun p hp =>
      le_of_tendsto' ((hV p hp).abs) (fun N => hbd N p hp)
    have hVtail : ∀ N : ℕ, ∀ p ∈ S,
        |V p - u N p| ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
      intro N p hp
      refine le_of_tendsto ((hV p hp).sub_const (u N p) |>.abs) ?_
      filter_upwards [eventually_ge_atTop N] with M hM
      exact hTail N M hM p hp
    -- continuity on the closed cylinder
    have hcont : ContinuousOn V S := by
      have hloc : TendstoLocallyUniformlyOn (fun N => u N) V atTop S := by
        rw [Metric.tendstoLocallyUniformlyOn_iff]
        intro ε hε x hx
        refine ⟨S ∩ {q | growthBarrier Ct τ q < growthBarrier Ct τ x + 1}, ?_, ?_⟩
        · exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
            ((continuous_growthBarrier Ct τ).continuousAt.eventually_lt continuousAt_const
              (lt_add_one _) |>.mono fun q hq => hq))
        · have hlim := tendsto_quadratic_tail ((2 * C) * (growthBarrier Ct τ x + 1))
          filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN y hy
          rw [Real.dist_eq]
          have h1 := hVtail N y hy.1
          have h2 : (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ y ≤
              (2 * C) * (growthBarrier Ct τ x + 1) / ((N : ℝ) + 1) ^ 2 := by
            rw [div_mul_eq_mul_div]
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hy.2.le (by positivity : 0 ≤ 2 * C)
          linarith
      exact hloc.continuousOn (Eventually.of_forall fun N => (hu N).2.1).frequently
    -- terminal and lateral values
    have hterm : ∀ p ∈ evolutionTerminalClosure autonomousWholeDomain (fun _ => 0) τ,
        V p = F (p.position, p.velocity) := by
      intro p hp
      have hpS : p ∈ S := ⟨hp.1.le, hp.1 ▸ hp.2⟩
      refine tendsto_nhds_unique (hV p hpS) ?_
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ‖p.position‖ ‖p.velocity‖)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      have hy : ‖p.position‖ ≤ (N : ℝ) + 1 := by
        have := le_max_left ‖p.position‖ ‖p.velocity‖; linarith
      have hz : ‖p.velocity‖ ≤ (N : ℝ) + 1 := by
        have := le_max_right ‖p.position‖ ‖p.velocity‖; linarith
      rw [(hu N).2.2.2.2.1 p hp]
      change F (p.position, p.velocity) =
        F (p.position, p.velocity) *
          (zCutoffN 1 N p.position * zCutoffN 1 N p.velocity)
      rw [zCutoffN_eq_one hy, zCutoffN_eq_one hz, mul_one, mul_one]
    have hlat : ∀ p ∈ evolutionLateralFrontier autonomousWholeDomain (fun _ => 0) τ, V p = 0 := by
      intro p hp
      have hpS : p ∈ S := ⟨hp.1, frontier_subset_closure hp.2⟩
      refine tendsto_nhds_unique (hV p hpS) ?_
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
      exact ((hu N).2.2.2.2.2 p hp).symm
    -- weak equation, Hörmander, pointwise equation
    have hweak : IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U V
      (fun _ => 0) := by
      refine weak_transport_equation_of_vanishing_viscosity 1 (by omega) lam Lam 1 1 hlam hLam
        one_pos le_rfl
        autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a) (identityDrift 1)
          autonomousWholeDomain_admissible (zeroCurve_piecewiseC1 1)
        (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a)
        (evolutionCoefficient_bounds A) (identityDrift_smooth 1) (identityDrift_bounds 1).1
          (identityDrift_bounds 1).2 τ
        (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds u V C hC0 ?_ ?_ ?_ ?_ ?_
      · intro N
        exact classical_viscous_terminalSolution_isWeak hΩo continuous_const
          (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a) (identityDrift_smooth
          1)
          ((isClassicalViscousTerminalSolution_zero_iff autonomousWholeDomain (fun _ => 0)
            (evolutionCoefficient A.a) (identityDrift 1) τ _ _).2 (hu N))
      · intro N
        filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        exact hbd N p (hUS hp)
      · exact (hcont.mono hUS).aestronglyMeasurable hU.measurableSet
      · filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        exact hVbd p (hUS hp)
      · intro ψ hψ
        refine tendsto_integral_of_dominated_convergence (fun p => C * |ψ p|) ?_ ?_ ?_ ?_
        · intro N
          exact (((hu N).2.1.mono hUS).aestronglyMeasurable hU.measurableSet).mul
            hψ.aestronglyMeasurable
        · exact hψ.norm.const_mul C
        · intro N
          filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hbd N p (hUS hp)) (abs_nonneg _)
        · filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
          exact (hV p (hUS hp)).mul_const _
    obtain ⟨V', hV', hrep⟩ := exists_smooth_kinetic_representative hH hlam
      (evolutionCoefficient_smooth A) (evolutionCoefficient_bounds A)
      (identityDrift_smooth 1) one_pos (identityDrift_bounds 1).2 U hU V hweak
    have hcontP :=
      (hcont.mono hUS).comp (evolutionHomeomorph 1).continuous.continuousOn (fun x hx => hx)
    have hEq := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcontP hV'.continuousOn hrep
    have hVsmooth := hV'.congr fun x hx => hEq hx
    refine ⟨V, hV, ⟨C, hC0, fun p hp => hVbd p hp⟩, hcont, ?_, ?_, ?_, ?_⟩
    · rw [evolutionPastInteriorRaw_eq_image]
      exact contDiffOn_comp_evolutionHomeomorph_iff.mp hVsmooth
    · exact transportedForwardOperator_eq_zero_of_smooth_weak (evolutionCoefficient_smooth A)
        (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hU
        hweak hVsmooth (Filter.EventuallyEq.refl _ _)
    · exact hterm
    · exact hlat
  have boundedConservationDatum_smoothCompact (N : ℕ) (τ : ℝ) :
      IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) τ
      (boundedConservationDatum F N) := by
    have hc := conservationDatum_smoothCompact N τ
    refine ⟨hF.mul hc.1, hc.2.1.mul_left, ?_⟩
    exact tsupport_mul_subset_right.trans hc.2.2
  have boundedConservationDatum_bound {C : ℝ} (hC : ∀ x, |F x| ≤ C) (N : ℕ) (x : EvolutionAmbientState 1) :
      |boundedConservationDatum F N x| ≤ C := by
    change |F x * conservationDatum N x| ≤ C
    rw [abs_mul, abs_of_nonneg (conservationDatum_bounds N x).1]
    exact (mul_le_mul_of_nonneg_left (conservationDatum_bounds N x).2
      (abs_nonneg _)).trans (by simpa using hC x)
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  choose v hv hvr _ using fun N =>
    hE.1 τ (boundedConservationDatum F N) (boundedConservationDatum_smoothCompact N τ)
  have hb (N : ℕ) : ∀ p ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, |v N p| ≤ C :=
    classical_abs_le_const
      (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
      continuous_const hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
      le_rfl zero_le_one
      ((isClassicalViscousTerminalSolution_zero_iff _ _ _ _ _ _ _).2 (hv N))
      (boundedConservationDatum_bound hC N)
  obtain ⟨u, hulim, hu⟩ := exists_bounded_fullspace_classical_limit
    τ F C hC0 hC v hv hb
  refine ⟨u, hu, ?_⟩
  intro q hqτ
  let p : KineticPoint 1 := ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩
  have hp : p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ :=
    ⟨hqτ ▸ q.2.1, subset_closure q.2.2.1⟩
  have heq (N : ℕ) : v N p = ∫ x, boundedConservationDatum F N x ∂E.2.master q := by
    let s : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
      ⟨q.1.2.2, q.2.2⟩
    have hr := hvr N q.1.1 (hqτ ▸ q.2.1) s
    have hi := hE.2.1 q.1.1 τ (hqτ ▸ q.2.1) s
      (terminalStateDatum (boundedConservationDatum F N))
    have hm := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
      q.1.1 τ (hqτ ▸ q.2.1) s (boundedConservationDatum F N)
      (boundedConservationDatum F N).measurable
    subst τ
    exact hr.trans (hi.trans hm.symm)
  have : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have ht : Tendsto (fun N => ∫ x, boundedConservationDatum F N x ∂E.2.master q)
      atTop (𝓝 (∫ x, F x ∂E.2.master q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun N => (boundedConservationDatum F N).measurable.aestronglyMeasurable)
      (integrable_const C) (fun N => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact boundedConservationDatum_bound hC N x
    · obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ‖x.1‖ ‖x.2‖)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      change F x = F x * (zCutoffN 1 N x.1 * zCutoffN 1 N x.2)
      have hy : ‖x.1‖ ≤ (N : ℝ) + 1 := by
        have := le_max_left ‖x.1‖ ‖x.2‖; linarith
      have hz : ‖x.2‖ ≤ (N : ℝ) + 1 := by
        have := le_max_right ‖x.1‖ ‖x.2‖; linarith
      rw [zCutoffN_eq_one hy, zCutoffN_eq_one hz, mul_one, mul_one]
  exact tendsto_nhds_unique ((hulim p hp).congr heq) ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

