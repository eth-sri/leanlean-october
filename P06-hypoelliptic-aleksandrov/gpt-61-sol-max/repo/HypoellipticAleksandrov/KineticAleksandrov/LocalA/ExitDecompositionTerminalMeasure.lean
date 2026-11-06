module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionTerminalTests
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Exact measure identification of the terminal interior face -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

variable {d : ℕ}

/-- The terminal evolution state retains velocity first and physical position second. -/
def exitStateCoordinates  (Q : KineticPoint d) : EvolutionAmbientState d :=
  (Q.velocity, Q.position)

/-- The actual state-coordinate projection is continuous. -/
theorem continuous_exitStateCoordinates  :
    Continuous (exitStateCoordinates (d := d)) :=
  continuous_velocity.prodMk continuous_position

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

variable (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})

/-- The terminal interior part of the actual exit measure is precisely the killed transition. -/
theorem ballExit_terminal_interior_map  :
    Measure.map exitStateCoordinates
      ((ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
        {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}) =
      ballTransition hH hLE hd hlam hLam B hB v₀ hR P T := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  let S : Set (KineticPoint d) := {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}
  let U := evolutionStateSet (PDE.euclideanBall v₀ R) (fun _ => 0) T.1

  let K := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
  let ρ := ballTransition hH hLE hd hlam hLam B hB v₀ hR P T
  have : IsFiniteMeasure ρ := ⟨(K.mass_le_one (ballEvolutionQuery P T)).trans_lt
    ENNReal.one_lt_top⟩
  have hSm  :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage continuous_velocity.measurable
  have hU : IsOpen U := by
    simpa only [U, evolutionStateSet, movingDomain_ball_zero] using
      (PDE.isOpen_euclideanBall v₀ R).prod isOpen_univ


  have heq (f : EvolutionAmbientState d → ℝ) (hfs : ContDiff ℝ PDE.smoothOrder f)
      (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
      (∫ x, f x ∂((μ.restrict S).map exitStateCoordinates)) = ∫ x, f x ∂ρ := by
    obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hfs.continuous
    let F : BoundedBorel (EvolutionAmbientState d) :=
      ⟨f, hfs.continuous.measurable,
        ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩⟩


    have hmn := integral_map (μ := μ.restrict S) (f := f)
      continuous_exitStateCoordinates.measurable.aemeasurable
      hfs.continuous.measurable.aestronglyMeasurable
    have hmr := integral_map (μ := K.fiberKernel
      (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
      (ballStartState P)) (f := f) measurable_subtype_coe.aemeasurable
      hfs.continuous.measurable.aestronglyMeasurable
    rw [K.map_fiberKernel_eq_master (PDE.isOpen_euclideanBall v₀ R).measurableSet
      P.1.time T.1 T.2.le (ballStartState P)] at hmr
    exact hmn.trans ((ballExit_terminal_probe_identity hH hLE hd hlam hLam B hB v₀ hR P T F (⟨hfs, hfc, hfU⟩)).trans hmr.symm)
  exact le_antisymm
    (measure_le_of_smooth_integral_le hU (by
        apply Measure.restrict_eq_self_of_ae_mem
        apply (ae_map_iff continuous_exitStateCoordinates.measurable.aemeasurable
          hU.measurableSet).mpr
        filter_upwards [ae_restrict_mem hSm] with Q hQ
        exact ⟨by simpa,
          mem_univ _⟩) (fun f hs hc hf _ => (heq f hs hc hf).le))
    (measure_le_of_smooth_integral_le hU (K.terminal_support (ballEvolutionQuery P T)) (fun f hs hc hf _ => (heq f hs hc hf).symm.le))

/-- The physical terminal interior measure is the map of the actual valid terminal fiber. -/
theorem ballExit_terminal_interior_eq_map  :
    (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T).restrict
      {Q | Q.velocity ∈ PDE.euclideanBall v₀ R} =
    Measure.map (fun w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) T.1 =>
      (ballStateStart T.1 w).1)
      ((localBallKernel hH hLE hd hlam hLam B hB v₀ hR).fiberKernel
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
        (ballStartState P)) := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  let S : Set (KineticPoint d) := {Q | Q.velocity ∈ PDE.euclideanBall v₀ R}
  let j : EvolutionAmbientState d → KineticPoint d := fun w => ⟨T.1, w.2, w.1⟩
  have hj : Measurable j :=
    (KineticPoint.continuous_mk continuous_const continuous_snd continuous_fst).measurable
  have hSm  :=
    (PDE.isOpen_euclideanBall v₀ R).measurableSet.preimage continuous_velocity.measurable

  have hmap : (μ.restrict S).map (j ∘ exitStateCoordinates) = μ.restrict S := by

    rw [Measure.map_congr (show j ∘ exitStateCoordinates =ᵐ[μ.restrict S] id by
        filter_upwards [(by
            filter_upwards [ae_restrict_mem hSm,
              ae_restrict_of_ae (ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T)]
              with Q hv hQ
            change Q.velocity ∈ PDE.euclideanBall v₀ R at hv
            rcases hQ with hQ | hQ
            · exact hQ.1
            · exact False.elim ((mem_interior_iff_notMem_frontier hv).mp
                ((PDE.isOpen_euclideanBall v₀ R).interior_eq.symm ▸ hv) hQ.2.2))] with Q hQ
        apply KineticPoint.ext
        · exact hQ.symm
        · rfl
        · rfl), Measure.map_id]
  have hid := congrArg (Measure.map j)
    (ballExit_terminal_interior_map hH hLE hd hlam hLam B hB v₀ hR P T)
  rw [Measure.map_map hj continuous_exitStateCoordinates.measurable, hmap] at hid
  dsimp only [ballTransition, ballEvolutionQuery] at hid
  rw [← MovingFiberKernel.map_fiberKernel_eq_master
    (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
    (ballStartState P), Measure.map_map hj measurable_subtype_coe] at hid
  exact hid

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
