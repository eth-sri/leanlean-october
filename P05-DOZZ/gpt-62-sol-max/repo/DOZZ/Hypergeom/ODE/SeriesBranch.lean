/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.LocalState
public import DOZZ.Hypergeom.ODE.SeriesEquation

/-! Continuation of the ordinary Gauss series along a regular star-convex branch. -/

@[expose] public section

open Filter Set unitInterval Topology

namespace DOZZ.Proofs

/-- The state `(f, f')` of the ordinary Gauss series. -/
noncomputable def ordinaryHypergeometricState (a b c : ℂ) (z : ℂ) : ℂ × ℂ :=
  (ordinaryHypergeometric a b c z, deriv (ordinaryHypergeometric a b c) z)

section
variable (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {z : ℂ}
include hc

private theorem ordinaryHypergeometric_state_hasDerivAt (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometricState a b c)
      (deriv (ordinaryHypergeometric a b c) z,
        deriv (deriv (ordinaryHypergeometric a b c)) z) z := by
  have ha := ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc z
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  exact ha.differentiableAt.hasDerivAt.prodMk ha.deriv.differentiableAt.hasDerivAt

/-- On the punctured unit disk, the ordinary-series state solves the explicit first-order system. -/
theorem ordinaryHypergeometricState_solves_gaussSystem_on_unitDisk
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometricState a b c)
      (gaussSystemOperator a b c z (ordinaryHypergeometricState a b c z)) z := by
  have hpair := ordinaryHypergeometric_state_hasDerivAt a b c hc hz
  have hsys := ordinaryHypergeometric_state_solves_gaussSystem a b c hc hz0 hz
  exact hpair.congr_deriv (by simpa [ordinaryHypergeometricState] using hsys.symm)

end

section
variable {U : Set ℂ} (hreg : U ⊆ gaussRegularPlane) (u : U)
  (hstar : StarConvex ℝ (u : ℂ) U)

/-- Use the straight path from the center to the target for the choice of continuation. -/
noncomputable def seriesBranchPath (z : U) : Path u z := by
  let g : unitInterval → ℂ := fun t => (1 - (t : ℝ)) • (u : ℂ) + (t : ℝ) • (z : ℂ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hmem (t : unitInterval) : g t ∈ U :=
    hstar z.property (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  refine ⟨⟨_, hg.subtype_mk hmem⟩, Subtype.ext ?_, Subtype.ext ?_⟩ <;> simp [g]

noncomputable def seriesBranchLift (a b c : ℂ) (z : U) :
    PathContinuationLift (subtypePathFunction (seriesBranchPath u hstar z))
      (gaussSystemOperator a b c) (ordinaryHypergeometricState a b c u) :=
  Classical.choice (exists_path_continuation_lift (subtypePathFunction_continuous _).continuousOn
    gaussRegularPlane gaussRegularPlane_isOpen (gaussSystemOperator a b c)
    (gaussSystemOperator_differentiableOn a b c)
    (fun t _ => hreg (subtypePathFunction_mem _ t)) (ordinaryHypergeometricState a b c u))

/-- The first component of the endpoint, extended by zero off the branch domain. -/
noncomputable def gaussSeriesBranchScalar (a b c z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ U then ((seriesBranchLift hreg u hstar a b c ⟨z, hz⟩).value 1).1 else 0

/-- Path independence identifies the endpoint with the local Picard disk. -/
theorem gaussSeriesBranchScalar_differentiableOn (hU : IsOpen U) (a b c : ℂ) :
    DifferentiableOn ℂ (gaussSeriesBranchScalar hreg u hstar a b c) U := by
  letI : ContractibleSpace U := StarConvex.contractibleSpace hstar ⟨u, u.property⟩
  intro z hz
  let x : U := ⟨z, hz⟩
  let L := seriesBranchLift hreg u hstar a b c
  obtain ⟨R, δ, hR, hδ, _, D, hcenter, hlocal⟩ := subtype_path_state_locally_eq_picard hU
    ((gaussSystemOperator_differentiableOn a b c).mono hreg) (L x) (fun w => (L w).value 1)
    (fun w {q} B => subtype_path_lifts_endpoint_eq_of_simplyConnected hreg a b c q
      (seriesBranchPath u hstar w) _ B (L w))
  have hd := (D.derivative z (by rw [hcenter]; exact Metric.mem_ball_self hR)).differentiableAt.fst
  apply DifferentiableAt.differentiableWithinAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz, Metric.ball_mem_nhds z hδ] with w hw hwδ
  simpa only [gaussSeriesBranchScalar, dif_pos hw] using congrArg Prod.fst (hlocal ⟨w, hw⟩ hwδ)

/-- Within the unit disk the straight path is entirely in the series domain, so its
ordinary-series state itself supplies a solution chart at every parameter. -/
theorem gaussSeriesBranchScalar_eq_ordinary (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    (hu : ‖(u : ℂ)‖ < 1) {z : ℂ} (hz : z ∈ U) (hnorm : ‖z‖ < 1) :
    gaussSeriesBranchScalar hreg u hstar a b c z = ordinaryHypergeometric a b c z := by
  let x : U := ⟨z, hz⟩
  let p := seriesBranchPath u hstar x
  let γ := subtypePathFunction p
  let L := seriesBranchLift hreg u hstar a b c x
  let H := gaussSystemOperator a b c
  let S := ordinaryHypergeometricState a b c
  let V := gaussRegularPlane ∩ Metric.ball (0 : ℂ) 1
  have hnormPath (t : ℝ) : ‖γ t‖ < 1 := by
    let s := Set.projIcc 0 1 zero_le_one t
    change ‖(1 - (s : ℝ)) • (u : ℂ) + (s : ℝ) • z‖ < 1
    have hmem := convex_ball (0 : ℂ) 1
      (by simpa only [Metric.mem_ball, dist_zero_right] using hu)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm)
      (sub_nonneg.mpr s.property.2) s.property.1 (by ring)
    simpa only [Metric.mem_ball, dist_zero_right] using hmem
  have hV (t : ℝ) : γ t ∈ V := ⟨hreg (subtypePathFunction_mem p t), by
    simpa only [Metric.mem_ball, dist_zero_right] using hnormPath t⟩
  have hcont : ContinuousOn γ (Icc 0 1) := (subtypePathFunction_continuous p).continuousOn
  have hScont : ContinuousOn (fun t => S (γ t)) (Icc 0 1) := by
    intro t ht
    exact ((ordinaryHypergeometric_state_hasDerivAt a b c hc (hnormPath t)).continuousAt.comp
      (subtypePathFunction_continuous p).continuousAt).continuousWithinAt
  have hVopen : IsOpen V := gaussRegularPlane_isOpen.inter Metric.isOpen_ball
  have hcharts (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      Nonempty (PathSolutionChart γ H (fun t => S (γ t)) t) := by
    obtain ⟨r, M, hr, hM, hb⟩ := exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton id continuousOn_id V hVopen H
      ((gaussSystemOperator_differentiableOn a b c).mono inter_subset_left)
      (by rintro w rfl; exact hV t)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds (hV t))
    refine ⟨⟨min r ε, lt_min hr hε, M, hM, S, ?_, ?_, 1, by norm_num, fun _ _ _ => rfl⟩⟩
    · exact fun w hw => (hb _ (mem_singleton _)).2 w (Metric.ball_subset_ball (min_le_left _ _) hw)
    · intro w hw
      have hv := hball (Metric.ball_subset_ball (min_le_right _ _) hw)
      exact ordinaryHypergeometricState_solves_gaussSystem_on_unitDisk a b c hc hv.1.1
        (by simpa only [Metric.mem_ball, dist_zero_right] using hv.2)
  have hγ₀ : γ 0 = u := by simp [γ, subtypePathFunction]
  have hγ₁ : γ 1 = z := by simpa [γ, subtypePathFunction, x] using congrArg Subtype.val p.target
  have heq := continuous_path_solution_lifts_unique hcont H L.value_continuous hScont
    (path_continuation_lift_has_solution_charts hcont L) hcharts
    (by rw [hγ₀]; exact L.value_initial) 1 (by norm_num)
  rw [hγ₁] at heq
  rw [gaussSeriesBranchScalar, dite_eq_left hz]
  change (L.value 1).1 = (S z).1
  exact congrArg Prod.fst heq

end

end DOZZ.Proofs
