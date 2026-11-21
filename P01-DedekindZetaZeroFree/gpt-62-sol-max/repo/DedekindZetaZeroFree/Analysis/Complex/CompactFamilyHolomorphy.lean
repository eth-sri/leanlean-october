module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.ContinuousMap.Algebra

@[expose] public section

open scoped Topology

namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

theorem compact_family_holomorphic {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → C(X, ℂ))
    (hc : ContinuousOn (fun p : ℂ × X => j p.1 p.2) (O ×ˢ Set.univ))
    (hd : ∀ x : X, DifferentiableOn ℂ (fun z => j z x) O) :
    DifferentiableOn ℂ j O := by
  have hj : ContinuousOn j O := by
    apply continuousOn_iff_continuous_restrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    let a : O × X → ℂ × X := fun p => (p.1.val,p.2)
    have ha : Continuous a := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact hc.comp_continuous ha (fun p => ⟨p.1.property, Set.mem_univ _⟩)
  intro s hs
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hs)
  let R := r/2
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : Metric.closedBall s R ⊆ O :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hrO
  have hcircle : CircleIntegrable j s R :=
    (hj.mono (Metric.sphere_subset_closedBall.trans hclosed)).circleIntegrable hR.le
  let g : ℂ → C(X,ℂ) := fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    circleIntegral (fun z => (z-w)⁻¹ • j z) s R
  have heq : Set.EqOn g j (Metric.ball s R) := by
    intro w hw
    ext x
    let L : C(X,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
    have hw' : w ∉ Metric.sphere s |R| := by
      rw [abs_of_pos hR]
      intro hh
      exact (ne_of_lt (Metric.mem_ball.mp hw)) hh
    have hi := hcircle.sub_zpow_smul (-1) hw'
    have hL : L (circleIntegral (fun z => (z-w)⁻¹ • j z) s R) =
        circleIntegral (fun z => (z-w)⁻¹ • j z x) s R := by
      rw [circleIntegral, circleIntegral, ← L.intervalIntegral_comp_comm (by simpa using hi.out)]
      simp only [map_smul]
      rfl
    change L ((2 * Real.pi * Complex.I : ℂ)⁻¹ • _) = _
    rw [map_smul, hL]
    exact (((hd x).mono hclosed).mono Metric.closure_ball_subset_closedBall).diffContOnCl
      |>.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hg : DifferentiableAt ℂ g s := by
    change DifferentiableAt ℂ (fun w => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      circleIntegral (fun z => (z-w)⁻¹ • j z) s R) s
    exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := s) hcircle (by
      simpa [abs_of_pos hR] using (ne_of_gt hR).symm)).const_smul
        (2 * Real.pi * Complex.I : ℂ)⁻¹).differentiableAt
  have he : g =ᶠ[𝓝 s] j :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds s hR) (fun w hw => heq hw)
  exact (hg.congr_of_eventuallyEq he.symm).differentiableWithinAt

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation
