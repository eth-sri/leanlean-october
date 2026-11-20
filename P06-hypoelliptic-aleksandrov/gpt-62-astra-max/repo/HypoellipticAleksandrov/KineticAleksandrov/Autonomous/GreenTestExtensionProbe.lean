module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCalculus

/-! # Compact probe realization of a position-cutoff test on the entire future closed slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Filter Metric
open SectionTwo TheoremA Evolution
open scoped Topology

/-- An arbitrary smooth physical test becomes a compact probe, with no cutoff error
in time or velocity on the specified future closed slab. -/
theorem exists_reconstruction_position_probe {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (a T : ℝ)
    (phi : Point → ℝ)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) (phi ∘ reconstructionPhysicalHomeomorph))
    (bx : ContDiffBump (0 : ℝ)) :
    ∃ F : exitProbeSubmodule,
      (∀ p, a ≤ p.time → p.time ≤ T → p.velocity 0 ∈ Icc H.lo H.hi →
        exitProbePhysical F p = bx (p.position 0) * phi p) ∧
      ∀ p, a ≤ p.time → p.time ≤ T → p.velocity 0 ∈ Icc H.lo H.hi →
        forwardScalarOperator A.a (exitProbePhysical F) p =
          bx (p.position 0) * forwardScalarOperator A.a phi p +
            p.velocity 0 * deriv bx (p.position 0) * phi p := by
  let Rt := max |a| |T| + 1
  let Rv := max |H.lo| |H.hi| + 1
  have hRt : 0 < Rt := by positivity
  have hRv : 0 < Rv := by positivity
  let bt := reconstructionPositionBump Rt hRt
  let bv := reconstructionPositionBump Rv hRv
  let f := phi ∘ reconstructionPhysicalHomeomorph
  let g := fun x =>
    bt (timeCoord 1 x) * bv (diffusedCoord 1 x 0) * bx (transportedCoord 1 x 0) * f x
  have hg :=
    ((bt.contDiff.comp (timeCoord 1).contDiff).mul
      (bv.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp
        (diffusedCoord 1).contDiff))).mul
      (bx.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp
        (transportedCoord 1).contDiff)) |>.mul hphi
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
  refine ⟨⟨g, hg, reconstruction_product_cutoff_compact bt bv bx f⟩, ?_, ?_⟩
  · intro p ha hT hv
    change g (reconstructionPhysicalHomeomorph.symm p) = _
    rw [((hloc p ha hT hv).eq_of_nhds)]
    simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  · intro p ha hT hv
    rw [exitProbePhysical_operator]
    rw [reconstruction_transportedOperator_congr _ _ (hloc p ha hT hv),
      reconstruction_position_cutoff_operator _ _ bx bx.contDiff f hphi]
    rw [← reconstruction_physical_operator_packed A phi hphi p]
    simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply, identityDrift]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
