module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureFuture
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsScaling
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Compact probe realization of a position-cutoff test on the entire future closed slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Filter Metric
open SectionTwo TheoremA Evolution
open scoped Topology
open MeasureTheory

/- An arbitrary smooth physical test becomes a compact probe, with no cutoff error
in time or velocity on the specified future closed slab. -/
theorem exists_reconstruction_position_probe {lam Lam }
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
  have hRt : 0 < Rt := by dsimp [Rt]; positivity
  have hRv : 0 < Rv := by dsimp [Rv]; positivity
  let bt := reconstructionPositionBump Rt hRt
  let bv := reconstructionPositionBump Rv hRv
  let f := phi ∘ reconstructionPhysicalHomeomorph
  let g : EvolutionVec 1 → ℝ := fun x =>
    bt (timeCoord 1 x) * bv (diffusedCoord 1 x 0) * bx (transportedCoord 1 x 0) * f x
  have hg :=
    ((bt.contDiff.comp (timeCoord 1).contDiff).mul
      (bv.contDiff.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp
        (diffusedCoord 1).contDiff))).mul
      (bx.contDiff.comp ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp
        (transportedCoord 1).contDiff)) |>.mul hphi
  have _h_xinl_0 : HasCompactSupport (fun x => bt (timeCoord 1 x) * bv (diffusedCoord 1 x 0) * bx (transportedCoord 1 x 0) * f x) := by
    let R := max bt.rOut (max bv.rOut bx.rOut)
    have hR : 0 ≤ R := bt.rOut_pos.le.trans (le_max_left _ _)
    apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EvolutionVec 1) R)
      (isClosed_tsupport _)
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    have hn : bt (timeCoord 1 x) ≠ 0 ∧ bv (diffusedCoord 1 x 0) ≠ 0 ∧
        bx (transportedCoord 1 x 0) ≠ 0 := by
      have hh := mul_ne_zero_iff.mp hx
      have hh' := mul_ne_zero_iff.mp hh.1
      exact ⟨(mul_ne_zero_iff.mp hh'.1).1, (mul_ne_zero_iff.mp hh'.1).2, hh'.2⟩
    have ht : |timeCoord 1 x| < bt.rOut := by
      have hh : timeCoord 1 x ∈ Function.support bt := hn.1
      rw [bt.support_eq] at hh
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
    have hv : |diffusedCoord 1 x 0| < bv.rOut := by
      have hh : diffusedCoord 1 x 0 ∈ Function.support bv := hn.2.1
      rw [bv.support_eq] at hh
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
    have hz : |transportedCoord 1 x 0| < bx.rOut := by
      have hh : transportedCoord 1 x 0 ∈ Function.support bx := hn.2.2
      rw [bx.support_eq] at hh
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hh
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    fin_cases i
    · exact ht.le.trans (le_max_left _ _)
    · exact hv.le.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact hz.le.trans ((le_max_right _ _).trans (le_max_right _ _))
  let F : exitProbeSubmodule := ⟨g, hg, _h_xinl_0⟩
  have hloc (p : Point) (ha : a ≤ p.time) (hT : p.time ≤ T)
      (hv : p.velocity 0 ∈ Icc H.lo H.hi) :
      g =ᶠ[𝓝 (reconstructionPhysicalHomeomorph.symm p)]
        (fun x => bx (transportedCoord 1 x 0) * f x) := by
    have ht : |p.time| < Rt := by
      have hh : |p.time| ≤ max |a| |T| := abs_le.mpr
        ⟨(neg_abs_le a).trans ha |>.trans' (neg_le_neg (le_max_left _ _)),
          hT.trans ((le_abs_self T).trans (le_max_right _ _))⟩
      dsimp only [Rt]
      linarith
    have hv' : |p.velocity 0| < Rv := by
      have hh : |p.velocity 0| ≤ max |H.lo| |H.hi| := abs_le.mpr
        ⟨(neg_abs_le H.lo).trans hv.1 |>.trans' (neg_le_neg (le_max_left _ _)),
          hv.2.trans ((le_abs_self H.hi).trans (le_max_right _ _))⟩
      dsimp only [Rv]
      linarith
    have ht1 := bt.eventuallyEq_one_of_mem_ball
      (show timeCoord 1 (reconstructionPhysicalHomeomorph.symm p) ∈ ball 0 bt.rIn by
        rw [mem_ball, Real.dist_eq, sub_zero]
        change |p.time| < Rt
        exact ht)
    have hv1 := bv.eventuallyEq_one_of_mem_ball
      (show diffusedCoord 1 (reconstructionPhysicalHomeomorph.symm p) 0 ∈ ball 0 bv.rIn by
        rw [mem_ball, Real.dist_eq, sub_zero]
        change |p.velocity 0| < Rv
        exact hv')
    have htt := ht1.comp_tendsto (timeCoord 1).continuous.continuousAt
    have hvv := hv1.comp_tendsto
      (((continuous_apply 0).comp (diffusedCoord 1).continuous).continuousAt)
    filter_upwards [htt, hvv] with x hx hy
    simp only [Function.comp_apply, Pi.one_apply] at hx hy
    dsimp only [g]
    rw [hx, hy]
    simp only [one_mul]
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
    have _h_xinl_0 : forwardScalarOperator A.a phi p =
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
    rw [← _h_xinl_0]
    simp only [f, Function.comp_apply, Homeomorph.apply_symm_apply, identityDrift]
    rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
