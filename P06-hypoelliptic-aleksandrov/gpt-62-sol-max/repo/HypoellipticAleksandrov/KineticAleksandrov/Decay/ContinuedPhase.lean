module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhaseLocalization
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockParameters
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! # Source block phase errors after continuation and trimming -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open scoped ENNReal
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Changing the transported base point splits the phase coordinate additively. -/
private theorem phaseCoordinate_split {d : ℕ} (ξ z0 : PDE.Vec d)
    (x y : EvolutionAmbientState d) :
    phaseCoordinate ξ z0 x = phaseCoordinate ξ z0 y + phaseCoordinate ξ y.2 x := by
  unfold phaseCoordinate PDE.vecDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.sub_apply]
  ring

/-- Each continued corridor measure has phase in a strip of quarter width. -/
theorem continued_phase_error {d : ℕ} {lam Lam m Lb σ : ℝ} {D : Set (PDE.Vec d)}
    {B : CoefficientField d} {b : PDE.Vec d → PDE.Vec d}
    (hsetting : SourceSetting lam Lam m Lb D B b)
    {ξ v0 z0 : PDE.Vec d} (hξ : PDE.vecNormSq ξ = 1)
    {γ : ℝ → PDE.Vec d} (hγ : Continuous γ)
    {S : TerminalOperatorFamily (PDE.euclideanBall 0 (blockEta m Lb)) γ}
    {K : MovingFiberKernel (PDE.euclideanBall 0 (blockEta m Lb)) γ}
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 (blockEta m Lb)) γ
      (PDE.isOpen_euclideanBall 0 (blockEta m Lb)).measurableSet (zIndependentCoefficient B) b S K)
    {S0 : TerminalOperatorFamily (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary}
    {K0 : MovingFiberKernel (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary}
    (hreal0 : RealizesTerminalEvolution (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (PDE.isOpen_euclideanBall v0 (4 * blockRho Lb)).measurableSet (zIndependentCoefficient B) b S0 K0)
    {q : EvolutionQuery (PDE.euclideanBall 0 (blockEta m Lb)) γ}
    (hq : q.1 = (σ, σ + blockL0 m, v0, z0))
    {R : Measure (EvolutionState (PDE.euclideanBall v0 (4 * blockRho Lb)) stationary
      (σ + blockL0 m))} {c : ℝ≥0∞}
    (hR : R.map Subtype.val = c • K.master q)
    (hsT : σ + blockL0 m ≤ σ + blockTime m Lb) :
    ∀ᵐ x ∂continuedMeasure K0 hsT R, |phaseCoordinate ξ z0 x -
      (phaseCenter ξ b γ σ (σ + blockL0 m) +
        4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤ 1 / 4 := by
  have hm : 0 < m := hsetting.2.2.1
  have hLb : 0 < Lb := hm.trans_le hsetting.2.2.2.1
  have hρ := blockRho_pos hLb
  have hη := blockEta_pos hm hLb
  have hστ : σ ≤ σ + blockL0 m := le_add_of_nonneg_right (blockL0_pos hm).le
  have hsmall := add_le_add (Lb_mul_blockEta_mul_blockL0_le hm hLb)
    (sixteen_Lb_mul_blockRho_pow_three_le hLb)
  have hv : v0 ∈ movingDomain (PDE.euclideanBall 0 (blockEta m Lb)) γ σ := by
    have h := q.2.2.1
    simpa only [hq] using h
  have hq' : q = movingQuery σ (σ + blockL0 m) hστ v0 z0 hv := Subtype.ext hq
  have hphase := phase_localization_of_center_curve lam Lam m Lb D B b hsetting
    σ (σ + blockL0 m) (blockEta m Lb) 0 γ γ hη hγ (fun _ => (add_zero _).symm)
    S K hreal ξ z0 v0 hξ hστ hv
  rw [← hq'] at hphase
  have hRphase : ∀ᵐ p ∂R, |phaseCoordinate ξ z0 p.1 -
      phaseCenter ξ b γ σ (σ + blockL0 m)| ≤ Lb * blockEta m Lb * blockL0 m := by
    have h := Measure.ae_smul_measure hphase c
    rw [← hR] at h
    have h' := ae_of_ae_map measurable_subtype_coe.aemeasurable h
    simpa only [add_sub_cancel_left] using h'
  have hKphase : ∀ᵐ p ∂R, ∀ᵐ x ∂continuationKernel K0 hsT p,
      |phaseCoordinate ξ p.1.2 x -
        (4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0))| ≤
          16 * Lb * blockRho Lb ^ 3 := by
    apply Filter.Eventually.of_forall
    intro p
    have hp := phase_localization_of_center_curve lam Lam m Lb D B b hsetting
      (σ + blockL0 m) (σ + blockTime m Lb) (4 * blockRho Lb) v0 stationary (fun _ => v0)
      (mul_pos (by norm_num) hρ) continuous_const (fun _ => (zero_add _).symm)
      S0 K0 hreal0 ξ p.1.2 p.1.1 hξ hsT p.2.1
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
  let A := phaseCenter ξ b γ σ (σ + blockL0 m)
  let C := 4 * blockRho Lb ^ 2 * PDE.vecDot ξ (b v0)
  have hc : Continuous (fun x : EvolutionAmbientState d => |phaseCoordinate ξ z0 x - (A + C)|) := by
    unfold phaseCoordinate PDE.vecDot
    fun_prop
  apply Measure.ae_comp_of_ae_ae ((isClosed_le hc continuous_const).measurableSet)
  filter_upwards [hRphase, hKphase] with p hp hk
  filter_upwards [hk] with x hx
  have he : phaseCoordinate ξ z0 x - (A + C) =
      (phaseCoordinate ξ z0 p.1 - A) + (phaseCoordinate ξ p.1.2 x - C) := by
    rw [phaseCoordinate_split ξ z0 x p.1]
    ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add hp hx).trans (by linarith only [hsmall]))

end HypoellipticAleksandrov.KineticAleksandrov.Decay
