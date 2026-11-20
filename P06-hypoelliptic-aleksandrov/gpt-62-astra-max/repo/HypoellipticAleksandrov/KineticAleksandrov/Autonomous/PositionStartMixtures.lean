module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

/-! # Finite terminal kernels for the position-start identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

section
variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (b : ℝ)

include hlam hLam A c J b in
/-- The existing terminal family as a measurable kernel, including zero-duration starts. -/
def positionStartTerminalKernel :
    Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily hlam hLam A c J b,
    positionStartTerminalFamily_measurable hlam hLam A c J b⟩

/-- Every actual active terminal family has mass at most one. -/
theorem positionStartTerminalKernel_mass_le_one (p : Point) :
    positionStartTerminalKernel hlam hLam A c J b p univ ≤ 1 := by
  change (enlargedActiveTerminalFamily hlam hLam A c J b p) univ ≤ 1
  unfold enlargedActiveTerminalFamily
  split
  · simp only [Measure.dirac_apply_of_mem (mem_univ p), le_refl]
  · apply (Measure.restrict_le_self univ).trans
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _
      else (0 : Measure Point)) univ ≤ 1
    split
    · simp
    positivity

end

/-- The terminal kernel is uniformly finite without a domination hypothesis. -/
instance positionStartTerminalKernel_isFiniteKernel
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (positionStartTerminalKernel hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    positionStartTerminalKernel_mass_le_one hlam hLam A c J b⟩

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (b : ℝ) (mu : Measure Point)

/-- Terminal mixtures retain the closed active velocity support. -/
theorem positionStartTerminalMixture_ae_closedActive :
    ∀ᵐ q ∂(positionStartTerminalKernel hlam hLam A c J b ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂enlargedActiveTerminalFamily hlam hLam A c J b p,
    q.velocity 0 ∈ closure c.active
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
    exact subset_closure ((visitActiveUnion_carrier c J).le hp.2).1
  · have hs := enlargedActiveExitMixture_ae_velocity
      hlam hLam A c J b (Measure.dirac p)
    rw [visitKernel_comp_dirac] at hs
    exact hs.filter_mono (ae_mono Measure.restrict_le_self)

/-- Finite all-time active mixtures retain open active support. -/
theorem positionStartAllTimeMixture_ae_active :
    ∀ᵐ q ∂(coreAllTimeGreenKernel hlam hLam A c ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p.velocity 0 ∈ c.active then
    stripGreen hlam hLam A (visitActiveInterval c) ⊤
      (coreAllTimePole c ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · exact (stripGreen_infinite_ae_future_carrier hlam hLam A
      (visitActiveInterval c) _).mono fun _ hq => hq.2
  simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
