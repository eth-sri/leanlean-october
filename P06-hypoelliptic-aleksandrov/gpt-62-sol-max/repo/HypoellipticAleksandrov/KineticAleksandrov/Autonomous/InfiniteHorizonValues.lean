module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonProbes
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctional
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear

/-! # Actual infinite Green probe values and their positive contraction bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
include lam Lam A H e

/-- The infinite Green measure determines the actual exit value of each ambient probe. -/
def infiniteExitProbeValue
    (f : exitProbeSubmodule) : ℝ :=
  exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
    ∂stripGreen A H ⊤ e

/-- Actual infinite Green probe values are a linear functional. -/
def infiniteExitProbeValueLinear :
    exitProbeSubmodule →ₗ[ℝ] ℝ where
  toFun := infiniteExitProbeValue A H e
  map_add' f g := by
    unfold infiniteExitProbeValue
    rw [_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.probe_operator_add]
    have hf : Integrable (forwardScalarOperator A.a (exitProbePhysical f))
        (stripGreen A H ⊤ e) :=
      stripGreen_integrable A H ⊤ e (exitProbeOperatorDatum A f)
    have hg : Integrable (forwardScalarOperator A.a (exitProbePhysical g))
        (stripGreen A H ⊤ e) :=
      stripGreen_integrable A H ⊤ e (exitProbeOperatorDatum A g)
    rw [integral_add hf hg]
    change exitProbePhysical f e.1 + exitProbePhysical g e.1 + _ = _
    ring
  map_smul' c f := by
    unfold infiniteExitProbeValue
    rw [_root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.probe_operator_smul, integral_const_mul]
    change c * exitProbePhysical f e.1 + _ = c * _
    ring

end

/-- Every compact ambient probe vanishes beyond some horizon later than the pole. -/
theorem infinite_probe_later_horizon (e : Point) (f : exitProbeSubmodule) :
    ∃ T : ℝ, e.time < T ∧ tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T} := by
  obtain ⟨M, hM⟩ := f.2.2.isCompact.bddAbove_image (Evolution.timeCoord 1).continuous.continuousOn
  refine ⟨max M e.time + 1, by linarith [le_max_right M e.time], ?_⟩
  intro x hx
  have hh : Evolution.timeCoord 1 x ≤ M := hM ⟨x, hx, rfl⟩
  exact lt_of_le_of_lt hh (by linarith [le_max_left M e.time])

/-- The infinite probe value is exactly the finite value at any later supporting horizon. -/
theorem infiniteExitProbeValue_eq_finite
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) (T : ℝ) (ht : e.1.time < T)
    (hs : tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T}) :
    infiniteExitProbeValueLinear A H e f =
      exitProbeValueLinear A H (stripEvolution A H) T
        (stripPoleFinite H e T ht) f := by
  exact congrArg (fun z => exitProbePhysical f e.1 + z)
    (infinite_probe_source_integral A H e T ht T le_rfl f hs).symm

/-- A compact early probe is zero on its later terminal plane. -/
theorem infinite_probe_zero_terminal (f : exitProbeSubmodule) (T : ℝ)
    (hs : tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T}) (p : Point) (ht : p.time = T) :
    exitProbePhysical f p = 0 := by
  change f.1 (reconstructionPhysicalHomeomorph.symm p) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hp := hs hx
  exact (ne_of_lt hp) ht

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
  (f : exitProbeSubmodule)

/-- Face bounds control the actual infinite Green probe value by contraction one. -/
theorem infiniteExitProbeValueLinear_bound (c : ℝ) (hc : 0 ≤ c)
    (hbd : ∀ p, |infiniteExitProbeCcLinear H f p| ≤ c) :
    |infiniteExitProbeValueLinear A H e f| ≤ c := by
  obtain ⟨T, ht, hs⟩ := infinite_probe_later_horizon e.1 f
  rw [infiniteExitProbeValue_eq_finite A H e f T ht hs]
  apply exitProbeValueLinear_bound A H _
    (stripEvolution_spec A H) T _ f c hc
  intro p
  rcases p.2 with hp | hp
  · change |exitProbePhysical f p.1| ≤ c
    rw [infinite_probe_zero_terminal f T hs p.1 hp.1, abs_zero]
    exact hc
  · exact hbd ⟨p.1, hp.2⟩

/-- Nonnegative compact face data have nonnegative actual infinite Green probe values. -/
theorem infiniteExitProbeValueLinear_nonneg (hbd : ∀ p, 0 ≤ infiniteExitProbeCcLinear H f p) :
    0 ≤ infiniteExitProbeValueLinear A H e f := by
  obtain ⟨T, ht, hs⟩ := infinite_probe_later_horizon e.1 f
  rw [infiniteExitProbeValue_eq_finite A H e f T ht hs]
  apply exitProbeValueLinear_nonneg A H _
    (stripEvolution_spec A H) T _ f
  intro p
  rcases p.2 with hp | hp
  · exact le_of_eq (infinite_probe_zero_terminal f T hs p.1 hp.1).symm
  · exact hbd ⟨p.1, hp.2⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
