module

import Mathlib.Topology.TietzeExtension
import HypoellipticAleksandrov.Analysis.SmoothCutoff

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.SmoothProbeDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasureGeneral
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Ambient smooth compact probes determine Borel measure families -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set Topology
open scoped CompactlySupported

/-- A compactly supported continuous scalar probe regarded as bounded Borel data. -/
def compactProbeDatum {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : C_c(X, ℝ)) : BoundedBorel X :=
  ⟨f, f.continuous.measurable, ⟨‖f.toBoundedContinuousFunction‖, norm_nonneg _, fun x => by
    simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply,
      Real.norm_eq_abs] using f.toBoundedContinuousFunction.norm_coe_le_norm x⟩⟩

/-- Ambient smooth compact probes are uniformly dense in continuous compact probes. -/
theorem exists_smooth_compact_probe_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : C_c(E, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C_c(E, ℝ), ContDiff ℝ (⊤ : ℕ∞) g ∧ ∀ x, |g x - f x| ≤ ε := by
  let fu : C_c((univ : Set E), ℝ) := f.comp (Homeomorph.Set.univ E).toCocompactMap
  obtain ⟨φ, hφ, hc, _, hclose⟩ := exists_smooth_compactSupport_close isOpen_univ fu ε hε
  let g : C_c(E, ℝ) := ⟨⟨φ, hφ.continuous⟩, hc⟩
  exact ⟨g, hφ, fun x => hclose ⟨x, mem_univ _⟩⟩

/-- Smooth compact ambient restrictions are uniformly dense on a closed embedded carrier. -/
theorem exists_smooth_compact_probe_close_embedding
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {j : X → E} (hj : IsClosedEmbedding j) (g : C_c(X, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : C_c(E, ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ x, |f (j x) - g x| ≤ ε := by
  obtain ⟨G, -, hG⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    g.toBoundedContinuousFunction hj
  obtain ⟨χ, hχ, hc, -, -, hone⟩ := HypoellipticAleksandrov.Analysis.exists_smooth_cutoff
    (g.hasCompactSupport.isCompact.image hj.continuous) isOpen_univ (subset_univ _)
  let F : C_c(E, ℝ) := ⟨⟨fun x => χ x * G x, hχ.continuous.mul G.continuous⟩, hc.mul_right⟩
  have hFg (x : X) : F (j x) = g x := by
    change χ (j x) * G (j x) = g x
    have hh : G (j x) = g x := congrFun hG x
    rw [hh]
    by_cases hx : g x = 0
    · rw [hx, mul_zero]
    · rw [hone _ ⟨x, subset_tsupport _ hx, rfl⟩, one_mul]
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close F ε hε
  exact ⟨f, hf, fun x => by simpa only [hFg x] using hclose (j x)⟩

/-- A subprobability measure family is Borel when all ambient smooth compact probe
integrals are Borel. This uses the dense-probe and measure measurability APIs. -/
theorem measurable_measure_family_of_smooth_tests
    {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace α]
    (ν : α → Measure E) [∀ a, IsFiniteMeasure (ν a)] (hmass : ∀ a, ν a univ ≤ 1)
    (H : ∀ f : C_c(E, ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      Measurable (fun a => ∫ x, f x ∂ν a)) : Measurable ν := by
  let P := {f : C_c(E, ℝ) // ContDiff ℝ (⊤ : ℕ∞) f}
  apply measurable_of_integral_measurable ν
  apply measurable_integral_of_dense (T := fun f : P => f.1) ν hmass
  · intro f ε hε
    obtain ⟨g, hg, hclose⟩ := exists_smooth_compact_probe_close f ε hε
    exact ⟨⟨g, hg⟩, hclose⟩
  · intro f
    exact H f.1 f.2

end HypoellipticAleksandrov.KineticAleksandrov
