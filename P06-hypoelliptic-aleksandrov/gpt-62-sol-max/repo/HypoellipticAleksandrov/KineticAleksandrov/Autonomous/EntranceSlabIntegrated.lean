module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabKernel

import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # Integrated quadratic counting for starts in a closed-right time slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval)
include lam Lam A

/-- A lower time bound makes the clipped active occupation of any finite start measure finite. -/
theorem entranceSlabGreen_isFiniteMeasure (a b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] (ha : ∀ᵐ p ∂mu, a ≤ p.time) :
    IsFiniteMeasure
      (enlargedVisitGreenKernel A (visitActiveUnion c J) b ∘ₘ mu) := by
  rw [enlargedVisitGreen_comp_eq_clipped A (visitActiveUnion c J) a b mu ha]
  infer_instance

/-- Finite mixtures of starts up to `b` obey the exact actual terminal/occupation identity. -/
theorem entranceSlabQuadratic_integrated_identity (a b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧
      p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    (∫ p, visitQuadratic c (p.velocity 0) ∂mu) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂mu.bind (enlargedActiveTerminalFamily A c J b)) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂(enlargedVisitGreenKernel A (visitActiveUnion c J) b ∘ₘ mu) := by
  have := entranceSlabGreen_isFiniteMeasure A c J a b mu (hmu.mono fun _ hp => hp.1)
  refine integral_eq_comp_add (K := entranceSlabTerminalKernel A c J b)
    (entranceSlabTerminal_quadratic_integrable A c J b mu) (visitCoefficient_integrable A _) ?_
  filter_upwards [hmu] with p hp
  exact entranceSlabQuadratic_closed_point_identity A c J b hJ p hp.2.1 hp.2.2

/-- The exact source quadratic bounds starts by their actual terminal and clipped occupation. -/
theorem entranceSlabQuadratic_mass_bound (a b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 *
        (mu.bind (enlargedActiveTerminalFamily A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal +
      2 * Lam *
        ((enlargedVisitGreenKernel A (visitActiveUnion c J) b ∘ₘ mu)
          univ).toReal := by
  have : IsFiniteMeasure
      (enlargedVisitGreenKernel A (visitActiveUnion c J) b ∘ₘ mu) :=
    entranceSlabGreen_isFiniteMeasure A c J a b mu
      (hmu.mono fun _ hp => hp.1)
  have hi := entranceSlabQuadratic_integrated_identity A c J a b hJ mu
    (hmu.mono fun _ hp => ⟨hp.1, hp.2.1, by
      rw [visitActiveUnion_carrier]
      have hv := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hp.2.2
      exact ⟨hv, hJ (subset_closure hv)⟩⟩)
  have hm := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.visitQuadratic_integral_lower_of_entrance_support c mu (hmu.mono fun _ hp => hp.2.2)
  rw [hi] at hm
  have ht' := entranceSlabQuadratic_integral_le_active c
    (mu.bind (enlargedActiveTerminalFamily A c J b))
    (entranceSlabTerminal_quadratic_integrable A c J b mu)
  exact hm.trans (add_le_add ht' (visitCoefficient_integral_le A _))

/-- Finite canonical slab counts satisfy the source quadratic estimate without a past-mass term. -/
theorem entranceSlabQuadratic_partial_mass_bound (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (a b : ℝ) (N : ℕ) :
    let mu := fun n => (enlargedVisitEntrance A c J s T P n).restrict
      {p | p.time ∈ Ioc a b}
    5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
      9 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N,
        ((mu n).bind (enlargedActiveTerminalFamily A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal) +
      2 * Lam * (∑ n ∈ Finset.range N,
        ((enlargedVisitGreenKernel A (visitActiveUnion c J) b ∘ₘ mu n)
          univ).toReal) := by
  dsimp only
  let mu := fun n => (enlargedVisitEntrance A c J s T P n).restrict
    {p | p.time ∈ Ioc a b}
  have hm (n : ℕ) : ∀ᵐ p ∂mu n,
      a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance := by
    have hv : ∀ᵐ p ∂mu n, p.velocity 0 ∈ closure c.entrance :=
      ((enlargedVisitEntrance_ae_support
      A c J s T P hs hT n).mono fun _ hp => hp.2.2).filter_mono
        (ae_mono Measure.restrict_le_self)
    have ht : ∀ᵐ p ∂mu n, p.time ∈ Ioc a b :=
      ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)
    filter_upwards [ht, hv] with p hp hvel
    exact ⟨hp.1.le, hp.2, hvel⟩
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ =>
    entranceSlabQuadratic_mass_bound A c J a b hJ (mu n) (hm n))
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
