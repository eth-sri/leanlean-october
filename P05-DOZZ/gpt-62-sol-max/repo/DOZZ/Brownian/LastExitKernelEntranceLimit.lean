/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceDensityLimit
public import DOZZ.Brownian.LastExitReferenceKernel

/-!
# Finite projections of the Brownian reference kernel

At positive rational offsets, the explicit Brownian reference future kernel has the finite Doob
density. This identifies the kernel probabilities in the last-exit cell formula with the
measurable entrance-density limit proved separately.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Finite rational projections of the Brownian reference future kernel converge on every
measurable event to the conditioned entrance finite-dimensional law as the start decreases to
zero. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection_tendsto_entrance
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (Q : Measure BrownianPath) (ν : ℝ) (hν : 0 < ν)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun k => (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).map
        (fun y i => y (offsets i)) A)
      atTop
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i))))) A)) := by
  let ts  := fun i => Real.toNNReal (offsets i)
  let ds  := brownianFirstHitElapsed n ts
  have hds := brownianFirstHitElapsed_positiveOffsets hoff hmono
  have hlimit := brownianDoobFinitePDF_measure_tendsto_entrance_event
    B Q hB ν hν hQ n ds hds xs hxs hxlim A hA
  have heq (k : ℕ) := brownianUpperConditionedReferenceFutureKernel_finite_projection_doob
      B hB ν (xs k) hν (hxs k) n offsets hoff hmono
  have hfun : (fun k =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).map
        (fun y i => y (offsets i)) A) =
      fun k => (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A := by
    funext k
    rw [heq k]
  grind

end DOZZ.Proofs

end
