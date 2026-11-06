/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! Almost-sure empirical approximation under a common spatial sampling law. -/
public section
open MeasureTheory ProbabilityTheory Filter Topology
namespace DOZZ.Proofs

theorem ae_empirical_average_tendsto
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hint : ∀ᵐ ω ∂P, Integrable (f ω) ν) :
    ∀ᵐ ω ∂P, ∀ᵐ q ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
  let Q  := Measure.infinitePi (fun _ : ℕ => ν)
  
  have hEvalIdent (i : ℕ) : IdentDistrib (fun q : ℕ → S => q i) id Q ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [Q] using (Measure.infinitePi_map_eval (fun _ : ℕ => ν) i)
  have hCoordIdent (i : ℕ) :
      IdentDistrib (fun q : ℕ → S => q i) (fun q => q 0) Q Q :=
    (hEvalIdent i).trans (hEvalIdent 0).symm
  have hindepCoord : iIndepFun (fun i (q : ℕ → S) => q i) Q := id (iIndepFun_infinitePi fun i => measurable_id')
  have hInner (ω : Ω) (hω : Integrable (f ω) ν) :
      ∀ᵐ q ∂Q,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
          atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    have hfmeas  :=
      hjoint.comp (by fun_prop : Measurable fun x : S => (ω, x))
    have hindep := hindepCoord.comp (fun _ => f ω) (fun _ => hfmeas)
    have hindep' : Pairwise (fun i j =>
        (fun q => f ω (q i)) ⟂ᵢ[Q] (fun q => f ω (q j))) := by
      intro i j hij
      exact hindep.indepFun hij
    have hident : ∀ i, IdentDistrib (fun q => f ω (q i))
        (fun q => f ω (q 0)) Q Q := by
      intro i
      exact (hCoordIdent i).comp hfmeas
    have hsampleIdent : IdentDistrib (fun q => f ω (q 0)) (f ω) Q ν :=
      (hEvalIdent 0).comp hfmeas
    have hsampleInt : Integrable (fun q => f ω (q 0)) Q :=
      hsampleIdent.integrable_iff.mpr hω
    have hmean  :=
      hsampleIdent.integral_eq
    have hlln := ProbabilityTheory.strong_law_ae (μ := Q)
      (fun i (q : ℕ → S) => f ω (q i)) hsampleInt hindep' hident
    filter_upwards [hlln] with q hq
    simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hmean] using hq
  have hIter : ∀ᵐ ω ∂P, ∀ᵐ q ∂Q,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    filter_upwards [hint] with ω hω
    exact hInner ω hω
  exact hIter


end DOZZ.Proofs
