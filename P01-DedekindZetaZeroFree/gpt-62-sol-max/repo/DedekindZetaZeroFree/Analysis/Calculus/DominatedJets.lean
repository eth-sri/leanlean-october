module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace DedekindZetaZeroFree

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem integral_contDiffOn_of_locally_dominated_jets
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (F : E → X → ℂ) (S : Set E) (hS : IsOpen S)
    (hsmooth : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (fun u => F u x) S)
    (hmeas : ∀ n : ℕ, ∀ u ∈ S,
      AEStronglyMeasurable (fun x => iteratedFDerivWithin ℝ n (fun v => F v x) S u) μ)
    (hbound : ∀ n : ℕ, ∀ u ∈ S, ∃ (s : Set E) (b : X → ℝ),
      s ∈ nhds u ∧ s ⊆ S ∧ Integrable b μ ∧
        ∀ᵐ x ∂μ, ∀ v ∈ s, ‖iteratedFDerivWithin ℝ n (fun w => F w x) S v‖ ≤ b x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u => ∫ x, F u x ∂μ) S ∧
      ∀ n : ℕ, ∀ u ∈ S,
        iteratedFDerivWithin ℝ n (fun v => ∫ x, F v x ∂μ) S u =
          ∫ x, iteratedFDerivWithin ℝ n (fun v => F v x) S u ∂μ := by
  have hint (n : ℕ) (u : E) (hu : u ∈ S) :
      Integrable (fun x => iteratedFDerivWithin ℝ n (fun v => F v x) S u) μ := by
    obtain ⟨s, b, hs, _, hb, h⟩ := hbound n u hu
    exact hb.mono' (hmeas n u hu) (h.mono fun x hx => hx u (mem_of_mem_nhds hs))
  let A (n : ℕ) (u : E) := ∫ x, iteratedFDerivWithin ℝ n (fun v => F v x) S u ∂μ
  have hd (n : ℕ) (u : E) (hu : u ∈ S) : HasFDerivAt (A n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ) (A (n + 1) u)) u := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    obtain ⟨s, b, hs, hsS, hb, h⟩ := hbound (n + 1) u hu
    have hf'm : AEStronglyMeasurable (fun x =>
        fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun v => F v x) S) S u) μ := by
      exact L.continuous.comp_aestronglyMeasurable (hmeas (n + 1) u hu)
    have hh := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (F := fun v x => iteratedFDerivWithin ℝ n (fun w => F w x) S v)
      (F' := fun v x => fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun w => F w x) S) S v)
      hs (Filter.eventually_of_mem (hS.mem_nhds hu) (fun v hv => hmeas n v hv)) (hint n u hu) hf'm
      (h.mono fun x hx v hv => by
        change ‖L (iteratedFDerivWithin ℝ (n + 1) (fun w => F w x) S v)‖ ≤ b x
        rw [L.norm_map]
        exact hx v hv) hb
      (Eventually.of_forall fun x v hv =>
        (((hsmooth x).differentiableOn_iteratedFDerivWithin (m := n)
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) hS.uniqueDiffOn v (hsS hv)).hasFDerivWithinAt
          |>.hasFDerivAt (hS.mem_nhds (hsS hv))))
    have heq : (∫ x, fderivWithin ℝ (iteratedFDerivWithin ℝ n (fun v => F v x) S) S u ∂μ) =
        L (A (n + 1) u) := by
      letI : TopologicalSpace (E [×(n + 1)]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E [×(n + 1)]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        (inferInstance : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      let Lc : (E [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
        { toLinearMap := L.toLinearEquiv.toLinearMap
          cont := by convert L.continuous using 1 }
      exact @ContinuousLinearMap.integral_comp_comm X (E [×(n + 1)]→L[ℝ] ℂ)
        (E →L[ℝ] E [×n]→L[ℝ] ℂ) _ μ ℝ _ _ _ _ _ _ _ _ _ Lc _ (hint (n + 1) u hu)
    rw [heq] at hh
    exact hh
  have heq (n : ℕ) : Set.EqOn (iteratedFDerivWithin ℝ n (fun u => ∫ x, F u x ∂μ) S) (A n) S := by
    induction n with
    | zero =>
      intro u hu
      simpa [A, iteratedFDerivWithin_zero_eq_comp, Function.comp_apply] using
        ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (μ := μ) (F u)).symm
    | succ n ih =>
      intro u hu
      rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply,
        fderivWithin_congr ih (ih hu), (hd n u hu).hasFDerivWithinAt.fderivWithin (hS.uniqueDiffOn u hu)]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ).symm_apply_apply _
  refine ⟨?_, fun n u hu => heq n hu⟩
  apply (contDiffOn_iff_continuousOn_differentiableOn hS.uniqueDiffOn).mpr
  constructor
  · intro n hn
    have hA : ContinuousOn (A n) S := fun u hu => (hd n u hu).continuousAt.continuousWithinAt
    exact hA.congr (heq n)
  · intro n hn
    have hA : DifferentiableOn ℝ (A n) S := fun u hu => (hd n u hu).differentiableAt.differentiableWithinAt
    exact hA.congr (heq n)

end DedekindZetaZeroFree

end
