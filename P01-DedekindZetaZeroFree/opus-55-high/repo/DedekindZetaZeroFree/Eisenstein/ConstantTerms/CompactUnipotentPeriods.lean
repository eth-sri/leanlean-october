module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactPeriod

open MeasureTheory
open KPGlobalEisensteinData
open scoped Topology ContDiff


section ChartSmoothness

variable {Q E : Type*} [TopologicalSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem compact_hasFDerivAt_integral {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure Q) [IsProbabilityMeasure μ]
    (f : E → Q → V) (f' : E → Q → E →L[ℝ] V)
    (hf : Continuous (Function.uncurry f)) (hf' : Continuous (Function.uncurry f'))
    (hd : ∀ g x, HasFDerivAt (fun g => f g x) (f' g x) g) (g : E) :
    HasFDerivAt (fun g => ∫ x, f g x ∂μ) (∫ x, f' g x ∂μ) g := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨B, hB⟩ := ((isCompact_closedBall g 1).prod (isCompact_univ : IsCompact (Set.univ : Set Q))).exists_bound_of_continuousOn hf'.continuousOn
  have hfm : ∀ a, AEStronglyMeasurable (f a) μ := by
    intro a
    exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
  have hf'm : AEStronglyMeasurable (f' g) μ :=
    (hf'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable_of_compactSpace
  have hfi : Integrable (f g) μ := by
    simpa [Function.uncurry, Function.comp_def] using
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact'
        isCompact_univ MeasurableSet.univ
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball g 1) (bound := fun _ => B) (Metric.ball_mem_nhds g zero_lt_one)
    (Filter.Eventually.of_forall hfm) hfi hf'm
  · exact Filter.Eventually.of_forall fun x a ha => hB (a, x)
      ⟨Metric.ball_subset_closedBall ha, Set.mem_univ x⟩
  · exact integrable_const B
  simp_all

set_option backward.isDefEq.respectTransparency false in

theorem compact_integral_smooth (μ : Measure Q) [IsProbabilityMeasure μ]
    (f : E → Q → ℂ)
    (hsmooth : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun g => f g x))
    (hjets : ∀ n : ℕ,
      Continuous (fun p : E × Q => iteratedFDeriv ℝ n (fun g => f g p.2) p.1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun g => ∫ x, f g x ∂μ) ∧
      ∀ n : ℕ, ∀ g : E,
        iteratedFDeriv ℝ n (fun g => ∫ x, f g x ∂μ) g =
          ∫ x, iteratedFDeriv ℝ n (fun g => f g x) g ∂μ := by
  let A (n : ℕ) (g : E) := ∫ x, iteratedFDeriv ℝ n (fun g => f g x) g ∂μ
  have hd (n : ℕ) (g : E) : HasFDerivAt (A n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ) (A (n + 1) g)) g := by
    let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    have hc : Continuous (fun p : E × Q =>
        fderiv ℝ (iteratedFDeriv ℝ n (fun g => f g p.2)) p.1) := by
      rw [show (fun p : E × Q => fderiv ℝ (iteratedFDeriv ℝ n (fun g => f g p.2)) p.1) =
        (fun p : E × Q => L (iteratedFDeriv ℝ (n + 1) (fun g => f g p.2) p.1)) from rfl]
      fun_prop
    have H := compact_hasFDerivAt_integral μ
      (fun g x => iteratedFDeriv ℝ n (fun g => f g x) g)
      (fun g x => fderiv ℝ (iteratedFDeriv ℝ n (fun g => f g x)) g)
      (hjets n) hc
      (fun g x => ((hsmooth x).differentiable_iteratedFDeriv (m := n)
        (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)) g).hasFDerivAt) g
    letI : TopologicalSpace (E [×(n + 1)]→L[ℝ] ℂ) :=
      (inferInstance : NormedAddCommGroup (E [×(n + 1)]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : TopologicalSpace (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
      (inferInstance : NormedAddCommGroup (E →L[ℝ] E [×n]→L[ℝ] ℂ)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let Lc : (E [×(n + 1)]→L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] E [×n]→L[ℝ] ℂ) :=
      { toLinearMap := L.toLinearEquiv.toLinearMap
        cont := by convert L.continuous using 1 }
    have hi : Integrable (fun x => iteratedFDeriv ℝ (n + 1) (fun g => f g x) g) μ := by
      have hc := (hjets (n + 1)).comp ((continuous_const (y := g)).prodMk (continuous_id (X := Q)))
      simpa [Function.comp_def] using hc.continuousOn.integrableOn_compact'
        isCompact_univ MeasurableSet.univ
    have Hcomm := @ContinuousLinearMap.integral_comp_comm Q (E [×(n + 1)]→L[ℝ] ℂ)
      (E →L[ℝ] E [×n]→L[ℝ] ℂ) _ μ ℝ _ _ _ _ _ _ _ _ _ Lc _ hi
    convert H using 1
    convert Hcomm.symm using 1
    rfl
  have heq : ∀ n : ℕ, iteratedFDeriv ℝ n (fun g => ∫ x, f g x ∂μ) = A n := by
    intro n
    induction n with
    | zero =>
      funext g
      simpa [A, iteratedFDeriv_zero_eq_comp, Function.comp_apply] using
        ((continuousMultilinearCurryFin0 ℝ E ℂ).symm.toContinuousLinearEquiv.integral_comp_comm (μ := μ) (f g)).symm
    | succ n ih =>
      funext g
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hd n g).fderiv]
      simp
  refine ⟨contDiff_of_differentiable_iteratedFDeriv (fun n _ => ?_), fun n g => congrFun (heq n) g⟩
  rw [heq n]
  exact fun g => (hd n g).differentiableAt
