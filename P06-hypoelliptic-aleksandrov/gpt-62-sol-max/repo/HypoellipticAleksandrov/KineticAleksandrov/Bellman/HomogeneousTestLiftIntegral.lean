module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Differentiating an integral with a compact parameter carrier -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology Metric
namespace HypoellipticAleksandrov.KineticAleksandrov

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Precompose a joint derivative with the spatial inclusion. -/
abbrev bellmanRestrictSpatial : ((E × ℝ) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip ((ContinuousLinearMap.id ℝ E).prod 0)

/-- The derivative in the spatial variables, leaving the radius fixed. -/
def bellmanSpatialJet (f : E × ℝ → F) (q : E × ℝ) : E →L[ℝ] F :=
  bellmanRestrictSpatial (fderiv ℝ f q)

@[simp] theorem bellmanSpatialJet_apply (f : E × ℝ → F) (q : E × ℝ) (e : E) :
    bellmanSpatialJet f q e = fderiv ℝ f q (e, 0) := by
  simp [bellmanSpatialJet, bellmanRestrictSpatial]

/-- Restrict a joint derivative to a slice at fixed radius. -/
theorem hasFDerivAt_bellmanSpatialJet {f : E × ℝ → F} {q : E} {r : ℝ}
    (hf : DifferentiableAt ℝ f (q, r)) :
    HasFDerivAt (fun x => f (x, r)) (bellmanSpatialJet f (q, r)) q := by
  have h : HasFDerivAt (fun x : E => (x, r)) ((ContinuousLinearMap.id ℝ E).prod 0) q :=
    (hasFDerivAt_id q).prodMk (hasFDerivAt_const r q)
  exact hf.hasFDerivAt.comp q h

/-- Restricting to spatial directions preserves regularity of the derivative. -/
theorem contDiffOn_bellmanSpatialJet {f : E × ℝ → F} {U : Set (E × ℝ)}
    {m n : WithTop ℕ∞} (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (bellmanSpatialJet f) U :=
  (bellmanRestrictSpatial (E := E) (F := F)).contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hU hm)

end

variable {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  [SecondCountableTopology A]

omit [NormedSpace ℝ E] [ProperSpace E] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology A] in
/-- A jointly continuous function has integrable parameter slices on a compact finite carrier. -/
theorem bellman_compact_parameter_integrable (mu : Measure A) [IsFiniteMeasure mu]
    {U : Set E} {f : E → A → F} (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    {q : E} (hq : q ∈ U) : Integrable (f q) mu := by
  have hc : Continuous (f q) := continuousOn_univ.mp
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun a _ => ⟨hq, trivial⟩))
  simpa only [IntegrableOn, Measure.restrict_univ] using
    ContinuousOn.integrableOn_compact' (μ := mu) isCompact_univ
      MeasurableSet.univ hc.continuousOn

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A] in
/-- Compactness bounds the parameter uniformly on a spatial neighborhood. -/
theorem bellman_compact_parameter_bound {U : Set E} (hU : IsOpen U)
    {f : E → A → F} (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    {q : E} (hq : q ∈ U) : ∃ s ∈ 𝓝 q, s ⊆ U ∧ ∃ C : ℝ,
      ∀ x ∈ s, ∀ a : A, ‖f x a‖ ≤ C := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU q hq
  have hp := half_pos hr
  have hsmall : closedBall q (r / 2) ⊆ U := by
    intro x hx
    apply hsub
    exact lt_of_le_of_lt hx (half_lt_self hr)
  have hc := (isCompact_closedBall q (r / 2)).prod (isCompact_univ : IsCompact (univ : Set A))
  obtain ⟨C, hC⟩ := hc.bddAbove_image (hf.mono (prod_mono hsmall Subset.rfl)).norm
  exact ⟨closedBall q (r / 2), closedBall_mem_nhds q hp, hsmall, C,
    fun x hx a => hC ⟨(x, a), ⟨hx, trivial⟩, rfl⟩⟩

omit [CompleteSpace F] [SecondCountableTopology A] in
/-- On an open spatial set a compact parameter integral has its expected first derivative. -/
theorem bellman_compact_parameter_hasFDerivAt (mu : Measure A) [IsFiniteMeasure mu]
    {U : Set E} (hU : IsOpen U) (f : E → A → F) (f' : E → A → E →L[ℝ] F)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hd : ∀ q ∈ U, ∀ a, HasFDerivAt (fun x => f x a) (f' q a) q)
    {q : E} (hq : q ∈ U) :
    HasFDerivAt (fun x => ∫ a, f x a ∂mu) (∫ a, f' q a ∂mu) q := by
  obtain ⟨s, hs, hsub, C, hC⟩ := bellman_compact_parameter_bound hU hf' hq
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
  · filter_upwards [hU.mem_nhds hq] with x hx
    exact (bellman_compact_parameter_integrable mu hf hx).aestronglyMeasurable
  · exact bellman_compact_parameter_integrable mu hf hq
  · exact (bellman_compact_parameter_integrable mu hf' hq).aestronglyMeasurable
  · exact ae_of_all _ (fun a x hx => hC x hx a)
  · exact integrable_const C
  · exact ae_of_all _ (fun a x hx => hd x (hsub hx) a)

omit [NormedSpace ℝ E] [CompleteSpace F] [SecondCountableTopology A] in
/-- Joint continuity on a compact parameter gives continuity of the parameter integral. -/
theorem bellman_compact_parameter_continuousAt (mu : Measure A) [IsFiniteMeasure mu]
    {U : Set E} (hU : IsOpen U) (f : E → A → F)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    {q : E} (hq : q ∈ U) : ContinuousAt (fun x => ∫ a, f x a ∂mu) q := by
  obtain ⟨s, hs, hsub, C, hC⟩ := bellman_compact_parameter_bound hU hf hq
  apply continuousAt_of_dominated
  · filter_upwards [hU.mem_nhds hq] with x hx
    exact (bellman_compact_parameter_integrable mu hf hx).aestronglyMeasurable
  · filter_upwards [hs] with x hx
    exact ae_of_all _ (fun a => hC x hx a)
  · exact integrable_const C
  · apply ae_of_all
    intro a
    have hc : ContinuousOn (fun x => f x a) U :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨hx, trivial⟩)
    exact hc.continuousAt (hU.mem_nhds hq)

omit [CompleteSpace F] [SecondCountableTopology A] in
/-- Two continuous parameter derivatives yield C² regularity of the actual integral. -/
theorem bellman_compact_parameter_contDiffOn_two (mu : Measure A) [IsFiniteMeasure mu]
    {U : Set E} (hU : IsOpen U) (f : E → A → F) (f' : E → A → E →L[ℝ] F)
    (f'' : E → A → E →L[ℝ] (E →L[ℝ] F))
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ univ))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ univ))
    (hf'' : ContinuousOn (Function.uncurry f'') (U ×ˢ univ))
    (hd : ∀ q ∈ U, ∀ a, HasFDerivAt (fun x => f x a) (f' q a) q)
    (hd' : ∀ q ∈ U, ∀ a, HasFDerivAt (fun x => f' x a) (f'' q a) q) :
    ContDiffOn ℝ 2 (fun x => ∫ a, f x a ∂mu) U := by
  have hc : ContinuousOn (fun x => ∫ a, f'' x a ∂mu) U := by
    intro q hq
    exact (bellman_compact_parameter_continuousAt mu hU f'' hf'' hq).continuousWithinAt
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun x => ∫ a, f' x a ∂mu, ⟨U, hU.mem_nhds hq, ?_⟩, ?_⟩
  · intro x hx
    exact bellman_compact_parameter_hasFDerivAt mu hU f f' hf hf' hd hx
  · apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ a, f'' x a ∂mu, ⟨U, hU.mem_nhds hq, ?_⟩, ?_⟩
    · intro x hx
      exact bellman_compact_parameter_hasFDerivAt mu hU f' f'' hf' hf'' hd' hx
    · exact contDiffAt_zero.mpr ⟨U, hU.mem_nhds hq, hc⟩

end HypoellipticAleksandrov.KineticAleksandrov
