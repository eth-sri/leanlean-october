module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Batteries.Tactic.Alias



/-!
# Reverse-time Steklov energy identities

This module proves the fixed-positive-step Hilbert-value energy identities for
forward and backward reverse-time Steklov averages in the spatial Gelfand
triple.  It does not assert an energy identity for an unregularized curve.
-/

 public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem normSq_sub_eq_inner_add_sub_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (r s : H) :
    ‖r‖ ^ 2 - ‖s‖ ^ 2 = inner ℝ (r + s) r - inner ℝ (r + s) s := by
  rw [inner_add_left, inner_add_left, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, real_inner_comm s r]
  ring

private theorem pivot_normSq_sub_eq_dualSub_apply_add
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)
    (r s : H10HilbertGraph hΩ) :
    ‖valueCLM hΩ r‖ ^ 2 - ‖valueCLM hΩ s‖ ^ 2 =
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ r) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ s)) (r + s) := by
  let vr : PDE.ScalarLp Ω (2 ) := valueCLM hΩ r
  let vs : PDE.ScalarLp Ω (2 ) := valueCLM hΩ s

  change ‖vr‖ ^ 2 - ‖vs‖ ^ 2 = _
  rw [ContinuousLinearMap.sub_apply,
    scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, ((valueCLM hΩ).map_add r s)]
  exact normSq_sub_eq_inner_add_sub_inner vr vs

variable {V : Type*}

private theorem tendsto_clm_apply
     [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V}
    {a : V →L[ℝ] ℝ} {b : V}
    (hf : Filter.Tendsto f L (𝓝 a)) (hg : Filter.Tendsto g L (𝓝 b)) :
    Filter.Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
  simpa only [Function.comp_def] using
    (isBoundedBilinearMap_apply.continuous.tendsto (a, b)).comp (hf.prodMk_nhds hg)

private theorem hasDerivAt_of_pivoted_curve
     [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : ℝ → V} {U : ℝ → V →L[ℝ] ℝ} {E : ℝ → ℝ}
    {y : ℝ → V →L[ℝ] ℝ} (hx : Continuous x) {t : ℝ}
    (hpivot : ∀ r s : ℝ, E r - E s = (U r - U s) (x r + x s))
    (hderiv : HasDerivAt U (y t) t) :
    HasDerivAt E (2 * y t (x t)) t := by
  let sharedTerm_9eb07bad91 := (𝓝[≠] t)





  have hSlopeE : Filter.Tendsto (slope E t) (sharedTerm_9eb07bad91) (𝓝 (2 * y t (x t))) := by
    have htwice : y t (x t + x t) = 2 * y t (x t) := by
      rw [ContinuousLinearMap.map_add]
      ring
    rw [← htwice]
    exact (tendsto_clm_apply (show Filter.Tendsto (slope U t) (sharedTerm_9eb07bad91) (𝓝 (y t)) by
        exact hderiv.tendsto_slope) (((hx.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).add tendsto_const_nhds)).congr' (show slope E t =ᶠ[sharedTerm_9eb07bad91]
      fun s => slope U t s (x s + x t) by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hst  := hs
        rw [slope_def_field, slope_def_module, hpivot s t,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
        rw [smul_eq_mul, ContinuousLinearMap.sub_apply]
        field_simp [sub_ne_zero.mpr hst]).symm
  exact hasDerivAt_iff_tendsto_slope.mpr hSlopeE

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b) (hbT : b + h ≤ T)

include hderiv hh ha0 hab hbT in
private theorem reverseTimeForwardSteklov_energy_identity_raw
     :
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a)‖ ^ 2 =
      2 * (∫ t in Set.Icc a b,
        (reverseTimeForwardSteklov T h g t)
          (reverseTimeForwardSteklov T h u t)) := by
  let x : ℝ → H10HilbertGraph hΩ := (reverseTimeForwardSteklov T h u)
  let y : ℝ → H10HilbertGraphDual hΩ := (reverseTimeForwardSteklov T h g)
  let E  := fun t => ‖valueCLM hΩ (x t)‖ ^ 2
  have hx : Continuous x := continuous_reverseTimeForwardSteklov T h hh u




  have hFTC : (∫ t in a..b, 2 * y t (x t)) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (((valueCLM hΩ).continuous.comp hx).norm.pow 2).continuousOn (by
        intro t ht
        apply hasDerivAt_of_pivoted_curve hx
          (fun r s => pivot_normSq_sub_eq_dualSub_apply_add hΩ (x r) (x s))
        exact hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv hh
          (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2]))
      ((continuous_const.mul ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply hx)).intervalIntegrable a b)
  calc
    ‖valueCLM hΩ (reverseTimeForwardSteklov T h u b)‖ ^ 2 -
        ‖valueCLM hΩ (reverseTimeForwardSteklov T h u a)‖ ^ 2 = E b - E a := rfl
    _ = ∫ t in a..b, 2 * y t (x t) := hFTC.symm
    _ = 2 * (∫ t in Ioc a b, y t (x t)) := by
      rw [intervalIntegral.integral_of_le hab, integral_const_mul]
    _ = 2 * (∫ t in Icc a b, y t (x t)) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = 2 * (∫ t in Icc a b,
        (reverseTimeForwardSteklov T h g t) (reverseTimeForwardSteklov T h u t)) := rfl

/-- Fixed-window forward Steklov energy identity in the reverse-time Gelfand triple. -/
alias reverseTimeForwardSteklov_energy_identity := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeForwardSteklov_energy_identity_raw


end HypoellipticAleksandrov.Parabolic.Dirichlet
