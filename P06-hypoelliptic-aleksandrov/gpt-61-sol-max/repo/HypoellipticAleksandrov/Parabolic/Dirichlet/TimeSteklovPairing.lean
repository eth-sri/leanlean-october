module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation

open private HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_integral_eq_norm_sq_toLp from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation


/-!
# Local convergence of reverse-time Steklov dual pairings

This module combines the local Bochner Steklov approximation with
the reverse-time `V*`--`V` pairing.  It makes no fixed-time representative,
trace, weak-derivative, or energy assertion.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {E : Type*}

private theorem memLp_on_Icc_of_reverseTimeLp
     [NormedAddCommGroup E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hb : b < T) :
    MemLp (f : ℝ → E) (2 ) (volume.restrict (Icc a b)) := by

  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    Measure.restrict_restrict_of_subset (show Icc a b ⊆ Ioo 0 T by
        intro t ht
        exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩)] using (Lp.memLp f).restrict (Icc a b)

private theorem memLp_on_Icc_of_continuous
     [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f (2 ) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc




private theorem sqrt_sqNorm_integral_triangle
     [NormedAddCommGroup E]
    {μ : Measure ℝ} (x y : ℝ → E)
    (hx : MemLp x (2 ) μ) (hy : MemLp y (2 ) μ) :
    √(∫ t, ‖x t‖ ^ 2 ∂μ) ≤
      √(∫ t, ‖x t - y t‖ ^ 2 ∂μ) + √(∫ t, ‖y t‖ ^ 2 ∂μ) := by
  let hxy := hx.sub hy
  have hEq : hx.toLp x = hxy.toLp (x - y) + hy.toLp y := by
    apply Lp.ext
    filter_upwards [hx.coeFn_toLp, hxy.coeFn_toLp, hy.coeFn_toLp,
      Lp.coeFn_add (hxy.toLp (x - y)) (hy.toLp y)] with t h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]
    simp only [Pi.sub_apply]
    abel
  have hxySq : ∫ t, ‖x t - y t‖ ^ 2 ∂μ = ‖hxy.toLp (x - y)‖ ^ 2 := by
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_integral_eq_norm_sq_toLp (x - y) hxy
  rw [_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_integral_eq_norm_sq_toLp x hx, hxySq,
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_integral_eq_norm_sq_toLp y hy, hEq]
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_add_le (hxy.toLp (x - y)) (hy.toLp y)

variable {E F : Type*}

private theorem integral_mul_norm_le_sqrt_mul_sqrt
     [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 ) μ) (hg : MemLp g (2 ) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

private theorem tendsto_integral_abs_bilin_of_sqNorm

    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ f : F, ∀ e : E, ‖B f e‖ ≤ ‖f‖ * ‖e‖)
    (μ : Measure ℝ) (u : ℝ → E) (g : ℝ → F)
    (uh : ℝ → ℝ → E) (gh : ℝ → ℝ → F)
    (hu : MemLp u (2 ) μ) (hg : MemLp g (2 ) μ)
    (hraw : Integrable (fun t => B (g t) (u t)) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 ) μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) (2 ) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h  => ∫ t, |B (gh h t) (uh h t) - B (g t) (u t)| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let sharedTerm_dd6b15b2e2 := ((√(∫ t, ‖g t‖ ^ 2 ∂μ)))
  have hUsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hU.sqrt
  have hGsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hG.sqrt
  rcases hUsqrt.isBoundedUnder_le.eventually_le with ⟨C, hC⟩

  have hUhNormBound : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
      (norm ∘ fun h : ℝ => √(∫ t, ‖uh h t‖ ^ 2 ∂μ)) :=
    isBoundedUnder_of_eventually_le ((show ∀ᶠ h : ℝ in 𝓝[>] 0,
      √(∫ t, ‖uh h t‖ ^ 2 ∂μ) ≤ C + √(∫ t, ‖u t‖ ^ 2 ∂μ) by
        filter_upwards [huh, hC] with h huh hC
        exact (sqrt_sqNorm_integral_triangle (uh h) u huh hu).trans
          (add_le_add_left hC _)).mono fun h hh => by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hh)



  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh, hgh] with h huh hgh
    have hdu  := huh.sub hu
    have hdg  := hgh.sub hg


    have hterm1  :=
      hdg.norm.integrable_mul huh.norm
    have hterm2  :=
      hg.norm.integrable_mul hdu.norm
    have hpoint : ∀ t : ℝ,
        |B (gh h t) (uh h t) - B (g t) (u t)| ≤
          ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ := by
      intro t
      change ‖B (gh h t) (uh h t) - B (g t) (u t)‖ ≤ _
      calc
        ‖B (gh h t) (uh h t) - B (g t) (u t)‖ =
            ‖B (gh h t - g t) (uh h t) + B (g t) (uh h t - u t)‖ := by
              congr 1
              rw [B.map_sub, ContinuousLinearMap.sub_apply, (B (g t)).map_sub]
              ring
        _ ≤ ‖B (gh h t - g t) (uh h t)‖ + ‖B (g t) (uh h t - u t)‖ := norm_add_le _ _
        _ ≤ ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ :=
          add_le_add (hB _ _) (hB _ _)

    have hholder1 := integral_mul_norm_le_sqrt_mul_sqrt
      (fun t => gh h t - g t) ((uh h)) hdg huh
    have hholder2 := integral_mul_norm_le_sqrt_mul_sqrt
      g (fun t => uh h t - u t) hg hdu
    calc
      (∫ t, |B (gh h t) (uh h t) - B (g t) (u t)| ∂μ) ≤
          ∫ t, ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ ∂μ := (integral_mono (show Integrable (fun t => |B (gh h t) (uh h t) - B (g t) (u t)|) μ by
              simpa only [Real.norm_eq_abs, Pi.sub_def] using ((memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hgh huh)).sub hraw).norm) (hterm1.add hterm2) hpoint)
      _ = (∫ t, ‖gh h t - g t‖ * ‖uh h t‖ ∂μ) +
          ∫ t, ‖g t‖ * ‖uh h t - u t‖ ∂μ := integral_add hterm1 hterm2
      _ ≤ √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh h t‖ ^ 2 ∂μ) +
          sharedTerm_dd6b15b2e2 * √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) :=
        add_le_add hholder1 hholder2
  · simpa only [add_zero] using (hGsqrt.zero_mul_isBoundedUnder_le hUhNormBound).add (show Tendsto (fun h : ℝ =>
      sharedTerm_dd6b15b2e2 * √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) by
      simpa only [mul_zero] using tendsto_const_nhds.mul hUsqrt)

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private def h10DualEvaluation
     :
    H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)

variable (g : H10HilbertGraphDual hΩ) (u : H10HilbertGraph hΩ)

private theorem h10DualEvaluation_apply

     :
    h10DualEvaluation hΩ g u = g u := rfl

private theorem h10DualEvaluation_le

     :
    ‖h10DualEvaluation hΩ g u‖ ≤ ‖g‖ * ‖u‖ := by
  simpa only [h10DualEvaluation_apply] using g.le_opNorm u




variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω)

private theorem tendsto_h10DualPairing_of_sqNorm

    (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (gh : ℝ → ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u (2 ) μ) (hg : MemLp g (2 ) μ)
    (hraw : Integrable (fun t => (g t) (u t)) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 ) μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) (2 ) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h  => ∫ t,
      |(gh h t) (uh h t) - (g t) (u t)| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [h10DualEvaluation_apply] using
    tendsto_integral_abs_bilin_of_sqNorm (B := h10DualEvaluation hΩ)
      (hB := h10DualEvaluation_le hΩ)
      μ u g uh gh hu hg hraw huh hgh hU hG

variable (T : ℝ)

private def forwardPrimalAverage

    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ → H10HilbertGraph hΩ :=
  fun h t => reverseTimeForwardSteklov T h u t

private def forwardDualAverage

    (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ → H10HilbertGraphDual hΩ :=
  fun h t => reverseTimeForwardSteklov T h g t

variable (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)

private def forwardPairingErrorIntegral


    (a b h : ℝ) : ℝ :=
  ∫ t in Icc a b,
    |(forwardDualAverage hΩ T g h t) (forwardPrimalAverage hΩ T u h t) - (g t) (u t)|

variable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T)

include ha hab hb
private theorem tendsto_forwardSteklov_dualPairing_integral_on_Icc_raw


     :
    Filter.Tendsto (forwardPairingErrorIntegral hΩ T u g a b)
      (𝓝[>] 0) (𝓝 0) := by
  let sharedTerm_308e2f95ea := (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin)
  let μ  := volume.restrict (Icc a b)
  let uh := forwardPrimalAverage hΩ T u
  let gh := forwardDualAverage hΩ T g








  change Tendsto (fun h  => ∫ t,
      |(gh h t) (uh h t) -
        (g t) (u t)| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_h10DualPairing_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    uh gh
    (by
        simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T u ha hb) (by
        simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T g ha hb) (by
        dsimp only [μ, reverseTimeVolume, reverseTimeOpenInterval]
        rw [← Measure.restrict_restrict_of_subset (show Icc a b ⊆ Ioo 0 T by
            intro t ht
            exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩)]
        exact (integrable_reverseTimeDualPairing hΩ T u g).restrict) (by
        filter_upwards [sharedTerm_308e2f95ea]
          with h hh
        change MemLp (reverseTimeForwardSteklov T h u) (2 ) μ
        simpa only [μ] using memLp_on_Icc_of_continuous
          (reverseTimeForwardSteklov T h u)
          (continuous_reverseTimeForwardSteklov T h hh u) a b) (by
        filter_upwards [sharedTerm_308e2f95ea]
          with h hh
        change MemLp (reverseTimeForwardSteklov T h g) (2 ) μ
        simpa only [μ] using memLp_on_Icc_of_continuous
          (reverseTimeForwardSteklov T h g)
          (continuous_reverseTimeForwardSteklov T h hh g) a b) (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab hb) (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_forwardSteklov_sqNorm_integral_on_Icc T g ha hab hb)

/-- Forward Steklov dual pairings converge locally in `L¹` on a strict
reverse-time interior interval. -/
theorem tendsto_forwardSteklov_dualPairing_integral_on_Icc


     :
    Filter.Tendsto
      (fun h  => ∫ t in Set.Icc a b,
        |(reverseTimeForwardSteklov T h g t)
            (reverseTimeForwardSteklov T h u t) - (g t) (u t)|)
      (𝓝[>] 0) (𝓝 0) :=
  (tendsto_forwardSteklov_dualPairing_integral_on_Icc_raw hΩ T u g ha hab hb)

end HypoellipticAleksandrov.Parabolic.Dirichlet
