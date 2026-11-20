module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import HypoellipticAleksandrov.Analysis.L2Convergence

/-!
# Local convergence of reverse-time Steklov dual pairings

This module combines the local Bochner Steklov approximation with
the reverse-time `V*`--`V` pairing.  It makes no fixed-time representative,
trace, weak-derivative, or energy assertion.
-/

@[expose] public section

open HypoellipticAleksandrov.Analysis Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Forward Steklov dual pairings converge locally in `L¹` on a strict
reverse-time interior interval. -/
theorem tendsto_forwardSteklov_dualPairing_integral_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        |(reverseTimeForwardSteklov T h g t)
            (reverseTimeForwardSteklov T h u t) - (g t) (u t)|)
      (𝓝[>] 0) (𝓝 0) := by
  have hμ : volume.restrict (Icc a b) ≤ reverseTimeVolume T :=
    Measure.restrict_mono (Icc_subset_Ioo ha hb) le_rfl
  have hmem {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : Lp E 2 (reverseTimeVolume T)) :
      ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (reverseTimeForwardSteklov T h f) 2 (volume.restrict (Icc a b)) :=
    (show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin).mono fun h hh =>
      (memLp_two_iff_integrable_sq_norm
        (continuous_reverseTimeForwardSteklov T h hh f).aestronglyMeasurable).mpr
          ((continuous_reverseTimeForwardSteklov T h hh f).norm.pow 2).integrableOn_Icc
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply, Real.norm_eq_abs] using
    tendsto_integral_norm_bilin_sub_of_sqNorm (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ))
      ((Lp.memLp g).mono_measure hμ) ((Lp.memLp u).mono_measure hμ) (hmem g) (hmem u)
      (tendsto_forwardSteklov_sqNorm_integral_on_Icc T g ha hab hb)
      (tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab hb)

end HypoellipticAleksandrov.Parabolic.Dirichlet
