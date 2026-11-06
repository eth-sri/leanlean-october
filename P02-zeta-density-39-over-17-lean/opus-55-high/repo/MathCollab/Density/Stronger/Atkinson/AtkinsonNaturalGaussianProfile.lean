module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_AMPLITUDE_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.ZetaGaussianNaturalDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootLogProfile
public import LaterPairs.Native.AtkinsonNaturalAmplitude
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Complex Set Filter
open scoped ContDiff Topology
namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC2Bound.comp_div {f : ℝ → ℂ} {a b M R c : ℝ}
    (hf : IntervalC2Bound f a b M R) (hc : 0 < c) :
    IntervalC2Bound (fun y => f (y / c)) (c * a) (c * b) M (R / c) := by pm_2020

theorem exists_intervalC2Bound_zetaQuadraticLogGaussian_root_natural :
    ∃ C : ℝ, 0 < C ∧ ∀ T G : ℝ, 0 < T → 1 ≤ G → G ^ 2 ≤ 2 * T →
      IntervalC2Bound (fun u => zetaGaussianQuadraticIntegral T G
        (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi)))) (1 / 4) 1 (C * G) G := by
  obtain ⟨C, hC, hbound⟩ := exists_intervalC2Bound_quadraticGaussian_profile_natural
    (v := atkinsonRootLogProfile) (a := 1 / 4) (b := 1) (by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      unfold atkinsonRootLogProfile
      fun_prop (disch := exact hu0.ne'))
  pm_435 C hC T G hT hG hGT
  apply (hbound T G hT hG hGT).congr_of_eventuallyEq
  intro u hu
  filter_upwards [Ioi_mem_nhds (show 0 < u by linarith [hu.1])] with y hy
  exact (zetaQuadraticLogGaussian_root_rescale hT hy G).symm


end MathCollab.Density.Stronger.Atkinson
