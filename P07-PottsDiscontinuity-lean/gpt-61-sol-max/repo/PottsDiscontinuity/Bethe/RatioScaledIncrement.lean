module
public import Mathlib

public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Moving pairs of roots and scaled logarithmic increments -/

@[expose] public section

open Set Filter Asymptotics
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- Strict differentiability controls two simultaneously moving endpoints,
including indices where they coincide. No division by their difference is used. -/
theorem ratio_scaled_increment_tendsto {ι : Type*} {l : Filter ι}
    {f : ℝ → ℝ} {f' x d : ℝ} (hf : HasStrictDerivAt f f' x)
    (u v a : ι → ℝ) (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 x))
    (hd : Tendsto (fun i => a i * (u i - v i)) l (𝓝 d)) :
    Tendsto (fun i => a i * (f (u i) - f (v i))) l (𝓝 (f' * d)) := by
  
  
  have hz : Tendsto (fun i => a i * (f (u i) - f (v i) - (u i - v i) * f')) l (𝓝 0) := IsLittleO.tendsto_zero_of_tendsto ((isBigO_refl a l).smul_isLittleO (IsLittleO.comp_tendsto (HasStrictFDerivAt.isLittleO (hasStrictDerivAt_iff_hasStrictFDerivAt.mp hf))
                                                                                                                                                                                                       (Tendsto.prodMk_nhds hu hv))) hd
  have ht := hz.add (hd.const_mul f')
  rw [zero_add] at ht
  apply ht.congr
  intro i
  ring

theorem ratio_hasStrictDerivAt_ell {c x : ℝ} (hc : 2 < c)
    (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0) :
    HasStrictDerivAt (ratioEll c) (ratioEllPrime c x) x := by
  apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2, eventually_ne_nhds hx0] with y hy hy0
    exact ratio_hasDerivAt_ell hc hy hy0
  · exact ratio_continuousAt_ellPrime hc (Ioo_subset_Icc_self hx) hx0

/-- The source pointwise moving-root log limit away from the origin. -/
theorem ratio_scaled_ell_tendsto {ι : Type*} {l : Filter ι} {c x d : ℝ}
    (hc : 2 < c) (hx : x ∈ Ioo (-Real.pi) Real.pi) (hx0 : x ≠ 0)
    (u v a : ι → ℝ) (hu : Tendsto u l (𝓝 x)) (hv : Tendsto v l (𝓝 x))
    (hd : Tendsto (fun i => a i * (u i - v i)) l (𝓝 d)) :
    Tendsto (fun i => a i * (ratioEll c (u i) - ratioEll c (v i))) l
      (𝓝 (ratioEllPrime c x * d)) :=
  ratio_scaled_increment_tendsto (ratio_hasStrictDerivAt_ell hc hx hx0) u v a hu hv hd

end PottsDiscontinuity.Bethe
