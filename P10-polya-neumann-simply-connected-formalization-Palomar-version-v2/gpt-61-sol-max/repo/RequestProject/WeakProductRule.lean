module

public import RequestProject.Finite
public import RequestProject.L2Pairing

/-! A single weak product rule for smooth L² multipliers. The value and derivative
multipliers are supplied as genuine maps, so the same argument covers affine and
bounded smooth coefficients without assuming a Sobolev product rule. -/

public section


namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped ContDiff

theorem isWeakGradient_l2Multiplier {Ω : Set ℂ} (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (T : L2 Ω →L[ℂ] L2 Ω)
    (D : Fin 2 → L2 Ω →L[ℂ] L2 Ω)
    (hT : ∀ u, (T u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun z => a z * u z)
    (hD : ∀ i u, (D i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ a z (coordDir i) * u z)
    {u : L2 Ω} {g : Fin 2 → L2 Ω} (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (T u) (fun i => T (g i) + D i u) := by
  intro φ hφ i
  have hweak := hu (fun z => a z * φ z)
    ⟨ha.mul hφ.1, hφ.2.1.mul_left, tsupport_mul_subset_right.trans hφ.2.2⟩ i
  have hleft : (∫ z in Ω, u z * fderiv ℝ (fun w => a w * φ w) z (coordDir i)) =
      (∫ z in Ω, D i u z * φ z) +
        ∫ z in Ω, T u z * fderiv ℝ φ z (coordDir i) := by
    calc
      _ = ∫ z in Ω, D i u z * φ z + T u z * fderiv ℝ φ z (coordDir i) := by
        apply integral_congr_ae
        filter_upwards [hT u, hD i u] with z hz hdz
        rw [fderiv_fun_mul (ha.differentiable (by simp) z)
          (hφ.1.differentiable (by simp) z), hz, hdz]
        simp <;> ring
      _ = _ := integral_add ((Lp.memLp (D i u)).integrable_mul hφ.memLp)
        ((Lp.memLp (T u)).integrable_mul (hφ.memLp_fderiv (coordDir i)))
  have hright : (∫ z in Ω, g i z * (a z * φ z)) = ∫ z in Ω, T (g i) z * φ z := by
    apply integral_congr_ae
    filter_upwards [hT (g i)] with z hz
    rw [hz]
    ring
  have hout := map_add (lpPair hφ.memLp) (T (g i)) (D i u)
  simp only [lpPair_apply] at hout
  rw [hleft, hright] at hweak
  rw [hout]
  linear_combination hweak

end PolyaNeumann
