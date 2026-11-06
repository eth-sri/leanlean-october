module
public import MathCollab.Density.Stronger.Parameters
public import MathCollab.Density.DetectorTruncation
public import MathCollab.Density.WeylInput
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Filter
open scoped Topology
noncomputable section
namespace MathCollab.Density.Stronger

/-- The residue is uniformly negligible for all independent scales 0 ≤ X ≤ T
and 1 ≤ Y ≤ T. No moment estimate is used. -/
theorem norm_residue_le {ρ : ℂ} {X Y T : ℝ}
    (hT : 1 ≤ T) (hX : 0 ≤ X) (hXT : X ≤ T)
    (hY : 1 ≤ Y) (hYT : Y ≤ T)
    (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : T ≤ |ρ.im|) (hγ' : |ρ.im| ≤ 2*T) :
    ‖detectorResidue ρ X Y‖ ≤ 72*T^3*Real.exp (-T) := by
  have hTpos : 0 < T := by linarith
  have hsqrt : Real.sqrt X ≤ T := by
    apply (Real.sqrt_le_left hTpos.le).2
    nlinarith
  have hpower : Y^(1-ρ.re) ≤ T := by
    calc
      _ ≤ Y := by
        simpa using Real.rpow_le_rpow_of_exponent_le hY
          (show 1-ρ.re ≤ 1 by linarith)
      _ ≤ T := hYT
  pm_1080 he T
  have hb := norm_detectorResidue_le hX (by linarith : 0 < Y) hβ hβ' (hT.trans hγ)
  calc
    _ ≤ 24*Real.sqrt X*Y^(1-ρ.re)*(1+|ρ.im|)*Real.exp (-|ρ.im|) := hb
    _ ≤ 24*T*T*(3*T)*Real.exp (-T) := by
      gcongr
      linarith
    _ = _ := by ring

/-- The actual contour detector is uniformly small for the stronger curve's
parameters. The Weyl input is proved and discharged; no moment is assumed. -/
theorem detector_eventually_small {σ δ ε : ℝ}
    (hσ : 3/4 < σ) (hδ : δ ≤ 1/8) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (detectorX δ T) (1 / detectorY σ T)‖ < ε := by
  pm_4426 σ smoothingExponent_pos hσ smoothingExponent_lt_one hσ.le.trans
  pm_5746 detector_error_scale hσ
  pm_4427 σ

/-- The literal exponentially smoothed series after removal of its n=1 term.
Terms with 2 ≤ n ≤ X vanish by the proved Möbius identity. -/
def detectorTail (ρ : ℂ) (X Y : ℝ) : ℂ :=
  ∑' n : ℕ, detectorTerm ρ X Y (n+2)

theorem detectorTail_decomposition {ρ : ℂ} {X Y : ℝ}
    (hX : 1 ≤ X) (hY : 0 < Y) (hρ : 0 ≤ ρ.re) :
    (Real.exp (-1/Y) : ℂ) + detectorTail ρ X Y = smoothedDetector ρ X (1/Y) := by
  have hs := summable_zeta_detector_series X hY hρ
  have he := hs.sum_add_tsum_nat_add 2
  have hz : detectorTerm ρ X Y 0 = 0 := by simp [detectorTerm, mollifierCoefficient]
  have ho : detectorTerm ρ X Y 1 = (Real.exp (-1/Y) : ℂ) := by
    simp [detectorTerm, mollifierCoefficient_one hX]
  have hfull : (∑' n : ℕ, detectorTerm ρ X Y n) = smoothedDetector ρ X (1/Y) := by
    apply tsum_congr
    intro n
    exact (smoothedDetector_term_eq ρ X Y n).symm
  change (∑ n ∈ Finset.range 2, detectorTerm ρ X Y n) + detectorTail ρ X Y =
    (∑' n : ℕ, detectorTerm ρ X Y n) at he
  pm_546 Finset.sum_range_succ Finset.sum_range_zero zero_add hz ho hfull he

/-- Uniform detection of every actual zero in the slab, with the exact new
parameters and the same ordinate. This does not yet choose a smooth dyadic block. -/
theorem detectorTail_eventually_large {σ δ : ℝ}
    (hσ : 3/4 < σ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/8) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      (1/2 : ℝ) ≤ ‖detectorTail ρ (detectorX δ T) (detectorY σ T)‖ := by
  pm_4429 σ smoothingExponent_pos hσ detector_eventually_small
  pm_5987 σ
  pm_4428 σ

end MathCollab.Density.Stronger
