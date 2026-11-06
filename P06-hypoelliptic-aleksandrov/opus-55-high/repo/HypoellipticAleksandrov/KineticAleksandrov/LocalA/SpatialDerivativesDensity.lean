module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesPairing
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The joint exit density and its L1 pairing give the same boundary integral -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory Filter
open scoped ENNReal

/-- A nonnegative joint density reconstructs the integral of bounded boundary data via L1. -/
theorem spatialDensity_integral
    {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]
    (dy : Measure Y) (dz : Measure Z) [SFinite dy] [SFinite dz]
    (ν : Measure (Y × Z)) (g : Y × Z → ℝ) (hg : Measurable g)
    (hn : ∀ᵐ p ∂dy.prod dz, 0 ≤ g p)
    (he : ν = (dy.prod dz).withDensity (fun p => ENNReal.ofReal (g p)))
    (G : Y → Lp ℂ 1 dz) (hG : ∀ y, (G y : Z → ℂ) =ᵐ[dz] fun z => (g (y, z) : ℂ))
    (F : Y × Z → ℝ) (hF : Integrable (fun p => (F p : ℂ)) ν)
    (f : Y → Lp ℝ ∞ dz) (hf : ∀ y, (f y : Z → ℝ) =ᵐ[dz] fun z => F (y, z)) :
    (∫ p, (F p : ℂ) ∂ν) = ∫ y, spatialDensityPairing dz (f y) (G y) ∂dy := by
  let ρ  := fun p => ENNReal.ofReal (g p)
  have hm : Measurable ρ := hg.ennreal_ofReal
  have ht : ∀ᵐ p ∂dy.prod dz, ρ p < ∞ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hn' : (fun p => (ρ p).toReal • (F p : ℂ)) =ᵐ[dy.prod dz]
      fun p => g p • (F p) := by
    filter_upwards [hn] with p hp
    aesop
  have hi : Integrable (fun p => g p • (F p : ℂ)) (dy.prod dz) := by
    apply Integrable.congr ((integrable_withDensity_iff_integrable_smul' hm ht).mp ?_) hn'
    grind
  rw [he, integral_withDensity_eq_integral_toReal_smul hm ht, integral_congr_ae hn', integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [spatialDensityPairing_apply]
  apply integral_congr_ae
  filter_upwards [hf y, hG y] with z hz hz'
  rw [hz, hz']
  simp only [Complex.real_smul]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
