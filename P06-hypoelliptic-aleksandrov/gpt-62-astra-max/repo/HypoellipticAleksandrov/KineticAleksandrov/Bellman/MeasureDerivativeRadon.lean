module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

/-! # Radon–Nikodym comparison of locally integrable test pairings -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

section
variable (μ ν : Measure ℝ)

/-- A Radon measure has a locally integrable Radon–Nikodym density against any dominating
measure. -/
theorem bellman_rnDeriv_locallyIntegrable
    [IsFiniteMeasureOnCompacts μ] :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_toReal_rnDeriv hK.measure_lt_top.ne

/-- Multiplying a locally integrable function by the density transfers local integrability. -/
theorem bellman_rnDeriv_mul_locallyIntegrable
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (f : ℝ → ℝ)
    (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal * f x) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  have ht := (integrable_toReal_rnDeriv_mul_iff hμν).2 ((integrable_indicator_iff hK.measurableSet).2 (hf.integrableOn_isCompact hK))
  rw [← integrable_indicator_iff hK.measurableSet]
  convert ht using 1
  funext x
  by_cases hx : x ∈ K <;> simp [hx]

/-- Equality on smooth tests gives equality of the two densities against a common dominator. -/
theorem bellman_test_pairing_rnDeriv_eq
    [IsFiniteMeasureOnCompacts μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hvolν : volume ≪ ν)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    ∀ᵐ x ∂ν, (μ.rnDeriv ν x).toReal = (volume.rnDeriv ν x).toReal * f x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (bellman_rnDeriv_locallyIntegrable μ ν)
    (bellman_rnDeriv_mul_locallyIntegrable volume ν hvolν f hf)
  intro φ hφ hc
  have he := ht ⟨φ, hφ, hc, by simp⟩
  simp only [smul_eq_mul]
  calc
    (∫ x, φ x * (μ.rnDeriv ν x).toReal ∂ν) = ∫ x, φ x ∂μ := by
      rw [show (fun x => φ x * (μ.rnDeriv ν x).toReal) =
        (fun x => (μ.rnDeriv ν x).toReal * φ x) by funext x; ring]
      exact integral_toReal_rnDeriv_mul hμν
    _ = ∫ x, φ x * f x := he
    _ = ∫ x, φ x * ((volume.rnDeriv ν x).toReal * f x) ∂ν := by
      rw [show (fun x => φ x * ((volume.rnDeriv ν x).toReal * f x)) =
        (fun x => (volume.rnDeriv ν x).toReal * (φ x * f x)) by funext x; ring]
      exact (integral_toReal_rnDeriv_mul hvolν).symm

end

/-- A positive Radon measure represented on smooth tests has the asserted Lebesgue density. -/
theorem bellman_measure_eq_withDensity_of_test_pairing (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (f : ℝ → ℝ) (hm : Measurable f)
    (hf : LocallyIntegrable f volume)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let ν := μ + volume
  have hμν : μ ≪ ν := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hvolν : volume ≪ ν := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hd : μ.rnDeriv ν =ᵐ[ν]
      (fun x => volume.rnDeriv ν x * ENNReal.ofReal (f x)) := by
    filter_upwards [(bellman_test_pairing_rnDeriv_eq μ ν hμν f hf hvolν ht), Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_lt_top volume ν]
      with x hx hμ hvol
    rw [← ENNReal.ofReal_toReal hμ.ne, hx, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hvol.ne]
  calc
    μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq μ ν hμν).symm
    _ = ν.withDensity (fun x => volume.rnDeriv ν x * ENNReal.ofReal (f x)) :=
      withDensity_congr_ae hd
    _ = (ν.withDensity (volume.rnDeriv ν)).withDensity
        (fun x => ENNReal.ofReal (f x)) :=
      withDensity_mul ν (Measure.measurable_rnDeriv volume ν) (hm.ennreal_ofReal)
    _ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
      rw [Measure.withDensity_rnDeriv_eq volume ν hvolν]

/-- A density representing a positive measure on smooth tests is nonnegative almost
everywhere. -/
theorem bellman_nonneg_of_test_pairing (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    ∀ᵐ x ∂volume, 0 ≤ f x := by
  let ν := μ + volume
  have hvolν : volume ≪ ν := (Measure.le_add_left le_rfl).absolutelyContinuous
  have he := hvolν.ae_le (bellman_test_pairing_rnDeriv_eq μ ν ((Measure.le_add_right le_rfl).absolutelyContinuous) f hf hvolν ht)
  filter_upwards [he, (hvolν.ae_le (Measure.rnDeriv_lt_top volume ν)), Measure.rnDeriv_pos hvolν] with x hx ht hxpos
  have hp : 0 ≤ (volume.rnDeriv ν x).toReal * f x := by
    rw [← hx]
    exact ENNReal.toReal_nonneg
  exact nonneg_of_mul_nonneg_right hp (ENNReal.toReal_pos hxpos.ne' ht.ne)

end HypoellipticAleksandrov.KineticAleksandrov
