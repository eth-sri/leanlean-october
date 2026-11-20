module

public import NearlyMinimax.HistoryPriorDensity


@[expose] public section

/-!
# The constructed path is the source density tilt of the reference law
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

/-- A measurable image of a pulled-back density is the corresponding density tilt. -/
theorem historyMap_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {f : A → B} (hf : Measurable f) {p : B → ℝ≥0∞} (hp : Measurable p) :
    Measure.map f (μ.withDensity (p ∘ f)) = (Measure.map f μ).withDensity p := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs,
    Measure.restrict_map hf hs, lintegral_map hp hf]
  rfl

variable {J : Type*} [Fintype J] [LinearOrder J]

variable (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*} [MeasurableSpace E] (π : Measure E)
    {a : E → ℝ} (ha : Measurable a)
include ha

/-- The actual unnormalized mixture is exactly the reference measure tilted by Phi. -/
theorem historyMarkedPriorRaw_eq_withDensity :
    historyMarkedPriorRaw dependent Δ t π a =
      (historyMarkedReferenceRaw dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity (historyReferenceRho Δ) t a h)) := by
  let p : HistoryMarked dependent E → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (historyMarkedDensity (historyReferenceRho Δ) t a h)
  have hp : Measurable p := (historyMarkedDensity_measurable dependent _ t ha).ennreal_ofReal
  have hm : ∀ g, Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
      (historyMarkedFiberPrior Δ t π a g) =
        (Measure.map (fun marks => (⟨g, marks⟩ : HistoryMarked dependent E))
          (Measure.pi (fun _ : Fin (historyShapeLength g) => π))).withDensity p := by
    intro g
    change _ = _
    exact historyMap_withDensity _ (measurable_sigma_mk_actual g) hp
  change _ = _
  unfold historyMarkedPriorRaw historyMarkedReferenceRaw
  rw [withDensity_sum]
  apply congrArg Measure.sum
  funext g
  rw [withDensity_smul_measure]
  exact congrArg (fun μ => ENNReal.ofReal (historyShapeReferenceWeight Δ g) • μ) (hm g)

/-- Thus the actual positive prior path uses precisely dnu_t = Phi_t d tau_0. -/
theorem historyMarkedPrior_eq_withDensity :
    historyMarkedPrior dependent Δ t π a =
      (historyMarkedReference dependent Δ π).withDensity
        (fun h => ENNReal.ofReal (historyMarkedDensity (historyReferenceRho Δ) t a h)) := by
  unfold historyMarkedPrior historyMarkedReference
  rw [withDensity_smul_measure, historyMarkedPriorRaw_eq_withDensity dependent Δ t π ha]

end NearlyMinimax
