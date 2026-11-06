module

public import NearlyMinimax.HistoryPriorDensity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# The constructed path is the source density tilt of the reference law
-/

𝚩
𝚯
𝚮
𝚨

/-- A measurable image of a pulled-back density is the corresponding density tilt. -/
theorem historyMap_withDensity [MeasurableSpace A] [MeasurableSpace B]
    μ (f : A → B) (hf : Measurable f) p (hp : Measurable p) :
    Measure.map f (μ.withDensity $ p ∘ f ) = (Measure.map f μ).withDensity p := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ $ hs.preimage hf , withDensity_apply _ hs,
    Measure.restrict_map hf hs, lintegral_map hp hf]
  rfl

𝚲

𝗇 𝔄 fun h => ENNReal.ofReal $ 𝚇₂ t a h
𝗇 𝔅 fun marks => 𝗬
𝗃 𝔇 ἀ dependent Δ t π a
/-- The actual unnormalized mixture is exactly the reference measure tilted by Phi. -/
theorem historyMarkedPriorRaw_eq_withDensity (dependent : 𝙁) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) a (ha : Measurable a) :
    𝔇 historyMarkedPriorRaw =
      (𝚊₂).withDensity
        𝔄 := by
  let p := 𝔄
  have hm : ∀ g, Measure.map 𝔅
      (𝔇 historyMarkedFiberPrior g) =
        (Measure.map 𝔅
          𝘰).withDensity p := by
    intro g
    exact historyMap_withDensity _ _ (historyMarked_measurable_mk dependent g) p (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
  unfold historyMarkedPriorRaw historyMarkedReferenceRaw
  rw [withDensity_sum]
  apply congrArg Measure.sum
  funext g
  rw [withDensity_smul_measure]
  exact congrArg (fun μ => ENNReal.ofReal 𝘎₁ • μ) $ hm g

/-- Thus the actual positive prior path uses precisely dnu_t = Phi_t d tau_0. -/
theorem historyMarkedPrior_eq_withDensity (dependent : 𝙁) (Δ : ℕ) (t : ℝ)
    [MeasurableSpace E] (π : Measure E) a (ha : Measurable a) :
    𝔇 historyMarkedPrior =
      (𝙤).withDensity
        𝔄 := by
  unfold historyMarkedPrior historyMarkedReference
  rw [withDensity_smul_measure, 𝔇 historyMarkedPriorRaw_eq_withDensity ha]
