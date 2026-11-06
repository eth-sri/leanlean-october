module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.Gluing

/-!
# Restricting the global density to a finite horizon

If `Γ_μ^∞ = Leb.withDensity G` on `(0,∞) × ℝ^d × ℝ^d`, then the finite-horizon Green measure
`Γ_μ^S` has the density `G ∘ ι` with respect to Lebesgue measure on `(0,S) × ℝ^d × ℝ^d`, where
`ι` is the literal inclusion of carriers; integrals of `G^q ∘ ι` over the finite carrier are the
integrals of `G^q` over the time-restricted infinite carrier.  This uses the proved horizon
restriction `SectionTwo.greenMeasure_horizonRestriction`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- The literal inclusion of the finite-horizon carrier into the infinite-horizon one. -/
def horizonInclusion (d : ℕ) (S : ℝ≥0∞) :
    ElapsedTime S × EvolutionAmbientState d → GreenCarrier d :=
  fun q => (elapsedInclusion le_top q.1, q.2)

lemma measurableEmbedding_elapsedInclusion {T S : ℝ≥0∞} (hTS : T ≤ S) :
    MeasurableEmbedding (elapsedInclusion hTS) := by
  have hT : MeasurableEmbedding (Subtype.val : ElapsedTime T → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime T)
  refine ⟨?_, measurable_elapsedInclusion hTS, ?_⟩
  · intro a b hab
    exact Subtype.ext (by simpa [elapsedInclusion] using congrArg Subtype.val hab)
  · intro B hB
    have : elapsedInclusion hTS '' B = (Subtype.val : ElapsedTime S → ℝ) ⁻¹'
        ((Subtype.val : ElapsedTime T → ℝ) '' B) := by
      ext τ
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        aesop
      aesop
    rw [this]
    exact measurable_subtype_coe (hT.measurableSet_image.2 hB)

variable (d : ℕ) (S : ℝ≥0∞)

lemma measurableEmbedding_horizonInclusion  :
    MeasurableEmbedding (horizonInclusion d S) :=
  (measurableEmbedding_elapsedInclusion (le_top : S ≤ ⊤)).prodMap MeasurableEmbedding.id

/-- Density transport along a measurable embedding. -/
lemma eq_withDensity_of_map_eq_emb {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (hf : MeasurableEmbedding f) {ν Γ' : Measure X} {G' : Z → ℝ≥0∞}
    (h : Γ'.map f = (ν.map f).withDensity G') :
    Γ' = ν.withDensity (fun x => G' (f x)) := by
  ext B hB
  have h1 : Γ' B = (Γ'.map f) (f '' B) := by
    rw [hf.map_apply, Set.preimage_image_eq _ hf.injective]
  rw [h1, h, withDensity_apply _ (hf.measurableSet_image.2 hB), withDensity_apply _ hB]
  exact ((MeasurePreserving.mk hf.measurable rfl).setLIntegral_comp_emb hf G' B).symm

/-- Lebesgue measure on the finite carrier pushes forward to the time-restricted one. -/
lemma map_horizonInclusion_lebesgue  :
    ((elapsedVolume S).prod (volume : Measure (EvolutionAmbientState d))).map
        (horizonInclusion d S) =
      (greenLebesgue d).restrict {p | ENNReal.ofReal p.1.1 < S} := by
  have h1 := Measure.map_prod_map (elapsedVolume S) (volume : Measure (EvolutionAmbientState d))
    (measurable_elapsedInclusion le_top) measurable_id
  rw [elapsedInclusion_map] at h1
  have h2 := Measure.prod_restrict (μ := elapsedVolume ⊤)
    (ν := (volume : Measure (EvolutionAmbientState d))) {τ : ElapsedTime ⊤ | ENNReal.ofReal τ.1 < S}
    univ
  rw [Measure.restrict_univ, Set.prod_univ] at h2
  have h3 : (greenLebesgue d).restrict {p | ENNReal.ofReal p.1.1 < S} =
      ((elapsedVolume ⊤).restrict _).prod
        volume := h2.symm
  aesop

end HypoellipticAleksandrov.KineticAleksandrov.Green
