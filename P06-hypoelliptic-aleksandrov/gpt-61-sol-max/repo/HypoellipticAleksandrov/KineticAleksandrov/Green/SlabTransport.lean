module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabSetting

/-!
# Transport of the slab measure to the regrouped carrier

Bookkeeping for `Green.SlabDensity`: the regrouping `(τ,(w,z)) ↦ ((τ,w),z)` carries the slab
restriction of `Γ` to `slabMeasure`, carries Lebesgue measure on the slab to `m ⊗ Leb`, and
transfers densities and the regrouped marginal and Fourier-marginal identities.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- Density transport along a measure-preserving measurable equivalence. -/
lemma eq_withDensity_of_map_eq {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (e : X ≃ᵐ Z) {ν : Measure X} {ρ : Measure Z} (he : MeasurePreserving e ν ρ)
    {Γ' : Measure X} {G' : Z → ℝ≥0∞} (hG : Γ'.map e = ρ.withDensity G') :
    Γ' = ν.withDensity (fun x => G' (e x)) := by
  ext B hB
  have h1 : Γ' B = (Γ'.map e) (e.symm ⁻¹' B) := by
    rw [e.map_apply]
    congr 1
    ext x
    simp

  rw [h1, hG, withDensity_apply _ (e.symm.measurable hB), withDensity_apply _ hB]
  have := he.setLIntegral_comp_preimage_emb e.measurableEmbedding G' (e.symm ⁻¹' B)
  rw [← this]
  congr 2
  ext x
  simp

/-- The regrouping carries Lebesgue measure on the slab to `slabBase ⊗ Leb`. -/
lemma measurePreserving_slabRegroup (d : ℕ) (T : ℝ) :
    MeasurePreserving (slabRegroup d) ((greenLebesgue d).restrict (slabSet T))
      ((slabBase d T).prod volume) := by
  have h : (greenLebesgue d).restrict (slabSet T) =
      ((elapsedVolume ⊤).restrict (slabTimeSet T)).prod
        (volume : Measure (EvolutionAmbientState d)) := by
    unfold greenLebesgue slabSet
    have := Measure.prod_restrict (μ := elapsedVolume ⊤)
      (ν := (volume : Measure (EvolutionAmbientState d))) (slabTimeSet T) univ
    rw [Measure.restrict_univ, Set.prod_univ] at this
    exact this.symm
  rw [h]
  exact (measurePreserving_prodAssoc _ _ _).symm


variable {d : ℕ} (T : ℝ)

/-- The preimage of a base set under the regrouping, intersected with the slab. -/
lemma regroup_preimage_prod  (E : Set (SlabBase d)) :
    (slabRegroup d) ⁻¹' (E ×ˢ (univ : PDE.VelocityRegion d)) ∩ slabSet T =
      {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} := by
  ext p
  simp [slabRegroup, slabSet, slabTimeSet, MeasurableEquiv.prodAssoc, and_comm]

variable (Γ : Measure (GreenCarrier d))

/-- Total mass of the regrouped slab measure. -/
lemma slabMeasure_univ   :
    slabMeasure d T Γ univ = Γ (slabSet T) := by
  unfold slabMeasure
  rw [MeasurableEquiv.map_apply, preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    univ_inter]

/-- The marginal identity of Lemma 5.1 for the regrouped slab measure. -/
lemma slabMeasure_fst
    (g : SlabBase d → ℝ≥0∞)
    (hg : ∀ E : Set (SlabBase d), MeasurableSet E →
      Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
        ∫⁻ y in E, g y ∂slabBase d T) :
    (slabMeasure d T Γ).fst = (slabBase d T).withDensity g := by
  ext E hE
  rw [Measure.fst_apply hE, withDensity_apply _ hE]
  unfold slabMeasure
  rw [MeasurableEquiv.map_apply, Measure.restrict_apply
    ((slabRegroup d).measurable (measurable_fst hE)), ← hg E hE,
    ← regroup_preimage_prod T E]
  congr 2
  ext p
  simp [slabRegroup, MeasurableEquiv.prodAssoc]

/-- The Fourier-marginal identity of Lemma 5.1 for the regrouped slab measure. -/
lemma slabMeasure_fourier
    (ξ : PDE.Vec d) (k : SlabBase d → ℂ)
    (hk : ∀ E : Set (SlabBase d), MeasurableSet E →
      ∫ y in E, k y ∂slabBase d T =
        ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
          Complex.exp (-((PDE.vecDot ξ p.2.2 ) * Complex.I)) ∂Γ)
    (E : Set (SlabBase d)) (hE : MeasurableSet E) :
    ∫ y in E, k y ∂slabBase d T =
      ∫ p in E ×ˢ (univ : PDE.VelocityRegion d),
        Complex.exp (-((PDE.vecDot ξ p.2 ) * Complex.I)) ∂slabMeasure d T Γ := by
  rw [hk E hE]
  unfold slabMeasure
  rw [MeasureTheory.setIntegral_map_equiv, Measure.restrict_restrict
    ((slabRegroup d).measurable (hE.prod MeasurableSet.univ)), regroup_preimage_prod T E]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Green
