module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakTesting
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Bounded signed-source distributional Duhamel identity

The smooth identity determines two finite positive source measures. Their equality
extends the identity to bounded Borel sources without pointwise smooth approximation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

variable (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (S : TerminalOperatorFamily Ω γ)
    (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g) (M : ℝ) (hM : 0 ≤ M)
    (hgb : ∀ p, |g p| ≤ M) (T : ℝ) {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
include hΩa hγ hreal hB hBs hb hg hM hgb

include hψ hc hψs in
/-- The bounded-source weak identity in product coordinates. -/
theorem duhamel_bounded_product_identity :
    (∫ q, transportedAdjoint B b ψ (packQ d q) *
      duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) =
      -(∫ q, ψ (packQ d q) * g ⟨q.1, q.2.1, q.2.2⟩) := by
  let Λ : ℝ × EvolutionAmbientState d → ℝ := fun q => transportedAdjoint B b ψ (packQ d q)
  let Ψ := fun q => ψ (packQ d q)
  have hΛ : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛc : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨ := hψ.continuous.comp continuous_packQ
  have hΨc := hasCompactSupport_comp_packQ hc
  have hpreΨ : tsupport Ψ = (packQ d) ⁻¹' tsupport ψ := by
    change tsupport (ψ ∘ (evolutionProdCLE d).symm.toHomeomorph) = _
    rw [tsupport_comp_eq_preimage]
    rfl
  have hpreΛ : tsupport Λ = (packQ d) ⁻¹' tsupport (transportedAdjoint B b ψ) := by
    change tsupport (transportedAdjoint B b ψ ∘ (evolutionProdCLE d).symm.toHomeomorph) = _
    rw [tsupport_comp_eq_preimage]
    rfl
  have hΨU : tsupport Ψ ⊆ boundedSourcePast Ω γ T := by
    rw [hpreΨ]
    intro q hq
    have hp := hψs hq
    change evolutionHomeomorph d (packQ d q) ∈ evolutionPastOpenCylinder Ω γ T at hp
    rw [duhamel_homeomorph_packQ] at hp
    exact hp
  have hΛU : tsupport Λ ⊆ boundedSourcePast Ω γ T := by
    rw [hpreΛ]
    intro q hq
    apply hΨU
    rw [hpreΨ]
    exact boundedSourceAdjoint_support ψ hq
  obtain ⟨a, haT, hfloor⟩ := exists_boundedSource_test_floor Λ hΛc T
  have heq := weakSourceMeasures_eq_of_smooth_identity K (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ Λ Ψ hΛ hΛc hΨ hΨc
    a T haT hfloor hΛU hΨU (fun φ hφ hφc hφU hφr =>
      duhamel_smooth_product_identity hΩa hΩ hγ B b S K hreal hB hBs hb T
        hψ hc hψs φ hφ hφc hφU hφr)
  have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
  have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
  have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
  have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
  let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
  let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
  let f : ℝ × EvolutionAmbientState d → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩
  have hf := hg.comp (KineticPoint.measurable_equivProd_symm d)
  have hfb : ∀ q, |f q| ≤ M := fun q => hgb _
  have hμ := integrable_bounded_real μ f hf M hfb
  have hμn := integrable_bounded_real μn f hf M hfb
  have hν := integrable_bounded_real (sourcePositiveMeasure Ψ) f hf M hfb
  have hνn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) f hf M hfb
  have hint : (∫ q, f q ∂(μ + sourcePositiveMeasure Ψ)) =
      ∫ q, f q ∂(μn + sourcePositiveMeasure (fun q => -Ψ q)) :=
    congrArg (fun ν => ∫ q, f q ∂ν) heq
  rw [integral_add_measure hμ hν, integral_add_measure hμn hνn] at hint
  have hact := integral_boundedSourceAction_positive_potential K hΩ hγ
    Λ hΛ hΛc a T hfloor g hg M hM hgb
  have hactn := integral_boundedSourceAction_positive_potential K hΩ hγ
    (fun q => -Λ q) hΛ.neg hΛc.neg a T (fun q hq => hfloor q (neg_ne_zero.mp hq)) g hg M hM hgb
  rw [hact, hactn, (integral_sourcePositiveMeasure Ψ hΨ.measurable f), (integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable f)] at hint
  let W : ℝ × EvolutionAmbientState d → ℝ :=
    fun q => duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
  have hWb : ∀ q, Λ q ≠ 0 → |W q| ≤ (T - a) * M := by
    intro q hq
    exact (abs_duhamelPotential_le K g M hM hgb ⟨q.1, q.2.1, q.2.2⟩ T ((hΛU (subset_tsupport Λ hq)).1).le).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left (hfloor q hq) T) hM)
  have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc W ((measurable_duhamelPotential K hΩ hγ T g hg).comp (KineticPoint.measurable_equivProd_symm d))
    ((T - a) * M) (mul_nonneg (sub_nonneg.mpr haT.le) hM) hWb
  have hsubbase := integral_positive_negative_weight_sub Ψ hΨ hΨc f hf M hM
    (fun q _ => hfb q)
  linarith

include hψ hc hψs in
/-- The signed bounded Borel identity in the existing transported coordinates. -/
theorem duhamel_bounded_weak_identity :
    (∫ q, transportedAdjoint B b ψ q *
      duhamelPotential K T g (evolutionHomeomorph d q)) =
      -(∫ q, ψ q * g (evolutionHomeomorph d q)) := by
  rw [integral_evolution_eq_prod, integral_evolution_eq_prod]
  simp only [duhamel_homeomorph_packQ]
  exact duhamel_bounded_product_identity hΩa hΩ hγ B b S K hreal hB hBs hb
    g hg M hM hgb T hψ hc hψs

/-- Bounded Borel sources give the existing kinetic weak-solution carrier. -/
theorem duhamel_bounded_isKineticWeakTransportedSolution :
    IsKineticWeakTransportedSolution B b (evolutionPastOpenCylinder Ω γ T)
      (duhamelPotential K T g) (fun p => -g p) := by
  have hU := (isOpen_duhamelCylinder
    (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T).preimage
      (evolutionHomeomorph d).continuous
  have hbound : Continuous (fun q : EvolutionVec d =>
      |T - (evolutionHomeomorph d q).time| * M) :=
    (continuous_const.sub (continuous_time.comp
      (evolutionHomeomorph d).continuous)).abs.mul continuous_const
  have hloc := hbound.continuousOn.locallyIntegrableOn
    (μ := volume) hU.measurableSet
  have hW := hloc.mono ((measurable_duhamelPotential K hΩ hγ T g hg).comp (evolutionHomeomorph d).continuous.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) hM)]
      apply abs_duhamelPotential_le_abs_time <;> assumption)
  apply (isWeakTransportedSolution_comp_iff B b _ _ _).1
  refine ⟨hW, fun ψ hψ hc hs => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [Function.comp_apply, neg_mul, integral_neg]
    simpa only [mul_comm] using (duhamel_bounded_weak_identity hΩa hΩ hγ B b S K hreal hB hBs hb g hg M hM hgb T hψ hc hs)
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
