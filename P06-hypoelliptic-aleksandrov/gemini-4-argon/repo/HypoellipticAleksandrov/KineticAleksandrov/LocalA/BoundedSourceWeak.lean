module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakTesting
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakDetermination
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelWeak

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
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- The bounded-source weak identity in product coordinates. -/
theorem duhamel_bounded_isKineticWeakTransportedSolution
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (T : ℝ) :
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
    (μ := (volume : Measure (EvolutionVec d))) hU.measurableSet
  have hmeas := (measurable_duhamelPotential K hΩ hγ T g hg).comp
    (evolutionHomeomorph d).continuous.measurable
  have hW := hloc.mono hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) hM)]
      exact abs_duhamelPotential_le_abs_time K g M hM hgb _ T)
  apply (isWeakTransportedSolution_comp_iff B b _ _ _).1
  refine ⟨hW, fun ψ hψ hc hs => ?_⟩
  have hfull : (∫ q, transportedAdjoint B b ψ q *
      duhamelPotential K T g (evolutionHomeomorph d q)) =
      -(∫ q, ψ q * g (evolutionHomeomorph d q)) := by
    rw [integral_evolution_eq_prod, integral_evolution_eq_prod]
    simp only [duhamel_homeomorph_packQ]
    let Λ : ℝ × EvolutionAmbientState d → ℝ := fun q => transportedAdjoint B b ψ (packQ d q)
    let Ψ : ℝ × EvolutionAmbientState d → ℝ := fun q => ψ (packQ d q)
    have hΛ : Continuous Λ :=
      (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
    have hΛc : HasCompactSupport Λ :=
      hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
    have hΨ : Continuous Ψ := hψ.continuous.comp continuous_packQ
    have hΨc : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
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
      have hp := hs hq
      change evolutionHomeomorph d (packQ d q) ∈ evolutionPastOpenCylinder Ω γ T at hp
      rw [duhamel_homeomorph_packQ] at hp
      exact hp
    have hΛU : tsupport Λ ⊆ boundedSourcePast Ω γ T := by
      rw [hpreΛ]
      intro q hq
      apply hΨU
      rw [hpreΨ]
      exact boundedSourceAdjoint_support ψ hq
    obtain ⟨a, haT, hfloor⟩ : ∃ a : ℝ, a < T ∧ ∀ q, Λ q ≠ 0 → a ≤ q.1 := by
      obtain ⟨lower, hLower⟩ := (hΛc.image continuous_fst).bddBelow
      refine ⟨min lower (T - 1), ?_, ?_⟩
      · exact (min_le_right lower (T - 1)).trans_lt (by linarith)
      · intro q hq
        exact (min_le_left lower (T - 1)).trans (hLower ⟨q, subset_tsupport Λ hq, rfl⟩)
    have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩa
    have heq : weakSourcePositiveMeasure K Λ Ψ a T = weakSourceNegativeMeasure K Λ Ψ a T := by
      have hidentity := (fun φ hφ hφc hφU hφr =>
        duhamel_smooth_product_identity hΩa hΩ hγ B b S K hreal hB hBs hb T
          hψ hc hs φ hφ hφc hφU hφr)
      have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
      have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
      have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
      have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
      let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
      let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
      have hfin : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
      have hnfin : IsFiniteMeasure μn := by dsimp only [μn]; infer_instance
      change μ + sourcePositiveMeasure Ψ = μn + sourcePositiveMeasure (fun q => -Ψ q)
      have hU := measurableSet_boundedSourcePast hΩo.measurableSet hγ T
      apply measure_eq_of_smooth_integral_eq (isOpen_boundedSourcePast hΩo hγ T)
      · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past K hΩo.measurableSet hγ,
          sourcePositiveMeasure_compl_eq_zero Ψ hU hΨU, add_zero]
      · rw [Measure.add_apply, boundedSourceActionMeasure_compl_past K hΩo.measurableSet hγ,
          sourcePositiveMeasure_compl_eq_zero (fun q => -Ψ q) hU
            (by rw [tsupport_neg_weight]; exact hΨU), add_zero]
      intro φ hφ hφc hφU hφr
      have hφb : ∀ q, |φ q| ≤ 1 := fun q => by
        rw [abs_of_nonneg (hφr q).1]
        exact (hφr q).2
      have hφm := hφ.continuous.measurable
      have hφμ := integrable_bounded_real μ φ hφm 1 hφb
      have hφμn := integrable_bounded_real μn φ hφm 1 hφb
      have hφΨ := integrable_bounded_real (sourcePositiveMeasure Ψ) φ hφm 1 hφb
      have hφΨn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) φ hφm 1 hφb
      rw [integral_add_measure hφμ hφΨ, integral_add_measure hφμn hφΨn]
      let g := φ ∘ KineticPoint.equivProd d
      have hgm : Measurable g := hφm.comp (KineticPoint.measurable_equivProd d)
      have hgb : ∀ p, |g p| ≤ 1 := fun p => hφb _
      have hfloorN : ∀ q, -Λ q ≠ 0 → a ≤ q.1 := fun q hq => hfloor q (neg_ne_zero.mp hq)
      have hact := integral_boundedSourceAction_positive_potential K hΩo.measurableSet hγ
        Λ hΛ hΛc a T hfloor g hgm 1 zero_le_one hgb
      have hactn := integral_boundedSourceAction_positive_potential K hΩo.measurableSet hγ
        (fun q => -Λ q) hΛ.neg hΛc.neg a T hfloorN g hgm 1 zero_le_one hgb
      have hbase := integral_sourcePositiveMeasure Ψ hΨ.measurable φ
      have hbasen := integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable φ
      have hWm : Measurable (fun q : ℝ × EvolutionAmbientState d =>
          duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩) :=
        (measurable_duhamelPotential K hΩo.measurableSet hγ T g hgm).comp
          (KineticPoint.measurable_equivProd_symm d)
      have hWb : ∀ q, Λ q ≠ 0 →
          |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - a := by
        intro q hq
        have ht := (hΛU (subset_tsupport Λ hq)).1
        have hbnd := abs_duhamelPotential_le K g 1 zero_le_one hgb
          ⟨q.1, q.2.1, q.2.2⟩ T ht.le
        have hpoint : |duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩| ≤ T - q.1 := by
          simpa only [mul_one] using hbnd
        exact hpoint.trans (sub_le_sub_left (hfloor q hq) T)
      have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc _ hWm
        (T - a) (sub_nonneg.mpr haT.le) hWb
      have hsubbase := integral_positive_negative_weight_sub Ψ hΨ hΨc φ hφm
        1 zero_le_one (fun q _ => hφb q)
      have hid := hidentity φ hφ hφc hφU hφr
      change (∫ q, φ q ∂μ) = _ at hact
      change (∫ q, φ q ∂μn) = _ at hactn
      rw [hact, hactn, hbase, hbasen]
      linarith only [hsub, hsubbase, hid]
    have hΛstart := sourcePositiveStartMeasure_isFinite Λ hΛ hΛc
    have hΛnstart := sourcePositiveStartMeasure_isFinite (fun q => -Λ q) hΛ.neg hΛc.neg
    have hΨfin := sourcePositiveMeasure_isFinite Ψ hΨ hΨc
    have hΨnfin := sourcePositiveMeasure_isFinite (fun q => -Ψ q) hΨ.neg hΨc.neg
    let μ := boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T
    let μn := boundedSourceActionMeasure K (sourcePositiveStartMeasure (fun q => -Λ q)) a T
    have hfin : IsFiniteMeasure μ := by dsimp only [μ]; infer_instance
    have hnfin : IsFiniteMeasure μn := by dsimp only [μn]; infer_instance
    let f : ℝ × EvolutionAmbientState d → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩
    have hf : Measurable f := hg.comp (KineticPoint.measurable_equivProd_symm d)
    have hfb : ∀ q, |f q| ≤ M := fun q => hgb _
    have hμ := integrable_bounded_real μ f hf M hfb
    have hμn := integrable_bounded_real μn f hf M hfb
    have hν := integrable_bounded_real (sourcePositiveMeasure Ψ) f hf M hfb
    have hνn := integrable_bounded_real (sourcePositiveMeasure (fun q => -Ψ q)) f hf M hfb
    have hint : (∫ q, f q ∂(μ + sourcePositiveMeasure Ψ)) =
        ∫ q, f q ∂(μn + sourcePositiveMeasure (fun q => -Ψ q)) :=
      congrArg (fun ν => ∫ q, f q ∂ν) heq
    rw [integral_add_measure hμ hν, integral_add_measure hμn hνn] at hint
    have hfloorN : ∀ q, -Λ q ≠ 0 → a ≤ q.1 := fun q hq => hfloor q (neg_ne_zero.mp hq)
    have hact := integral_boundedSourceAction_positive_potential K hΩ hγ
      Λ hΛ hΛc a T hfloor g hg M hM hgb
    have hactn := integral_boundedSourceAction_positive_potential K hΩ hγ
      (fun q => -Λ q) hΛ.neg hΛc.neg a T hfloorN g hg M hM hgb
    have hbase := integral_sourcePositiveMeasure Ψ hΨ.measurable f
    have hbasen := integral_sourcePositiveMeasure (fun q => -Ψ q) hΨ.neg.measurable f
    change (∫ q, f q ∂μ) = _ at hact
    change (∫ q, f q ∂μn) = _ at hactn
    rw [hact, hactn, hbase, hbasen] at hint
    let W : ℝ × EvolutionAmbientState d → ℝ :=
      fun q => duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
    have hWm : Measurable W :=
      (measurable_duhamelPotential K hΩ hγ T g hg).comp
        (KineticPoint.measurable_equivProd_symm d)
    have hWb : ∀ q, Λ q ≠ 0 → |W q| ≤ (T - a) * M := by
      intro q hq
      have ht := (hΛU (subset_tsupport Λ hq)).1
      exact (abs_duhamelPotential_le K g M hM hgb ⟨q.1, q.2.1, q.2.2⟩ T ht.le).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_left (hfloor q hq) T) hM)
    have hsub := integral_positive_negative_weight_sub Λ hΛ hΛc W hWm
      ((T - a) * M) (mul_nonneg (sub_nonneg.mpr haT.le) hM) hWb
    have hsubbase := integral_positive_negative_weight_sub Ψ hΨ hΨc f hf M hM
      (fun q _ => hfb q)
    change (∫ q, Λ q * W q) = -(∫ q, Ψ q * f q)
    linarith only [hint, hsub, hsubbase]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [Function.comp_apply, neg_mul, integral_neg]
    simpa only [mul_comm] using hfull
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
