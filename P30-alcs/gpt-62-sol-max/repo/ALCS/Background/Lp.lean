module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! # Translations and concatenation of inputs on the half-line -/

open MeasureTheory Filter Set
open scoped ENNReal

variable {U : Type*}

/-- Lebesgue measure on the nonnegative half-line. -/
noncomputable abbrev muPlus : Measure ℝ := volume.restrict (Ici 0)

/-- Play `u` before time `a`, and then start `v`. -/
noncomputable def concat (a : ℝ) (u v : ℝ → U) (t : ℝ) : U :=
  if t < a then u t else v (t - a)

namespace ALCS

lemma concat_congr {f f' g g' : ℝ → U} (a : ℝ)
    (hf : f =ᵐ[muPlus] f') (hg : g =ᵐ[muPlus] g') :
    concat a f g =ᵐ[muPlus] concat a f' g' := by
  have hm : MeasurePreserving (fun t => t - a) (volume.restrict (Ici a)) muPlus := by
    simpa only [preimage_sub_const_Ici, zero_add] using
      (measurePreserving_sub_right volume a).restrict_preimage (measurableSet_Ici (a := (0 : ℝ)))
  filter_upwards [hf, ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ici).1 (hm.quasiMeasurePreserving.ae hg))]
    with t h₁ h₂
  grind [concat]

variable [NormedAddCommGroup U] {p : ℝ≥0∞}

lemma concat_measurable (a : ℝ) {f g : ℝ → U} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (concat a f g) :=
  .ite measurableSet_Iio hf (hg.comp_measurable (measurable_id.sub_const a))

/-- Translate an input after extending it by zero to the whole line. -/
private lemma exists_translate (a : ℝ) (u : Lp U p muPlus) :
    ∃ v : Lp U p muPlus, ‖v‖ ≤ ‖u‖ ∧
      ⇑v =ᵐ[muPlus] fun t => (Ici (0 : ℝ)).indicator ⇑u (t - a) := by
  have h := (memLp_indicator_iff_restrict measurableSet_Ici).2 (Lp.memLp u)
  have ha := measurePreserving_sub_right (volume : Measure ℝ) a
  have hv := (h.comp_measurePreserving ha).mono_measure (ν := muPlus) Measure.restrict_le_self
  refine ⟨hv.toLp _, ?_, hv.coeFn_toLp⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
  grw [eLpNorm_mono_measure _ Measure.restrict_le_self,
    eLpNorm_comp_measurePreserving h.aestronglyMeasurable ha,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici]

theorem exists_shift (a : ℝ) (u : Lp U p muPlus) :
    ∃ v : Lp U p muPlus, ‖v‖ ≤ ‖u‖ ∧ ⇑u =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨v, hv, he⟩ := exists_translate (-a) u
  refine ⟨v, hv, ((concat_congr a .rfl he).trans ?_).symm⟩
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with t ht
  simp [concat, indicator_of_mem ht]

theorem exists_delay (a : ℝ) (u : Lp U p muPlus) :
    ∃ v : Lp U p muPlus, ‖v‖ ≤ ‖u‖ ∧ ⇑v =ᵐ[muPlus] concat a 0 ⇑u := by
  obtain ⟨v, hv, he⟩ := exists_translate a u
  exact ⟨v, hv, he.trans (.of_forall fun t => by simp [indicator, concat, ← not_lt])⟩

lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ t ∂muPlus, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound h)

end ALCS
