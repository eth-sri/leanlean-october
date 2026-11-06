module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Inputs: the space `L^p(ℝ₊; U)`, concatenation, shifts and truncations

This file contains the measure-theoretic plumbing on inputs used throughout the
development. Nothing here is specific to control systems.

## Conventions

* `L^p(ℝ₊; U)` is Mathlib's `Lp U p muPlus`, where `muPlus` is Lebesgue measure
  restricted to `ℝ₊ = [0, ∞)`. Its elements are almost-everywhere classes;
  `⇑u : ℝ → U` is an (arbitrary) representative, whose values at negative times
  are irrelevant.
* The `τ`-concatenation `u ⋄_τ v` of the paper is `concat τ u v`, defined on raw
  functions `ℝ → U`. Statements about inputs are phrased as "`w` is an element of
  `L^p(ℝ₊; U)` whose representative is a.e. equal to `concat τ ⇑u ⇑v`".

## Main declarations

* `muPlus`, `concat`, `ALCS.concat_congr` : definitions, and independence of
  the concatenation from the chosen representatives.
* `ALCS.shiftLeft a u` : the input `s ↦ u (a + s)`; `ALCS.exists_shift` gives
  `u = u ⋄_a (shiftLeft a u)`, and `ALCS.tendsto_norm_shiftLeft_sub` is the
  continuity of translations in `L^p` for `p < ∞`.
* `ALCS.exists_delay` : the delayed input `0 ⋄_a u`, with the same norm bound.
* `ALCS.truncate τ u` : the input `u ⋄_τ 0`; `ALCS.tendsto_norm_truncate` says
  that `‖u‖_{L^p(0, τ)} → 0` as `τ → 0` for `p < ∞`.
* `ALCS.exists_concat` : for `p = ∞`, the concatenation of two inputs of norm
  at most `C` is an input of norm at most `C`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

variable {U : Type*}

/-- Lebesgue measure on `ℝ₊ = [0, ∞)`. -/
noncomputable abbrev muPlus : Measure ℝ := volume.restrict (Set.Ici 0)

/-- The `τ`-concatenation `u ⋄_τ v` of the paper: equal to `u s` for `s < τ` and to
`v (s - τ)` for `s ≥ τ` ("play `u` on `[0, τ)`, then play `v`"). -/
noncomputable def concat (τ : ℝ) (u v : ℝ → U) : ℝ → U :=
  fun s => if s < τ then u s else v (s - τ)

namespace ALCS

/-! ## Translations of the half-line -/

/-! ## Concatenation -/

/-- The concatenation does not depend on the chosen representatives. For the second
argument, the null set has to be transported by a translation. -/
lemma concat_congr {f f' g g' : ℝ → U} (a : ℝ)
    (hf : f =ᵐ[muPlus] f') (hg : g =ᵐ[muPlus] g') :
    concat a f g =ᵐ[muPlus] concat a f' g' := by
  have hm : MeasurePreserving (fun s => -a + s) (volume.restrict (Set.Ici a)) muPlus := by
    have h := (measurePreserving_add_left (volume : Measure ℝ) (-a)).restrict_preimage
      (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
    rwa [Set.preimage_const_add_Ici, zero_sub, neg_neg] at h
  have hg₁ := hm.quasiMeasurePreserving.ae hg
  have hg₂ := (ae_restrict_iff'
    (measurableSet_Ici : MeasurableSet (Set.Ici a))).1 hg₁
  filter_upwards [hf, ae_restrict_of_ae hg₂] with t hft hgt
  by_cases ht : t < a
  · simp [concat, ht, hft]
  · simpa only [concat, ite_eq_right ht, sub_eq_neg_add] using
      hgt (Set.mem_Ici.2 (not_lt.1 ht))

variable [NormedAddCommGroup U]

/-! ## Extension by zero to the whole line -/

/-- Extension by zero to `ℝ` of a function on `ℝ₊`. -/
noncomputable def zeroExt (f : ℝ → U) : ℝ → U := (Set.Ici (0 : ℝ)).indicator f

section General

variable {p : ℝ≥0∞}

lemma memLp_zeroExt (u : Lp U p muPlus) : MemLp (zeroExt ⇑u) p volume :=
  (memLp_indicator_iff_restrict measurableSet_Ici).2 (Lp.memLp u)

/-! ## Left shifts `u ↦ u (a + ·)` -/

/-- The left shift `s ↦ u (a + s)` of an input. (For `a < 0`, the input is first
extended by zero to negative times.) -/
noncomputable def shiftLeft (a : ℝ) (u : Lp U p muPlus) : Lp U p muPlus :=
  (((memLp_zeroExt u).comp_measurePreserving
    (measurePreserving_add_left volume a)).mono_measure Measure.restrict_le_self).toLp
      (zeroExt ⇑u ∘ fun s => a + s)

lemma shiftLeft_ae (a : ℝ) (u : Lp U p muPlus) :
    ⇑(shiftLeft a u) =ᵐ[muPlus] (zeroExt ⇑u ∘ fun s => a + s) :=
  (((memLp_zeroExt u).comp_measurePreserving
    (measurePreserving_add_left volume a)).mono_measure Measure.restrict_le_self).coeFn_toLp

lemma norm_shiftLeft_le (a : ℝ) (u : Lp U p muPlus) : ‖shiftLeft a u‖ ≤ ‖u‖ := by
  rw [shiftLeft, Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
  calc
    eLpNorm (zeroExt ⇑u ∘ fun s => a + s) p muPlus
        ≤ eLpNorm (zeroExt ⇑u ∘ fun s => a + s) p volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (zeroExt ⇑u) p volume := eLpNorm_comp_measurePreserving
      (memLp_zeroExt u).aestronglyMeasurable (measurePreserving_add_left volume a)
    _ = eLpNorm (⇑u) p muPlus := eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici

/-! ## Delays `u ↦ 0 ⋄_a u` -/

/-- Delayed input: the input `0 ⋄_a u` (zero on `[0, a)`, then `u`)
belongs to `L^p(ℝ₊; U)`, with norm at most `‖u‖`. -/
theorem exists_delay (a : ℝ) (u : Lp U p muPlus) :
    ∃ w : Lp U p muPlus, ‖w‖ ≤ ‖u‖ ∧
      ⇑w =ᵐ[muPlus] concat a ⇑(0 : Lp U p muPlus) ⇑u := by
  have hraw : (zeroExt ⇑u ∘ fun s => -a + s) = concat a (fun _ => (0 : U)) ⇑u := by
    funext s
    by_cases h : s < a
    · simp [Function.comp_apply, zeroExt, concat, h]
    · simp [Function.comp_apply, concat, h, neg_add_eq_sub, zeroExt]
  exact ⟨shiftLeft (-a) u, norm_shiftLeft_le _ _, (shiftLeft_ae _ _).trans
    ((Filter.EventuallyEq.of_eq hraw).trans
      (concat_congr a (Lp.coeFn_zero U p muPlus).symm (.refl _ _)))⟩

/-! ## Truncations `u ↦ u ⋄_τ 0` -/

/-! ## Continuity of left shifts for `p < ∞` -/

end General

/-! ## Inputs in `L^∞(ℝ₊; U)` -/

section Infinity

/-- A pointwise bound gives membership in `L^∞`, without a finite-measure assumption. -/
lemma memLp_of_bound {f : ℝ → U} (hf : StronglyMeasurable f)
    {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C) : MemLp f ∞ muPlus :=
  memLp_top_of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

/-- The representative of an `L^∞` class obeys its norm bound a.e. -/
lemma ae_norm_le (u : Lp U ∞ muPlus) : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ ‖u‖ := by
  have htop := eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑u) muPlus] with t ht
  rw [← htop] at ht
  simpa only [Lp.norm_def, htop, toReal_enorm] using
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top u) ht

/-- An everywhere bounded, strongly measurable representative. -/
lemma exists_bounded_rep (u : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ∃ f : ℝ → U, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ C) ∧ ⇑u =ᵐ[muPlus] f := by
  let f : ℝ → U := fun t => if ‖u t‖ ≤ C then u t else 0
  have hf : StronglyMeasurable f := StronglyMeasurable.ite
    ((Lp.stronglyMeasurable u).norm.measurableSet_le stronglyMeasurable_const)
    (Lp.stronglyMeasurable u) stronglyMeasurable_const
  refine ⟨f, hf, (fun t => by dsimp [f]; split_ifs <;> simp_all), ?_⟩
  filter_upwards [ae_norm_le u] with t ht
  simp [f, ht.trans hu]

/-- The `L^∞` class of a bounded raw function has the same bound. -/
lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top hf.aestronglyMeasurable]
  calc
    (eLpNormEssSup f muPlus).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (eLpNormEssSup_le_of_ae_bound (.of_forall hb))
    _ = C := ENNReal.toReal_ofReal hC

/-- For `p = ∞`, concatenation preserves a common norm bound. -/
lemma exists_concat (a : ℝ) (u v : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ C ∧ ⇑w =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u hC hu
  obtain ⟨g, hg, hgb, hvg⟩ := exists_bounded_rep v hC hv
  have hb (t : ℝ) : ‖concat a f g t‖ ≤ C := by
    by_cases ht : t < a
    · simpa [concat, ht] using hfb t
    · simpa [concat, ht] using hgb (t - a)
  have hm := memLp_of_bound (StronglyMeasurable.ite measurableSet_Iio hf
    (hg.comp_measurable (measurable_id.sub_const a))) hb
  exact ⟨hm.toLp _, norm_toLp_le hm hC hb, hm.coeFn_toLp.trans (concat_congr a huf hvg).symm⟩

end Infinity

end ALCS
