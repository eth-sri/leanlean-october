module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Inputs: the space `L^∞(ℝ₊; U)`, concatenation and shifts

Measure-theoretic plumbing on `L^∞` inputs. `L^∞(ℝ₊; U)` is Mathlib's
`Lp U ∞ muPlus`, where `muPlus` is Lebesgue measure restricted to `ℝ₊ = [0, ∞)`;
its elements are a.e. classes. The `τ`-concatenation `u ⋄_τ v` of the paper is
`concat τ u v`, a pointwise operation on raw functions; statements about inputs
are phrased as "`w` is an `L^∞` class whose representative is a.e. equal to
`concat τ ⇑u ⇑v`".

## Main declarations

* `muPlus`, `concat`, `concat_congr`;
* `exists_toLp_le`: a bounded strongly measurable raw function yields an `L^∞`
  class of the same bound;
* `exists_concat`: for `p = ∞` the concatenation of two inputs of norm at most
  `C` is an input of norm at most `C`;
* `exists_delay`, `exists_shift`: the delayed input `0 ⋄_a u` and the shifted
  input `u (a + ·)`, both of norm at most `‖u‖`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

variable {U : Type*} [NormedAddCommGroup U]

/-- Lebesgue measure on `ℝ₊ = [0, ∞)`. -/
noncomputable abbrev muPlus : Measure ℝ := volume.restrict (Set.Ici 0)

/-- The `τ`-concatenation `u ⋄_τ v` of the paper: equal to `u s` for `s < τ` and to
`v (s - τ)` for `s ≥ τ` ("play `u` on `[0, τ)`, then play `v`"). -/
noncomputable def concat (τ : ℝ) (u v : ℝ → U) : ℝ → U :=
  fun s => if s < τ then u s else v (s - τ)

namespace ALCS

/-! ## Concatenation -/

/-- `s ↦ -a + s` sends `[a, ∞)` to `ℝ₊`, preserving Lebesgue measure. -/
theorem measurePreserving_unshift (a : ℝ) :
    MeasurePreserving (fun s => -a + s) (volume.restrict (Set.Ici a)) muPlus := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) (-a)).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
  rwa [Set.preimage_const_add_Ici, zero_sub, neg_neg] at h

/-- The concatenation does not depend on the chosen representatives. For the second
argument, the null set has to be transported by a translation. -/
lemma concat_congr {f f' g g' : ℝ → U} (a : ℝ)
    (hf : f =ᵐ[muPlus] f') (hg : g =ᵐ[muPlus] g') :
    concat a f g =ᵐ[muPlus] concat a f' g' := by
  have hg₁ := (measurePreserving_unshift a).quasiMeasurePreserving.ae hg
  have hg₂ := (ae_restrict_iff'
    (measurableSet_Ici : MeasurableSet (Set.Ici a))).1 hg₁
  filter_upwards [hf, ae_restrict_of_ae hg₂] with t hft hgt
  by_cases ht : t < a
  · simp [concat, ht, hft]
  · simpa only [concat, ite_eq_right ht, sub_eq_neg_add] using
      hgt (Set.mem_Ici.2 (not_lt.1 ht))

lemma concat_stronglyMeasurable {f g : ℝ → U}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (a : ℝ) :
    StronglyMeasurable (concat a f g) :=
  StronglyMeasurable.ite measurableSet_Iio hf
    (hg.comp_measurable (measurable_id.sub_const a))

/-! ## Inputs in `L^∞(ℝ₊; U)` -/

/-- The `L^∞` norm is bounded by any nonnegative a.e. bound. -/
lemma lp_norm_le {u : Lp U ∞ muPlus} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ C) : ‖u‖ ≤ C := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  rw [Lp.norm_def, htop]
  calc (eLpNormEssSup (⇑u) muPlus).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hb)
    _ = C := ENNReal.toReal_ofReal hC

/-- The representative of an `L^∞` class obeys its norm bound a.e. -/
lemma ae_norm_le (u : Lp U ∞ muPlus) : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ ‖u‖ := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  have hfin : eLpNormEssSup (⇑u) muPlus ≠ ⊤ := by
    rw [← htop]; exact Lp.eLpNorm_ne_top u
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑u) muPlus] with t ht
  simpa only [Lp.norm_def, htop, toReal_enorm] using ENNReal.toReal_mono hfin ht

/-- The `L^∞` class of a bounded raw function has the same bound. -/
lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  apply lp_norm_le hC
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]
  exact hb t

/-- A bounded strongly measurable raw function yields an `L^∞` class of the same bound. -/
lemma exists_toLp_le {g : ℝ → U} (hg : StronglyMeasurable g) {C : ℝ}
    (hb : ∀ t, ‖g t‖ ≤ C) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ C ∧ ⇑w =ᵐ[muPlus] g := by
  have hm : MemLp g ∞ muPlus :=
    memLp_top_of_bound hg.aestronglyMeasurable C (ae_of_all _ hb)
  exact ⟨hm.toLp g, norm_toLp_le hm ((norm_nonneg _).trans (hb 0)) hb, hm.coeFn_toLp⟩

/-- An input whose representative is pointwise bounded by `C`. The representative is
only modified where it exceeds `C`. -/
lemma exists_bounded_rep (u : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ∃ f : ℝ → U, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ C) ∧ ⇑u =ᵐ[muPlus] f := by
  let f : ℝ → U := fun t => if ‖u t‖ ≤ C then u t else 0
  have hf : StronglyMeasurable f :=
    StronglyMeasurable.ite
      ((Lp.stronglyMeasurable u).norm.measurableSet_le stronglyMeasurable_const)
      (Lp.stronglyMeasurable u) stronglyMeasurable_const
  refine ⟨f, hf, fun t => ?_, ?_⟩
  · by_cases ht : ‖u t‖ ≤ C <;> simp [f, ht, hC]
  · filter_upwards [ae_norm_le u] with t ht
    simp [f, ht.trans hu]

/-- For `p = ∞`, concatenation preserves a common norm bound: if `‖u‖, ‖v‖ ≤ C`, then
`u ⋄_a v` is an input of norm at most `C`. -/
lemma exists_concat (a : ℝ) (u v : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ C ∧ ⇑w =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u hC hu
  obtain ⟨g, hg, hgb, hvg⟩ := exists_bounded_rep v hC hv
  have hb : ∀ t, ‖concat a f g t‖ ≤ C := by
    intro t
    by_cases ht : t < a
    · simpa [concat, ht] using hfb t
    · simpa [concat, ht] using hgb (t - a)
  obtain ⟨w, hw, hw'⟩ := exists_toLp_le (concat_stronglyMeasurable hf hg a) hb
  exact ⟨w, hw, hw'.trans (concat_congr a huf hvg).symm⟩

/-- Delayed input: the input `0 ⋄_a u` (zero on `[0, a)`, then `u`) belongs to
`L^∞(ℝ₊; U)`, with norm at most `‖u‖`. -/
theorem exists_delay (a : ℝ) (u : Lp U ∞ muPlus) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ ‖u‖ ∧
      ⇑w =ᵐ[muPlus] concat a ⇑(0 : Lp U ∞ muPlus) ⇑u :=
  exists_concat a 0 u (norm_nonneg _) (by simp) le_rfl

/-- Shifted input: for `a ≥ 0`, `u₁ := u (a + ·)` satisfies `‖u₁‖ ≤ ‖u‖` and
`u = u ⋄_a u₁`. -/
lemma exists_shift (a : ℝ) (u : Lp U ∞ muPlus) :
    ∃ u₁ : Lp U ∞ muPlus, ‖u₁‖ ≤ ‖u‖ ∧ ⇑u =ᵐ[muPlus] concat a ⇑u ⇑u₁ := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u (norm_nonneg _) le_rfl
  have hg : StronglyMeasurable fun s : ℝ => f (a + s) :=
    hf.comp_measurable (measurable_const.add measurable_id)
  obtain ⟨u₁, hu₁, hu₁'⟩ := exists_toLp_le hg fun t => hfb (a + t)
  refine ⟨u₁, hu₁, huf.trans ?_⟩
  have hpt : f = concat a f (fun s => f (a + s)) := funext fun s => by
    by_cases hs : s < a
    · simp [concat, hs]
    · simp [concat, hs, show a + (s - a) = s by ring]
  rw [hpt]
  exact concat_congr a huf.symm hu₁'.symm

end ALCS
