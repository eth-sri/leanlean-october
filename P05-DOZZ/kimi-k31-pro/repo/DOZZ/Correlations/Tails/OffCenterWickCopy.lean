/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterPinCopy
public import DOZZ.Correlations.Tails.OffCenterWickLaw

/-! The independent pin copy at the level of weighted regularized masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The copied local circle field used in the one-insertion tail estimate. -/
noncomputable def copiedCircle {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ)
    (z : ℂ) (q : Ω × Ω) (p : localCircle) : ℝ :=
  Xc q.2 z 0 + (Xc q.1 (z + p.val.1) p.val.2 - Xc q.1 z 0) +
    localPinCoefficient z p.val.1 * (Xc q.2 z 0 - Xc q.1 z 0)

/-- The original translated circle law retains the pin-dependent variance. -/
theorem offCenter_circle_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    HasLaw (fun ω => Xc ω (z + p.val.1) p.val.2)
      (gaussianReal 0 (p.val.2 + 2 * Real.log ‖z + p.val.1‖).toNNReal) P := by
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hg := hG.hasGaussianLaw_eval (z + p.val.1, p.val.2)
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, hm, ← covariance_self hg.aemeasurable,
    offCenter_circle_self_covariance P X Xc hX hc z hz p]

/-- The field replacement preserves every finite local circle vector. -/
theorem copied_circle_fdd_law
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : ι → localCircle) :
    P.map (fun ω i => Xc ω (z + (p i).val.1) (p i).val.2) =
      (P.prod P).map (fun q i => copiedCircle Xc z q (p i)) := by
  let S : Ω → Option localCircle → ℝ := fun ω j =>
    j.elim (Xc ω z 0) (fun p => Xc ω (z + p.val.1) p.val.2)
  let T : Ω × Ω → Option localCircle → ℝ := fun q j =>
    j.elim (Xc q.2 z 0) (fun p => copiedCircle Xc z q p)
  have hS : Measurable S := by
    apply measurable_pi_iff.mpr
    intro j
    cases j with
    | none => exact hm.comp (measurable_id.prodMk (measurable_const (a := (z, (0 : ℝ)))))
    | some p => exact hm.comp (measurable_id.prodMk
        (measurable_const (a := (z + p.val.1, p.val.2))))
  have hT : Measurable T := by
    apply measurable_pi_iff.mpr
    intro j
    have h1 (x : ℂ) (r : ℝ) : Measurable (fun q : Ω × Ω => Xc q.1 x r) :=
      hm.comp (measurable_fst.prodMk (measurable_const (a := (x, r))))
    have h2 (x : ℂ) (r : ℝ) : Measurable (fun q : Ω × Ω => Xc q.2 x r) :=
      hm.comp (measurable_snd.prodMk (measurable_const (a := (x, r))))
    cases j with
    | none => exact h2 z 0
    | some p =>
      exact ((h2 z 0).add ((h1 _ _).sub (h1 z 0))).add
        (((h2 z 0).sub (h1 z 0)).const_mul _)
  let E : (Option localCircle → ℝ) → ι → ℝ := fun f i => f (some (p i))
  have hE : Measurable E := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have h := congrArg (fun μ => μ.map E)
    (offCenter_circle_pin_copy_law P X Xc hX hc hm z hz)
  change (P.map S).map E = ((P.prod P).map T).map E at h
  rw [Measure.map_map hE hS, Measure.map_map hE hT] at h
  exact h

/-- The copied circle has the original scalar Gaussian law. -/
theorem copied_circle_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    HasLaw (fun q => copiedCircle Xc z q p)
      (gaussianReal 0 (p.val.2 + 2 * Real.log ‖z + p.val.1‖).toNNReal) (P.prod P) := by
  have he := copied_circle_fdd_law (ι := Unit) P X Xc hX hc hm z hz (fun _ => p)
  have hmS : Measurable (fun ω (_ : Unit) => Xc ω (z + p.val.1) p.val.2) :=
    measurable_pi_iff.mpr fun _ => hm.comp (measurable_id.prodMk
      (measurable_const (a := (z + p.val.1, p.val.2))))
  have hmT : Measurable (fun q (_ : Unit) => copiedCircle Xc z q p) := by
    apply measurable_pi_iff.mpr
    intro i
    unfold copiedCircle
    have h1 (x : ℂ) (r : ℝ) : Measurable (fun q : Ω × Ω => Xc q.1 x r) :=
      hm.comp (measurable_fst.prodMk (measurable_const (a := (x, r))))
    have h2 (x : ℂ) (r : ℝ) : Measurable (fun q : Ω × Ω => Xc q.2 x r) :=
      hm.comp (measurable_snd.prodMk (measurable_const (a := (x, r))))
    exact ((h2 z 0).add ((h1 _ _).sub (h1 z 0))).add
      (((h2 z 0).sub (h1 z 0)).const_mul _)
  have he' := congrArg (fun μ => μ.map (fun f : Unit → ℝ => f ())) he
  rw [Measure.map_map (measurable_pi_apply ()) hmS,
    Measure.map_map (measurable_pi_apply ()) hmT] at he'
  exact ⟨((measurable_pi_apply ()).comp hmT).aemeasurable,
    he'.symm.trans (offCenter_circle_hasLaw P X Xc hX hc z hz p).map_eq⟩

end DOZZ.Proofs
