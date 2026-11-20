/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ChaosLawFDD

/-! Finite-reference spatial integral laws for the inversion regularization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Equality of joint laws gives equality of the second marginals. -/
theorem map_snd_eq_of_joint_law {Ω Ω' E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace F]
    {P : Measure Ω} {P' : Measure Ω'} {a : Ω → E × F} {b : Ω' → E × F}
    (ha : AEMeasurable a P) (hb : AEMeasurable b P') (h : P.map a = P'.map b) :
    P.map (fun ω => (a ω).2) = P'.map (fun ω => (b ω).2) := by
  simpa only [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable ha,
    AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hb, Function.comp_def] using
    congrArg (Measure.map Prod.snd) h

section
variable {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S] [Nonempty S]
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (ν : FiniteMeasure S)

/-- Finite-reference spatial law transfer retains arbitrary auxiliary finite coordinates.
The normalization argument preserves their coupling to the whole sampled field. -/
theorem spatialIntegral_joint_vector_law_of_fdd_finite {k m : ℕ} (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (z : Fin m → S → ℝ → ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) (ν : Measure S))
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) (ν : Measure S))
    (hFDD : ∀ n (xs : Fin n → S), P.map (fun ω => (V ω, fun i => X ω (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Y ω (xs i)))) :
    P.map (fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂(ν : Measure S))) =
      P'.map (fun ω => (V' ω, fun j => ∫ x, z j x (Y ω x) ∂(ν : Measure S))) := by
  classical
  let z' : Fin m → S → ℝ → ℝ := fun j x t => (ν.mass : ℝ) * z j x t
  have hmeasure : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) :=
    congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hint {a : S → ℝ} (ha : Integrable a (ν : Measure S)) :
      Integrable (fun x => (ν.mass : ℝ) * a x) (ν.normalize : Measure S) := by
    by_cases hm : ν.mass = 0
    · simp [hm]
    · rw [hmeasure] at ha
      exact ((integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) (by finiteness)).mp ha).const_mul _
  have he := (chaosLawFDD_of_integrable (ν.normalize : Measure S) X Y V V' z'
    hV hV' hX hY
    (fun j => measurable_const.mul (hz j))
    (fun j => (hintX j).mono fun _ h => hint h) (fun j => (hintY j).mono fun _ h => hint h) hFDD
    (0 : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ)).1
  have hmass (a : S → ℝ) : (∫ x, (ν.mass : ℝ) * a x ∂(ν.normalize : Measure S)) =
      ∫ x, a x ∂(ν : Measure S) := by
    rw [hmeasure, integral_smul_nnreal_measure, integral_const_mul]
    rfl
  simpa only [z', hmass] using he

/-- Measurable fields with equal finite-dimensional laws have equal finite vectors of spatial
integrals against a finite reference measure, whenever the transformed sections are integrable. -/
theorem spatialIntegral_vector_law_of_fdd_finite {m : ℕ} (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (z : Fin m → S → ℝ → ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) (ν : Measure S))
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) (ν : Measure S))
    (hFDD : ∀ n (xs : Fin n → S), P.map (fun ω i => X ω (xs i)) =
      P'.map (fun ω i => Y ω (xs i))) :
    P.map (fun ω j => ∫ x, z j x (X ω x) ∂(ν : Measure S)) =
      P'.map (fun ω j => ∫ x, z j x (Y ω x) ∂(ν : Measure S)) := by
  let V : Fin 0 → ℝ := Fin.elim0
  have hfdd (n : ℕ) (xs : Fin n → S) :
      P.map (fun ω => (V, fun i => X ω (xs i))) = P'.map (fun ω => (V, fun i => Y ω (xs i))) := by
    have hmX : Measurable (fun ω i => X ω (xs i)) :=
      measurable_pi_iff.mpr (fun i => hX.comp (measurable_id.prodMk measurable_const))
    have hmY : Measurable (fun ω i => Y ω (xs i)) :=
      measurable_pi_iff.mpr (fun i => hY.comp (measurable_id.prodMk measurable_const))
    have hL : Measurable (Prod.mk V : (Fin n → ℝ) → _) := measurable_const.prodMk measurable_id
    simpa only [Measure.map_map hL hmX, Measure.map_map hL hmY, Function.comp_def] using
      congrArg (Measure.map (Prod.mk V)) (hFDD n xs)
  have hmX : Measurable (fun ω j => ∫ x, z j x (X ω x) ∂(ν : Measure S)) :=
    measurable_pi_iff.mpr fun j => ((hz j).comp (measurable_snd.prodMk hX)).stronglyMeasurable.integral_prod_right'.measurable
  exact map_snd_eq_of_joint_law (measurable_const.prodMk hmX).aemeasurable (measurable_const.prodMk (measurable_pi_iff.mpr fun j => ((hz j).comp (measurable_snd.prodMk hY)).stronglyMeasurable.integral_prod_right'.measurable)).aemeasurable
    (spatialIntegral_joint_vector_law_of_fdd_finite ν X Y (fun _ => V) (fun _ => V)
      measurable_const measurable_const z hX hY hz hintX hintY hfdd)

end

end DOZZ.Proofs
