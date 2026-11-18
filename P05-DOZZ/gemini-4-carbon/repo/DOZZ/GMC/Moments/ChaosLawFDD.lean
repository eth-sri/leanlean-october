/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import DOZZ.GMC.Moments.ExactScale

/-! Transfer of laws through empirical approximations. -/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory Function
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- An integrable nonnegative spatial weight times a Wick exponential has integrable spatial
sections almost surely. -/
theorem ae_integrable_weighted_wick_sections
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν]
    (W : Ω → S → ℝ) (v : S → ℝ≥0) (w : S → ℝ) (γ : ℝ)
    (hW : Measurable (fun p : Ω × S => W p.1 p.2))
    (hv : Measurable v) (hw : Measurable w)
    (hLaw : ∀ x, HasLaw (fun ω => W ω x) (gaussianReal (0 : ℝ) (v x)) P)
    (hw_nonneg : ∀ x, 0 ≤ w x) (hw_int : Integrable w ν) :
    ∀ᵐ ω ∂P, Integrable (fun x => w x * Real.exp (γ * W ω x - γ ^ 2 / 2 * (v x : ℝ))) ν := by
  let g : Ω × S → ℝ := fun p => w p.2 * Real.exp (γ * W p.1 p.2 - γ ^ 2 / 2 * (v p.2 : ℝ))
  have hg : Measurable g := by fun_prop
  have hpt (x : S) : Integrable (fun ω => g (ω, x)) P ∧ (∫ ω, g (ω, x) ∂P) = w x := by
    have hExpMap : Integrable (fun y : ℝ => Real.exp (γ * y)) (P.map (fun ω => W ω x)) := by
      rw [(hLaw x).map_eq]; exact integrable_exp_mul_gaussianReal γ
    have hExp : Integrable (fun ω => Real.exp (γ * W ω x)) P := by
      simpa only [Function.comp_def] using
        (integrable_map_measure hExpMap.aestronglyMeasurable (hLaw x).aemeasurable).mp hExpMap
    have hge (ω : Ω) : g (ω, x) = (w x * Real.exp (-(γ ^ 2 / 2 * (v x : ℝ)))) * Real.exp (γ * W ω x) := by
      dsimp [g]; rw [sub_eq_add_neg, add_comm, Real.exp_add]; ring
    refine ⟨(hExp.const_mul _).congr (Eventually.of_forall fun ω => (hge ω).symm), ?_⟩
    simp_rw [hge, integral_const_mul, gaussian_exponential_moment_of_hasLaw (hLaw x) γ,
      mul_assoc, ← Real.exp_add]
    rw [show -(γ ^ 2 / 2 * (v x : ℝ)) + (v x : ℝ) * γ ^ 2 / 2 = 0 by ring, Real.exp_zero, mul_one]
  refine ((integrable_prod_iff' hg.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => (hpt x).1,
    hw_int.congr (Eventually.of_forall fun x => ?_)⟩).prod_right_ae
  rw [← (hpt x).2]
  exact (integral_congr_ae (Eventually.of_forall fun ω =>
    Real.norm_of_nonneg (mul_nonneg (hw_nonneg x) (Real.exp_nonneg _)))).symm

private lemma tendsto_bcf_of_ae {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (u : ℕ → Ω → E) (uLim : Ω → E) (hu : ∀ n, AEMeasurable (u n) μ)
    (hut : ∀ᵐ ω ∂μ, Tendsto (fun n => u n ω) atTop (𝓝 (uLim ω)))
    (φ : BoundedContinuousFunction E ℝ) :
    Tendsto (fun n => ∫ ω, φ (u n ω) ∂μ) atTop (𝓝 (∫ ω, φ (uLim ω) ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    (fun n => φ.continuous.aestronglyMeasurable.comp_aemeasurable (hu n))
    (integrable_const _) (fun n => Eventually.of_forall fun ω => φ.norm_coe_le_norm (u n ω))
    (hut.mono fun _ hω => φ.continuous.continuousAt.tendsto.comp hω)

/-- If two sequences of random vectors have the same law at every index and converge almost
everywhere on their respective finite measure spaces, then their limits agree in law as tested
by every bounded continuous real function. -/
theorem integral_bcf_eq_of_map_eq_of_ae_tendsto
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (f : ℕ → Ω → E) (g : ℕ → Ω' → E) (fLimit : Ω → E) (gLimit : Ω' → E)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : ∀ n, AEMeasurable (g n) P')
    (hmap : ∀ n, Measure.map (f n) P = Measure.map (g n) P')
    (hf_tendsto : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fLimit ω)))
    (hg_tendsto : ∀ᵐ ω ∂P', Tendsto (fun n => g n ω) atTop (𝓝 (gLimit ω)))
    (φ : BoundedContinuousFunction E ℝ) :
    (∫ ω, φ (fLimit ω) ∂P) = ∫ ω, φ (gLimit ω) ∂P' := by
  refine tendsto_nhds_unique (tendsto_bcf_of_ae f fLimit hf hf_tendsto φ)
    ((tendsto_bcf_of_ae g gLimit hg hg_tendsto φ).congr' (Eventually.of_forall fun n => ?_))
  rw [← integral_map (hg n) φ.continuous.measurable.aestronglyMeasurable, ← hmap n,
    integral_map (hf n) φ.continuous.measurable.aestronglyMeasurable]

private noncomputable def empVec {S : Type*} {k m n : ℕ}
    (z : Fin m → S → ℝ → ℝ) (u : ℕ → S) (w : (Fin k → ℝ) × (Fin n → ℝ)) :
    (Fin k → ℝ) × (Fin m → ℝ) :=
  (w.1, fun j => (n : ℝ)⁻¹ * ∑ i : Fin n, z j (u i.val) (w.2 i))

private lemma emp_single_model {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [IsProbabilityMeasure ν]
    {k m : ℕ} (X : Ω → S → ℝ) (V : Ω → Fin k → ℝ) (z : Fin m → S → ℝ → ℝ)
    (hV : Measurable V) (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hint : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) ν) :
    let Q := Measure.infinitePi (fun _ : ℕ => ν)
    let E : ℕ → Ω × (ℕ → S) → (Fin k → ℝ) × (Fin m → ℝ) :=
      fun r p => empVec z p.2 (V p.1, fun i : Fin r => X p.1 (p.2 i.val))
    let L : Ω → (Fin k → ℝ) × (Fin m → ℝ) := fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂ν)
    (∀ r, Measurable (E r)) ∧ Measurable L ∧
      (∀ᵐ p ∂P.prod Q, Tendsto (fun r => E r p) atTop (𝓝 (L p.1))) ∧
      (∀ ψ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ,
        (∫ p, ψ (L p.1) ∂P.prod Q) = ∫ ω, ψ (L ω) ∂P) := by
  intro Q E L
  have hXz (j : Fin m) : Measurable (fun p : Ω × S => z j p.2 (X p.1 p.2)) := by fun_prop
  have hEm (r : ℕ) : Measurable (E r) :=
    (hV.comp measurable_fst).prodMk (measurable_pi_iff.2 fun j =>
      measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        (hz j).comp ((by fun_prop : Measurable fun p : Ω × (ℕ → S) => p.2 i.val).prodMk (by fun_prop))))
  have hLm : Measurable L :=
    hV.prodMk (measurable_pi_iff.2 fun j => (hXz j).stronglyMeasurable.integral_prod_right'.measurable)
  have hEvalIdent (i : ℕ) : IdentDistrib (fun q : ℕ → S => q i) id Q ν :=
    ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id,
      by simpa [Q] using Measure.infinitePi_map_eval (fun _ : ℕ => ν) i⟩
  have hindepCoord : iIndepFun (fun i (q : ℕ → S) => q i) Q := by
    simpa [Q] using iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id) (by fun_prop)
  have hsc (j : Fin m) : ∀ᵐ p ∂P.prod Q,
      Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val)))
        atTop (𝓝 (∫ x, z j x (X p.1 x) ∂ν)) := by
    let f : Ω → S → ℝ := fun ω x => z j x (X ω x)
    have hset : MeasurableSet {p : Ω × (ℕ → S) |
        Tendsto (fun r : ℕ => (r : ℝ)⁻¹ * ∑ i : Fin r, f p.1 (p.2 i.val)) atTop (𝓝 (∫ x, f p.1 x ∂ν))} :=
      measurableSet_tendsto_fun (l := atTop) (by dsimp [f]; intro r; fun_prop)
        ((hXz j).stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst)
    refine (Measure.ae_prod_iff_ae_ae hset).2 ((hint j).mono fun ω hω => ?_)
    have hfm : Measurable (f ω) := (hXz j).comp (measurable_const.prodMk measurable_id)
    have hind := hindepCoord.comp (fun _ => f ω) (fun _ => hfm)
    have hs0 := (hEvalIdent 0).comp hfm
    have hmean : (∫ q, f ω (q 0) ∂Q) = ∫ x, f ω x ∂ν := hs0.integral_eq
    refine (ProbabilityTheory.strong_law_ae (μ := Q) (fun i q => f ω (q i))
      (hs0.integrable_iff.2 hω) (fun _ _ hij => hind.indepFun hij)
      fun i => ((hEvalIdent i).trans (hEvalIdent 0).symm).comp hfm).mono fun q hq => ?_
    simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hmean] using hq
  have hlim : ∀ᵐ p ∂P.prod Q, Tendsto (fun r => E r p) atTop (𝓝 (L p.1)) :=
    (ae_all_iff.2 hsc).mono fun p hp => by
      have hp2 := (Prod.tendsto_iff
        (fun r : ℕ => (V p.1, fun j => (r : ℝ)⁻¹ * ∑ i : Fin r, z j (p.2 i.val) (X p.1 (p.2 i.val))))
        (V p.1, fun j => ∫ x, z j x (X p.1 x) ∂ν)).2 ⟨tendsto_const_nhds, tendsto_pi_nhds.2 hp⟩
      simpa [E, L, empVec] using hp2
  refine ⟨hEm, hLm, hlim, fun ψ => ?_⟩
  have hφ : AEStronglyMeasurable (fun ω => ψ (L ω)) (Measure.map Prod.fst (P.prod Q)) := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact (ψ.continuous.measurable.comp hLm).aestronglyMeasurable
  have h := integral_map measurable_fst.aemeasurable hφ
  rw [Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h.symm

section
variable {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
include S P P'

/-- The law of finitely many Wick integrals, jointly with finitely many field coordinates, is
determined by the finite dimensional laws of a jointly measurable field. -/
theorem chaosLawFDD_of_integrable

    (ν : Measure S) [IsProbabilityMeasure ν] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (z : Fin m → S → ℝ → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) ν)
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) ν)
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    Measure.map (fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂ν)) P =
      Measure.map (fun ω => (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν)) P' ∧
    (∫ ω, φ (V ω, fun j => ∫ x, z j x (X ω x) ∂ν) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν) ∂P' := by
  obtain ⟨hEXm, hLXm, hXlim, hXfst⟩ := emp_single_model P ν X V z hV hX hz hintX
  obtain ⟨hEYm, hLYm, hYlim, hYfst⟩ := emp_single_model P' ν Y V' z hV' hY hz hintY
  let Q := Measure.infinitePi (fun _ : ℕ => ν)
  have hmap (r : ℕ) :
      Measure.map (fun p : Ω × (ℕ → S) => empVec z p.2 (V p.1, fun i : Fin r => X p.1 (p.2 i.val))) (P.prod Q) =
      Measure.map (fun p : Ω' × (ℕ → S) => empVec z p.2 (V' p.1, fun i : Fin r => Y p.1 (p.2 i.val))) (P'.prod Q) := by
    refine Measure.ext fun t ht => ?_
    rw [Measure.map_apply (hEXm r) ht, Measure.map_apply (hEYm r) ht,
      Measure.prod_apply_symm ((hEXm r) ht), Measure.prod_apply_symm ((hEYm r) ht)]
    refine lintegral_congr fun u => ?_
    have htr : Measurable (empVec z u : ((Fin k → ℝ) × (Fin r → ℝ)) → (Fin k → ℝ) × (Fin m → ℝ)) :=
      measurable_fst.prodMk (by fun_prop)
    have hbX : Measurable fun ω : Ω => (V ω, fun i : Fin r => X ω (u i.val)) :=
      hV.prodMk (measurable_pi_iff.2 fun i => hX.comp (measurable_id.prodMk measurable_const))
    have hbY : Measurable fun ω : Ω' => (V' ω, fun i : Fin r => Y ω (u i.val)) :=
      hV'.prodMk (measurable_pi_iff.2 fun i => hY.comp (measurable_id.prodMk measurable_const))
    have hsec : Measure.map (empVec z u ∘ fun ω => (V ω, fun i : Fin r => X ω (u i.val))) P =
        Measure.map (empVec z u ∘ fun ω => (V' ω, fun i : Fin r => Y ω (u i.val))) P' := by
      rw [← Measure.map_map htr hbX, ← Measure.map_map htr hbY, hFDD r fun i => u i.val]
    change P ((empVec z u ∘ fun ω => (V ω, fun i : Fin r => X ω (u i.val))) ⁻¹' t) =
      P' ((empVec z u ∘ fun ω => (V' ω, fun i : Fin r => Y ω (u i.val))) ⁻¹' t)
    rw [← Measure.map_apply (htr.comp hbX) ht, hsec, Measure.map_apply (htr.comp hbY) ht]
  have htestAll (ψ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
      (∫ ω, ψ (V ω, fun j => ∫ x, z j x (X ω x) ∂ν) ∂P) =
        ∫ ω, ψ (V' ω, fun j => ∫ x, z j x (Y ω x) ∂ν) ∂P' :=
    (hXfst ψ).symm.trans ((integral_bcf_eq_of_map_eq_of_ae_tendsto _ _ _ _
      (fun r => (hEXm r).aemeasurable) (fun r => (hEYm r).aemeasurable) hmap hXlim hYlim ψ).trans (hYfst ψ))
  refine ⟨ext_of_forall_integral_eq_of_IsFiniteMeasure fun ψ => ?_, htestAll φ⟩
  rw [integral_map hLXm.aemeasurable ψ.continuous.measurable.aestronglyMeasurable, htestAll ψ,
    ← integral_map hLYm.aemeasurable ψ.continuous.measurable.aestronglyMeasurable]

/-- Bounded nonnegative weights on a finite reference space satisfy the integrability hypotheses
automatically. -/
theorem chaosLawFDD_boundedWeights

    (ν : FiniteMeasure S) [Nonempty S] {k m : ℕ}
    (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (variance : S → ℝ≥0) (weight : Fin m → S → ℝ) (γ : ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hvariance : Measurable variance)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hweight_bdd : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, weight j x ≤ C)
    (hXlaw : ∀ x, HasLaw (fun ω => X ω x) (gaussianReal 0 (variance x)) P)
    (hYlaw : ∀ x, HasLaw (fun ω => Y ω x) (gaussianReal 0 (variance x)) P')
    (hFDD : ∀ (r : ℕ) (xs : Fin r → S),
      Measure.map (fun ω => (V ω, fun i => X ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => Y ω (xs i))) P')
    (φ : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ) :
    (∫ ω, φ (V ω, fun j => ∫ x, weight j x *
      Real.exp (γ * X ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P) =
      ∫ ω, φ (V' ω, fun j => ∫ x, weight j x *
      Real.exp (γ * Y ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) ∂P' := by
  let z : Fin m → S → ℝ → ℝ := fun j x t =>
    ((ν.mass : ℝ) * weight j x) * Real.exp (γ * t - γ ^ 2 / 2 * (variance x : ℝ))
  have hw_int (j : Fin m) : Integrable (fun x => (ν.mass : ℝ) * weight j x) (ν.normalize : Measure S) := by
    obtain ⟨C, _, hC⟩ := hweight_bdd j
    exact ((integrable_const C).mono' (hweight j).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hweight_nonneg j x)] using hC x)).const_mul _
  have hIntX (j : Fin m) := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) X variance
    (fun x => (ν.mass : ℝ) * weight j x) γ hX hvariance ((hweight j).const_mul _) hXlaw
    (fun x => mul_nonneg (by positivity) (hweight_nonneg j x)) (hw_int j)
  have hIntY (j : Fin m) := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) Y variance
    (fun x => (ν.mass : ℝ) * weight j x) γ hY hvariance ((hweight j).const_mul _) hYlaw
    (fun x => mul_nonneg (by positivity) (hweight_nonneg j x)) (hw_int j)
  have hLaw := (chaosLawFDD_of_integrable (ν.normalize : Measure S) X Y V V' z hV hV' hX hY
    (by dsimp [z]; intro j; fun_prop) hIntX hIntY hFDD φ).2
  have hmeas_smul : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) :=
    congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hsmul (f : S → ℝ) (j : Fin m) :
      (∫ x, weight j x * Real.exp (γ * f x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure S)) =
      ∫ x, z j x (f x) ∂(ν.normalize : Measure S) := by
    rw [hmeas_smul, integral_smul_nnreal_measure]
    change (ν.mass : ℝ) * _ = _
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by dsimp [z]; ring)
  simp_rw [hsmul]
  exact hLaw


end
end DOZZ.Proofs
