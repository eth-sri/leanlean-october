/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ChaosLawFDDLimit
import Mathlib.Analysis.Complex.Basic

/-! Open-set mass laws from bounded continuous test laws. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Bounded continuous distance cutoffs increasing to the indicator of an open set. -/
noncomputable def gmcOpenApprox (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    BoundedContinuousFunction ℂ ℝ := by
  classical
  by_cases h : U = Set.univ
  · exact 1
  · exact BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => min 1 ((n : ℝ) * Metric.infDist x Uᶜ))
      (continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _)))
      1 (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (by norm_num) (mul_nonneg (by positivity) Metric.infDist_nonneg))

section
variable (U : Set ℂ) (hU : IsOpen U)

theorem gmcOpenApprox_bounds (n : ℕ) (x : ℂ) :
    0 ≤ gmcOpenApprox U hU n x ∧ gmcOpenApprox U hU n x ≤ 1 := by
  classical
  by_cases h : U = Set.univ
  · simp [gmcOpenApprox, h]
  · constructor
    · simp only [gmcOpenApprox, h]
      exact le_min (by norm_num) (mul_nonneg (by positivity) Metric.infDist_nonneg)
    · simp only [gmcOpenApprox, h]
      exact min_le_left _ _

theorem gmcOpenApprox_tendsto (x : ℂ) :
    Tendsto (fun n => gmcOpenApprox U hU n x) atTop (𝓝 (U.indicator 1 x)) := by
  classical
  by_cases h : U = Set.univ
  · simp [gmcOpenApprox, h]
  · have hcomp : (Uᶜ : Set ℂ).Nonempty := by
      by_contra hn
      have he  := Set.not_nonempty_iff_eq_empty.mp hn
      exact h (by
        ext y
        have hy : y ∉ Uᶜ := by simp [he]
        simpa using hy)
    by_cases hx : x ∈ U
    · let d  := Metric.infDist x (Uᶜ : Set ℂ)
      have hx' : x ∉ Uᶜ := by simpa using hx
      have hd : 0 < d := by
        simpa [d] using (hU.isClosed_compl.notMem_iff_infDist_pos hcomp).1 hx'
      obtain ⟨N, hN⟩ := exists_nat_gt (d⁻¹)
      have hev : ∀ᶠ n : ℕ in atTop,
          gmcOpenApprox U hU n x = 1 := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : d⁻¹ < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
        have hmul : 1 ≤ (n : ℝ) * d := by
          have hlt := mul_lt_mul_of_pos_right hn' hd
          have hinv : d⁻¹ * d = 1 := by field_simp
          linarith
        have hmul' : 1 ≤ (n : ℝ) * Metric.infDist x Uᶜ := by assumption
        simp [gmcOpenApprox, h, min_eq_left hmul']
      have htarget : U.indicator (1 : ℂ → ℝ) x = 1 := by simp [hx]
      rw [htarget]
      exact tendsto_nhds_of_eventually_eq hev
    · have hd : Metric.infDist x (Uᶜ : Set ℂ) = 0 := Metric.infDist_zero_of_mem hx
      have hev : ∀ᶠ n : ℕ in atTop, gmcOpenApprox U hU n x = 0 := by
        filter_upwards [] with n
        simp [gmcOpenApprox, h, hd]
      have htarget : U.indicator (1 : ℂ → ℝ) x = 0 := by simp [hx]
      rw [htarget]
      exact tendsto_nhds_of_eventually_eq hev

end

theorem gmcOpenApprox_integral_tendsto
    (μ : Measure ℂ) [IsFiniteMeasure μ] (U : Set ℂ) (hU : IsOpen U) :
    Tendsto (fun n => ∫ x, gmcOpenApprox U hU n x ∂μ) atTop
      (𝓝 ((μ U).toReal)) := by
  let F : ℂ → ℝ := U.indicator 1
  have hboundInt : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const 1
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖gmcOpenApprox U hU n x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (gmcOpenApprox_bounds U hU n x).1]
    exact (gmcOpenApprox_bounds U hU n x).2
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => gmcOpenApprox U hU n x) atTop (𝓝 (F x)) := by
    filter_upwards [] with x
    exact gmcOpenApprox_tendsto U hU x
  have hDCT := tendsto_integral_of_dominated_convergence
    (bound := fun _ : ℂ => (1 : ℝ))
    (fun n => (gmcOpenApprox U hU n).continuous.aestronglyMeasurable)
    hboundInt hbound hpoint
  have hFint : (∫ x, F x ∂μ) = (μ U).toReal := by
    simp [F, integral_indicator_one hU.measurableSet, measureReal_def]
  simpa [F, hFint] using hDCT

section
variable (U : Set ℂ) (hU : IsOpen U) (n : ℕ)

/-- Open-set distance approximations vanish outside the open set. -/
theorem gmcOpenApprox_zero_outside
    (x : ℂ) (hx : x ∉ U) : gmcOpenApprox U hU n x = 0 := by
  classical
  have h : U ≠ univ := fun h => hx (h ▸ mem_univ x)
  simp [gmcOpenApprox, h, Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx)]

/-- Every distance approximation has support in the closure of the approximated open set. -/
theorem gmcOpenApprox_tsupport_subset :
    tsupport (gmcOpenApprox U hU n : ℂ → ℝ) ⊆ closure U := by
  apply closure_mono
  intro x hx
  by_contra h
  exact hx (gmcOpenApprox_zero_outside U hU n x h)

end

/-- Distance approximations recover the mass of a relatively compact open set under
any measure finite on its closure. -/
theorem gmcOpenApprox_integral_tendsto_of_finite_closure
    (μ : Measure ℂ) (U : Set ℂ) (hU : IsOpen U) (hfin : μ (closure U) < ⊤) :
    Tendsto (fun n => ∫ x, gmcOpenApprox U hU n x ∂μ) atTop (𝓝 ((μ U).toReal)) := by
  let : IsFiniteMeasure (μ.restrict (closure U)) := ⟨by
    rwa [Measure.restrict_apply_univ]⟩
  have he n := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) (s := closure U) (f := gmcOpenApprox U hU n)
      (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun h => hx (gmcOpenApprox_tsupport_subset U hU n h)))
  have hmass : μ.restrict (closure U) U = μ U := by
    rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr subset_closure]
  simpa only [he, hmass] using gmcOpenApprox_integral_tendsto (μ.restrict (closure U)) U hU

section

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- A finite-vector law is unchanged by undoing a reindexing of the coordinates. -/
theorem identDistrib_pi_of_reindex {ι ι' R : Type*} [MeasurableSpace R] (e : ι' ≃ ι)
    {f : Ω → ι → R} {g : Ω' → ι → R}
    (h : IdentDistrib (fun ω => f ω ∘ e) (fun ω => g ω ∘ e) P P') : IdentDistrib f g P P' := by
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using
    h.comp (u := fun (p : ι' → R) i => p (e.symm i)) (by fun_prop)

/-- Undo two independent reindexings in a joint finite-vector law. -/
theorem identDistrib_pair_pi_of_reindex {ι ι' κ κ' R S : Type*}
    [MeasurableSpace R] [MeasurableSpace S] (a : ι' ≃ ι) (b : κ' ≃ κ)
    {f : Ω → (ι → R) × (κ → S)} {g : Ω' → (ι → R) × (κ → S)}
    (h : IdentDistrib (fun ω => ((f ω).1 ∘ a, (f ω).2 ∘ b))
      (fun ω => ((g ω).1 ∘ a, (g ω).2 ∘ b)) P P') : IdentDistrib f g P P' := by
  simpa only [Function.comp_def, Equiv.apply_symm_apply, Prod.eta] using
    h.comp (u := fun p : (ι' → R) × (κ' → S) => (fun i => p.1 (a.symm i), fun j => p.2 (b.symm j)))
      (by fun_prop)

variable [IsFiniteMeasure P] [IsFiniteMeasure P']

/-- Laws of continuous test integrals determine laws of open masses, retaining a fixed auxiliary
random variable. Only finiteness on the closure of each tested open set is needed. -/
theorem identDistrib_open_mass_pair {E κ : Type*}
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [Fintype κ]
    {V : Ω → E} {V' : Ω' → E} (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j))
    (M : Ω → Measure ℂ) (N : Ω' → Measure ℂ)
    (hM : ∀ ω j, M ω (closure (U j)) < ⊤) (hN : ∀ ω j, N ω (closure (U j)) < ⊤)
    (hlaw : ∀ n, IdentDistrib (fun ω => (V ω, fun j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω))
      (fun ω => (V' ω, fun j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂N ω)) P P') :
    IdentDistrib (fun ω => (V ω, fun j => M ω (U j))) (fun ω => (V' ω, fun j => N ω (U j))) P P' := by
  let A := fun n ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω
  let B := fun n ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂N ω
  have hA n : AEMeasurable (A n) P := (hlaw n).aemeasurable_fst.snd
  have hB n : AEMeasurable (B n) P' := (hlaw n).aemeasurable_snd.snd
  have hV : AEMeasurable V P := (hlaw 0).aemeasurable_fst.fst
  have hV' : AEMeasurable V' P' := (hlaw 0).aemeasurable_snd.fst
  let a := fun ω j => (M ω (U j)).toReal
  let b := fun ω j => (N ω (U j)).toReal
  have hta j : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω j) atTop (𝓝 (a ω j)) :=
    ae_of_all _ fun ω => gmcOpenApprox_integral_tendsto_of_finite_closure _ _ (hU j) (hM ω j)
  have htb j : ∀ᵐ ω ∂P', Tendsto (fun n => B n ω j) atTop (𝓝 (b ω j)) :=
    ae_of_all _ fun ω => gmcOpenApprox_integral_tendsto_of_finite_closure _ _ (hU j) (hN ω j)
  have ha : AEMeasurable a P := AEMeasurable.of_eval fun j =>
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hA n).eval j) (hta j)
  have hb : AEMeasurable b P' := AEMeasurable.of_eval fun j =>
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hB n).eval j) (htb j)
  have hi : IdentDistrib (fun ω => (V ω, a ω)) (fun ω => (V' ω, b ω)) P P' :=
    ⟨hV.prodMk ha, hV'.prodMk hb,
      gmc_limit_joint_test_vector_law V V' hV hV' A B a b hA hB ha hb (fun n => (hlaw n).map_eq)
        (fun j => tendstoInMeasure_of_tendsto_ae (fun n => ((hA n).eval j).aestronglyMeasurable) (hta j))
        (fun j => tendstoInMeasure_of_tendsto_ae (fun n => ((hB n).eval j).aestronglyMeasurable) (htb j))⟩
  have hm ω j := ENNReal.ofReal_toReal ((measure_mono subset_closure).trans_lt (hM ω j)).ne
  have hn ω j := ENNReal.ofReal_toReal ((measure_mono subset_closure).trans_lt (hN ω j)).ne
  simpa only [Function.comp_def, a, b, hm, hn] using
    hi.comp (u := fun p : E × (κ → ℝ) => (p.1, fun j => ENNReal.ofReal (p.2 j))) (by fun_prop)

/-- Open-set mass laws without auxiliary coordinates. -/
theorem identDistrib_open_mass {κ : Type*} [Fintype κ] (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j))
    (M : Ω → Measure ℂ) (N : Ω' → Measure ℂ)
    (hM : ∀ ω j, M ω (closure (U j)) < ⊤) (hN : ∀ ω j, N ω (closure (U j)) < ⊤)
    (hlaw : ∀ n, IdentDistrib (fun ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω)
      (fun ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂N ω) P P') :
    IdentDistrib (fun ω j => M ω (U j)) (fun ω j => N ω (U j)) P P' :=
  (identDistrib_open_mass_pair (V := fun _ => (0 : ℝ)) (V' := fun _ => (0 : ℝ))
    U hU M N hM hN (fun n => (hlaw n).comp (measurable_const.prodMk measurable_id))).comp measurable_snd

end

end DOZZ.Proofs
