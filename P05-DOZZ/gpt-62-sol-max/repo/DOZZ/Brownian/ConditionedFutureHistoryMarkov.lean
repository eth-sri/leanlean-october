/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedCylinderRead
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Full-history deterministic-time Markov property

The finite-schedule factorization extends from coordinate vectors to the complete path history
and rational future by the cylinder π-system.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The endpoint-conditioned rational future has the current value at every nonpositive
relative rational time, almost surely under the state disintegration. -/
theorem conditionedPositiveEndpointFutureKernel_nonpos_coordinate_ae
    {P : Measure BrownianPath} [IsFiniteMeasure P]
    (t : ℝ≥0) (q : ℚ) (hq : (q : ℝ) ≤ 0) :
    ∀ᵐ z ∂((P.map (conditionedPositiveHistory t)) ⊗ₘ
      conditionedPositiveEndpointFutureKernel t P),
      z.2 q = z.1 ⟨t, le_rfl⟩ := by
  let e : (Set.Iic t → ℝ) → ℝ := fun h => h ⟨t, le_rfl⟩
  have he : Measurable e := measurable_pi_apply _
  have hH := measurable_conditionedPositiveHistory t
  have hs : (P.map (conditionedPositiveHistory t)).map e = P.map (conditionedPositiveStateAt t) :=
    Measure.map_map he hH
  have hmeas : MeasurableSet {z : ℝ × (ℚ → ℝ) | z.2 q = z.1} :=
    measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd) measurable_fst
  have hd : ∀ᵐ z ∂((P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P),
      z.2 q = z.1 := by
    rw [conditionedPositiveFutureKernel_compProd,
      ae_map_iff ((measurable_conditionedPositiveStateAt t).prodMk
        (measurable_conditionedPositiveFutureRationalEvals t)).aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun p => conditionedPositiveFutureRationalEvals_nonpos t p hq
  have := Measure.ae_ae_of_ae_compProd hd
  rw [← hs] at this
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd) (he.comp measurable_fst))
  filter_upwards [ae_of_ae_map he.aemeasurable this] with h hh
  simpa [conditionedPositiveEndpointFutureKernel, e, Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply] using hh

section
variable {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
  (hP : IsNegativeConditionedBrownianLaw ν P) (t : ℝ≥0) (ht : 0 < (t : ℝ))
include ν hP ht

/-- The complete rational future conditioned on the path history through deterministic time `t`
depends on that history only through its endpoint. -/
theorem conditionedPositiveFutureHistoryKernel_ae_eq_endpoint :
    conditionedPositiveFutureHistoryKernel t P =ᵐ[P.map (conditionedPositiveHistory t)]
      conditionedPositiveEndpointFutureKernel t P := by
  classical
  let pair := fun p => (conditionedPositiveHistory t p, conditionedPositiveFutureRationalEvals t p)
  let μ := P.map (conditionedPositiveHistory t) ⊗ₘ conditionedPositiveEndpointFutureKernel t P
  have hpair : Measurable pair := (measurable_conditionedPositiveHistory t).prodMk
    (measurable_conditionedPositiveFutureRationalEvals t)
  apply (conditionedPositiveFutureHistoryKernel_eq_endpoint_iff_compProd t P).mpr
  refine Eq.trans ?_ (Measure.map_id (μ := μ))
  refine (identDistrib_of_prod_pi_fdd (P := P) (P' := μ) (g := id)
    hpair.aemeasurable aemeasurable_id ?_).map_eq
  intro I J
  let zero : Set.Iic t := ⟨0, t.property⟩
  let tip : Set.Iic t := ⟨t, le_rfl⟩
  let p : Set.Iic t → Prop := fun i => i ≠ zero ∧ i ≠ tip
  let q : ℚ → Prop := fun r => 0 < (r : ℝ)
  let k := (I.filter p).card
  let n := (J.filter q).card
  let a := (I.filter p).orderEmbOfFin rfl
  let r : Fin n ↪o ℚ := (J.filter q).orderEmbOfFin rfl
  have ha i : p (a i) := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ _ _)).2
  have hr i : q (r i) := (Finset.mem_filter.mp (Finset.orderEmbOfFin_mem _ _ _)).2
  let as : Fin (k + 1) → Set.Iic t := Fin.snoc a tip
  let s : Fin (k + 1) → ℝ≥0 := fun i => (as i).1
  have hs i : s i ≤ t := (as i).2
  have hlast : s (Fin.last k) = t := by simp [s, as, tip]
  have ha0 (i : Fin k) : 0 < (a i).val := bot_lt_iff_ne_bot.mpr fun hi =>
    (ha i).1 (Subtype.ext hi)
  have hat (i : Fin k) : (a i).val < t := lt_of_le_of_ne (a i).2 fun hi =>
    (ha i).2 (Subtype.ext hi)
  have hpos i : 0 < (s i : ℝ) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rwa [hlast]
    · simpa [s, as] using NNReal.coe_pos.mpr (ha0 j)
  have hmono : StrictMono s := by
    intro i j hij
    cases i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
      cases j using Fin.lastCases with
      | last => simpa [s, as, tip] using hat i
      | cast j =>
        have h : (a i).val < (a j).val := a.strictMono (by simpa using hij)
        simpa [s, as] using h
  obtain ⟨hrMono, hcross⟩ := rationalFutureSchedule t r hr r.strictMono
  let project := fun z : (Set.Iic t → ℝ) × (ℚ → ℝ) => (fun i => z.1 (as i), fun j => z.2 (r j))
  have hpj : Measurable project := (measurable_pi_iff.mpr fun _ =>
    (measurable_pi_apply _).comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).comp measurable_snd)
  let read := fun z : (Fin (k + 1) → ℝ) × (Fin n → ℝ) =>
    (readFiltered I p (fun i => z.1 i.castSucc)
      (fun i => if (i : Set.Iic t) = zero then 0 else z.1 (Fin.last k)),
     readFiltered J q z.2 (fun _ => z.1 (Fin.last k)))
  have hread : Measurable read := by
    have hd : Measurable (fun z : (Fin (k + 1) → ℝ) × (Fin n → ℝ) => fun i : I =>
        if (i : Set.Iic t) = zero then 0 else z.1 (Fin.last k)) := by
      refine measurable_pi_iff.mpr fun i => ?_
      by_cases hi : (i : Set.Iic t) = zero
      · simp [hi]
      · simpa [hi, Function.comp_def] using (measurable_pi_apply (Fin.last k)).comp
          (measurable_fst : Measurable (Prod.fst : (Fin (k + 1) → ℝ) × (Fin n → ℝ) → _))
    exact (measurable_readFiltered I p (measurable_pi_iff.mpr fun _ =>
      (measurable_pi_apply _).comp measurable_fst) hd).prodMk
        (measurable_readFiltered J q measurable_snd
          (measurable_pi_iff.mpr fun _ => (measurable_pi_apply (Fin.last k)).comp measurable_fst))
  have hdecode (z : (Set.Iic t → ℝ) × (ℚ → ℝ)) (hz : z.1 zero = 0)
      (hdiag : ∀ j : J, (j : ℝ) ≤ 0 → z.2 j = z.1 tip) :
      read (project z) = Prod.map I.restrict J.restrict z := by
    apply Prod.ext
    · change readFiltered I p (fun i => z.1 (as i.castSucc))
        (fun i => if (i : Set.Iic t) = zero then 0 else z.1 (as (Fin.last k))) = _
      simp only [as, Fin.snoc_castSucc, Fin.snoc_last]
      apply readFiltered_restrict
      intro i hi
      by_cases h0 : (i : Set.Iic t) = zero
      · simp [h0, hz]
      · have ht' : (i : Set.Iic t) = tip := by simpa [p, h0] using hi
        rw [ite_eq_right h0, ht']
    · change readFiltered J q (fun i => z.2 (r i)) (fun _ => z.1 (as (Fin.last k))) = _
      simp only [as, Fin.snoc_last]
      exact readFiltered_restrict J q z.2 _ fun j hj => (hdiag j (le_of_not_gt hj)).symm
  have hP0 : ∀ᵐ w ∂P, (pair w).1 zero = 0 := by
    filter_upwards [hP.2.2.1] with w hw
    change -(w 0) = 0
    simp [hw]
  have hμ0 : ∀ᵐ z ∂μ, z.1 zero = 0 := by
    have hm : MeasurableSet {h : Set.Iic t → ℝ | h zero = 0} :=
      measurableSet_eq_fun (measurable_pi_apply zero) measurable_const
    exact Measure.ae_compProd_of_ae_fst _ hm
      ((ae_map_iff (measurable_conditionedPositiveHistory t).aemeasurable hm).mpr hP0)
  have hd : ∀ᵐ z ∂μ, ∀ j : J, (j : ℝ) ≤ 0 → z.2 j = z.1 tip := by
    refine ae_all_iff.mpr fun j => ?_
    by_cases hj : (j : ℝ) ≤ 0
    · filter_upwards [conditionedPositiveEndpointFutureKernel_nonpos_coordinate_ae
        (P := P) t (j : ℚ) hj] with z hz _
      exact hz
    · simp [hj]
  refine map_eq_of_read (hpj.comp hpair) hpj hread ?_ ?_ ?_
  · filter_upwards [hP0] with w hw
    exact hdecode (pair w) hw fun j hj => conditionedPositiveFutureRationalEvals_nonpos _ _ hj
  · filter_upwards [hμ0, hd] with z hz hz'
    exact hdecode z hz hz'
  · exact (conditionedPositiveFutureHistory_finite_projection_compProd hP t ht s hpos hs
      hmono hlast r hr (strictMono_finAppend_of_cross _ _ hmono hrMono
        (fun i j => (hs i).trans_lt (hcross j)))
      (strictMono_finAppend_endpoint hrMono hcross)).symm

/-- Conditional expectation of any integrable rational-future functional given the complete
history through `t` is its endpoint-kernel integral. -/
theorem conditionedPositiveHistory_condExp_rationalFuture
    (G : (ℚ → ℝ) → ℝ) (hG : StronglyMeasurable G)
    (hGint : Integrable (fun p => G (conditionedPositiveFutureRationalEvals t p)) P) :
    P[fun p => G (conditionedPositiveFutureRationalEvals t p) |
        conditionedPositiveNaturalFiltration t] =ᵐ[P]
      fun p => ∫ y, G y ∂conditionedPositiveEndpointFutureKernel t P
        (conditionedPositiveHistory t p) := by
  have hk := conditionedPositiveFutureHistoryKernel_ae_eq_endpoint hP t ht
  have hkernel : ∀ᵐ p ∂P,
      conditionedPositiveFutureHistoryKernel t P (conditionedPositiveHistory t p) =
        conditionedPositiveFutureKernel t P (conditionedPositiveStateAt t p) := by
    have hk' := Filter.Eventually.filter_mono
      (P.tendsto_ae_map (measurable_conditionedPositiveHistory t).aemeasurable) hk
    filter_upwards [hk'] with p hp
    simpa [conditionedPositiveEndpointFutureKernel,
      Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
      conditionedPositiveHistory_current] using hp
  have hcond := conditionedPositiveFutureHistoryKernel_condExp_of_ae_eq_endpoint
    t P G hG hGint hkernel
  filter_upwards [hcond] with p hp
  simpa [conditionedPositiveEndpointFutureKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
    conditionedPositiveHistory_current] using hp

end

end DOZZ.Proofs

end
