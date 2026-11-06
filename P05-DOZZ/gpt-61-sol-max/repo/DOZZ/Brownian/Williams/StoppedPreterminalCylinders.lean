/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.StoppedPaths
public import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Tactic

/-!
# Recovering stopped-path cylinders from preterminal marked laws

The lifetime is retained in every finite observation law. Letting a positive observation time
decrease to zero recovers the full lifetime marginal. A finite path cylinder then splits at
its largest observation: before the lifetime it is given by the marked law; at or after the
lifetime its terminal value is fixed, and that observation can be removed.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace DOZZ.Proofs

variable (n : ℕ) (ss : Fin (n+1) → ℝ≥0)

include n ss in
/-- Positive-coordinate observations of a stopped path, with the real lifetime mark. -/
def stoppedPreterminalObservation
    (z : StoppedBrownianPath) : (Fin (n+1) → ℝ) × ℝ :=
  ((fun i => -(z.2 (ss i))), (z.1 : ℝ))

include n ss in
theorem measurable_stoppedPreterminalObservation  :
    Measurable (stoppedPreterminalObservation n ss) :=
  (measurable_pi_iff.mpr fun _ =>
    ((ContinuousMap.measurable_eval _).comp measurable_snd).neg).prodMk
      (NNReal.continuous_coe.measurable.comp measurable_fst)

/-- Equality of every nonempty positive-time observation law retained before its lifetime. -/
def SameStoppedPreterminalLaws (μ η : Measure StoppedBrownianPath) : Prop :=
  ∀ (n : ℕ) (ss : Fin (n+1) → ℝ≥0), StrictMono ss → 0 < ss 0 →
    (μ.restrict {z | ss (Fin.last n) < z.1}).map (stoppedPreterminalObservation n ss) =
    (η.restrict {z | ss (Fin.last n) < z.1}).map (stoppedPreterminalObservation n ss)

/-- A finite stopped-path cylinder with a lifetime event. -/
def stoppedPathCylinder (U : Set ℝ) (I : Finset ℝ≥0) (S : ℝ≥0 → Set ℝ) :
    Set StoppedBrownianPath := {z | (z.1 : ℝ) ∈ U ∧ ∀ t ∈ I, -(z.2 t) ∈ S t}

variable {μ η : Measure StoppedBrownianPath} [_inst1 : IsFiniteMeasure μ] [_inst2 : IsFiniteMeasure η] (h : SameStoppedPreterminalLaws μ η) (hμpos : ∀ᵐ z ∂μ, 0 < z.1) (hηpos : ∀ᵐ z ∂η, 0 < z.1)

include μ η _inst1 _inst2 h hμpos hηpos in
/-- Positive lifetimes and the preterminal marked laws determine the whole lifetime marginal. -/
theorem SameStoppedPreterminalLaws.lifetime_event_eq

    (U : Set ℝ) (hU : MeasurableSet U) :
    μ {z | (z.1 : ℝ) ∈ U} = η {z | (z.1 : ℝ) ∈ U} := by
  have hcut (s : ℝ≥0) (hs : 0 < s) :
      μ {z | (z.1 : ℝ) ∈ U ∧ s < z.1} = η {z | (z.1 : ℝ) ∈ U ∧ s < z.1} := by
    have he := congrArg (fun M : Measure ((Fin 1 → ℝ) × ℝ) => M (univ ×ˢ U))
      (h 0 (fun _ => s) (by intro i j hij; exfalso; omega) hs)
    rw [Measure.map_apply (measurable_stoppedPreterminalObservation _ _) (MeasurableSet.univ.prod hU),
      Measure.map_apply (measurable_stoppedPreterminalObservation _ _) (MeasurableSet.univ.prod hU),
      Measure.restrict_apply ((MeasurableSet.univ.prod hU).preimage
        (measurable_stoppedPreterminalObservation _ _)),
      Measure.restrict_apply ((MeasurableSet.univ.prod hU).preimage
        (measurable_stoppedPreterminalObservation _ _))] at he
    have hevent : stoppedPreterminalObservation 0 (fun _ => s) ⁻¹' (univ ×ˢ U) ∩
        {z : StoppedBrownianPath | s < z.1} = {z | (z.1 : ℝ) ∈ U ∧ s < z.1} := by
      continuity
    simpa only [Fin.last_zero, hevent] using he
  let E : ℕ → Set StoppedBrownianPath := fun n =>
    {z | (z.1 : ℝ) ∈ U ∧ 1/(n+1 : ℝ≥0) < z.1}
  have hmono : Monotone E := by
    intro i j hij z hz
    refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
    gcongr
  have hunion (M : Measure StoppedBrownianPath) (hpos : ∀ᵐ z ∂M, 0 < z.1) :
      (⋃ n, E n) =ᵐ[M] {z | (z.1 : ℝ) ∈ U} := by
    filter_upwards [hpos] with z hz
    apply propext
    constructor
    · continuity
    · intro hzU
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hz
      exact mem_iUnion.mpr ⟨n, hzU, hn⟩
  have heq (n : ℕ) : μ (E n) = η (E n) := hcut _ (by positivity)
  have hl := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hr := tendsto_measure_iUnion_atTop (μ := η) hmono
  rw [measure_congr (hunion μ hμpos)] at hl
  rw [measure_congr (hunion η hηpos)] at hr
  apply tendsto_nhds_unique hl
  convert hr using 1
  funext n
  exact heq n

/-- A positive-time cylinder retained before its largest observation is determined by the
corresponding marked observation law. -/
theorem SameStoppedPreterminalLaws.preterminal_cylinder_eq
    {μ η : Measure StoppedBrownianPath} (h : SameStoppedPreterminalLaws μ η)
    (U : Set ℝ) (hU : MeasurableSet U) (I : Finset ℝ≥0) (hI : I.Nonempty)
    (hpos : ∀ t ∈ I, 0 < t) (S : ℝ≥0 → Set ℝ) (hS : ∀ t, MeasurableSet (S t)) :
    μ (stoppedPathCylinder U I S ∩ {z | I.max' hI < z.1}) =
      η (stoppedPathCylinder U I S ∩ {z | I.max' hI < z.1}) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, I.card = n+1 := by
    simp_all
  let e : Fin (n+1) ≃o I := I.orderIsoOfFin hn
  let ss : Fin (n+1) → ℝ≥0 := fun i => (e i).val
  have hlast : ss (Fin.last n) = I.max' hI := by
    apply le_antisymm
    · exact Finset.le_max' I _ (e (Fin.last n)).property
    · obtain ⟨i, hi⟩ := e.surjective ⟨I.max' hI, Finset.max'_mem I hI⟩
      have hi' : ss i = I.max' hI := congrArg Subtype.val hi
      rw [← hi']
      exact e.monotone (Fin.le_last i)
  let A : Set (Fin (n+1) → ℝ) := {x | ∀ i, x i ∈ S (ss i)}
  have hA : MeasurableSet A := by
    measurability
  have he := congrArg (fun M : Measure ((Fin (n+1) → ℝ) × ℝ) => M (A ×ˢ U))
    (h n ss e.strictMono (hpos _ (e 0).property))
  rw [Measure.map_apply (measurable_stoppedPreterminalObservation _ _) (hA.prod hU),
    Measure.map_apply (measurable_stoppedPreterminalObservation _ _) (hA.prod hU),
    Measure.restrict_apply ((hA.prod hU).preimage (measurable_stoppedPreterminalObservation _ _)),
    Measure.restrict_apply ((hA.prod hU).preimage (measurable_stoppedPreterminalObservation _ _)),
    hlast] at he
  have hpre : stoppedPreterminalObservation n ss ⁻¹' (A ×ˢ U) = stoppedPathCylinder U I S := by
    ext z
    simp only [mem_preimage, mem_prod, stoppedPreterminalObservation, A,
      stoppedPathCylinder, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hu⟩
      refine ⟨hu, ?_⟩
      intro t ht
      obtain ⟨i, hi⟩ := e.surjective ⟨t, ht⟩
      grind
    continuity
  rwa [hpre] at he

/-- Every finite lifetime-marked path cylinder is measurable. -/
theorem measurableSet_stoppedPathCylinder (U : Set ℝ) (hU : MeasurableSet U)
    (I : Finset ℝ≥0) (S : ℝ≥0 → Set ℝ) (hS : ∀ t, MeasurableSet (S t)) :
    MeasurableSet (stoppedPathCylinder U I S) := by
  have heq : stoppedPathCylinder U I S =
      {z : StoppedBrownianPath | (z.1 : ℝ) ∈ U} ∩
        ⋂ t : {t : ℝ≥0 // t ∈ I}, {z : StoppedBrownianPath | -(z.2 t.val) ∈ S t.val} := by
    ext z
    simp [stoppedPathCylinder]
  rw [heq]
  exact (hU.preimage (NNReal.continuous_coe.measurable.comp measurable_fst)).inter
    (MeasurableSet.iInter fun t => (hS t.val).preimage
      (((ContinuousMap.measurable_eval t.val).comp measurable_snd).neg))

include μ η _inst1 _inst2 h hμpos hηpos in
/-- The preterminal laws, positive lifetimes, and the fixed terminal value determine all
finite cylinders at positive observation times, including observations after the lifetime. -/
theorem SameStoppedPreterminalLaws.positive_cylinder_eq

    (c : ℝ) (hμend : ∀ᵐ z ∂μ, ∀ t, z.1 ≤ t → -(z.2 t) = c)
    (hηend : ∀ᵐ z ∂η, ∀ t, z.1 ≤ t → -(z.2 t) = c)
    (U : Set ℝ) (hU : MeasurableSet U) (I : Finset ℝ≥0)
    (hpos : ∀ t ∈ I, 0 < t) (S : ℝ≥0 → Set ℝ) (hS : ∀ t, MeasurableSet (S t)) :
    μ (stoppedPathCylinder U I S) = η (stoppedPathCylinder U I S) := by
  classical
  induction I using Finset.strongInductionOn generalizing U with
  | _ I ih =>
    by_cases hI : I.Nonempty
    · let t := I.max' hI
      let J := I.erase t
      have htI  := Finset.max'_mem I hI
      have hJ  := Finset.erase_ssubset htI
      have hJpos : ∀ r ∈ J, 0 < r := fun r hr => hpos r (Finset.mem_of_mem_erase hr)
      let E := stoppedPathCylinder U I S
      let F := {z : StoppedBrownianPath | z.1 ≤ t}
      have hE := measurableSet_stoppedPathCylinder U hU I S hS
      have hF : MeasurableSet F := measurableSet_le measurable_fst measurable_const
      have hsplit : E = (E ∩ {z : StoppedBrownianPath | t < z.1}) ∪ (E ∩ F) := by
        ext z
        grind
      have hdisj : Disjoint (E ∩ {z : StoppedBrownianPath | t < z.1}) (E ∩ F) := by
        grind
      have hpre := h.preterminal_cylinder_eq U hU I hI hpos S hS
      have hpost : μ (E ∩ F) = η (E ∩ F) := by
        by_cases hc : c ∈ S t
        · have hevent (M : Measure StoppedBrownianPath)
              (hend : ∀ᵐ z ∂M, ∀ r, z.1 ≤ r → -(z.2 r) = c) :
              (E ∩ F) =ᵐ[M] stoppedPathCylinder (U ∩ Iic (t : ℝ)) J S := by
            filter_upwards [hend] with z hz
            apply propext
            simp only [E, F, stoppedPathCylinder, mem_inter_iff, mem_ofPred_eq, mem_Iic,
              NNReal.coe_le_coe]
            grind
          rw [measure_congr (hevent μ hμend), measure_congr (hevent η hηend)]
          exact ih J hJ (U ∩ Iic (t : ℝ)) (hU.inter measurableSet_Iic) hJpos
        · have hzero (M : Measure StoppedBrownianPath)
              (hend : ∀ᵐ z ∂M, ∀ r, z.1 ≤ r → -(z.2 r) = c) : M (E ∩ F) = 0 := by
            apply measure_eq_zero_iff_ae_notMem.mpr
            filter_upwards [hend] with z hz
            intro hzE
            have hx := hzE.1.2 t htI
            rw [hz t hzE.2] at hx
            exact hc hx
          rw [hzero μ hμend, hzero η hηend]
      change μ E = η E
      rw [hsplit, measure_union hdisj (hE.inter hF), measure_union hdisj (hE.inter hF),
        hpre, hpost]
    · have hIempty  := Finset.not_nonempty_iff_eq_empty.mp hI
      subst I
      simpa [stoppedPathCylinder] using h.lifetime_event_eq hμpos hηpos U hU

end DOZZ.Proofs
end
