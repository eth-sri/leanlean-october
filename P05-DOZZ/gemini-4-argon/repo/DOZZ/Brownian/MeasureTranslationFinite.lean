/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Disjointed

/-!
# Joint integration against a finite measure parameter

This is a finite-measure building block for the random translation action on lateral measures.
It expresses a parameter-dependent integral through the product of a Dirac measure and the
varying finite measure, then extends from measurable indicators by `ennreal_induction`.
-/

@[expose] public section

open MeasureTheory
open Function
open scoped ENNReal

namespace DOZZ.Proofs

/-- If `f` is jointly measurable, integrating its sections against a varying finite measure is
jointly measurable in the section parameter and the measure. -/
theorem measurable_lintegral_finiteMeasure_parameter
    {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
    {f : X × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : X × FiniteMeasure β =>
      ∫⁻ y, f (z.1, y) ∂(z.2 : Measure β)) := by
  classical
  let diracFinite : X → FiniteMeasure X := fun x =>
    ⟨Measure.dirac x, MeasureTheory.isFiniteMeasure_dirac⟩
  refine Measurable.ennreal_induction
    (motive := fun g : X × β → ℝ≥0∞ =>
      Measurable (fun z : X × FiniteMeasure β =>
        ∫⁻ y, g (z.1, y) ∂(z.2 : Measure β))) ?_ ?_ ?_ hf
  · intro c s hs
    have hsec x : MeasurableSet (Prod.mk x ⁻¹' s) :=
      hs.preimage (measurable_const.prodMk measurable_id)
    have hprodSection x (μ : FiniteMeasure β) :
        (Measure.dirac x).prod (μ : Measure β) s =
      (μ : Measure β) (Prod.mk x ⁻¹' s) := by
      rw [Measure.prod_apply hs]
      exact lintegral_dirac' x (measurable_measure_prodMk_left hs)
    have hformula x (μ : FiniteMeasure β) :
        ∫⁻ y, (s.indicator fun _ => c) (x, y) ∂(μ : Measure β) =
          c * ((Measure.dirac x).prod (μ : Measure β) s) := by
      simp only [← Set.indicator_comp_right]
      change ∫⁻ y, (Prod.mk x ⁻¹' s).indicator (fun _ => c) y ∂(μ : Measure β) = _
      rw [lintegral_indicator_const (hsec x) c, hprodSection]
    have hmeas : Measurable (fun z : X × FiniteMeasure β =>
        c * ((Measure.dirac z.1).prod (z.2 : Measure β) s)) := measurable_const.mul ((fun s hs => (Measure.measurable_coe hs).comp ((FiniteMeasure.measurable_fun_prod).comp ((show Measurable diracFinite by apply Measurable.subtype_mk; exact Measure.measurable_dirac).comp measurable_fst |>.prodMk measurable_snd : Measurable (fun z : X × FiniteMeasure β => (diracFinite z.1, z.2))))) s hs)
    simpa only [hformula] using hmeas
  · rintro g k - hg hk hgm hkm
    simp only [Pi.add_apply]
    have hsection_meas (z : X × FiniteMeasure β) : Measurable (fun y => g (z.1, y)) :=
      hg.comp (measurable_const.prodMk measurable_id)
    rw [(show (fun z : X × FiniteMeasure β => ∫⁻ y, g (z.1, y) + k (z.1, y) ∂(z.2 : Measure β)) = fun z => (∫⁻ y, g (z.1, y) ∂(z.2 : Measure β)) + ∫⁻ y, k (z.1, y) ∂(z.2 : Measure β) by funext z; exact lintegral_add_left (hsection_meas z) _)]
    exact hgm.add hkm
  · intro g hg hgmono hgm
    have hsection_meas n (z : X × FiniteMeasure β) :
        Measurable (fun y => g n (z.1, y)) :=
      (hg n).comp (measurable_const.prodMk measurable_id)
    have hmono (z : X × FiniteMeasure β) : Monotone fun n y => g n (z.1, y) :=
      fun i j hij y => hgmono hij (z.1, y)
    rw [(show (fun z : X × FiniteMeasure β => ∫⁻ y, (⨆ n, g n (z.1, y)) ∂(z.2 : Measure β)) = fun z => ⨆ n, ∫⁻ y, g n (z.1, y) ∂(z.2 : Measure β) by funext z; exact lintegral_iSup (fun n => hsection_meas n z) (hmono z))]
    exact Measurable.iSup hgm

/-- Translation is jointly measurable on finite measures. The proof checks evaluations on
measurable sets and writes each evaluation as an integral of a jointly measurable indicator. -/
theorem measurable_translateFiniteMeasure :
    Measurable (fun z : ℝ × FiniteMeasure ℝ => z.2.map (fun s => s + z.1)) := by
  have hmeasure : Measurable (fun z : ℝ × FiniteMeasure ℝ =>
      (z.2 : Measure ℝ).map (fun s => s + z.1)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEq t (μ : FiniteMeasure ℝ) :
        ((μ : Measure ℝ).map (fun s => s + t)) A =
          ∫⁻ s, A.indicator (fun _ => 1) (s + t) ∂(μ : Measure ℝ) := by
      rw [Measure.map_apply (by fun_prop : Measurable (fun s => s + t)) hA]
      calc
        (μ : Measure ℝ) ((fun s : ℝ => s + t) ⁻¹' A) =
            ∫⁻ s, ((fun s => s + t) ⁻¹' A).indicator (fun _ => 1) s ∂(μ : Measure ℝ) :=
          (lintegral_indicator_one (hA.preimage (by fun_prop))).symm
        _ = ∫⁻ s, A.indicator (fun _ => 1) (s + t) ∂(μ : Measure ℝ) := by
          apply lintegral_congr
          intro s
          have hind := Set.indicator_comp_right (s := A) (fun u => u + t)
            (g := fun _ => (1 : ℝ≥0∞)) (x := s)
          rw [(show (fun x => (1 : ℝ≥0∞)) ∘ (fun u => u + t) = fun _ => 1 by funext x; rfl)] at hind
          exact hind
    convert (measurable_lintegral_finiteMeasure_parameter (f := (fun z => A.indicator (fun _ => 1) (z.2 + z.1))) ((measurable_const.indicator hA).comp (by fun_prop))) using 1
    funext z
    exact hEq z.1 z.2
  exact Measurable.subtype_mk hmeasure

/-- A bounded window used to approximate a locally finite measure on the line. -/
def translationWindow (n : ℕ) : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)

/-- Finiteness on the standard compact exhaustion of the real line. -/
def LocallyFiniteOnTranslationWindows (μ : Measure ℝ) : Prop :=
  ∀ n : ℕ, μ (translationWindow n) < ⊤

theorem measurableSet_locallyFiniteOnTranslationWindows :
    MeasurableSet {μ : Measure ℝ | LocallyFiniteOnTranslationWindows μ} := by
  rw [show {μ : Measure ℝ | LocallyFiniteOnTranslationWindows μ} =
      ⋂ n : ℕ, {μ | μ (translationWindow n) < ⊤} by
        ext μ
        simp [LocallyFiniteOnTranslationWindows]]
  apply MeasurableSet.iInter
  intro n
  exact (measurableSet_Iio : MeasurableSet (Set.Iio (⊤ : ℝ≥0∞))).preimage
    (Measure.measurable_coe measurableSet_Icc)

/-- A countable measurable partition of the line obtained by disjointizing the compact windows. -/
def translationShell (n : ℕ) : Set ℝ := disjointed translationWindow n

theorem translationShell_subset_window n :
    translationShell n ⊆ translationWindow n :=
  disjointed_subset _ _

theorem translationShell_pairwise_disjoint :
    Pairwise (Disjoint on translationShell) :=
  disjoint_disjointed _

theorem translationShell_iUnion : (⋃ n, translationShell n) = Set.univ := by
  change (⋃ n, disjointed translationWindow n) = Set.univ
  rw [iUnion_disjointed]
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  refine ⟨n, ?_⟩
  exact abs_le.mp (le_of_lt (by exact_mod_cast hn))

theorem measurableSet_translationShell n : MeasurableSet (translationShell n) := by
  change MeasurableSet (disjointed translationWindow n)
  rw [disjointed_eq_inter_compl]
  refine measurableSet_Icc.inter ?_
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact (measurableSet_Icc : MeasurableSet (translationWindow i)).compl

/-- Restrict a measure to a measurable set, retaining it as a finite measure when the mass is
finite and using zero as a measurable fallback otherwise. -/
noncomputable def finiteRestrictionOnSet (A : Set ℝ) (μ : Measure ℝ) : FiniteMeasure ℝ :=
  if h : μ A < ⊤ then
    ⟨μ.restrict A, (MeasureTheory.isFiniteMeasure_restrict).2 (ne_of_lt h)⟩
  else 0

theorem measurable_finiteRestrictionOnSet A (hA : MeasurableSet A) :
    Measurable (finiteRestrictionOnSet A) := by
  have hbase : Measurable (fun μ : Measure ℝ => (finiteRestrictionOnSet A μ : Measure ℝ)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have heq : (fun μ : Measure ℝ => (finiteRestrictionOnSet A μ : Measure ℝ) s) =
        fun μ => if h : μ A < ⊤ then μ (s ∩ A) else 0 := by
      funext μ
      by_cases h : μ A < ⊤
      · simp [finiteRestrictionOnSet, h, Measure.restrict_apply hs]
      · simp [finiteRestrictionOnSet, h]
    rw [heq]
    exact Measurable.ite ((measurableSet_Iio : MeasurableSet (Set.Iio (⊤ : ℝ≥0∞))).preimage (Measure.measurable_coe hA)) (Measure.measurable_coe (hs.inter hA)) measurable_const
  exact Measurable.subtype_mk hbase

/-- A globally measurable extension of translation to locally finite measures. It is the sum of
the translated restrictions to a measurable disjoint exhaustion; on locally finite measures this
agrees with translating the original measure. -/
noncomputable def locallyFiniteTranslation (z : ℝ × Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n =>
    ((finiteRestrictionOnSet (translationShell n) z.2).map (fun s => s + z.1) : Measure ℝ)
  )

theorem measurable_locallyFiniteTranslation : Measurable locallyFiniteTranslation := by
  let terms : (ℝ × Measure ℝ) → ℕ → Measure ℝ := fun z n =>
    ((finiteRestrictionOnSet (translationShell n) z.2).map (fun s => s + z.1) : Measure ℝ)
  change Measurable (fun z : ℝ × Measure ℝ => Measure.sum (terms z))
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hterm n : Measurable (fun z : ℝ × Measure ℝ => terms z n A) := by
    dsimp [terms]
    exact (Measure.measurable_coe hA).comp (measurable_subtype_coe.comp (measurable_translateFiniteMeasure.comp (measurable_fst.prodMk ((measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp measurable_snd))))
  have hsum (z : ℝ × Measure ℝ) := Measure.sum_apply (terms z) hA
  convert Measurable.tsum (L := SummationFilter.unconditional ℕ) hterm using 1
  funext z
  exact hsum z

theorem locallyFiniteTranslation_eq_map
    t (μ : Measure ℝ) (hμ : LocallyFiniteOnTranslationWindows μ) :
    locallyFiniteTranslation (t, μ) = μ.map (fun s => s + t) := by
  classical
  let D := translationShell
  have hfinite n : μ (D n) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (translationShell_subset_window n))
    exact hμ n
  have hterm n :
      ((finiteRestrictionOnSet (D n) μ).map (fun s => s + t) : Measure ℝ) =
        (μ.restrict (D n)).map (fun s => s + t) := by
    rw [(show finiteRestrictionOnSet (D n) μ = ⟨μ.restrict (D n), (MeasureTheory.isFiniteMeasure_restrict).2 (ne_of_lt (hfinite n))⟩ by apply Subtype.ext; simp [finiteRestrictionOnSet, hfinite n])]
    rfl
  calc
    locallyFiniteTranslation (t, μ) =
        Measure.sum (fun n => (μ.restrict (D n)).map (fun s => s + t)) := by
          simp only [locallyFiniteTranslation, D]
          congr 1
          funext n
          exact hterm n
    _ = (Measure.sum (fun n => μ.restrict (D n))).map (fun s => s + t) :=
      (Measure.map_sum (show Measurable (fun s => s + t) by fun_prop).aemeasurable).symm
    _ = μ.map (fun s => s + t) := by rw [(show Measure.sum (fun n => μ.restrict (D n)) = μ by rw [← Measure.restrict_iUnion translationShell_pairwise_disjoint (fun n => measurableSet_translationShell n), translationShell_iUnion, Measure.restrict_univ])]

end DOZZ.Proofs

end
