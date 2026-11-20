/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Disjointed
public import DOZZ.GMC.MeasurableIntegrals

/-! # Joint translation of finite measures -/

@[expose] public section

open MeasureTheory
open Function
open scoped ENNReal

namespace DOZZ.Proofs

/-- Translation is jointly measurable on finite measures. The proof checks evaluations on
measurable sets and writes each evaluation as an integral of a jointly measurable indicator. -/
theorem measurable_translateFiniteMeasure :
    Measurable (fun z : ℝ × FiniteMeasure ℝ => z.2.map (fun s => s + z.1)) := by
  have hmeasure : Measurable (fun z : ℝ × FiniteMeasure ℝ =>
      (z.2 : Measure ℝ).map (fun s => s + z.1)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    let integrand : ℝ × ℝ → ℝ≥0∞ := fun z => A.indicator (fun _ => 1) (z.2 + z.1)
    have htrans : Measurable (fun z : ℝ × ℝ => z.2 + z.1) := by fun_prop
    have hintegrand : Measurable integrand := (measurable_const.indicator hA).comp htrans
    have hint := measurable_lintegral_finiteMeasure_parameter (f := integrand) hintegrand
    have hEq (t : ℝ) (μ : FiniteMeasure ℝ) :
        ((μ : Measure ℝ).map (fun s => s + t)) A =
          ∫⁻ s, A.indicator (fun _ => 1) (s + t) ∂(μ : Measure ℝ) := by
      exact Eq.mpr
        (id
          (congrArg (fun _a => _a = ∫⁻ (s : ℝ), A.indicator (fun x => 1) (s + t) ∂↑μ)
            (Measure.map_apply (Measurable.add_const measurable_id' t) hA)))
        (have hs := MeasurableSet.preimage hA (Measurable.add_const measurable_id' t);
        Trans.trans (Eq.symm (lintegral_indicator_one hs))
          (Eq.refl (∫⁻ (s : ℝ), ((fun s => s + t) ⁻¹' A).indicator (fun x => 1) s ∂↑μ)))
    convert hint using 1
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
  have hwindow : MeasurableSet (translationWindow n) := measurableSet_Icc
  exact (measurableSet_Iio : MeasurableSet (Set.Iio (⊤ : ℝ≥0∞))).preimage
    (Measure.measurable_coe hwindow)

/-- A countable measurable partition of the line obtained by disjointizing the compact windows. -/
def translationShell (n : ℕ) : Set ℝ := disjointed translationWindow n

theorem translationShell_subset_window (n : ℕ) :
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
  have hbound  := le_of_lt (by exact_mod_cast hn)
  exact abs_le.mp hbound

theorem measurableSet_translationShell (n : ℕ) : MeasurableSet (translationShell n) := by
  change MeasurableSet (disjointed translationWindow n)
  rw [disjointed_eq_inter_compl]
  refine measurableSet_Icc.inter ?_
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact (measurableSet_Icc : MeasurableSet (translationWindow i)).compl

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
  have hterm (n : ℕ) : Measurable (fun z : ℝ × Measure ℝ => terms z n A) := by
    exact id
      (have hres :=
        Measurable.comp (measurable_finiteRestrictionOnSet (translationShell n) (measurableSet_translationShell n))
          measurable_snd;
      have hpair := Measurable.prodMk measurable_fst hres;
      have hmap := Measurable.comp measurable_translateFiniteMeasure hpair;
      Measurable.comp (Measure.measurable_coe hA) (Measurable.comp measurable_subtype_coe hmap))
  have hsum (z : ℝ × Measure ℝ)  :=
    Measure.sum_apply (terms z) hA
  convert Measurable.tsum (L := SummationFilter.unconditional ℕ) hterm using 1
  funext z
  exact hsum z

theorem locallyFiniteTranslation_eq_map
    (t : ℝ) (μ : Measure ℝ) (hμ : LocallyFiniteOnTranslationWindows μ) :
    locallyFiniteTranslation (t, μ) = μ.map (fun s => s + t) := by
  classical
  let D  := translationShell
  have hDmeas  := fun n => measurableSet_translationShell n
  have hDdisj  := translationShell_pairwise_disjoint
  have hDunion  := translationShell_iUnion
  have hfinite (n : ℕ) : μ (D n) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (translationShell_subset_window n))
    exact hμ n
  have hrestrict : Measure.sum (fun n => μ.restrict (D n)) = μ := by
    rw [← Measure.restrict_iUnion hDdisj hDmeas, hDunion, Measure.restrict_univ]
  have hterm (n : ℕ) :
      ((finiteRestrictionOnSet (D n) μ).map (fun s => s + t) : Measure ℝ) =
        (μ.restrict (D n)).map (fun s => s + t) := by
    have hr : finiteRestrictionOnSet (D n) μ =
        ⟨μ.restrict (D n), (MeasureTheory.isFiniteMeasure_restrict).2 (ne_of_lt (hfinite n))⟩ := by
      apply Subtype.ext
      simp [finiteRestrictionOnSet, hfinite n]
    rw [hr]
    rfl
  have hmeas : Measurable (fun s : ℝ => s + t) := by fun_prop
  calc
    locallyFiniteTranslation (t, μ) =
        Measure.sum (fun n => (μ.restrict (D n)).map (fun s => s + t)) := by
          simp only [locallyFiniteTranslation, D]
          congr 1
          funext n
          exact hterm n
    _ = (Measure.sum (fun n => μ.restrict (D n))).map (fun s => s + t) :=
      (Measure.map_sum hmeas.aemeasurable).symm
    _ = μ.map (fun s => s + t) := by rw [hrestrict]

end DOZZ.Proofs

end
