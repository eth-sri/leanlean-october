module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Measure domination from smooth nonnegative probes (domain domination ingredient)

Outside-context measure theory.  On a finite-dimensional real normed space, a finite measure `ν`
supported on an open set `U` is dominated by a finite measure `μ` as soon as
`∫ f dν ≤ ∫ f dμ` for every smooth compactly supported `f ≥ 0` with `tsupport f ⊆ U`.

* `exists_smooth_bump_of_isCompact_subset_isOpen`: smooth Urysohn bump `1_K ≤ f ≤ 1_V`.
* `measure_le_of_smooth_integral_le`: the domination criterion.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth bump function with compact support inside the open set `V`, equal to one on the
compact set `K ⊆ V`, with values in `[0, 1]`. -/
theorem exists_smooth_bump_of_isCompact_subset_isOpen {K V : Set E} (hK : IsCompact K)
    (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ ∀ x ∈ K, f x = 1 := by
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hdisj : Disjoint _ K :=
    disjoint_compl_left_iff_subset.2 (self_subset_thickening hδ K)
  obtain ⟨f, hfs, hfr, hf0, hf1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K)).isClosed_compl
    hK.isClosed hdisj
  have hsupp : Function.support f ⊆ thickening δ K := by
    intro x hx
    by_contra hxn
    simp_all
  have htsupp : tsupport f ⊆ cthickening δ K :=
    closure_minimal (hsupp.trans (thickening_subset_cthickening δ K)) isClosed_cthickening
  refine ⟨f, hfs, (hK.cthickening).of_isClosed_subset (isClosed_tsupport f) htsupp,
    htsupp.trans hδV, fun x => hfr ⟨x, rfl⟩, fun x hx => (hf1 x).1 hx⟩

/-- Domination criterion: a finite measure `ν` supported on the open set `U` is dominated by the
finite measure `μ` if the integral inequality holds for all smooth compactly supported
nonnegative `f` with `tsupport f ⊆ U`. -/
theorem measure_le_of_smooth_integral_le {U : Set E} (hU : IsOpen U) {ν μ : Measure E}
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (hν : ν.restrict U = ν)
    (h : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x, 0 ≤ f x) → ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ) :
    ν ≤ μ := by
  have hopen : ∀ V : Set E, IsOpen V → V ⊆ U → ν V ≤ μ V := by
    intro V hV hVU
    rw [hV.measure_eq_iSup_isCompact]
    refine iSup_le fun K => iSup_le fun hKV => iSup_le fun hK => ?_
    obtain ⟨f, hfs, hfc, hfV, hf01, hfK⟩ := exists_smooth_bump_of_isCompact_subset_isOpen hK hV hKV
    have hcont : Continuous f := hfs.continuous
    have hnn  := fun x => (hf01 x).1
    have hint_ν : Integrable f ν := hcont.integrable_of_hasCompactSupport hfc
    have hint_μ : Integrable f μ := hcont.integrable_of_hasCompactSupport hfc
    have hle := h f hfs hfc (hfV.trans hVU) hnn
    calc ν K = ∫⁻ x, K.indicator 1 x ∂ν := (lintegral_indicator_one hK.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal _ ∂ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · simp_all
        simp_all
      _ = ENNReal.ofReal _ :=
        (ofReal_integral_eq_lintegral_ofReal hint_ν (Filter.Eventually.of_forall hnn)).symm
      _ ≤ ENNReal.ofReal _ := ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ x, ENNReal.ofReal _ ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint_μ (Filter.Eventually.of_forall hnn)
      _ ≤ ∫⁻ x, V.indicator 1 x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ V
        · simp_all
        · have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hfV hx'))
          simp_all
      _ = μ V := lintegral_indicator_one hV.measurableSet
  rw [Measure.le_iff]
  intro A hA
  have hνA : ν A = ν (A ∩ U) := by
    conv_lhs => rw [← hν]
    rw [Measure.restrict_apply hA]
  have hmain : ν (A ∩ U) ≤ μ (A ∩ U) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨W, hAW, hW, hμW⟩ := Set.exists_isOpen_lt_of_lt _ _ hlt
    have h1 : ν _ ≤ ν _ := measure_mono (subset_inter hAW inter_subset_right)
    have h2  := hopen _ (hW.inter hU) inter_subset_right
    have h3 : μ (W ∩ U) ≤ μ W := measure_mono inter_subset_left
    grind
  rw [hνA]
  exact hmain.trans (measure_mono inter_subset_left)

end HypoellipticAleksandrov.KineticAleksandrov
