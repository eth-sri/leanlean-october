module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The oriented interval primitive of a real measure with a continuous scalar weight. -/
def bellmanMeasurePrimitive (μ : Measure ℝ) (g : ℝ → ℝ) (a y : ℝ) : ℝ :=
  ∫ z in a..y, g z ∂μ

/-- A continuous weight is integrable on every finite interval of a locally finite real
measure. -/
theorem bellmanMeasureWeight_intervalIntegrable (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable g μ a b := hg.continuousOn.intervalIntegrable

/-- The interval primitive of an arbitrary locally finite measure is measurable, even with
atoms. -/
theorem bellmanMeasurePrimitive_stronglyMeasurable (μ : Measure ℝ) [SFinite μ]
    (g : ℝ → ℝ) (hg : Measurable g) (a : ℝ) :
    StronglyMeasurable (bellmanMeasurePrimitive μ g a) := by
  let A : Set (ℝ × ℝ) := {w | a < w.2 ∧ w.2 ≤ w.1}
  let B : Set (ℝ × ℝ) := {w | w.1 < w.2 ∧ w.2 ≤ a}
  have hA : MeasurableSet A := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hB : MeasurableSet B := by
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have ha := (((hg.comp measurable_snd).indicator hA).stronglyMeasurable).integral_prod_right' (ν := μ)
  have hb := (((hg.comp measurable_snd).indicator hB).stronglyMeasurable).integral_prod_right' (ν := μ)
  have he : bellmanMeasurePrimitive μ g a =
      (fun y => ∫ z, A.indicator (fun w => g w.2) (y, z) ∂μ) -
      (fun y => ∫ z, B.indicator (fun w => g w.2) (y, z) ∂μ) := by
    funext y
    unfold bellmanMeasurePrimitive intervalIntegral
    have heA : (fun z => A.indicator (fun w => g w.2) (y, z)) =
        (Ioc a y).indicator g := by
      funext z
      rfl
    have heB : (fun z => B.indicator (fun w => g w.2) (y, z)) =
        (Ioc y a).indicator g := by
      funext z
      rfl
    simp
    rw [heA, heB, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rw [he]
  exact ha.sub hb

/-- Oriented measure primitives have the exact additive interval increment. -/
theorem bellmanMeasurePrimitive_sub (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (a b y : ℝ) :
    bellmanMeasurePrimitive μ g a y - bellmanMeasurePrimitive μ g a b =
      ∫ z in b..y, g z ∂μ := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (bellmanMeasureWeight_intervalIntegrable μ g hg a b)
    (bellmanMeasureWeight_intervalIntegrable μ g hg b y)
  change (∫ z in a..y, g z ∂μ) - (∫ z in a..b, g z ∂μ) = _
  linarith


/-- The primitive is bounded by the integral of |g| on any collar containing zero and x. -/
theorem bellmanMeasurePrimitive_norm_bound (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (a b x : ℝ) (hx : x ∈ Icc a b) :
    ‖bellmanMeasurePrimitive μ g 0 x‖ ≤
      ∫ z in Icc (min 0 a) (max 0 b), ‖g z‖ ∂μ := by
  have hs : uIoc 0 x ⊆ Icc (min 0 a) (max 0 b) := by
    intro z hz
    rcases le_total 0 x with h | h
    · rw [uIoc_of_le h] at hz
      exact ⟨(min_le_left 0 a).trans hz.1.le,
        hz.2.trans (hx.2.trans (le_max_right 0 b))⟩
    · rw [uIoc_of_ge h] at hz
      exact ⟨(min_le_right 0 a).trans (hx.1.trans hz.1.le),
        hz.2.trans (le_max_left 0 b)⟩
  have hi : IntegrableOn (fun z => ‖g z‖) (Icc (min 0 a) (max 0 b)) μ :=
    hg.norm.continuousOn.integrableOn_Icc
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_mono_set hi (ae_of_all _ fun z => norm_nonneg (g z))
      (ae_of_all _ fun z hz => hs hz))

/-- A weighted measure primitive is Lebesgue integrable on every compact real interval. -/
theorem bellmanMeasurePrimitive_integrableOn_Icc (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    IntegrableOn (bellmanMeasurePrimitive μ g 0) (Icc a b) volume := by
  apply (integrable_const (∫ z in Icc (min 0 a) (max 0 b), ‖g z‖ ∂μ)).mono' (bellmanMeasurePrimitive_stronglyMeasurable μ g hg.measurable 0).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact bellmanMeasurePrimitive_norm_bound μ g hg a b x hx

/-- The actual weighted measure primitive is locally Lebesgue integrable. -/
theorem bellmanMeasurePrimitive_locallyIntegrable (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) :
    LocallyIntegrable (bellmanMeasurePrimitive μ g 0) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact bellmanMeasurePrimitive_integrableOn_Icc μ g hg (x - 1) (x + 1)


/-- A weighted measure primitive satisfies the weak derivative identity on a test collar. -/
theorem bellmanMeasurePrimitive_weak_Icc (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (r R : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : tsupport φ ⊆ Ioo r R) :
    (∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x) =
      -∫ z in Ioc r R, g z * φ z ∂μ  := by
  have bellman_measure_triangle_swap (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] (r : ℝ) (R : ℝ) (g ψ : ℝ → ℝ) (hg : Continuous g) (hψ : Continuous ψ) :
      (∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ) =
      ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
    let ν := μ.restrict (Ioc r R)
    let νvol := volume.restrict (Icc r R)
    let T : Set (ℝ × ℝ) := {w | w.1 ≤ w.2}
    have hT : MeasurableSet T := (isClosed_le continuous_fst continuous_snd).measurableSet
    have hgi : Integrable g ν := hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hψi : Integrable ψ νvol := hψ.continuousOn.integrableOn_Icc
    have ht := (hgi.mul_prod hψi).indicator hT
    have hleft : (∫ x, ∫ z, T.indicator (fun w => g w.1 * ψ w.2) (z, x)
        ∂ν ∂νvol) = ∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change (∫ z, T.indicator (fun w => g w.1 * ψ w.2) (z, x) ∂ν) =
        ∫ z in Ioc r x, g z * ψ x ∂μ
      have he : (fun z => T.indicator (fun w => g w.1 * ψ w.2) (z, x)) =
          (Iic x).indicator (fun z => g z * ψ x) := by
        funext z
        rfl
      rw [he, integral_indicator measurableSet_Iic]
      change (∫ z, g z * ψ x ∂(μ.restrict (Ioc r R)).restrict (Iic x)) = _
      rw [Measure.restrict_restrict measurableSet_Iic]
      have hs : Iic x ∩ Ioc r R = Ioc r x := by
        ext z
        change (z ≤ x ∧ r < z ∧ z ≤ R) ↔ r < z ∧ z ≤ x
        constructor
        · exact fun h => ⟨h.2.1, h.1⟩
        · exact fun h => ⟨h.2, h.1, h.2.trans hx.2⟩
      rw [hs]
    have hright : (∫ z, ∫ x, T.indicator (fun w => g w.1 * ψ w.2) (z, x)
        ∂νvol ∂ν) = ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z hz
      change (∫ x, T.indicator (fun w => g w.1 * ψ w.2) (z, x) ∂νvol) =
        ∫ x in Icc z R, g z * ψ x
      have he : (fun x => T.indicator (fun w => g w.1 * ψ w.2) (z, x)) =
          (Ici z).indicator (fun x => g z * ψ x) := by
        funext x
        rfl
      rw [he, integral_indicator measurableSet_Ici]
      change (∫ x, g z * ψ x ∂(volume.restrict (Icc r R)).restrict (Ici z)) = _
      rw [Measure.restrict_restrict measurableSet_Ici]
      have hs : Ici z ∩ Icc r R = Icc z R := by
        ext x
        change (z ≤ x ∧ r ≤ x ∧ x ≤ R) ↔ z ≤ x ∧ x ≤ R
        constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, hz.1.le.trans h.1, h.2⟩
      rw [hs]
    calc
      _ = ∫ x, ∫ z, T.indicator (fun w => g w.1 * ψ w.2) (z, x) ∂ν ∂νvol :=
        hleft.symm
      _ = ∫ z, ∫ x, T.indicator (fun w => g w.1 * ψ w.2) (z, x) ∂νvol ∂ν :=
        integral_integral_swap ht.swap
      _ = _ := hright
  have hφd := (contDiff_infty_iff_deriv.mp hφ).2
  have he : (∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x) =
      ∫ x in Icc r R, ∫ z in Ioc r x, g z * deriv φ x ∂μ := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change bellmanMeasurePrimitive μ g r x * deriv φ x =
      ∫ z in Ioc r x, g z * deriv φ x ∂μ
    rw [bellmanMeasurePrimitive, intervalIntegral.integral_of_le hx.1, integral_mul_const]
  rw [he, bellman_measure_triangle_swap μ r R g (deriv φ) hg hφd.continuous]
  have ht : (∫ z in Ioc r R, (∫ x in Icc z R, g z * deriv φ x) ∂μ) =
      ∫ z in Ioc r R, -(g z * φ z) ∂μ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    change (∫ x in Icc z R, g z * deriv φ x) = -(g z * φ z)
    rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hz.2,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc
        (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hz.2,
      (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl R) (hs h).2))]
    ring
  rw [ht, integral_neg]

/-- The primitive based at zero has exactly the weighted measure as its distributional
derivative. -/
theorem bellmanMeasurePrimitive_weak (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) = -∫ x, g x * φ x ∂μ := by
  by_cases hn : (tsupport φ).Nonempty
  · obtain ⟨r₀, _, hmin⟩ := hcφ.exists_isMinOn hn continuousOn_id
    obtain ⟨R₀, _, hmax⟩ := hcφ.exists_isMaxOn hn continuousOn_id
    let r := r₀ - 1
    let R := R₀ + 1
    have hs : tsupport φ ⊆ Ioo r R := by
      intro x hx
      have hl : r₀ ≤ x := hmin hx
      have hr : x ≤ R₀ := hmax hx
      dsimp [r, R]
      constructor <;> linarith
    have hdr := tsupport_deriv_subset.trans hs
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hlhs : (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) =
        ∫ x in Icc r R, bellmanMeasurePrimitive μ g 0 x * deriv φ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport
        (fun hd => hx ⟨(hdr hd).1.le, (hdr hd).2.le⟩), mul_zero]
    have hrhs : (∫ x, g x * φ x ∂μ) = ∫ x in Ioc r R, g x * φ x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport
        (fun hd => hx ⟨(hs hd).1, (hs hd).2.le⟩), mul_zero]
    have he : (∫ x in Icc r R, bellmanMeasurePrimitive μ g 0 x * deriv φ x) =
        ∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x := by
      have hi : IntegrableOn (fun x => bellmanMeasurePrimitive μ g 0 x * deriv φ x)
          (Icc r R) volume :=
        ((bellmanMeasurePrimitive_locallyIntegrable μ g hg).integrableOn_isCompact
          isCompact_Icc).mul_continuousOn hφd.continuous.continuousOn isCompact_Icc
      have hc : IntegrableOn (fun x => bellmanMeasurePrimitive μ g 0 r * deriv φ x)
          (Icc r R) volume :=
        (hφd.continuous.continuousOn.integrableOn_Icc).const_mul _
      have hfun : (fun x => bellmanMeasurePrimitive μ g r x * deriv φ x) =
          (fun x => bellmanMeasurePrimitive μ g 0 x * deriv φ x -
            bellmanMeasurePrimitive μ g 0 r * deriv φ x) := by
        funext x
        have hp := bellmanMeasurePrimitive_sub μ g hg 0 r x
        change bellmanMeasurePrimitive μ g 0 x - bellmanMeasurePrimitive μ g 0 r =
          bellmanMeasurePrimitive μ g r x at hp
        rw [← hp]
        ring
      have hle : r ≤ R := by
        obtain ⟨x, hx⟩ := hn
        exact (hs hx).1.le.trans (hs hx).2.le
      have hdInt : (∫ x in Icc r R, deriv φ x) = 0 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc
            (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hle,
          (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl r) (hs h).1)), (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl R) (hs h).2)), sub_self]
      rw [hfun, integral_sub hi hc, integral_const_mul, hdInt, mul_zero, sub_zero]
    rw [hlhs, hrhs, he]
    exact bellmanMeasurePrimitive_weak_Icc μ g hg r R φ hφ hs
  · have hz : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
    rw [hz, deriv_zero]
    simp

end HypoellipticAleksandrov.KineticAleksandrov

