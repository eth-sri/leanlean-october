module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeTriangle
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitive
import Mathlib.MeasureTheory.Integral.Prod

/-! # The actual distributional derivative of a weighted measure primitive -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- A weighted measure primitive satisfies the weak derivative identity on a test collar. -/
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
    have hdr : tsupport (deriv φ) ⊆ Ioo r R := tsupport_deriv_subset.trans hs
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hr0 : φ r = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl r) (hs h).1)
    have hR0 : φ R = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl R) (hs h).2)
    have hlhs : (∫ x, bellmanMeasurePrimitive μ g 0 x * deriv φ x) =
        ∫ x in Icc r R, bellmanMeasurePrimitive μ g 0 x * deriv φ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := deriv φ)
        (fun hd => hx ⟨(hdr hd).1.le, (hdr hd).2.le⟩), mul_zero]
    have hrhs : (∫ x, g x * φ x ∂μ) = ∫ x in Ioc r R, g x * φ x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := φ)
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
          hr0, hR0, sub_self]
      rw [hfun, integral_sub hi hc, integral_const_mul, hdInt, mul_zero, sub_zero]
    rw [hlhs, hrhs, he]
    have hφd := (contDiff_infty_iff_deriv.mp hφ).2
    have hR := image_eq_zero_of_notMem_tsupport
      (fun h => (lt_irrefl R) (hs h).2)
    have he : (∫ x in Icc r R, bellmanMeasurePrimitive μ g r x * deriv φ x) =
        ∫ x in Icc r R, ∫ z in Ioc r x, g z * deriv φ x ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      change bellmanMeasurePrimitive μ g r x * deriv φ x =
        ∫ z in Ioc r x, g z * deriv φ x ∂μ
      rw [bellmanMeasurePrimitive, intervalIntegral.integral_of_le hx.1, integral_mul_const]
    have _h_xinl_1 : (∫ x in Icc r R, ∫ z in Ioc r x, g z * (deriv φ) x ∂μ) =
        ∫ z in Ioc r R, (∫ x in Icc z R, g z * (deriv φ) x) ∂μ := by
      let ψ := (deriv φ)
      have hψ := hφd.continuous
      let ν := μ.restrict (Ioc r R)
      let νvol := volume.restrict (Icc r R)
      let T : Set (ℝ × ℝ) := {w | w.1 ≤ w.2}
      have hT : MeasurableSet T := (isClosed_le continuous_fst continuous_snd).measurableSet
      have hgi : Integrable g ν := hg.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hψi : Integrable ψ νvol := hψ.continuousOn.integrableOn_Icc
      have hp := hgi.mul_prod hψi
      have ht := hp.indicator hT
      have hleft : (∫ x, ∫ z, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)
          ∂ν ∂νvol) = ∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro x hx
        change (∫ z, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x) ∂ν) =
          ∫ z in Ioc r x, g z * ψ x ∂μ
        have he : (fun z => T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)) =
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
      have hright : (∫ z, ∫ x, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)
          ∂νvol ∂ν) = ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro z hz
        change (∫ x, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x) ∂νvol) =
          ∫ x in Icc z R, g z * ψ x
        have he : (fun x => T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x)) =
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
        _ = ∫ x, ∫ z, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x) ∂ν ∂νvol :=
          hleft.symm
        _ = ∫ z, ∫ x, T.indicator (fun w : ℝ × ℝ => g w.1 * ψ w.2) (z, x) ∂νvol ∂ν :=
          integral_integral_swap ht.swap
        _ = _ := hright
    rw [he, _h_xinl_1]
    have ht : (∫ z in Ioc r R, (∫ x in Icc z R, g z * deriv φ x) ∂μ) =
        ∫ z in Ioc r R, -(g z * φ z) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro z hz
      change (∫ x in Icc z R, g z * deriv φ x) = -(g z * φ z)
      rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hz.2,
        intervalIntegral.integral_deriv_of_contDiffOn_Icc
          (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hz.2,
        hR]
      ring
    rw [ht, integral_neg]
  · have hz : φ = 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
    rw [hz, deriv_zero]
    simp only [Pi.zero_apply, mul_zero, integral_zero, neg_zero]

end HypoellipticAleksandrov.KineticAleksandrov
