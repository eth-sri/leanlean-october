module

public import PDEFoundation.Sobolev.OneDimensional.Primitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.MeasureTheory.Integral.Prod

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Scalar weak identity for one-dimensional interval primitives

This file proves the bounded scalar distributional identity underlying the
one-dimensional Sobolev bridge.  It is deliberately scalar: transport to the
native `Vec 1` weak-derivative interface belongs in a separate foundational
measure-equivalence file.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- On an oriented interval with ordered endpoints, the interval primitive is
the corresponding closed-interval set integral. -/
theorem intervalPrimitive_eq_setIntegral_Icc
    {r x : ℝ} (hrx : r ≤ x) (g : ℝ → ℝ) :
    intervalPrimitive r g x = ∫ y in Icc r x, g y := by
  rw [intervalPrimitive, intervalIntegral.integral_of_le hrx,
    ← integral_Icc_eq_integral_Ioc]

/-- Triangular Fubini for a real measure and real Lebesgue measure, retaining atoms of μ. -/
theorem setIntegral_Ioc_Icc_swap (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (r R : ℝ) (g ψ : ℝ → ℝ) (hg : IntegrableOn g (Icc r R) μ) (hψ : ContinuousOn ψ (Icc r R)) :
    (∫ x in Icc r R, ∫ z in Ioc r x, g z * ψ x ∂μ) =
      ∫ z in Ioc r R, (∫ x in Icc z R, g z * ψ x) ∂μ := by
  let ν := μ.restrict (Ioc r R)
  let νvol := volume.restrict (Icc r R)
  let T : Set (ℝ × ℝ) := {w | w.1 ≤ w.2}
  have hT : MeasurableSet T := (isClosed_le continuous_fst continuous_snd).measurableSet
  have hgi : Integrable g ν := hg.mono_set Ioc_subset_Icc_self
  have hψi : Integrable ψ νvol := hψ.integrableOn_Icc
  have hp : Integrable (fun w : ℝ × ℝ => g w.1 * ψ w.2) (ν.prod νvol) := hgi.mul_prod hψi
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


/-- Triangular Fubini on a closed real interval. -/
theorem setIntegral_setIntegral_Icc_swap
    {r R : ℝ} {g ψ : ℝ → ℝ}
    (hg : IntegrableOn g (Icc r R) volume)
    (hψ : ContinuousOn ψ (Icc r R)) :
    ∫ x in Icc r R, (∫ y in Icc r x, g y * ψ x) =
      ∫ y in Icc r R, (∫ x in Icc y R, g y * ψ x) := by
  simpa only [integral_Icc_eq_integral_Ioc] using setIntegral_Ioc_Icc_swap volume r R g ψ hg hψ

/-- A compactly supported `C¹` test function has the expected derivative
tail integral on a collar containing its support. -/
theorem setIntegral_deriv_tail_eq_neg
    {r R y : ℝ} (hy : y ∈ Icc r R) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo r R) :
    ∫ x in Icc y R, deriv φ x = -φ y := by
  have hRzero : φ R = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hR
    exact (not_lt_of_ge le_rfl) (hsupp hR).2
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hy.2,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc hφ.contDiffOn hy.2,
    hRzero]
  ring

/-- The local weak identity for a primitive of a weighted measure; the lower endpoint
is omitted in the measure integral, so no atomlessness assumption is needed. -/
theorem intervalIntegral_weak_identity_Icc (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    {r R : ℝ} {g φ : ℝ → ℝ} (hg : IntegrableOn g (Icc r R) μ) (hφ : ContDiff ℝ 1 φ)
    (hs : tsupport φ ⊆ Ioo r R) :
    (∫ x in Icc r R, (∫ z in r..x, g z ∂μ) * deriv φ x) =
      -∫ z in Ioc r R, g z * φ z ∂μ := by
  have he : (∫ x in Icc r R, (∫ z in r..x, g z ∂μ) * deriv φ x) =
      ∫ x in Icc r R, ∫ z in Ioc r x, g z * deriv φ x ∂μ := by
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    rw [intervalIntegral.integral_of_le hx.1, integral_mul_const]
  rw [he, setIntegral_Ioc_Icc_swap μ r R g (deriv φ) hg
    (hφ.continuous_deriv (by simp)).continuousOn, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
  rw [integral_const_mul, setIntegral_deriv_tail_eq_neg ⟨hz.1.le, hz.2⟩ hφ hs, mul_neg]

/-- The global weak identity is obtained on a collar containing the support of the test.
Changing the base point of the primitive only subtracts a constant. -/
theorem intervalIntegral_weak_identity (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    {g φ : ℝ → ℝ} (hg : LocallyIntegrable g μ)
    (hP : LocallyIntegrable (fun x => ∫ z in (0 : ℝ)..x, g z ∂μ) volume)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, (∫ z in (0 : ℝ)..x, g z ∂μ) * deriv φ x) = -∫ z, g z * φ z ∂μ := by
  obtain ⟨R, hR, hbound⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  let r := -R
  have hrR : r ≤ R := by dsimp [r]; linarith
  have hs : tsupport φ ⊆ Ioo r R := fun x hx => abs_lt.mp (by simpa [Real.norm_eq_abs] using hbound x hx)
  have hds := tsupport_deriv_subset.trans hs
  have hφr : φ r = 0 := image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl r) (hs h).1)
  have hlhs : (∫ x in Icc r R, (∫ z in (0 : ℝ)..x, g z ∂μ) * deriv φ x) =
      ∫ x, (∫ z in (0 : ℝ)..x, g z ∂μ) * deriv φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => mul_eq_zero_of_right _
      (image_eq_zero_of_notMem_tsupport fun hd => hx (Ioo_subset_Icc_self (hds hd)))
  have hrhs : (∫ x in Ioc r R, g x * φ x ∂μ) = ∫ x, g x * φ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => mul_eq_zero_of_right _
      (image_eq_zero_of_notMem_tsupport fun hd => hx (Ioo_subset_Ioc_self (hs hd)))
  let P (x : ℝ) := ∫ z in (0 : ℝ)..x, g z ∂μ
  have hi (a b : ℝ) : IntervalIntegrable g μ a b :=
    intervalIntegrable_iff.2 ((hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have he (x : ℝ) : (∫ z in r..x, g z ∂μ) * deriv φ x = P x * deriv φ x - P r * deriv φ x := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r x)
    change P r + (∫ z in r..x, g z ∂μ) = P x at h
    rw [← h, add_mul, add_sub_cancel_left]
  have hd : ContinuousOn (deriv φ) (Icc r R) := (hφ.continuous_deriv (by simp)).continuousOn
  have hcst : IntegrableOn (fun x => P r * deriv φ x) (Icc r R) := hd.integrableOn_Icc.const_mul _
  have hprim : IntegrableOn (fun x => P x * deriv φ x) (Icc r R) :=
    (hP.integrableOn_isCompact isCompact_Icc).mul_continuousOn hd isCompact_Icc
  have hlocal := intervalIntegral_weak_identity_Icc μ
    (hg.integrableOn_isCompact isCompact_Icc) hφ hs
  simp_rw [he] at hlocal
  rw [integral_sub hprim hcst, integral_const_mul, setIntegral_deriv_tail_eq_neg ⟨le_rfl, hrR⟩ hφ hs,
    hφr, neg_zero, mul_zero, sub_zero, hlhs, hrhs] at hlocal
  exact hlocal

/-- The bounded scalar distributional identity for an interval primitive.
This is intentionally not yet the native-vector weak-derivative theorem. -/
theorem intervalPrimitive_scalar_weak_identity_Icc
    {r R : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc r R) volume) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo r R) :
    ∫ x in Icc r R, intervalPrimitive r g x * deriv φ x =
      -∫ x in Icc r R, g x * φ x := by
  simpa only [intervalPrimitive, integral_Icc_eq_integral_Ioc] using
    intervalIntegral_weak_identity_Icc volume hg hφ hsupp

/-- The bounded scalar weak identity on the open interval.  Atomlessness of
real volume makes the endpoint choice immaterial. -/
theorem intervalPrimitive_scalar_weak_identity_Ioo
    {a b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc a b) volume) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, intervalPrimitive a g x * deriv φ x =
      -∫ x in Ioo a b, g x * φ x := by
  simpa only [restrict_Ioo_eq_restrict_Icc] using
    (intervalPrimitive_scalar_weak_identity_Icc hg hφ hsupp)

end

end PDE
