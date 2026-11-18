module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- A smooth real function has a smooth integral primitive. -/
theorem capacity_primitive_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ x in a..v, f x) := by
  have hd (v : ℝ) : HasDerivAt (fun v => ∫ x in a..v, f x) (f v) v :=
    intervalIntegral.integral_hasDerivAt_right (hf.continuous.intervalIntegrable a v)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun v => (hd v).differentiableAt, ?_⟩
  rw [(funext fun v => (hd v).deriv)]
  exact hf

/-- The cumulative integral of a nonnegative compactly supported function is bounded
by its total integral when its support lies to the right of the starting point. -/
theorem capacity_cumulative_bounds {f : ℝ → ℝ} {a : ℝ}
    (hi : Integrable f volume) (hn : ∀ v, 0 ≤ f v)
    (hs : tsupport f ⊆ Ioi a) (v : ℝ) :
    0 ≤ (∫ x in a..v, f x) ∧ (∫ x in a..v, f x) ≤ ∫ x, f x := by
  by_cases hav : a ≤ v
  · rw [intervalIntegral.integral_of_le hav]
    exact ⟨integral_nonneg (fun x => hn x),
      setIntegral_le_integral hi (Filter.Eventually.of_forall hn)⟩
  · have hva : v ≤ a := (not_le.mp hav).le
    have hz : (∫ x in v..a, f x) = 0 := by
      rw [intervalIntegral.integral_of_le hva]
      apply integral_eq_zero_of_ae
      apply (ae_restrict_iff' measurableSet_Ioc).mpr
      exact Filter.Eventually.of_forall fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun ht => (not_lt_of_ge hx.2) (hs ht))
    rw [intervalIntegral.integral_symm, hz, neg_zero]
    exact ⟨le_rfl, integral_nonneg hn⟩


/-- A smooth convex test with second derivative twice a compact interval majorant. -/
theorem exists_capacity_test (E : Interval) :
    ∃ chi Phi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) ∧ ContDiff ℝ (⊤ : ℕ∞) Phi ∧
      (∀ v, deriv (deriv Phi) v = 2 * chi v) ∧
      (∀ v, |deriv Phi v| ≤ 2 * (E.hi - E.lo))  := by
  have exists_capacity_cutoff :
      ∃ chi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ Ioo (E.lo - (E.hi - E.lo) / 2) (E.hi + (E.hi - E.lo) / 2) ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) := by
    let a := E.lo - (E.hi - E.lo) / 2
    let b := E.hi + (E.hi - E.lo) / 2
    have hsub : Icc E.lo E.hi ⊆ Ioo a b := by
      intro v hv
      dsimp only [a, b]
      constructor <;> linarith [E.ordered, hv.1, hv.2]
    obtain ⟨chi, hs, hc, hsup, h01, h1⟩ :=
      exists_smooth_bump_of_isCompact_subset_isOpen (isCompact_Icc : IsCompact (Icc E.lo E.hi))
        isOpen_Ioo hsub
    refine ⟨chi, hs, hc, hsup, h01, h1, ?_⟩
    have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
    have he : (∫ v, chi v) = ∫ v in Ioo a b, chi v := by
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun v hv => image_eq_zero_of_notMem_tsupport (fun ht => hv (hsup ht)))).symm
    rw [he]
    have hm := integral_mono (hi.restrict (s := Ioo a b)) (integrable_const 1)
      (fun v => (h01 v).2)
    have hab : 0 ≤ b - a := by dsimp only [a, b]; linarith [E.ordered]
    have hv : (∫ _v in Ioo a b, 1) = b - a := by
      simp [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.toReal_ofReal hab]
    rw [hv] at hm
    exact hm.trans_eq (by dsimp only [a, b]; ring)
  obtain ⟨chi, hs, hc, hsup, hn, h1, hm⟩ := exists_capacity_cutoff
  let a := E.lo - (E.hi - E.lo) / 2
  let F : ℝ → ℝ := fun v => 2 * (∫ x in a..v, chi x) - ∫ x, chi x
  let Phi : ℝ → ℝ := fun v => ∫ x in 0..v, F x
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_const.mul (capacity_primitive_smooth hs a)).sub contDiff_const
  have hdF (v : ℝ) : HasDerivAt F (2 * chi v) v := by
    exact ((intervalIntegral.integral_hasDerivAt_right (hs.continuous.intervalIntegrable a v) hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt).const_mul 2).sub_const _
  have hdPhi (v : ℝ) : HasDerivAt Phi (F v) v :=
    intervalIntegral.integral_hasDerivAt_right (hF.continuous.intervalIntegrable 0 v)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
  have he := funext fun v => (hdPhi v).deriv
  refine ⟨chi, Phi, hs, hc, hn, h1, hm, capacity_primitive_smooth hF 0, ?_, ?_⟩
  · intro v
    rw [he]
    exact (hdF v).deriv
  · intro v
    rw [he]
    have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
    have hsupport : tsupport chi ⊆ Ioi a := fun x hx => (hsup hx).1
    obtain ⟨hlo, hhi⟩ := capacity_cumulative_bounds hi (fun x => (hn x).1) hsupport v
    have ht : 0 ≤ ∫ x, chi x := integral_nonneg (fun x => (hn x).1)
    apply abs_le.mpr
    constructor <;> linarith


/-- The forward operator on a velocity-only test has only its diffusion term. -/
theorem capacity_velocity_operator (a : ℝ → ℝ → ℝ) (Phi : ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => Phi (q.velocity 0)) p =
      a (p.position 0) (p.velocity 0) * deriv (deriv Phi) (p.velocity 0) := by
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp [kineticTimeDerivative, deriv_const]

/-- Raw physical smoothness of a smooth velocity-only test. -/
theorem capacity_velocity_smooth {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) :
    ContDiff ℝ (⊤ : ℕ∞)
      ((fun q : Point => Phi (q.velocity 0)) ∘ (KineticPoint.equivProd 1).symm) :=
  hPhi.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.snd)

/-- A derivative bound controls differences of the convex test on the closed strip. -/
theorem capacity_test_difference {Phi : ℝ → ℝ} (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ v, |deriv Phi v| ≤ D)
    (H : Interval) {x y : ℝ} (hx : x ∈ Icc H.lo H.hi) (hy : y ∈ Icc H.lo H.hi) :
    |Phi y - Phi x| ≤ D * (H.hi - H.lo) := by
  have hb : |y - x| ≤ H.hi - H.lo := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  simpa using (Convex.norm_image_sub_le_of_norm_deriv_le (fun v (_ : v ∈ (univ : Set ℝ)) => hPhi.differentiable (by norm_num) v) (fun v (_ : v ∈ (univ : Set ℝ)) => by simpa using hd v) convex_univ (mem_univ x) (mem_univ y)).trans (mul_le_mul_of_nonneg_left hb hD)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

